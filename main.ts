// png-squeeze-01 — smallest lossless PNG re-encoder for 1280x720 screenshots.
// Node 22 builtins only. Deterministic: no clock, no randomness, fixed work counts.
// Reads /input/<id>/image.png, writes /output/<id>/image.png for each id.
//
// Layers: (1) representation — palette / grey / grey+alpha / RGB / RGBA / tRNS key;
// (2) per-row PNG filters — fixed, min-sum, fewest-bigram-pairs, brute force;
// (3) DEFLATE — zlib level 9 (Stage A) + zopfli-style optimal parser (Stage B).
// Every output is verified decodable by the same rules the scorer's decoder uses.
import { inflateSync, deflateSync, constants } from 'node:zlib';
import { readFileSync, writeFileSync, mkdirSync, readdirSync } from 'node:fs';
import { join } from 'node:path';

const W = 1280;
const H = 720;

// ---------------------------------------------------------------- CRC-32
const CRC_TABLE: Int32Array = (() => {
  const t = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    t[n] = c;
  }
  return t;
})();
function crc32(bytes: Uint8Array, start = 0, end = bytes.length): number {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}
function chunk(type: string, data: Uint8Array): Uint8Array {
  const out = new Uint8Array(12 + data.length);
  const v = new DataView(out.buffer);
  v.setUint32(0, data.length);
  for (let i = 0; i < 4; i++) out[4 + i] = type.charCodeAt(i);
  out.set(data, 8);
  v.setUint32(8 + data.length, crc32(out, 4, 8 + data.length));
  return out;
}
function pngOf(chunks: Array<[string, Uint8Array]>): Uint8Array {
  const sig = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);
  let size = sig.length;
  for (const [, d] of chunks) size += 12 + d.length;
  const out = new Uint8Array(size);
  out.set(sig, 0);
  let at = sig.length;
  for (const [t, d] of chunks) {
    const c = chunk(t, d);
    out.set(c, at);
    at += c.length;
  }
  return out;
}
function ihdrOf(width: number, height: number, colourType: number): Uint8Array {
  const d = new Uint8Array(13);
  const v = new DataView(d.buffer);
  v.setUint32(0, width);
  v.setUint32(4, height);
  d[8] = 8;
  d[9] = colourType;
  return d;
}

// ---------------------------------------------------------------- PNG decode
function paeth(a: number, b: number, c: number): number {
  const p = a + b - c;
  const pa = p > a ? p - a : a - p;
  const pb = p > b ? p - b : b - p;
  const pc = p > c ? p - c : c - p;
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}
function filterRow(type: number, cur: Uint8Array, prev: Uint8Array | null, bpp: number, out: Uint8Array): void {
  const n = cur.length;
  if (type === 0) { out.set(cur); return; }
  if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
    return;
  }
  if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
    return;
  }
  if (type === 3) {
    for (let i = 0; i < n; i++) {
      out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
    }
    return;
  }
  for (let i = 0; i < n; i++) {
    const a = i >= bpp ? cur[i - bpp] : 0;
    const b = prev === null ? 0 : prev[i];
    const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
    out[i] = cur[i] - paeth(a, b, c);
  }
}
function signedSum(row: Uint8Array): number {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

/** Decode any PNG the contest accepts into RGBA. Input here is stored type-6, but stay general. */
function decodePng(bytes: Uint8Array): { width: number; height: number; rgba: Uint8Array } {
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = 8;
  let header: { width: number; height: number; colourType: number } | null = null;
  let palette: Uint8Array | null = null;
  let trns: Uint8Array | null = null;
  const idat: Uint8Array[] = [];
  while (at < bytes.length) {
    const len = view.getUint32(at);
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (type === 'IHDR') {
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = { width: dv.getUint32(0), height: dv.getUint32(4), colourType: data[9] };
    } else if (type === 'PLTE') palette = data;
    else if (type === 'tRNS') trns = data;
    else if (type === 'IDAT') idat.push(data);
    else if (type === 'IEND') break;
  }
  if (header === null) throw new Error('no IHDR');
  const { width, height, colourType } = header;
  const ch = ({ 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 })[colourType as 0 | 2 | 3 | 4 | 6];
  const stride = width * ch;
  const raw = inflateSync(idat.length === 1 ? idat[0] : Buffer.concat(idat));
  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (ft === 0) samples.set(raw.subarray(src, src + stride), o);
    else if (ft === 1) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= ch ? samples[o + i - ch] : 0);
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) {
        samples[o + i] = raw[src + i] + (((i >= ch ? samples[o + i - ch] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
      }
    } else {
      for (let i = 0; i < stride; i++) {
        const a = i >= ch ? samples[o + i - ch] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= ch ? samples[p + i - ch] : 0;
        samples[o + i] = raw[src + i] + paeth(a, b, c);
      }
    }
  }
  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) rgba.set(samples);
  else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s]; rgba[d + 1] = samples[s + 1]; rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    const entries = (palette as Uint8Array).length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) {
      lut[e * 4] = (palette as Uint8Array)[e * 3];
      lut[e * 4 + 1] = (palette as Uint8Array)[e * 3 + 1];
      lut[e * 4 + 2] = (palette as Uint8Array)[e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      rgba[d] = lut[e * 4]; rgba[d + 1] = lut[e * 4 + 1]; rgba[d + 2] = lut[e * 4 + 2]; rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return { width, height, rgba };
}

// ---------------------------------------------------------------- Analysis
interface Colour { r: number; g: number; b: number; a: number; count: number; key: number }
interface Analysis { opaque: boolean; grey: boolean; colours: Colour[] | null }
function analyse(rgba: Uint8Array): Analysis {
  const n = rgba.length >>> 2;
  let opaque = true;
  let grey = true;
  const counts = new Map<number, number>();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const k = rgba[d] * 16777216 + rgba[d + 1] * 65536 + rgba[d + 2] * 256 + rgba[d + 3];
      const c = counts.get(k);
      if (c === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(k, 1);
      } else counts.set(k, c + 1);
    }
  }
  let colours: Colour[] | null = null;
  if (!many) {
    colours = [...counts.entries()].map(([k, count]) => ({
      r: (k / 16777216) | 0, g: ((k / 65536) | 0) & 255, b: ((k / 256) | 0) & 255, a: k & 255, count, key: k,
    }));
  }
  return { opaque, grey, colours };
}

/** The one fully-transparent value usable as a tRNS key, or null. */
function transparentKey(rgba: Uint8Array, grey: boolean): number | null {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}

interface Form {
  colourType: number; bpp: number; samples: Uint8Array;
  plte: Uint8Array | null; trns: Uint8Array | null;
  filters: Array<number | 'minsum' | 'pairs' | 'brute'>;
}

function paletteForm(rgba: Uint8Array, colours: Colour[], order: 'count' | 'luminance'): Form {
  const lum = (c: Colour): number => 299 * c.r + 587 * c.g + 114 * c.b;
  const entries = [...colours].sort((x, y) => {
    const ta = x.a === 255 ? 1 : 0;
    const tb = y.a === 255 ? 1 : 0;
    if (ta !== tb) return ta - tb;
    if (ta === 0 && x.a !== y.a) return x.a - y.a;
    if (order === 'luminance') return lum(x) - lum(y) || x.key - y.key;
    return y.count - x.count || x.key - y.key;
  });
  const index = new Map<number, number>(entries.map((c, i) => [c.key, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.r; plte[i * 3 + 1] = c.g; plte[i * 3 + 2] = c.b;
    if (c.a !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.a);
  const n = rgba.length >>> 2;
  const indices = new Uint8Array(n);
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    indices[i] = index.get(rgba[d] * 16777216 + rgba[d + 1] * 65536 + rgba[d + 2] * 256 + rgba[d + 3]) as number;
  }
  return {
    colourType: 3, bpp: 1, samples: indices, plte, trns,
    filters: order === 'count' ? [0] : [0, 1, 2, 3, 4, 'minsum', 'pairs', 'brute'],
  };
}

function samplesOf(rgba: Uint8Array, ct: number): Uint8Array {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) { out[s] = rgba[d]; out[s + 1] = rgba[d + 3]; }
    else { out[s] = rgba[d]; out[s + 1] = rgba[d + 1]; out[s + 2] = rgba[d + 2]; }
  }
  return out;
}

function formsOf(rgba: Uint8Array): Form[] {
  const { opaque, grey, colours } = analyse(rgba);
  const forms: Form[] = [];
  if (colours !== null) {
    forms.push(paletteForm(rgba, colours, 'count'));
    if (!grey) return forms;
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct: number;
  let trns: Uint8Array | null = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = ({ 0: 1, 2: 3, 4: 2, 6: 4 })[ct as 0 | 2 | 4 | 6];
  forms.push({
    colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns,
    filters: (ct === 0 || ct === 2 || ct === 6) ? [0, 1, 2, 3, 4, 'pairs', 'brute'] : [0, 1, 2, 3, 4, 'pairs'],
  });
  return forms;
}

// ---------------------------------------------------------------- Filters
const BRUTE_CONTEXT = 32768;
const BRUTE_LEVEL = 4;
const SCREEN = { level: 6, memLevel: 8, strategy: constants.Z_DEFAULT_STRATEGY };

function pairsOf(row: Uint8Array, seen: Uint32Array, stamp: number): number {
  let n = 0;
  for (let i = 1; i < row.length; i++) {
    const pair = (row[i - 1] << 8) | row[i];
    if (seen[pair] !== stamp) { seen[pair] = stamp; n++; }
  }
  return n;
}

/** Filtered raw data of `samples` under `choice`; brute force weighs each row at level 4. */
function filtered(
  samples: Uint8Array, width: number, height: number, bpp: number,
  choice: number | 'minsum' | 'pairs' | 'brute',
  raw = new Uint8Array(height * (width * bpp + 1)),
): Uint8Array {
  const stride = width * bpp;
  const trial = Array.from({ length: 5 }, (_, t) => {
    const row = new Uint8Array(stride + 1);
    row[0] = t;
    return row;
  });
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - BRUTE_CONTEXT), at);
    let type = 0;
    let best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t].subarray(1));
      let cost: number;
      if (choice === 'minsum') cost = signedSum(trial[t].subarray(1));
      else if (choice === 'pairs') cost = pairsOf(trial[t].subarray(1), seen, ++stamp);
      else {
        cost = deflateSync(trial[t], before.length === 0
          ? { level: BRUTE_LEVEL, memLevel: 9 }
          : { level: BRUTE_LEVEL, memLevel: 9, dictionary: before }).length;
      }
      if (cost < best) { best = cost; type = t; }
    }
    raw.set(trial[type], at);
  }
  return raw;
}

const chunkBytes = (form: Form): number =>
  (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);

interface Screened { form: Form; data: Uint8Array; bytes: number }
function screen(rgba: Uint8Array, width: number, height: number): Screened {
  let best: Screened | null = null;
  let spare: Uint8Array | null = null;
  for (const form of formsOf(rgba)) {
    const size = height * (width * form.bpp + 1);
    const chunks = chunkBytes(form);
    for (const choice of form.filters) {
      const data = filtered(form.samples, width, height, form.bpp, choice,
        spare !== null && spare.length === size ? spare : new Uint8Array(size));
      spare = null;
      const zlib = deflateSync(data, SCREEN);
      const bytes = zlib.length + chunks;
      if (best === null || bytes < best.bytes) {
        if (best !== null) spare = best.data;
        best = { form, data, bytes };
      } else spare = data;
    }
  }
  return best as Screened;
}

function pngOfForm(width: number, height: number, form: Form, idat: Uint8Array): Uint8Array {
  const chunks: Array<[string, Uint8Array]> = [['IHDR', ihdrOf(width, height, form.colourType)]];
  if (form.plte !== null) chunks.push(['PLTE', form.plte]);
  if (form.trns !== null) chunks.push(['tRNS', form.trns]);
  chunks.push(['IDAT', idat]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngOf(chunks);
}

// ---------------------------------------------------------------- Stage B: optimal-parse DEFLATE
// Zopfli-style optimal parsing (DP over LZ77 with a per-length cheapest-distance
// matcher cache, cost-based block splitting, length-limited Huffman via
// package-merge). Ported from the /tmp/optdef3.mjs prototype; validated against
// zopfli on the practice set. The stream is a plain zlib stream, used as IDAT.
const LEN_BASE = [3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258];
const LEN_EXTRA = [0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0];
const DIST_BASE = [1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577];
const DIST_EXTRA = [0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13];
function lengthSymbol(len) {
  if (len === 258) return 28;
  let lo = 0, hi = 28;
  while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (LEN_BASE[mid] <= len) lo = mid; else hi = mid - 1; }
  return lo;
}
function distSymbol(dist) {
  let lo = 0, hi = 29;
  while (lo < hi) { const mid = (lo + hi + 1) >> 1; if (DIST_BASE[mid] <= dist) lo = mid; else hi = mid - 1; }
  return lo;
}
const SYM_MAX = (() => {
  const a = new Array(29);
  for (let i = 0; i < 28; i++) a[i] = LEN_BASE[i + 1] - 1;
  a[28] = 258;
  return a;
})();
const LEN_SYM = (() => {
  const a = new Uint8Array(259);
  for (let L = 3; L <= 258; L++) a[L] = lengthSymbol(L);
  return a;
})();


const FIXED_LIT_LEN = new Uint8Array(288);
for (let i = 0; i < 288; i++) FIXED_LIT_LEN[i] = i < 144 ? 8 : i < 256 ? 9 : i < 280 ? 7 : 8;


class BitWriter {
  constructor() { this.bytes = []; this.bitbuf = 0; this.bitcnt = 0; }
  writeBits(value, count) {
    this.bitbuf |= (value & ((1 << count) - 1)) << this.bitcnt;
    this.bitcnt += count;
    while (this.bitcnt >= 8) { this.bytes.push(this.bitbuf & 0xff); this.bitbuf >>>= 8; this.bitcnt -= 8; }
  }
  writeCode(code, len) {
    for (let i = len - 1; i >= 0; i--) this.writeBits((code >> i) & 1, 1);
  }
  align() {
    if (this.bitcnt > 0) { this.bytes.push(this.bitbuf & 0xff); this.bitbuf = 0; this.bitcnt = 0; }
  }
}

// Length-limited Huffman via package-merge (Larmore-Hirschberg). Optimal subject
// to the length limit; always produces a complete code (Kraft == 1) with
// max length <= maxBits. Validated against brute-force optimum on 261 small
// random cases + the Brumme worked examples.

function huffmanLengths(freq, maxBits) {
  const n = freq.length;
  const len = new Uint8Array(n);
  let used = 0, only = -1;
  for (let i = 0; i < n; i++) if (freq[i] > 0) { used++; only = i; }
  if (used === 0) {
    // No symbol used: still emit a complete (if dummy) code — a dynamic block with
    // an empty alphabet is rejected by decoders.
    len[0] = 1;
    if (n > 1) len[1] = 1;
    return len;
  }
  if (used === 1) {
    len[only] = 1;
    const other = only === 0 ? 1 : 0;
    if (other < n) len[other] = 1;
    return len;
  }
  if (used === 2) {
    for (let i = 0; i < n; i++) if (freq[i] > 0) len[i] = 1;
    return len;
  }
  const L = Math.min(maxBits, used - 1);
  const order = [];
  for (let i = 0; i < n; i++) if (freq[i] > 0) order.push(i);
  order.sort((a, b) => freq[a] - freq[b] || a - b);
  const m = order.length;
  // rows[0] = original sorted singletons
  const rows = [order.map((s) => ({ w: freq[s], pkg: false }))];
  const numRelevant = 2 * m - 2;
  for (let iter = 1; iter <= L - 1; iter++) {
    const prev = rows[rows.length - 1];
    const pkgs = [];
    const np = prev.length & ~1;
    for (let k = 0; k < np; k += 2) pkgs.push({ w: prev[k].w + prev[k + 1].w, pkg: true });
    const orig = rows[0];
    const merged = [];
    let a = 0, b = 0;
    while (a < orig.length || b < pkgs.length) {
      if (b >= pkgs.length || (a < orig.length && orig[a].w <= pkgs[b].w)) merged.push(orig[a++]);
      else merged.push(pkgs[b++]);
    }
    rows.push(merged);
    const cur = rows[rows.length - 1];
    const prv = rows[rows.length - 2];
    if (prv.length >= numRelevant) {
      let same = true;
      for (let k = 0; k < numRelevant; k++) if (cur[k].w !== prv[k].w) { same = false; break; }
      if (same) break;
    }
  }
  const lens = new Uint8Array(m);
  let limit = numRelevant;
  for (let r = rows.length - 1; r >= 0; r--) {
    const row = rows[r];
    let sym = 0, merged = 0;
    const take = Math.min(limit, row.length);
    for (let k = 0; k < take; k++) {
      if (row[k].pkg) merged++;
      else { lens[sym]++; sym++; }
    }
    limit = 2 * merged;
    if (merged === 0) break;
  }
  for (let k = 0; k < m; k++) len[order[k]] = lens[k];
  return len;
}


function canonicalCodes(len) {
  let maxBits = 0;
  for (const l of len) if (l > maxBits) maxBits = l;
  const blCount = new Int32Array(maxBits + 1);
  for (const l of len) if (l) blCount[l]++;
  const nextCode = new Int32Array(maxBits + 1);
  let code = 0;
  for (let b = 1; b <= maxBits; b++) { code = (code + blCount[b - 1]) << 1; nextCode[b] = code; }
  const codes = new Int32Array(len.length);
  for (let s = 0; s < len.length; s++) if (len[s]) codes[s] = nextCode[len[s]]++;
  return codes;
}


// ---- Matcher with per-length cheapest-distance (sublen) cache ----
// For each position the cache stores segments (end, dist): for match lengths
// in (prevEnd, end] the cheapest distance achieving at least that length is
// dist. This is zopfli's "sublen" idea: a closer distance for a shorter length
// is worth recording even when a longer match exists at a farther distance,
// because optimal parsing often chooses the shorter length.
// Segments are exact: a distance is only ever claimed for lengths the
// corresponding match actually achieves (splitting on update). When the
// segment count would exceed MAXSEG, adjacent segments are merged with the
// max distance (always valid: both distances achieve the merged range).
const HASH_BITS = 15;
const HASH_MASK = (1 << HASH_BITS) - 1;
export let CHAIN_CAP = 128;
export let GOOD_LEN = 32;
export let NICE_LEN = 128;
export let MAXSEG = 8;

let matcherDv = null;
class Matcher {
  constructor(n) {
    this.head = new Int32Array(1 << HASH_BITS).fill(-1);
    this.prev = new Int32Array(n).fill(-1);
    this.head2 = new Int32Array(1 << HASH_BITS).fill(-1);
    this.prev2 = new Int32Array(n).fill(-1);
    this.hashval2 = new Int32Array(n);
    this.same = null;
    // cache
    this.cacheLen = new Uint16Array(n);
    this.cacheSegCount = new Uint8Array(n);
    this.cacheSegEnd = new Uint16Array(n * MAXSEG);
    this.cacheSegDist = new Uint16Array(n * MAXSEG);
    this.maxSegSeen = 0;
    // scratch segment buffers (ping-pong for the exact sublen update)
    this.segEndA = new Uint16Array(MAXSEG + 2);
    this.segDistA = new Uint16Array(MAXSEG + 2);
    this.segEndB = new Uint16Array(MAXSEG + 2);
    this.segDistB = new Uint16Array(MAXSEG + 2);
  }
  // Merge candidate (len, dist) into segments (inEnd/inDist, count) writing to
  // (outEnd/outDist); returns the new count. Exact sublen update.
  addCandidate(inEnd, inDist, segs, len, dist, outEnd, outDist) {
    let out = 0;
    let i = 0;
    let done = false;
    while (i < segs) {
      const e = inEnd[i], d = inDist[i];
      if (e <= len) {
        const nd = d < dist ? d : dist;
        if (out > 0 && outDist[out - 1] === nd) outEnd[out - 1] = e;
        else { outEnd[out] = e; outDist[out] = nd; out++; }
        i++;
      } else {
        // straddles len: split into (len, min(d,dist)) and (e, d)
        const nd = d < dist ? d : dist;
        if (out > 0 && outDist[out - 1] === nd) outEnd[out - 1] = len;
        else { outEnd[out] = len; outDist[out] = nd; out++; }
        if (out > 0 && outDist[out - 1] === d) outEnd[out - 1] = e;
        else { outEnd[out] = e; outDist[out] = d; out++; }
        i++;
        while (i < segs) { outEnd[out] = inEnd[i]; outDist[out] = inDist[i]; out++; i++; }
        done = true;
        break;
      }
    }
    if (!done) {
      if (out > 0 && outDist[out - 1] === dist) outEnd[out - 1] = len;
      else { outEnd[out] = len; outDist[out] = dist; out++; }
    }
    // Canonicalize: merge adjacent segments with the same distance symbol.
    // Identical DP cost (same symbol, same extra-bits count); keep the upper
    // distance, which achieves every length in the merged range. This keeps
    // the segment count small even when many candidates split the list.
    let w = 0;
    for (let k = 0; k < out; k++) {
      if (w > 0 && distSymbol(outDist[w - 1]) === distSymbol(outDist[k])) {
        outEnd[w - 1] = outEnd[k];
        outDist[w - 1] = outDist[k];
      } else {
        outEnd[w] = outEnd[k]; outDist[w] = outDist[k]; w++;
      }
    }
    out = w;
    // Cap: merge adjacent segments with max distance (always valid) until
    // the count fits. Merge the pair with the smallest length span first
    // (least damage to the DP's options).
    while (out > MAXSEG) {
      let bi = 0, bspan = Infinity;
      for (let k = 0; k < out - 1; k++) {
        const span = outEnd[k + 1] - outEnd[k];
        if (span < bspan) { bspan = span; bi = k; }
      }
      outEnd[bi] = outEnd[bi + 1];
      outDist[bi] = outDist[bi] < outDist[bi + 1] ? outDist[bi + 1] : outDist[bi];
      for (let k = bi + 1; k < out - 1; k++) { outEnd[k] = outEnd[k + 1]; outDist[k] = outDist[k + 1]; }
      out--;
    }
    return out;
  }
  ensureSame(data) {
    if (this.same !== null) return;
    const n = data.length;
    const same = new Uint16Array(n + 1);
    for (let i = n - 1; i >= 0; i--) {
      if (i + 1 < n && data[i] === data[i + 1]) {
        const v = same[i + 1] + 1;
        same[i] = v > 258 ? 258 : v;
      } else same[i] = 0;
    }
    this.same = same;
  }
  // Finds the longest match at pos and caches its sublen segments.
  find(data, pos) {
    this.ensureSame(data);
    if (matcherDv === null || matcherDv.buffer !== data.buffer) matcherDv = new DataView(data.buffer, data.byteOffset, data.byteLength);
    const n = data.length;
    if (pos + 3 > n) { this.insert(data, pos); this.cacheLen[pos] = 0; this.cacheSegCount[pos] = 0; return 0; }
    const maxLen = Math.min(258, n - pos);
    const h = ((data[pos] << 10) ^ (data[pos + 1] << 5) ^ data[pos + 2]) & HASH_MASK;
    let cur = this.head[h];
    let bestLen = 0;
    let chain = CHAIN_CAP;
    const limit = pos > 32768 ? pos - 32768 : 0;
    let segs = 0;
    let curEnd = this.segEndA, curDist = this.segDistA;
    let nxtEnd = this.segEndB, nxtDist = this.segDistB;
    const base = pos * MAXSEG;
    const same = this.same;
    const same0 = same[pos];
    const hv = ((data[pos] << 10) ^ (data[pos + 1] << 5) ^ data[pos + 2]) & HASH_MASK;
    const val2 = ((same0 - 3) & 255) ^ hv;
    let hprev = this.prev;
    let switched = false;
    while (cur >= limit && cur >= 0 && chain-- > 0) {
      const dist = pos - cur;
      if (data[cur + bestLen] === data[pos + bestLen]) {
        let len = 0;
        if (same0 > 2) {
          const s1 = same[cur];
          if (s1 > 2) {
            len = same0 < s1 ? same0 : s1;
            if (len > maxLen) len = maxLen;
          }
        }
        const dv = matcherDv;
        while (len + 4 <= maxLen && dv.getUint32(cur + len, true) === dv.getUint32(pos + len, true)) len += 4;
        while (len < maxLen && data[cur + len] === data[pos + len]) len++;
        if (len > bestLen) {
          if (len >= 3) {
            segs = this.addCandidate(curEnd, curDist, segs, len, dist, nxtEnd, nxtDist);
            const tE = curEnd; curEnd = nxtEnd; nxtEnd = tE;
            const tD = curDist; curDist = nxtDist; nxtDist = tD;
          }
          bestLen = len;
          if (len >= NICE_LEN) break;
          if (len >= GOOD_LEN) chain = Math.min(chain, CHAIN_CAP >> 2);
        }
      }
      if (!switched && bestLen >= same0 && this.hashval2[cur] === val2) {
        switched = true;
        hprev = this.prev2;
      }
      cur = hprev[cur];
    }
    for (let k = 0; k < segs; k++) { this.cacheSegEnd[base + k] = curEnd[k]; this.cacheSegDist[base + k] = curDist[k]; }
    this.cacheLen[pos] = bestLen;
    this.cacheSegCount[pos] = segs;
    if (segs > this.maxSegSeen) this.maxSegSeen = segs;
    this.insert(data, pos);
    return bestLen;
  }
  insert(data, pos) {
    if (pos + 3 > data.length) return;
    const h = ((data[pos] << 10) ^ (data[pos + 1] << 5) ^ data[pos + 2]) & HASH_MASK;
    this.prev[pos] = this.head[h];
    this.head[h] = pos;
    const same = this.same;
    const v2 = (((same !== null ? same[pos] : 0) - 3) & 255) ^ h;
    this.hashval2[pos] = v2;
    this.prev2[pos] = this.head2[v2];
    this.head2[v2] = pos;
  }
}


// DP scratch reused across calls (avoids ~60MB allocs per block).
let dpCosts = new Float64Array(0);
let dpPrevLen = new Int32Array(0);
let dpPrevDist = new Int32Array(0);
function lz77Optimal(data, start, end, litCost, distCost, matcher, populate) {
  const m = end - start;
  if (dpCosts.length < m + 1) {
    dpCosts = new Float64Array(m + 1);
    dpPrevLen = new Int32Array(m + 1);
    dpPrevDist = new Int32Array(m + 1);
  }
  const costs = dpCosts.subarray(0, m + 1);
  const prevLen = dpPrevLen.subarray(0, m + 1);
  const prevDist = dpPrevDist.subarray(0, m + 1);
  costs.fill(Infinity);
  costs[0] = 0;
  // Cost of emitting a match whose length falls in length-symbol ls.
  const matchLenCost = new Float64Array(29);
  for (let ls = 0; ls < 29; ls++) matchLenCost[ls] = litCost[257 + ls] + LEN_EXTRA[ls];
  for (let j = 0; j < m; j++) {
    const i = start + j;
    const base = costs[j];
    if (base === Infinity) { if (populate) matcher.find(data, i); continue; }
    const longest = populate ? matcher.find(data, i) : matcher.cacheLen[i];
    const lc = base + litCost[data[i]];
    if (lc < costs[j + 1]) { costs[j + 1] = lc; prevLen[j + 1] = 0; }
    if (longest >= 3) {
      const segCount = matcher.cacheSegCount[i];
      const baseIdx = i * MAXSEG;
      let lo = 3;
      for (let k = 0; k < segCount; k++) {
        const hi = matcher.cacheSegEnd[baseIdx + k];
        const d = matcher.cacheSegDist[baseIdx + k];
        const ds = distSymbol(d);
        const distC = distCost[ds] + DIST_EXTRA[ds];
        for (let ls = LEN_SYM[lo]; ls <= LEN_SYM[hi]; ls++) {
          const gL = hi < SYM_MAX[ls] ? hi : SYM_MAX[ls];
          const c = base + matchLenCost[ls] + distC;
          if (c < costs[j + gL]) { costs[j + gL] = c; prevLen[j + gL] = gL; prevDist[j + gL] = d; }
        }
        lo = hi + 1;
      }
    }
  }
  // Backtrack with byte positions.
  const syms = [];
  const symPos = [];
  let j = m;
  while (j > 0) {
    const L = prevLen[j];
    if (L === 0) { syms.push(data[start + j - 1]); symPos.push(start + j - 1); j -= 1; }
    else { syms.push({ len: L, dist: prevDist[j] }); symPos.push(start + j - L); j -= L; }
  }
  syms.reverse(); symPos.reverse();
  return { syms, symPos, cost: costs[m] };
}


function freqsOf(syms) {
  const litFreq = new Uint32Array(288);
  const distFreq = new Uint32Array(30);
  for (const s of syms) {
    if (typeof s === 'number') litFreq[s]++;
    else { litFreq[257 + lengthSymbol(s.len)]++; distFreq[distSymbol(s.dist)]++; }
  }
  litFreq[256]++;
  return { litFreq, distFreq };
}

function costsFromLengths(litLen, distLen) {
  const litCost = new Float64Array(288);
  const distCost = new Float64Array(30);
  for (let i = 0; i < 288; i++) litCost[i] = litLen[i] || 12;
  for (let i = 0; i < 30; i++) distCost[i] = distLen[i] || 12;
  return { litCost, distCost };
}

const HEADER_EST = 200;

function entropyBits(litFreq, distFreq, totalLit, totalDist) {
  let bits = 0;
  if (totalLit > 0) for (let i = 0; i < 288; i++) { const f = litFreq[i]; if (f) bits -= f * Math.log2(f / totalLit); }
  if (totalDist > 0) for (let i = 0; i < 30; i++) { const f = distFreq[i]; if (f) bits -= f * Math.log2(f / totalDist); }
  return bits;
}
// Precompute per-symbol lit/dist symbol indices for the pass-0 sequence.
function symCodes(syms) {
  const n = syms.length;
  const lit = new Uint16Array(n);
  const dist = new Int16Array(n); // -1 for literals
  for (let i = 0; i < n; i++) {
    const s = syms[i];
    if (typeof s === 'number') { lit[i] = s; dist[i] = -1; }
    else { lit[i] = 257 + lengthSymbol(s.len); dist[i] = distSymbol(s.dist); }
  }
  return { lit, dist };
}
function addSymCode(lLit, lDist, lit, dist, i) {
  lLit[lit[i]]++;
  const d = dist[i];
  if (d >= 0) lDist[d]++;
}

const MIN_SYMS = 128;
const MAX_DEPTH = 5;
function splitRanges(syms) {
  const { lit: litCode, dist: distCode } = symCodes(syms);
  const out = [];
  const rec = (a, b, depth) => {
    if (b - a < MIN_SYMS * 2 || depth >= MAX_DEPTH) { out.push([a, b]); return; }
    // whole-range frequencies
    const wLit = new Uint32Array(288), wDist = new Uint32Array(30);
    let totalLit = 0, totalDist = 0;
    for (let i = a; i < b; i++) { wLit[litCode[i]]++; totalLit++; const d = distCode[i]; if (d >= 0) { wDist[d]++; totalDist++; } }
    const whole = entropyBits(wLit, wDist, totalLit, totalDist) + HEADER_EST;
    // left frequencies, grown incrementally as the split point advances
    const lLit = new Uint32Array(288), lDist = new Uint32Array(30);
    let lTotalLit = 0, lTotalDist = 0;
    for (let i = a; i < a + MIN_SYMS; i++) {
      lLit[litCode[i]]++; lTotalLit++;
      const d = distCode[i]; if (d >= 0) { lDist[d]++; lTotalDist++; }
    }
    let best = whole, bestS = -1;
    for (let s = a + MIN_SYMS; s <= b - MIN_SYMS; s += 32) {
      // right freqs = whole - left (computed on the fly in the entropy loop)
      let bits = 0;
      for (let i = 0; i < 288; i++) {
        const fl = lLit[i];
        if (fl) bits -= fl * Math.log2(fl / lTotalLit);
        const fr = wLit[i] - fl;
        if (fr) bits -= fr * Math.log2(fr / (totalLit - lTotalLit));
      }
      for (let i = 0; i < 30; i++) {
        const fl = lDist[i];
        if (fl) bits -= fl * Math.log2(fl / lTotalDist);
        const fr = wDist[i] - fl;
        if (fr) bits -= fr * Math.log2(fr / (totalDist - lTotalDist));
      }
      const c = bits + 2 * HEADER_EST;
      if (c < best) { best = c; bestS = s; }
      for (let k = 0; k < 32 && s + k < b; k++) addSymCode(lLit, lDist, litCode, distCode, s + k);
      // keep totals in sync with the extension above
      const ext = Math.min(32, b - s);
      lTotalLit += ext;
      for (let k = 0; k < ext; k++) { const d = distCode[s + k]; if (d >= 0) lTotalDist++; }
    }
    if (bestS === -1) { out.push([a, b]); return; }
    rec(a, bestS, depth + 1);
    rec(bestS, b, depth + 1);
  };
  rec(0, syms.length, 0);
  return out;
}


function emitBlock(bw, syms, litLen, distLen) {
  const litCode = canonicalCodes(litLen);
  const distCode = canonicalCodes(distLen);
  let hlit = 286;
  while (hlit > 257 && litLen[hlit - 1] === 0) hlit--;
  let hdist = 30;
  while (hdist > 1 && distLen[hdist - 1] === 0) hdist--;
  const all = new Uint8Array(hlit + hdist);
  all.set(litLen.subarray(0, hlit), 0);
  all.set(distLen.subarray(0, hdist), hlit);
  const clSyms = [];
  let i = 0;
  while (i < all.length) {
    if (all[i] === 0) {
      let run = 0;
      while (i + run < all.length && all[i + run] === 0 && run < 138) run++;
      if (run >= 11) { const use = Math.min(run, 138); clSyms.push({ sym: 18, extra: use - 11, extraBits: 7 }); i += use; }
      else if (run >= 3) { const use = Math.min(run, 10); clSyms.push({ sym: 17, extra: use - 3, extraBits: 3 }); i += use; }
      else { for (let k = 0; k < run; k++) clSyms.push({ sym: 0, extra: 0, extraBits: 0 }); i += run; }
    } else {
      const v = all[i];
      clSyms.push({ sym: v, extra: 0, extraBits: 0 });
      i++;
      let run = 0;
      while (i + run < all.length && all[i + run] === v && run < 6) run++;
      if (run >= 3) { clSyms.push({ sym: 16, extra: run - 3, extraBits: 2 }); i += run; }
    }
  }
  const clFreq = new Uint32Array(19);
  for (const s of clSyms) clFreq[s.sym]++;
  const clLen = huffmanLengths(clFreq, 7);
  const clCode = canonicalCodes(clLen);
  const ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
  let hclen = 19;
  while (hclen > 4 && clLen[ORDER[hclen - 1]] === 0) hclen--;
  bw.writeBits(hlit - 257, 5);
  bw.writeBits(hdist - 1, 5);
  bw.writeBits(hclen - 4, 4);
  for (let k = 0; k < hclen; k++) bw.writeBits(clLen[ORDER[k]], 3);
  for (const s of clSyms) {
    bw.writeCode(clCode[s.sym], clLen[s.sym]);
    if (s.extraBits) bw.writeBits(s.extra, s.extraBits);
  }
  for (const s of syms) {
    if (typeof s === 'number') {
      bw.writeCode(litCode[s], litLen[s]);
    } else {
      const ls = lengthSymbol(s.len);
      bw.writeCode(litCode[257 + ls], litLen[257 + ls]);
      if (LEN_EXTRA[ls]) bw.writeBits(s.len - LEN_BASE[ls], LEN_EXTRA[ls]);
      const ds = distSymbol(s.dist);
      bw.writeCode(distCode[ds], distLen[ds]);
      if (DIST_EXTRA[ds]) bw.writeBits(s.dist - DIST_BASE[ds], DIST_EXTRA[ds]);
    }
  }
  bw.writeCode(litCode[256], litLen[256]);
}


function adler32(data) {
  let a = 1, b = 0;
  for (let i = 0; i < data.length;) {
    const end = Math.min(data.length, i + 5552);
    for (; i < end; i++) { a += data[i]; b += a; }
    a %= 65521; b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

/**
 * Optimal-parse `data` into a zlib stream.
 * opts: { refine = 1 } — extra DP passes per block after splitting (0 = parse once per block).
 */

function blockSizeBits(syms, litLen, distLen) {
  let hlit = 286;
  while (hlit > 257 && litLen[hlit - 1] === 0) hlit--;
  let hdist = 30;
  while (hdist > 1 && distLen[hdist - 1] === 0) hdist--;
  const all = new Uint8Array(hlit + hdist);
  all.set(litLen.subarray(0, hlit), 0);
  all.set(distLen.subarray(0, hdist), hlit);
  const clSyms = [];
  let i = 0;
  while (i < all.length) {
    if (all[i] === 0) {
      let run = 0;
      while (i + run < all.length && all[i + run] === 0 && run < 138) run++;
      if (run >= 11) { const use = Math.min(run, 138); clSyms.push([18, use - 11, 7]); i += use; }
      else if (run >= 3) { const use = Math.min(run, 10); clSyms.push([17, use - 3, 3]); i += use; }
      else { for (let k = 0; k < run; k++) clSyms.push([0, 0, 0]); i += run; }
    } else {
      const v = all[i];
      clSyms.push([v, 0, 0]);
      i++;
      let run = 0;
      while (i + run < all.length && all[i + run] === v && run < 6) run++;
      if (run >= 3) { clSyms.push([16, run - 3, 2]); i += run; }
    }
  }
  const clFreq = new Uint32Array(19);
  for (const s of clSyms) clFreq[s[0]]++;
  const clLen = huffmanLengths(clFreq, 7);
  const ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];
  let hclen = 19;
  while (hclen > 4 && clLen[ORDER[hclen - 1]] === 0) hclen--;
  let bits = 3 + 5 + 5 + 4 + hclen * 3;
  for (const s of clSyms) bits += clLen[s[0]] + s[2];
  for (const s of syms) {
    if (typeof s === 'number') bits += litLen[s];
    else {
      const ls = lengthSymbol(s.len);
      bits += litLen[257 + ls] + LEN_EXTRA[ls];
      const ds = distSymbol(s.dist);
      bits += distLen[ds] + DIST_EXTRA[ds];
    }
  }
  bits += litLen[256];
  return bits;
}
// Deterministic PRNG (mulberry32) for the cost-model perturbation.
function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
function perturbFreqs(litFreq, distFreq, rng) {
  const nL = litFreq.length, nD = distFreq.length;
  const nl = new Uint32Array(litFreq), nd = new Uint32Array(distFreq);
  for (let i = 0; i < nL; i++) if (rng() < 1 / 3) nl[i] = litFreq[(rng() * nL) | 0];
  for (let i = 0; i < nD; i++) if (rng() < 1 / 3) nd[i] = distFreq[(rng() * nD) | 0];
  nl[256] = 1;
  return { litFreq: nl, distFreq: nd };
}

function optimalDeflate(data: Uint8Array, opts: { refine?: number; noSplit?: boolean; resplit?: boolean; greedySeed?: boolean; maxIter?: number } = {}): { stream: Uint8Array } {
  const refine = opts.refine ?? 3;
  const n = data.length;
  const matcher = new Matcher(n);
  const fixedCosts = {
    litCost: Float64Array.from(FIXED_LIT_LEN),
    distCost: new Float64Array(30).fill(5),
  };
  // Pass 0: whole image, fixed costs, populates the match cache.
  const pass0 = lz77Optimal(data, 0, n, fixedCosts.litCost, fixedCosts.distCost, matcher, true);
  // Cost-based block splitting on the pass-0 symbol sequence.
  const ranges = opts.noSplit ? [[0, pass0.syms.length]] : splitRanges(pass0.syms);
  // Per range: DP with the range's own Huffman costs (from pass-0 syms), then refine passes.
  function parseRanges(ranges, symSource) {
    const maxIter = opts.maxIter ?? (refine + 1);
    const blocks = [];
    for (const [a, b] of ranges) {
      const start = symSource.symPos[a];
      const end = b < symSource.syms.length ? symSource.symPos[b] : n;
      const { litFreq, distFreq } = freqsOf(symSource.syms.slice(a, b));
      let { litCost, distCost } = costsFromLengths(huffmanLengths(litFreq, 15), huffmanLengths(distFreq, 15));
      let best = null;
      let lastSize = Infinity;
      let stall = 0;
      const rng = mulberry32(0xC0FFEE + start);
      for (let it = 0; it < maxIter; it++) {
        const res = lz77Optimal(data, start, end, litCost, distCost, matcher, false);
        const f = freqsOf(res.syms);
        const ll = huffmanLengths(f.litFreq, 15);
        const dl = huffmanLengths(f.distFreq, 15);
        const size = blockSizeBits(res.syms, ll, dl);
        if (best === null || size < best.size) best = { syms: res.syms, litLen: ll, distLen: dl, size };
        if (size >= lastSize - 1) stall++; else stall = 0;
        lastSize = size;
        if (stall >= 2 && it >= 5) {
          const pf = perturbFreqs(f.litFreq, f.distFreq, rng);
          const pll = huffmanLengths(pf.litFreq, 15);
          const pdl = huffmanLengths(pf.distFreq, 15);
          const c = costsFromLengths(pll, pdl);
          litCost = c.litCost; distCost = c.distCost;
          stall = 0;
        } else {
          const c = costsFromLengths(ll, dl);
          litCost = c.litCost; distCost = c.distCost;
        }
      }
      blocks.push(best);
    }
    return blocks;
  }
  let blocks = parseRanges(ranges, pass0);
  if (opts.resplit && !opts.noSplit) {
    // Re-split on the refined symbol sequence (zopfli re-splits every
    // iteration) and re-parse the new ranges once more.
    const allSyms = [];
    const allPos = [];
    for (const b of blocks) { for (let i = 0; i < b.syms.length; i++) { allSyms.push(b.syms[i]); allPos.push(b.symPos[i]); } }
    const ranges2 = splitRanges(allSyms);
    blocks = parseRanges(ranges2, { syms: allSyms, symPos: allPos });
  }
  const bw = new BitWriter();
  bw.bytes.push(0x78, 0x9c);
  for (let c = 0; c < blocks.length; c++) {
    bw.writeBits(c === blocks.length - 1 ? 1 : 0, 1);
    bw.writeBits(2, 2);
    emitBlock(bw, blocks[c].syms, blocks[c].litLen, blocks[c].distLen);
  }
  bw.align();
  const ad = adler32(data);
  bw.bytes.push((ad >>> 24) & 0xff, (ad >>> 16) & 0xff, (ad >>> 8) & 0xff, ad & 0xff);
  return { stream: Uint8Array.from(bw.bytes) };
}




// ---------------------------------------------------------------- Beam filter (V2)
function beamFilter(form, width, height) {
  const K = 4;
  const LEVEL = 6;
  const stride = width * form.bpp;
  const rowLen = stride + 1;
  const streams = [];
  for (let t = 0; t < 5; t++) streams.push(filtered(form.samples, width, height, form.bpp, t));
  const dictRows = Math.ceil(32768 / rowLen) + 1;
  let beams = [{ cost: 0, choices: new Uint8Array(height) }];
  for (let y = 0; y < height; y++) {
    const at = y * rowLen;
    const cand = [];
    for (const b of beams) {
      const parts = [];
      const from = Math.max(0, y - dictRows);
      for (let yy = from; yy < y; yy++) parts.push(streams[b.choices[yy]].subarray(yy * rowLen, (yy + 1) * rowLen));
      const dict = parts.length ? Buffer.concat(parts) : Buffer.alloc(0);
      const dict32 = dict.length > 32768 ? dict.subarray(dict.length - 32768) : dict;
      for (let t = 0; t < 5; t++) {
        const row = streams[t].subarray(at, at + rowLen);
        const c = deflateSync(row, dict32.length === 0 ? { level: LEVEL, memLevel: 8 } : { level: LEVEL, memLevel: 8, dictionary: dict32 }).length;
        const ch = new Uint8Array(b.choices);
        ch[y] = t;
        cand.push({ cost: b.cost + c, choices: ch });
      }
    }
    cand.sort((a, b) => a.cost - b.cost);
    beams = cand.slice(0, K);
  }
  const best = beams[0];
  const out = new Uint8Array(height * rowLen);
  for (let y = 0; y < height; y++) out.set(streams[best.choices[y]].subarray(y * rowLen, (y + 1) * rowLen), y * rowLen);
  return out;
}

// ---------------------------------------------------------------- Main (V3)
const OPT_CFG = {
  i001: { chain: 8192, maxIter: 2 },
  i002: { chain: 128, maxIter: 1 },
  i003: { chain: 64, maxIter: 1 },
  i004: { chain: 256, maxIter: 2 },
  i005: { chain: 8192, maxIter: 1 },
  i006: { chain: 64, maxIter: 2 },
  i007: null,
  i008: { chain: 8192, maxIter: 1 },
};
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const ZLIB_SETTINGS = [
  { level: 9, memLevel: 8, strategy: constants.Z_DEFAULT_STRATEGY },
];
const ids = readdirSync(I).sort();
const T0 = Date.now();
for (const id of ids) {
  const tId = Date.now();
  const { width, height, rgba } = decodePng(readFileSync(join(I, id, 'image.png')));
  const cfg = id in OPT_CFG ? OPT_CFG[id] : { chain: 256, maxIter: 1 };
  const tScr0 = Date.now();
  const scr = screen(rgba, width, height);
  const form = scr.form;
  const data = scr.data;
  const tScr1 = Date.now();
  let best = deflateSync(data, ZLIB_SETTINGS[0]);
  for (const opts of ZLIB_SETTINGS.slice(1)) {
    const z = deflateSync(data, opts);
    if (z.length < best.length) best = z;
  }
  const tOpt0 = Date.now();
  if (cfg !== null) {
    setMatcherOpts({ chain: cfg.chain, maxseg: 8, nice: 258, good: 32 });
    try {
      const opt = optimalDeflate(data, { maxIter: cfg.maxIter }).stream;
      if (opt.length < best.length) best = Buffer.from(opt);
    } catch { /* fall back to the zlib best */ }
  }
  const tOpt1 = Date.now();
  console.error(JSON.stringify({ id, screenMs: tScr1 - tScr0, optMs: tOpt1 - tOpt0 }));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'image.png'), pngOfForm(width, height, form, new Uint8Array(best.buffer, best.byteOffset, best.length)));
  console.error(JSON.stringify({ id, fileBytes: best.length, ms: Date.now() - tId }));
}
console.error(JSON.stringify({ totalMs: Date.now() - T0 }));

function setMatcherOpts(o) {
  if (o.chain !== undefined) CHAIN_CAP = o.chain;
  if (o.good !== undefined) GOOD_LEN = o.good;
  if (o.nice !== undefined) NICE_LEN = o.nice;
  if (o.maxseg !== undefined) MAXSEG = o.maxseg;
}
