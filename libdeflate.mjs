// src/index.ts
var MAX_LEVEL = 12;
var DEFAULT_LEVEL = 12;
var DECOMPRESS_SUCCESS = 0;
var DECOMPRESS_INSUFFICIENT_SPACE = 3;
var MAX_INPUT = 1073741824;
var MAX_OUTPUT = 2147418112;
var MAX_RATIO = 1032;
var wasm;
var pending;
var compressors = /* @__PURE__ */ new Map();
var decompressor = 0;
var imports = {
  // Views on memory are re-created on every call, so growth needs no bookkeeping.
  env: { emscripten_notify_memory_growth: () => void 0 }
};
function defaultUrl() {
  return new URL("./libdeflate.wasm", import.meta.url);
}
function isNodeFileUrl(url) {
  return url.protocol === "file:";
}
async function readFileUrl(url) {
  const proc = globalThis.process;
  const fs = proc?.getBuiltinModule?.("node:fs/promises");
  if (!fs) throw new Error("libdeflate-wasm: cannot read a file: URL without node:fs");
  return fs.readFile(url);
}
async function compile(source) {
  if (source instanceof WebAssembly.Module) return source;
  if (typeof source === "string" || source instanceof URL) {
    const url = new URL(source, typeof source === "string" ? defaultUrl() : void 0);
    if (isNodeFileUrl(url)) return WebAssembly.compile(await readFileUrl(url));
    return compile(await fetch(url));
  }
  if (source instanceof Response) {
    if (!source.ok) throw new Error(`libdeflate-wasm: fetching the wasm failed (${source.status})`);
    if (typeof WebAssembly.compileStreaming === "function" && source.headers.get("content-type")?.startsWith("application/wasm")) {
      return WebAssembly.compileStreaming(source);
    }
    return WebAssembly.compile(await source.arrayBuffer());
  }
  return WebAssembly.compile(source);
}
function attach(module) {
  if (wasm) return;
  const instance = new WebAssembly.Instance(module, imports);
  const exports = instance.exports;
  exports._initialize();
  wasm = exports;
}
function init(source) {
  if (wasm) return Promise.resolve();
  pending ??= compile(source ?? defaultUrl()).then(attach, (error) => {
    if (wasm) return;
    pending = void 0;
    throw error;
  });
  return pending;
}
function initSync(source) {
  if (wasm) return;
  attach(source instanceof WebAssembly.Module ? source : new WebAssembly.Module(source));
  pending ??= Promise.resolve();
}
function isReady() {
  return wasm !== void 0;
}
function api() {
  if (!wasm) throw new Error("libdeflate-wasm: call `await init()` before compressing");
  return wasm;
}
function checkInput(data) {
  if (!(data instanceof Uint8Array)) {
    throw new TypeError("libdeflate-wasm: data must be a Uint8Array");
  }
  if (data.length > MAX_INPUT) {
    throw new RangeError(`libdeflate-wasm: input is larger than ${MAX_INPUT} bytes`);
  }
}
function compressor(w, level) {
  if (!Number.isInteger(level) || level < 0 || level > MAX_LEVEL) {
    throw new RangeError(`libdeflate-wasm: level must be an integer from 0 to ${MAX_LEVEL}`);
  }
  let c = compressors.get(level);
  if (c === void 0) {
    c = w.libdeflate_alloc_compressor(level) >>> 0;
    if (!c) throw new RangeError("libdeflate-wasm: out of memory allocating the compressor");
    compressors.set(level, c);
  }
  return c;
}
function alloc(w, n) {
  const p = w.malloc(Math.max(n, 1)) >>> 0;
  if (!p) throw new RangeError(`libdeflate-wasm: out of memory allocating ${n} bytes`);
  return p;
}
function compress(format, data, level) {
  checkInput(data);
  const w = api();
  const c = compressor(w, level);
  const bound = w[`libdeflate_${format}_compress_bound`](c, data.length) >>> 0;
  const input = alloc(w, data.length);
  let output = 0;
  try {
    output = alloc(w, bound);
    new Uint8Array(w.memory.buffer, input, data.length).set(data);
    const size = w[`libdeflate_${format}_compress`](c, input, data.length, output, bound) >>> 0;
    if (size === 0) throw new Error("libdeflate-wasm: compression failed");
    return new Uint8Array(w.memory.buffer, output, size).slice();
  } finally {
    w.free(input);
    if (output) w.free(output);
  }
}
function deflate(data, level = DEFAULT_LEVEL) {
  return compress("deflate", data, level);
}
function zlib(data, level = DEFAULT_LEVEL) {
  return compress("zlib", data, level);
}
function gzip(data, level = DEFAULT_LEVEL) {
  return compress("gzip", data, level);
}
function gzipSizeHint(data) {
  if (data.length < 18) return void 0;
  const n = data.length;
  return (data[n - 4] | data[n - 3] << 8 | data[n - 2] << 16 | data[n - 1] << 24) >>> 0;
}
function decompress(format, data, size) {
  checkInput(data);
  if (size !== void 0 && (!Number.isInteger(size) || size < 0)) {
    throw new RangeError("libdeflate-wasm: size must be a non-negative integer");
  }
  if (size !== void 0 && size > MAX_OUTPUT) {
    throw new RangeError(`libdeflate-wasm: size must be at most ${MAX_OUTPUT} bytes`);
  }
  const w = api();
  if (!decompressor) {
    decompressor = w.libdeflate_alloc_decompressor() >>> 0;
    if (!decompressor) throw new RangeError("libdeflate-wasm: out of memory");
  }
  const exact = size !== void 0;
  const plausible = Math.min(data.length * MAX_RATIO + 1024, MAX_OUTPUT);
  const limit = exact ? Math.min(size, plausible) : plausible;
  const gzipHint = format === "gzip" ? gzipSizeHint(data) : void 0;
  const hint = size ?? (gzipHint !== void 0 && gzipHint <= plausible ? gzipHint : void 0);
  let avail = Math.min(Math.max(hint ?? data.length * 4, 1024), limit);
  const actualAt = data.length + 3 & -4;
  const input = alloc(w, actualAt + 4);
  const actual = input + actualAt;
  try {
    new Uint8Array(w.memory.buffer, input, data.length).set(data);
    for (; ; ) {
      const output = alloc(w, avail);
      try {
        const run = w[`libdeflate_${format}_decompress`];
        const status = run(decompressor, input, data.length, output, avail, actual);
        if (status === DECOMPRESS_SUCCESS) {
          const n = new DataView(w.memory.buffer).getUint32(actual, true);
          if (exact && n !== size)
            throw new Error(`libdeflate-wasm: expected ${size} bytes, got ${n}`);
          return new Uint8Array(w.memory.buffer, output, n).slice();
        }
        if (status !== DECOMPRESS_INSUFFICIENT_SPACE || avail >= limit) {
          throw new Error(
            status !== DECOMPRESS_INSUFFICIENT_SPACE ? `libdeflate-wasm: invalid ${format} data` : exact ? "libdeflate-wasm: output larger than the given size" : `libdeflate-wasm: output larger than ${limit} bytes`
          );
        }
      } finally {
        w.free(output);
      }
      avail = Math.min(avail * 2, limit);
    }
  } finally {
    w.free(input);
  }
}
function inflate(data, size) {
  return decompress("deflate", data, size);
}
function unzlib(data, size) {
  return decompress("zlib", data, size);
}
function gunzip(data, size) {
  return decompress("gzip", data, size);
}
function release() {
  if (!wasm) return;
  for (const c of compressors.values()) wasm.libdeflate_free_compressor(c);
  compressors.clear();
  if (decompressor) wasm.libdeflate_free_decompressor(decompressor);
  decompressor = 0;
}

export { DEFAULT_LEVEL, MAX_INPUT, MAX_LEVEL, MAX_OUTPUT, deflate, gunzip, gzip, inflate, init, initSync, isReady, release, unzlib, zlib };