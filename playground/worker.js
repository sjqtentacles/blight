// The checker worker: instantiates the raw cdylib (no wasm-bindgen) and answers check requests.
const { instance } = await WebAssembly.instantiateStreaming(fetch("./blight_playground.wasm"), {});
const { memory, bp_alloc, bp_check, bp_free_input, bp_free_report } = instance.exports;
postMessage({ ready: true });

onmessage = (e) => {
  const t0 = performance.now();
  const bytes = new TextEncoder().encode(e.data.source);
  const inPtr = bp_alloc(bytes.length);
  new Uint8Array(memory.buffer, inPtr, bytes.length).set(bytes);
  const outPtr = bp_check(inPtr, bytes.length);
  bp_free_input(inPtr, bytes.length);
  const outLen = new DataView(memory.buffer).getUint32(outPtr, true);
  const report = new TextDecoder().decode(new Uint8Array(memory.buffer, outPtr + 4, outLen));
  bp_free_report(outPtr);
  postMessage({ report, ms: Math.round(performance.now() - t0) });
};
