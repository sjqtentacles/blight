// R2 smoke test: instantiate the raw checker cdylib and check hello_nat.bl's source — the
// headless twin of what the page's Web Worker does. Usage:
//   node playground/smoke.mjs target/wasm32-unknown-unknown/release/blight_playground.wasm
import { readFile } from "node:fs/promises";

const wasmPath = process.argv[2] ?? "target/wasm32-unknown-unknown/release/blight_playground.wasm";
const source = await readFile("examples/hello_nat.bl", "utf8");

const { instance } = await WebAssembly.instantiate(await readFile(wasmPath), {});
const { memory, bp_alloc, bp_check, bp_free_input, bp_free_report } = instance.exports;

const bytes = new TextEncoder().encode(source);
const inPtr = bp_alloc(bytes.length);
new Uint8Array(memory.buffer, inPtr, bytes.length).set(bytes);
const outPtr = bp_check(inPtr, bytes.length);
bp_free_input(inPtr, bytes.length);

const outLen = new DataView(memory.buffer).getUint32(outPtr, true);
const report = new TextDecoder().decode(new Uint8Array(memory.buffer, outPtr + 4, outLen));
bp_free_report(outPtr);

console.log(report);
if (!report.includes("main : Nat")) {
  console.error("SMOKE FAIL: report does not state `main : Nat`");
  process.exit(1);
}
if (!/re-check/.test(report)) {
  console.error("SMOKE FAIL: report does not mention the independent re-check");
  process.exit(1);
}
console.log("SMOKE OK");
