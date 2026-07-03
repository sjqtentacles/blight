// Blight playground main-thread glue: owns the UI and a killable Web Worker (a divergent check
// cannot wedge the tab — the worker is terminated and restarted on timeout).
import { EXAMPLES } from "./examples.js";

const src = document.getElementById("src");
const out = document.getElementById("out");
const status = document.getElementById("status");
const examples = document.getElementById("examples");

for (const name of Object.keys(EXAMPLES)) {
  const opt = document.createElement("option");
  opt.value = name;
  opt.textContent = name;
  examples.appendChild(opt);
}
examples.onchange = () => {
  if (examples.value) { src.value = EXAMPLES[examples.value]; check(); }
};

let worker = null;
let timer = null;
function freshWorker() {
  if (worker) worker.terminate();
  worker = new Worker("./worker.js", { type: "module" });
  worker.onmessage = (e) => {
    if (e.data.ready) { status.textContent = "checker ready"; return; }
    clearTimeout(timer);
    out.textContent = e.data.report;
    out.className = e.data.report.startsWith("ok:") ? "" : "err";
    status.textContent = `checked in ${e.data.ms} ms`;
  };
}
freshWorker();

const TIMEOUT_MS = 20000;
function check() {
  status.textContent = "checking…";
  out.textContent = "…";
  out.className = "";
  clearTimeout(timer);
  timer = setTimeout(() => {
    status.textContent = "timed out — worker restarted";
    out.textContent = `check exceeded ${TIMEOUT_MS / 1000}s and was stopped (the checker runs in a worker; your tab is fine)`;
    out.className = "err";
    freshWorker();
  }, TIMEOUT_MS);
  worker.postMessage({ source: src.value });
}
document.getElementById("check").onclick = check;
src.addEventListener("keydown", (e) => {
  if ((e.metaKey || e.ctrlKey) && e.key === "Enter") { e.preventDefault(); check(); }
});
