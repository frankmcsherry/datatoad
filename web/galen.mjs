// Run the real galen dataset THROUGH THE REACTOR (the same wasm the browser
// loads), under Node's V8 — representative of the in-browser experience.
// Mounts the six galen CSVs into a virtual FS and replays galen.dt's commands.
import { WASI, File, OpenFile, PreopenDirectory, ConsoleStdout } from "@bjorn3/browser_wasi_shim";
import fs from "node:fs";

const DIR = "/Users/mcsherry/Projects/datasets/flowlog/galen";
const names = ["C", "P", "Q", "R", "S", "U"];

const files = new Map();
let bytes = 0;
for (const n of names) {
  const data = fs.readFileSync(`${DIR}/${n}.csv`);
  bytes += data.length;
  files.set(`${n}.csv`, new File(data));
}
console.log(`mounted ${names.length} files, ${(bytes / 1e6).toFixed(1)} MB total`);

const stdout = ConsoleStdout.lineBuffered((l) => console.log(l));
const stderr = ConsoleStdout.lineBuffered((l) => console.log("[stderr]", l));
const root = new PreopenDirectory("/", files);

const wasi = new WASI([], [], [new OpenFile(new File([])), stdout, stderr, root]);
const wasmBytes = fs.readFileSync("target/wasm32-wasip1/release/datatoad_web.wasm");
const { instance } = await WebAssembly.instantiate(wasmBytes, {
  wasi_snapshot_preview1: wasi.wasiImport,
});
wasi.initialize(instance);

const { alloc, eval: evalLine, memory } = instance.exports;
const enc = new TextEncoder();
function run(line) {
  const b = enc.encode(line);
  const ptr = alloc(b.length);
  new Uint8Array(memory.buffer, ptr, b.length).set(b);
  evalLine(ptr, b.length);
}

const galen = [
  ".time reset",
  ".flow c /C.csv", ".flow p /P.csv", ".flow q /Q.csv",
  ".flow r /R.csv", ".flow s /S.csv", ".flow u /U.csv",
  ".time galen loaded",
  "p(x,z) :- p(x,y), p(y,z).",
  "q(x,r,z) :- p(x,y), q(y,r,z).",
  "q(x,q,z) :- q(x,r,z), s(r,q).",
  "p(x,z) :- p(y,w), u(w,r,z), q(x,r,y).",
  "p(x,z) :- c(y,w,z), p(x,w), p(x,y).",
  "q(x,e,o) :- q(x,y,z), q(z,u,o), r(y,u,e).",
  ".time galen inference complete",
  ".list",
  ".test p 7560179",
  ".test q 16595494",
];

const t0 = performance.now();
for (const line of galen) run(line);
console.log(`\nwall clock: ${((performance.now() - t0) / 1000).toFixed(1)} s`);
