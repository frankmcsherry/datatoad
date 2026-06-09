import { WASI, File, OpenFile, PreopenDirectory, ConsoleStdout } from "@bjorn3/browser_wasi_shim";
import fs from "node:fs";

const wasmBytes = fs.readFileSync("datatoad_web.wasm"); // the file the page fetches
let out = "";
const stdout = ConsoleStdout.lineBuffered((l) => { out += l + "\n"; });
const stderr = ConsoleStdout.lineBuffered((l) => { out += "[stderr] " + l + "\n"; });
const root = new PreopenDirectory("/", new Map());
const wasi = new WASI([], [], [new OpenFile(new File([])), stdout, stderr, root]);
const { instance } = await WebAssembly.instantiate(wasmBytes, { wasi_snapshot_preview1: wasi.wasiImport });
wasi.initialize(instance);
const { alloc, eval: evalLine, memory } = instance.exports;
const enc = new TextEncoder();
function run(line) {
  const bytes = enc.encode(line);
  const ptr = alloc(bytes.length);
  new Uint8Array(memory.buffer, ptr, bytes.length).set(bytes);
  evalLine(ptr, bytes.length);
}
const session = [
  "R(0, 0)           :- .",
  "R(x, 999999)      :- :range(1, x, 1000000) .",
  "S(x, 0)           :- :range(0, x, 999999).",
  "S(999999, x)      :- :range(1, x, 1000000) .",
  "T(0, x)           :- :range(0, x, 999999).",
  "T(999999, 999999) :- .",
  "Path(w, x, y, z) :- R(w, x), S(x, y), T(y, z).",
  ".list",
];
for (const line of session) { out += "> " + line + "\n"; run(line); }
process.stdout.write(out);
