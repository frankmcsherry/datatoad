// Node harness exercising the datatoad WASI reactor through the same shim the
// browser page uses. Validates: reactor init, the alloc/eval string ABI,
// stdout capture, persistent State across calls, and .flow from a virtual FS.
import { WASI, File, OpenFile, PreopenDirectory, ConsoleStdout } from "@bjorn3/browser_wasi_shim";
import fs from "node:fs";

const wasmBytes = fs.readFileSync("target/wasm32-wasip1/release/datatoad_web.wasm");
const csv = fs.readFileSync("arc.csv");

let out = "";
const stdout = ConsoleStdout.lineBuffered((l) => { out += l + "\n"; });
const stderr = ConsoleStdout.lineBuffered((l) => { out += "[stderr] " + l + "\n"; });

// Preopen "/" holding arc.csv, so the guest opens "/arc.csv".
const root = new PreopenDirectory("/", new Map([["arc.csv", new File(csv)]]));

const wasi = new WASI([], [], [new OpenFile(new File([])), stdout, stderr, root]);
const { instance } = await WebAssembly.instantiate(wasmBytes, {
  wasi_snapshot_preview1: wasi.wasiImport,
});
wasi.initialize(instance); // reactor, not a command

const { alloc, eval: evalLine, memory } = instance.exports;
const enc = new TextEncoder();
function run(line) {
  const bytes = enc.encode(line);
  const ptr = alloc(bytes.length);
  new Uint8Array(memory.buffer, ptr, bytes.length).set(bytes);
  evalLine(ptr, bytes.length);
}

const session = [
  ".note --- demo 1: inline facts + synthetic gen + recursion ---",
  "edge(1,2) :- .", "edge(2,3) :- .", "edge(1,3) :- .",
  ".list",
  ".note synthetic graph with no file: a 30x30 grid of arcs via :range",
  "arc(x,y) :- :range(0,x,30), :range(0,y,30).",
  "path(x,y) :- arc(x,y).",
  "path(x,z) :- path(x,y), arc(y,z).",
  ".list",
  ".note --- demo 2: load data from the (virtual) filesystem ---",
  ".wipe",
  ".time reset",
  ".flow arc /arc.csv",
  ".time loaded",
  "path(x,y) :- arc(x,y).",
  "path(x,z) :- path(x,y), arc(y,z).",
  ".time reach computed",
  ".list",
  ".test path 40000",
];
for (const line of session) { out += "> " + line + "\n"; run(line); }

process.stdout.write(out);
