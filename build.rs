fn main() {
    // The shader is compiled at runtime by the Metal driver (no Xcode required).
    // We only need to trigger a rebuild when the source changes.
    println!("cargo:rerun-if-changed=src/facts/radix_sort_metal.metal");
}
