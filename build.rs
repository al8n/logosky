use std::env;

fn main() {
  // Avoid unnecessary rebuilds.
  println!("cargo:rerun-if-changed=build.rs");

  // Always rerun if these env vars change.
  println!("cargo:rerun-if-env-changed=CARGO_TARPAULIN");
  println!("cargo:rerun-if-env-changed=CARGO_CFG_TARPAULIN");

  // Detect tarpaulin by environment variable
  if env::var("CARGO_TARPAULIN").is_ok() {
    enable_cfg("tarpaulin");
  }
}

/// Emit `cargo:rustc-cfg=...` to define a conditional compilation flag.
fn enable_cfg(flag: &str) {
  println!("cargo:rustc-cfg={}", flag);
}
