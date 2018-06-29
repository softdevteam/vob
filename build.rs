extern crate rustc_version;

use rustc_version::{version_meta, Channel};

fn main() {
    // Set features depending on channel
    if let Channel::Nightly = version_meta().unwrap().channel {
        println!("cargo:rustc-cfg=nightly");
        // Nightly supports https://github.com/rust-lang/rust/issues/48763
        println!("cargo:rustc-cfg=reverse_bits");
    }
}
