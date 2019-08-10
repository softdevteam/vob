extern crate rustc_version;

use rustc_version::{version, Version};

fn main() {
    // Set features depending on channel
    if version().unwrap() >= Version::parse("1.37.0").unwrap() {
        println!("cargo:rustc-cfg=reverse_bits");
    }
}
