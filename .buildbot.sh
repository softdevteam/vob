#! /bin/sh

set -e

export CARGO_HOME="`pwd`/.cargo"
export RUSTUP_HOME="`pwd`/.rustup"

curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs > rustup.sh
sh rustup.sh --default-host x86_64-unknown-linux-gnu --default-toolchain stable -y --no-modify-path

export PATH=`pwd`/.cargo/bin/:$PATH

cargo test
cargo test --features "unsafe_internals"
cargo test --release
cargo test --release --features "unsafe_internals"
cargo bench

cargo fmt --all -- --check

which cargo-deny || cargo install cargo-deny || true
if [ "X`which cargo-deny`" != "X" ]; then
    cargo-deny check license
fi
