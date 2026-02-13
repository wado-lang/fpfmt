# Floating Point Formatter (fpfmt)

This is a Rust library crate to format floating point numbers.

## Compatibility

The crate is `no_std` and `wasm32-unknown-unknown` compatible.

## Development

```sh
cargo test && cargo test --features small
cargo fmt
cargo clippy && cargo clippy --features small
cargo bench -p bench
cargo bench -p bench --features small
```
