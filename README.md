# fpfmt [![crates.io](https://img.shields.io/crates/v/fpfmt)](https://crates.io/crates/fpfmt)

Rust port of [rsc/fpfmt](https://github.com/rsc/fpfmt), a floating-point formatting algorithm.

Provides shortest-representation and fixed-width formatting of f64 values, as well as parsing decimal strings back to f64.

## API

- `short(f: f64) -> (u64, i32)` — shortest decimal that round-trips back to f
- `parse(d: u64, p: i32) -> f64` — round `d * 10^p` to nearest f64
- `parse_text(s: &[u8]) -> Option<f64>` — parse a decimal string to f64
- `fixed_width(f: f64, n: i32) -> (u64, i32)` — n-digit decimal form
- `fmt_float(s: &mut [u8], d: u64, p: i32, nd: i32) -> usize` — format into buffer
- `digits(d: u64) -> i32` — number of decimal digits

## Tools

Regenerate the power-of-10 table:

```sh
cargo run -p pow10gen
```

## Features

### `small` — compact tables for Wasm

The core algorithm needs `10^p` as a 128-bit normalized mantissa for each
exponent `p` in −348..=347. By default, all 696 entries are stored in a flat
lookup table (696 × 16 = 11 KB).

The `small` feature decomposes the lookup using `10^p = 10^(27q) × 10^r`
where `p = 27q + r` and `0 ≤ r < 27`. This replaces the single table with:

- `POW10_COARSE`: 26 entries of `(u64, u64)` for `10^(27q)` — 416 bytes
- `POW10_FINE`: 27 entries of `u64` for `10^r` — 216 bytes

Fine entries need only one `u64` (not two) because `10^r` for `r ≤ 26` is
exact at 128 bits and the low 64 bits are always zero.

At runtime, `prescale` multiplies the two factors back together with u128
arithmetic instead of doing a direct table lookup. This reduces Wasm binary
size from 14 KB to **4 KB** with a modest formatting slowdown (~1.6x),
while parsing is unaffected. Still **2.4x faster** than ryu for formatting.

```toml
fpfmt = { version = "0.2", features = ["small"] }
```

## Benchmarks

Formatting and parsing 8 representative f64 values (`1.0`, `0.1`, `3.14`, `PI`, `E`, `1e23`, `5e-324`, `1.7976931348623157e308`).

Measured on Apple M3 Pro, macOS 15.7.3 (aarch64):

| Task                      |  fpfmt | fpfmt `small` |    ryu | stdlib |
| ------------------------- | -----: | ------------: | -----: | -----: |
| **format** (f64 → string) |  63 ns |         99 ns | 239 ns | 529 ns |
| **parse** (string → f64)  | 690 ns |        700 ns |      — | 675 ns |

```sh
cargo bench -p bench
cargo bench -p bench --features small
```

## Wasm size

| Configuration |            Size |
| ------------- | --------------: |
| default       |    14,379 bytes |
| `small`       | **4,175 bytes** |

```sh
cargo build --target wasm32-unknown-unknown --release -p wasm-size
cargo build --target wasm32-unknown-unknown --release -p wasm-size --features small
wc -c target/wasm32-unknown-unknown/release/wasm_size.wasm
```

## License

Same as the original: BSD-style. See [LICENSE](LICENSE).
