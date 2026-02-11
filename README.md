# fpfmt

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

## Benchmarks

Formatting and parsing 8 representative f64 values (`1.0`, `0.1`, `3.14`, `PI`, `E`, `1e23`, `5e-324`, `1.7976931348623157e308`).

Measured on Apple M3 Pro, macOS 15.7.3 (aarch64):

| Task | fpfmt | ryu | stdlib |
|------|------:|----:|-------:|
| **format** (f64 → string) | 102 ns | 164 ns | 535 ns |
| **parse** (string → f64) | 797 ns | — | 702 ns |

```sh
cargo bench -p bench
```

## Wasm size

32,905 bytes for `short` + `parse` as a cdylib (`wasm32-unknown-unknown`, `-Os`).

```sh
RUSTFLAGS="-C opt-level=s" cargo build --target wasm32-unknown-unknown --release -p wasm-size
RUSTFLAGS="-C opt-level=z" cargo build --target wasm32-unknown-unknown --release -p wasm-size
wc -c target/wasm32-unknown-unknown/release/wasm_size.wasm
```

## License

Same as the original: BSD-style. See [LICENSE](LICENSE).
