// Comprehensive tests ported from Go fpfmt_test.go.

#![allow(clippy::float_cmp, clippy::unreadable_literal)]

use fpfmt::*;

const TEST_IVY: &str = include_str!("testdata/test.ivy");
include!("hard_tests.rs");

// ---- Utility functions ----

/// `ldexp(x, exp)` returns `x * 2**exp`.
fn ldexp(x: f64, mut exp: i32) -> f64 {
    // 2^1023 as f64
    const POW2_1023: f64 = 8.98846567431158e+307; // f64::from_bits(0x7FE0000000000000)
    // 2^(-1022) as f64
    const POW2_NEG1022: f64 = 2.2250738585072014e-308; // f64::from_bits(0x0010000000000000)

    if x == 0.0 || x.is_infinite() || x.is_nan() {
        return x;
    }
    let mut result = x;
    while exp > 1023 {
        result *= POW2_1023;
        exp -= 1023;
    }
    while exp < -1022 {
        result *= POW2_NEG1022;
        exp += 1022;
    }
    result * f64::from_bits(((exp + 1023) as u64) << 52)
}

/// Parse a hex float literal like `0x1.0000000000001p-229`.
fn parse_hex_float(s: &str) -> f64 {
    if let Some(rest) = s.strip_prefix('-') {
        return -parse_hex_float(rest);
    }
    let s = s.strip_prefix("0x").or_else(|| s.strip_prefix("0X")).unwrap_or(s);

    let (mant_str, exp_str) = s
        .split_once('p')
        .or_else(|| s.split_once('P'))
        .expect("hex float must contain 'p'");
    let exp: i32 = exp_str.parse().unwrap();

    let (int_str, frac_str) = mant_str.split_once('.').unwrap_or((mant_str, ""));

    let int_val = u64::from_str_radix(int_str, 16).unwrap();
    let frac_val = if frac_str.is_empty() {
        0u64
    } else {
        u64::from_str_radix(frac_str, 16).unwrap()
    };
    let frac_bits = frac_str.len() as i32 * 4;

    // combined mantissa = int_val * 2^frac_bits + frac_val
    let combined = (int_val << frac_bits as u32) | frac_val;
    // value = combined * 2^(exp - frac_bits)
    ldexp(combined as f64, exp - frac_bits)
}

/// Returns the next f64 toward positive infinity.
fn nextafter_up(f: f64) -> f64 {
    if f.is_nan() || f == f64::INFINITY {
        return f;
    }
    if f == 0.0 {
        return f64::from_bits(1);
    }
    let bits = f.to_bits();
    if f > 0.0 {
        f64::from_bits(bits + 1)
    } else {
        f64::from_bits(bits - 1)
    }
}

/// Returns the next f64 toward negative infinity.
fn nextafter_down(f: f64) -> f64 {
    if f.is_nan() || f == f64::NEG_INFINITY {
        return f;
    }
    if f == 0.0 {
        return -f64::from_bits(1);
    }
    let bits = f.to_bits();
    if f > 0.0 {
        f64::from_bits(bits - 1)
    } else {
        f64::from_bits(bits + 1)
    }
}

// ---- Test data generators ----

struct IvyTest {
    n: i32,
    f: f64,
    d: u64,
    p: i32,
}

fn ivy_tests() -> Vec<IvyTest> {
    let mut tests = vec![IvyTest {
        n: 7,
        f: parse_hex_float("0x1.18352262653f8p+19"),
        d: 5738651,
        p: -1,
    }];

    for line in TEST_IVY.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        // Format: (N ftoa HEXFLOAT) is D P
        let rest = line.strip_prefix('(').expect("bad ivy line: missing (");
        let (n_str, rest) = rest.split_once(' ').expect("bad ivy line: missing space after N");
        let n: i32 = n_str.parse().expect("bad ivy line: bad N");

        let rest = rest.strip_prefix("ftoa ").expect("bad ivy line: missing ftoa");
        let (hex_str, rest) = rest.split_once(')').expect("bad ivy line: missing )");
        let f = parse_hex_float(hex_str);

        let rest = rest.strip_prefix(" is ").expect("bad ivy line: missing is");
        let (d_str, p_str) = rest.split_once(' ').expect("bad ivy line: missing space before P");
        let d: u64 = d_str.parse().expect("bad ivy line: bad D");
        let p: i32 = p_str.parse().expect("bad ivy line: bad P");

        tests.push(IvyTest { n, f, d, p });
    }

    tests
}

/// Equivalent of Go's `someTestFloats()`: powers of 2, powers of 10, unique ivy inputs.
fn some_test_floats() -> Vec<f64> {
    let mut floats = Vec::new();

    // Powers of 2: 2^e for e in -1074..=1024
    for e in -1074..=1024i32 {
        let f = if e >= -1022 {
            if e <= 1023 {
                // Normal: 2^e = f64 with biased exponent (e+1023), mantissa 0
                f64::from_bits(((e + 1023) as u64) << 52)
            } else {
                // e = 1024 -> infinity
                f64::INFINITY
            }
        } else {
            // Subnormal: 2^e where -1074 <= e < -1022
            // bit position in mantissa field = e + 1074
            f64::from_bits(1u64 << (e + 1074) as u32)
        };
        floats.push(f);
    }

    // Powers of 10: 10^p for p in -308..=308
    for p in -308..=308i32 {
        floats.push(10.0_f64.powi(p));
    }

    // Unique inputs from ivy test data.
    let mut last = -1.0_f64;
    for tt in ivy_tests() {
        if tt.f != last {
            last = tt.f;
            floats.push(last);
        }
    }

    floats
}

/// Equivalent of Go's `testFloats()`: `someTestFloats` plus nextafter neighbors.
fn all_test_floats() -> Vec<f64> {
    let mut floats = Vec::new();
    for f in some_test_floats() {
        floats.push(f);
        floats.push(nextafter_down(f));
        floats.push(nextafter_up(f));
    }
    floats
}

/// Generate floats from the hard table (ported from Go's `hardFloats`).
fn hard_floats() -> Vec<f64> {
    let mut out = Vec::new();
    for &(p, xmin, xmax) in HARD {
        // Go uses -int(math.Floor(math.Log2(math.Pow10(p)))) which is -floor(p*log2(10)).
        // Use the integer approximation: floor(p * 108853 / 32768).
        let pe = -((p * 108_853) >> 15);
        for exp in (pe - 3..=pe + 64).step_by(3) {
            let f = ldexp(xmin as f64, exp);
            if f != 0.0 && !f.is_infinite() {
                out.push(f);
            }
            let f = ldexp(xmax as f64, exp);
            if f != 0.0 && !f.is_infinite() {
                out.push(f);
            }
        }
    }
    out
}

/// Generate random floats matching Go's `math/rand/v2` `ChaCha8` with zero seed.
fn rand_floats() -> Vec<f64> {
    let seed = [0u8; 32];
    let mut rng = chacha8rand::ChaCha8Rand::new(&seed);
    let mut fs = Vec::with_capacity(10000);
    let n: u64 = (1u64 << 63) - (1u64 << 52); // 0x7FF0000000000000
    for _ in 0..10000 {
        let x = uint64n(&mut rng, n);
        fs.push(f64::from_bits(x));
    }
    fs
}

/// Port of Go's `math/rand/v2` `Uint64N` (Lemire's algorithm).
fn uint64n(rng: &mut chacha8rand::ChaCha8Rand, n: u64) -> u64 {
    if n.is_power_of_two() {
        return rng.read_u64() & (n - 1);
    }
    let (mut hi, mut lo) = mul128(rng.read_u64(), n);
    if lo < n {
        let thresh = n.wrapping_neg() % n;
        while lo < thresh {
            (hi, lo) = mul128(rng.read_u64(), n);
        }
    }
    hi
}

fn mul128(a: u64, b: u64) -> (u64, u64) {
    let r = u128::from(a) * u128::from(b);
    ((r >> 64) as u64, r as u64)
}

// ---- Tests ----

/// `TestShort` comprehensive: verify `short(f)` round-trips for all test floats.
/// Port of Go's `TestShort` (uscale implementation).
#[test]
fn test_short_all_test_floats() {
    let mut fail = 0;
    for f in all_test_floats() {
        if f == 0.0 || f.is_infinite() {
            continue;
        }
        let (d, p) = short(f);
        let f2 = parse(d, p);
        if f != f2 {
            eprintln!(
                "short({f:e} = {:#018x}) roundtrip failed: d={d}, p={p}, got {f2:e}",
                f.to_bits(),
            );
            fail += 1;
            assert!(fail < 100, "too many failures");
        }
    }
    assert_eq!(fail, 0, "{fail} failures in short roundtrip (all_test_floats)");
}

/// `TestShort` for hard floats.
#[test]
fn test_short_hard_floats() {
    let mut fail = 0;
    for f in hard_floats() {
        if f == 0.0 || f.is_infinite() {
            continue;
        }
        let (d, p) = short(f);
        let f2 = parse(d, p);
        if f != f2 {
            eprintln!(
                "short({f:e} = {:#018x}) roundtrip failed: d={d}, p={p}, got {f2:e}",
                f.to_bits(),
            );
            fail += 1;
            assert!(fail < 100, "too many failures");
        }
    }
    assert_eq!(fail, 0, "{fail} failures in short roundtrip (hard_floats)");
}

/// `TestShort` for random floats.
#[test]
fn test_short_rand_floats() {
    let mut fail = 0;
    for f in rand_floats() {
        if f == 0.0 || f.is_infinite() {
            continue;
        }
        let (d, p) = short(f);
        let f2 = parse(d, p);
        if f != f2 {
            eprintln!(
                "short({f:e} = {:#018x}) roundtrip failed: d={d}, p={p}, got {f2:e}",
                f.to_bits(),
            );
            fail += 1;
            assert!(fail < 100, "too many failures");
        }
    }
    assert_eq!(fail, 0, "{fail} failures in short roundtrip (rand_floats)");
}

/// `TestShort`: verify formatted output matches Rust's shortest representation.
/// In Go this compares against `strconv.FormatFloat`; here we verify minimality.
#[test]
fn test_short_minimality() {
    let mut fail = 0;
    for f in all_test_floats() {
        if f == 0.0 || f.is_infinite() {
            continue;
        }
        let (d, p) = short(f);
        let nd = digits(d);

        // Verify minimality: reducing to nd-1 digits should NOT round-trip.
        if nd > 1 {
            // Divide d by 10, losing the last digit. If this still round-trips,
            // then short returned too many digits.
            let d_fewer = (d + 5) / 10; // round to nd-1 digits
            let f_fewer = parse(d_fewer, p + 1);
            if f_fewer == f {
                eprintln!(
                    "short({f:e}) not minimal: d={d} ({nd}d), d_fewer={d_fewer} also works",
                );
                fail += 1;
                assert!(fail < 100, "too many failures");
            }
        }
    }
    assert_eq!(fail, 0, "{fail} failures in short minimality");
}

/// `TestParse` comprehensive: verify parse against Rust stdlib for many inputs.
/// Port of Go's `TestParse` / `parseTests`.
#[test]
fn test_parse_comprehensive() {
    let mut fail = 0;

    for f in all_test_floats() {
        if f.is_infinite() || f == 0.0 {
            continue;
        }

        // Test with 17-digit fixed width
        let (d, p) = fixed_width(f, 17);
        let s = format!("{d}e{p}");
        let have = parse_text(s.as_bytes());
        if have != Some(f) {
            eprintln!("parse_text({s}) = {have:?}, want {f:e}");
            fail += 1;
        }

        // Nudge test for 17 digits
        if p > -300 {
            for i in -3i64..=3 {
                let d1 = d.wrapping_add(i as u64);
                let s = format!("{d1}e{p}");
                let want: f64 = match s.parse() {
                    Ok(v) => v,
                    Err(_) => continue,
                };
                if want.is_infinite() {
                    continue;
                }
                if let Some(have) = parse_text(s.as_bytes()) {
                    if have != want {
                        eprintln!(
                            "parse_text({s}) = {have:e}, want {want:e} (17d nudge i={i})",
                        );
                        fail += 1;
                    }
                }
            }
        }

        // Test with 18-digit fixed width
        let (d, p) = fixed_width(f, 18);
        let s = format!("{d}e{p}");
        let have = parse_text(s.as_bytes());
        if have != Some(f) {
            eprintln!("parse_text({s}) = {have:?}, want {f:e}");
            fail += 1;
        }

        // Nudge test for 18 digits
        if p > -300 {
            for i in -3i64..=3 {
                let d1 = d.wrapping_add((i * 20) as u64);
                let s = format!("{d1}e{p}");
                let want: f64 = match s.parse() {
                    Ok(v) => v,
                    Err(_) => continue,
                };
                if want.is_infinite() {
                    continue;
                }
                if let Some(have) = parse_text(s.as_bytes()) {
                    if have != want {
                        eprintln!(
                            "parse_text({s}) = {have:e}, want {want:e} (18d nudge i={i})",
                        );
                        fail += 1;
                    }
                }
            }
        }

        // 19-digit test from Rust's standard formatting
        let s = format!("{f:.18e}");
        let dot_pos = s.find('.').unwrap();
        let t = format!("{}{}", &s[..dot_pos], &s[dot_pos + 1..]);
        let e_pos = t.find('e').unwrap();
        let d19: u64 = t[..e_pos].parse().unwrap();
        let exp19: i32 = t[e_pos + 1..].parse().unwrap();
        let p19 = exp19 - (e_pos as i32 - 1);
        let s19 = format!("{d19}e{p19}");
        let want: f64 = s19.parse().unwrap_or(f64::INFINITY);
        if !want.is_infinite() {
            if let Some(have) = parse_text(s19.as_bytes()) {
                if have != want {
                    eprintln!("parse_text({s19}) = {have:e}, want {want:e} (19d)");
                    fail += 1;
                }
            }
        }

        assert!(fail < 100, "too many failures");
    }
    assert_eq!(fail, 0, "{fail} failures in parse comprehensive");
}

/// `TestParseRaw`: verify `Parse(d, p)` against Rust stdlib for ivy test data.
/// Port of Go's `TestParseRaw`.
#[test]
fn test_parse_ivy_raw() {
    let mut fail = 0;
    for tt in ivy_tests() {
        let s = format!("{}e{}", tt.d, tt.p);
        let want: f64 = s.parse().unwrap();
        let have = parse(tt.d, tt.p);
        if have != want {
            eprintln!(
                "parse({}e{}) = {have:e}, want {want:e}",
                tt.d, tt.p,
            );
            fail += 1;
            assert!(fail < 100, "too many failures");
        }
    }
    assert_eq!(fail, 0, "{fail} failures in parse ivy raw");
}

/// `TestFixedWidth`: verify `fixed_width` against ivy test data.
/// Port of Go's `TestFixedWidth`.
#[test]
fn test_fixed_width_ivy() {
    let mut fail = 0;
    let mut have_buf = [0u8; 32];
    let mut want_buf = [0u8; 32];

    for tt in ivy_tests() {
        if tt.n > 18 {
            continue;
        }
        let (d, p) = fixed_width(tt.f, tt.n);
        let have_n = fmt_float(&mut have_buf, d, p, tt.n);
        let want_n = fmt_float(&mut want_buf, tt.d, tt.p, tt.n);
        if have_buf[..have_n] != want_buf[..want_n] {
            let have_s = std::str::from_utf8(&have_buf[..have_n]).unwrap();
            let want_s = std::str::from_utf8(&want_buf[..want_n]).unwrap();
            eprintln!(
                "fixed({:#x}, {}) = {have_s} want {want_s}",
                tt.f.to_bits(),
                tt.n,
            );
            fail += 1;
            assert!(fail < 100, "too many failures");
        }
    }
    assert_eq!(fail, 0, "{fail} failures in fixed_width ivy");
}
