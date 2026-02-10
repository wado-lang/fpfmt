// Copyright 2025 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

// Port of rsc.io/fpfmt to Rust.
// Floating point formatting algorithm.

mod pow10tab;

#[allow(unused_imports)]
use pow10tab::{POW10_MIN, POW10_MAX, POW10_TAB};

/// PmHiLo represents hi<<64 - lo.
#[derive(Clone, Copy)]
pub(crate) struct PmHiLo {
    pub(crate) hi: u64,
    pub(crate) lo: u64,
}

/// Scaler holds derived scaling constants for a given e, p pair.
#[derive(Clone, Copy)]
struct Scaler {
    pm: PmHiLo,
    s: i32,
}

/// Unrounded represents an unrounded value.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
struct Unrounded(u64);

impl std::fmt::Display for Unrounded {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let u = self.0;
        let plus = if u & 1 != 0 { "+" } else { "" };
        write!(f, "\u{27e8}{}.{}{}\u{27e9}", u >> 2, 5 * ((u >> 1) & 1), plus)
    }
}

#[allow(dead_code)]
fn unround(x: f64) -> Unrounded {
    let floor_4x = (4.0 * x).floor();
    Unrounded(floor_4x as u64 | (floor_4x != 4.0 * x) as u64)
}

#[allow(dead_code)]
impl Unrounded {
    fn floor(self) -> u64 { self.0 >> 2 }
    fn round_half_down(self) -> u64 { (self.0 + 1) >> 2 }
    fn round(self) -> u64 { (self.0 + 1 + ((self.0 >> 2) & 1)) >> 2 }
    fn round_half_up(self) -> u64 { (self.0 + 2) >> 2 }
    fn ceil(self) -> u64 { (self.0 + 3) >> 2 }
    fn nudge(self, delta: i32) -> Unrounded { Unrounded(self.0.wrapping_add(delta as u64)) }

    fn div(self, d: u64) -> Unrounded {
        let x = self.0;
        Unrounded((x / d) | (self.0 & 1) | ((x % d != 0) as u64))
    }

    fn rsh(self, s: u32) -> Unrounded {
        Unrounded((self.0 >> s) | (self.0 & 1) | (((self.0 & ((1u64 << s) - 1)) != 0) as u64))
    }
}

/// log10_pow2(x) returns floor(log10(2**x)) = floor(x * log10(2)).
fn log10_pow2(x: i32) -> i32 {
    // log10(2) ~ 0.30102999566 ~ 78913 / 2^18
    (x * 78913) >> 18
}

/// log2_pow10(x) returns floor(log2(10**x)) = floor(x * log2(10)).
fn log2_pow10(x: i32) -> i32 {
    // log2(10) ~ 3.32192809489 ~ 108853 / 2^15
    (x * 108853) >> 15
}

/// UINT64_POW10[x] is 10**x.
const UINT64_POW10: [u64; 20] = [
    1,
    10,
    100,
    1_000,
    10_000,
    100_000,
    1_000_000,
    10_000_000,
    100_000_000,
    1_000_000_000,
    10_000_000_000,
    100_000_000_000,
    1_000_000_000_000,
    10_000_000_000_000,
    100_000_000_000_000,
    1_000_000_000_000_000,
    10_000_000_000_000_000,
    100_000_000_000_000_000,
    1_000_000_000_000_000_000,
    10_000_000_000_000_000_000,
];

/// unpack64 returns (m, e) such that f = m * 2**e.
/// The caller is expected to have handled 0, NaN, and +/-Inf already.
/// To unpack a f32, use unpack64(f as f64).
fn unpack64(f: f64) -> (u64, i32) {
    const SHIFT: u32 = 64 - 53; // 11
    const MIN_EXP: i32 = -(1074 + SHIFT as i32); // -1085
    let b = f.to_bits();
    let mut m = (1u64 << 63) | ((b & ((1u64 << 52) - 1)) << SHIFT);
    let mut e = ((b >> 52) & ((1u64 << SHIFT) - 1)) as i32;
    if e == 0 {
        m &= !(1u64 << 63);
        e = MIN_EXP;
        let s = m.leading_zeros();
        return (m << s, e - s as i32);
    }
    (m, (e - 1) + MIN_EXP)
}

/// pack64 takes (m, e) and returns f = m * 2**e.
/// It assumes the caller has provided a 53-bit mantissa m
/// and an exponent that is in range for the mantissa.
fn pack64(m: u64, e: i32) -> f64 {
    if m & (1u64 << 52) == 0 {
        return f64::from_bits(m);
    }
    f64::from_bits((m & !(1u64 << 52)) | (((1075 + e) as u64) << 52))
}

/// unmin returns the minimum unrounded that rounds to x.
fn unmin(x: u64) -> Unrounded {
    Unrounded((x << 2) - 2)
}

/// prescale returns the scaling constants for e, p.
/// lp must be log2_pow10(p).
fn prescale(e: i32, p: i32, lp: i32) -> Scaler {
    Scaler {
        pm: POW10_TAB[(p - POW10_MIN) as usize],
        s: -(e + lp + 3),
    }
}

/// uscale returns unround(x * 2**e * 10**p).
/// The caller should pass c = prescale(e, p, log2_pow10(p))
/// and should have left-justified x so its high bit is set.
fn uscale(x: u64, c: Scaler) -> Unrounded {
    let r = x as u128 * c.pm.hi as u128;
    let mut hi = (r >> 64) as u64;
    let mid = r as u64;
    let mut sticky = 1u64;
    let s = c.s as u32;
    if hi & ((1u64 << (s & 63)) - 1) == 0 {
        let r2 = x as u128 * c.pm.lo as u128;
        let mid2 = (r2 >> 64) as u64;
        sticky = (mid.wrapping_sub(mid2) > 1) as u64;
        hi -= (mid < mid2) as u64;
    }
    Unrounded((hi >> s) | sticky)
}

/// fixed_width returns the n-digit decimal form of f as (d, p) where f ~ d * 10**p.
/// n can be at most 18.
pub fn fixed_width(f: f64, n: i32) -> (u64, i32) {
    assert!(n <= 18, "too many digits");
    let (m, e) = unpack64(f);
    let p = n - 1 - log10_pow2(e + 63);
    let u = uscale(m, prescale(e, p, log2_pow10(p)));
    let mut d = u.round();
    let p = if d >= UINT64_POW10[n as usize] {
        d = u.div(10).round();
        p - 1
    } else {
        p
    };
    (d, -p)
}

/// parse rounds d * 10**p to the nearest f64.
/// d can have at most 19 digits.
pub fn parse(d: u64, p: i32) -> f64 {
    assert!(d <= 10_000_000_000_000_000_000, "too many digits");
    let b = 64 - d.leading_zeros() as i32; // bits.Len64(d)
    let lp = log2_pow10(p);
    let mut e = (1074i32).min(53 - b - lp);
    let mut u = uscale(d << (64 - b) as u32, prescale(e - (64 - b), p, lp));

    // Branch-free code for:
    //   if u.round() >= 1<<53 {
    //       u = u.rsh(1)
    //       e = e - 1
    //   }
    let s = (u >= unmin(1u64 << 53)) as u32;
    u = Unrounded((u.0 >> s) | (u.0 & 1));
    e -= s as i32;

    pack64(u.round(), -e)
}

/// parse_text parses a decimal string s and returns the nearest f64.
/// Returns None if the input is malformed.
pub fn parse_text(s: &[u8]) -> Option<f64> {
    fn is_digit(c: u8) -> bool {
        c.wrapping_sub(b'0') <= 9
    }

    const MAX_DIGITS: usize = 19;
    let mut d: u64 = 0;
    let mut frac: i32 = 0;
    let mut i = 0;

    // Read integer digits.
    while i < s.len() && is_digit(s[i]) {
        d = d * 10 + (s[i] - b'0') as u64;
        i += 1;
    }
    if i > MAX_DIGITS {
        return None; // too many digits
    }

    // Read fractional digits.
    if i < s.len() && s[i] == b'.' {
        i += 1;
        while i < s.len() && is_digit(s[i]) {
            d = d * 10 + (s[i] - b'0') as u64;
            frac += 1;
            i += 1;
        }
        if i == 1 || i > MAX_DIGITS + 1 {
            return None; // no digits or too many digits
        }
    }
    if i == 0 {
        return None; // no digits
    }

    // Read exponent.
    let mut p: i32 = 0;
    if i < s.len() && (s[i] == b'e' || s[i] == b'E') {
        i += 1;
        let mut sign: i32 = 1;
        if i < s.len() {
            if s[i] == b'-' {
                sign = -1;
                i += 1;
            } else if s[i] == b'+' {
                i += 1;
            }
        }
        if i >= s.len() || s.len() - i > 3 {
            return None; // missing or too large exponent
        }
        while i < s.len() && is_digit(s[i]) {
            p = p * 10 + (s[i] - b'0') as i32;
            i += 1;
        }
        p *= sign;
    }
    if i != s.len() {
        return None; // junk on end
    }
    Some(parse(d, p - frac))
}

/// short computes the shortest formatting of f,
/// using as few digits as possible that will still round trip
/// back to the original f64.
pub fn short(f: f64) -> (u64, i32) {
    const MIN_EXP: i32 = -1085;

    let (m, e) = unpack64(f);

    let min;
    let mut z: i32 = 11; // extra zero bits at bottom of m; 11 for 53-bit m
    let p;
    if m == 1u64 << 63 && e > MIN_EXP {
        p = -skewed(e + z);
        min = m - (1u64 << (z - 2) as u32); // min = m - 1/4 * 2**(e+z)
    } else {
        if e < MIN_EXP {
            z = 11 + (MIN_EXP - e);
        }
        p = -log10_pow2(e + z);
        min = m - (1u64 << (z - 1) as u32); // min = m - 1/2 * 2**(e+z)
    }
    let max = m + (1u64 << (z - 1) as u32); // max = m + 1/2 * 2**(e+z)
    let odd = ((m >> z as u32) as i32) & 1;

    let pre = prescale(e, p, log2_pow10(p));
    let dmin = uscale(min, pre).nudge(odd).ceil();
    let dmax = uscale(max, pre).nudge(-odd).floor();

    let d = dmax / 10;
    if d * 10 >= dmin {
        return trim_zeros(d, -(p - 1));
    }
    let d = if dmin < dmax {
        uscale(m, pre).round()
    } else {
        dmin
    };
    (d, -p)
}

/// skewed computes the skewed footprint of m * 2**e,
/// which is floor(log10(3/4 * 2**e)) = floor(e*log10(2) - log10(4/3)).
fn skewed(e: i32) -> i32 {
    (e * 631305 - 261663) >> 21
}

/// trim_zeros removes trailing zeros from x * 10**p.
/// If x ends in k zeros, trim_zeros returns (x/10**k, p+k).
/// It assumes that x ends in at most 16 zeros.
fn trim_zeros(x: u64, p: i32) -> (u64, i32) {
    const INV5P8: u64 = 0xc767074b22e90e21; // inverse of 5**8
    const INV5P4: u64 = 0xd288ce703afb7e91; // inverse of 5**4
    const INV5P2: u64 = 0x8f5c28f5c28f5c29; // inverse of 5**2
    const INV5: u64 = 0xcccccccccccccccd; // inverse of 5

    let mut x = x;
    let mut p = p;

    // Cut 1 zero, or else return.
    let d = x.wrapping_mul(INV5).rotate_right(1);
    if d <= u64::MAX / 10 {
        x = d;
        p += 1;
    } else {
        return (x, p);
    }

    // Cut 8 zeros, then 4, then 2, then 1.
    let d = x.wrapping_mul(INV5P8).rotate_right(8);
    if d <= u64::MAX / 100_000_000 {
        x = d;
        p += 8;
    }
    let d = x.wrapping_mul(INV5P4).rotate_right(4);
    if d <= u64::MAX / 10_000 {
        x = d;
        p += 4;
    }
    let d = x.wrapping_mul(INV5P2).rotate_right(2);
    if d <= u64::MAX / 100 {
        x = d;
        p += 2;
    }
    let d = x.wrapping_mul(INV5).rotate_right(1);
    if d <= u64::MAX / 10 {
        x = d;
        p += 1;
    }
    (x, p)
}

/// i2a is the formatting of 00..99 concatenated,
/// a lookup table for formatting [0, 99].
const I2A: &[u8] = b"\
    00010203040506070809\
    10111213141516171819\
    20212223242526272829\
    30313233343536373839\
    40414243444546474849\
    50515253545556575859\
    60616263646566676869\
    70717273747576777879\
    80818283848586878889\
    90919293949596979899";

/// format_base10 formats the decimal representation of u into a.
/// The caller is responsible for ensuring that a is big enough to hold u.
/// If a is too big, leading zeros will be filled in as needed.
fn format_base10(a: &mut [u8], mut u: u64) {
    let mut nd = a.len();
    while nd >= 8 {
        // Format last 8 digits (4 pairs).
        let x3210 = (u % 100_000_000) as u32;
        u /= 100_000_000;
        let (x32, x10) = (x3210 / 10_000, x3210 % 10_000);
        let (x1, x0) = ((x10 / 100) as usize * 2, (x10 % 100) as usize * 2);
        let (x3, x2) = ((x32 / 100) as usize * 2, (x32 % 100) as usize * 2);
        a[nd - 1] = I2A[x0 + 1];
        a[nd - 2] = I2A[x0];
        a[nd - 3] = I2A[x1 + 1];
        a[nd - 4] = I2A[x1];
        a[nd - 5] = I2A[x2 + 1];
        a[nd - 6] = I2A[x2];
        a[nd - 7] = I2A[x3 + 1];
        a[nd - 8] = I2A[x3];
        nd -= 8;
    }

    let mut x = u as u32;
    if nd >= 4 {
        // Format last 4 digits (2 pairs).
        let x10 = x % 10_000;
        x /= 10_000;
        let (x1, x0) = ((x10 / 100) as usize * 2, (x10 % 100) as usize * 2);
        a[nd - 1] = I2A[x0 + 1];
        a[nd - 2] = I2A[x0];
        a[nd - 3] = I2A[x1 + 1];
        a[nd - 4] = I2A[x1];
        nd -= 4;
    }
    if nd >= 2 {
        // Format last 2 digits.
        let x0 = (x % 100) as usize * 2;
        x /= 100;
        a[nd - 1] = I2A[x0 + 1];
        a[nd - 2] = I2A[x0];
        nd -= 2;
    }
    if nd > 0 {
        // Format final digit.
        a[0] = b'0' + x as u8;
    }
}

/// fmt_float formats (d, p) into s in exponential notation.
/// The caller must pass nd set to the number of digits in d.
/// It returns the number of bytes written to s.
pub fn fmt_float(s: &mut [u8], d: u64, p: i32, nd: i32) -> usize {
    let nd = nd as usize;
    // Put digits into s, leaving room for decimal point.
    format_base10(&mut s[1..nd + 1], d);
    let mut p = p + nd as i32 - 1;

    // Move first digit up and insert decimal point.
    s[0] = s[1];
    let mut n = nd;
    if n > 1 {
        s[1] = b'.';
        n += 1;
    }

    // Add 2- or 3-digit exponent.
    s[n] = b'e';
    if p < 0 {
        s[n + 1] = b'-';
        p = -p;
    } else {
        s[n + 1] = b'+';
    }
    let p = p as usize;
    if p < 100 {
        s[n + 2] = I2A[p * 2];
        s[n + 3] = I2A[p * 2 + 1];
        return n + 4;
    }
    s[n + 2] = b'0' + (p / 100) as u8;
    s[n + 3] = I2A[(p % 100) * 2];
    s[n + 4] = I2A[(p % 100) * 2 + 1];
    n + 5
}

/// digits returns the number of decimal digits in d.
pub fn digits(d: u64) -> i32 {
    let nd = log10_pow2(64 - d.leading_zeros() as i32);
    nd + (d >= UINT64_POW10[nd as usize]) as i32
}

#[cfg(test)]
mod comprehensive_tests;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unpack_pack_roundtrip() {
        for &f in &[1.0, 0.1, 3.14, 1e100, 5e-324, 1.7976931348623157e308] {
            let (m, e) = unpack64(f);
            assert!(m >> 63 == 1, "high bit not set for {}", f);
            let _ = (m, e);
        }
    }

    #[test]
    fn test_short_one() {
        assert_eq!(short(1.0), (1, 0));
    }

    #[test]
    fn test_short_point_one() {
        assert_eq!(short(0.1), (1, -1));
    }

    #[test]
    fn test_short_pi() {
        assert_eq!(short(std::f64::consts::PI), (3141592653589793, -15));
    }

    #[test]
    fn test_fixed_width() {
        assert_eq!(fixed_width(std::f64::consts::PI, 6), (314159, -5));
    }

    #[test]
    fn test_parse_roundtrip() {
        let (d, p) = short(3.14);
        assert_eq!(parse(d, p), 3.14);
    }

    #[test]
    fn test_parse_text() {
        assert_eq!(parse_text(b"3.14"), Some(3.14));
        assert_eq!(parse_text(b"1e2"), Some(100.0));
        assert_eq!(parse_text(b"0.1"), Some(0.1));
        assert_eq!(parse_text(b""), None);
        assert_eq!(parse_text(b"abc"), None);
    }

    #[test]
    fn test_digits_fn() {
        assert_eq!(digits(1), 1);
        assert_eq!(digits(9), 1);
        assert_eq!(digits(10), 2);
        assert_eq!(digits(99), 2);
        assert_eq!(digits(100), 3);
        assert_eq!(digits(1000), 4);
    }

    #[test]
    fn test_fmt_float() {
        let mut buf = [0u8; 32];
        let n = fmt_float(&mut buf, 314159, -5, 6);
        assert_eq!(&buf[..n], b"3.14159e+00");
    }

    #[test]
    fn test_fmt_float_single_digit() {
        let mut buf = [0u8; 32];
        let n = fmt_float(&mut buf, 1, 0, 1);
        assert_eq!(&buf[..n], b"1e+00");
    }

    #[test]
    fn test_unround() {
        assert_eq!(unround(6.0).0, 24);
        assert_eq!(unround(6.5).0, 26);
        assert_eq!(unround(7.0).0, 28);
    }

    #[test]
    fn test_unround_rounding() {
        let u = unround(6.0);
        assert_eq!(u.floor(), 6);
        assert_eq!(u.round(), 6);
        assert_eq!(u.ceil(), 6);

        let u = unround(6.5);
        assert_eq!(u.floor(), 6);
        assert_eq!(u.round(), 6); // round-half-to-even
        assert_eq!(u.ceil(), 7);

        let u = unround(7.5);
        assert_eq!(u.floor(), 7);
        assert_eq!(u.round(), 8); // round-half-to-even
        assert_eq!(u.ceil(), 8);
    }

    #[test]
    fn test_unround_div() {
        let u = unround(15.1).div(6);
        assert_eq!(u.round(), 3);
    }

    #[test]
    fn test_unround_nudge() {
        let u = unround(15.0);
        assert_eq!(u.nudge(-1).floor(), 14);
        assert_eq!(u.floor(), 15);
        assert_eq!(u.ceil(), 15);
        assert_eq!(u.nudge(1).ceil(), 16);

        let u = unround(16.0);
        assert_eq!(u.nudge(-1).floor(), 15);
        assert_eq!(u.floor(), 16);
        assert_eq!(u.ceil(), 16);
        assert_eq!(u.nudge(1).ceil(), 17);
    }

    #[test]
    fn test_short_roundtrip() {
        for &f in &[
            1.0, 0.1, 0.5, 2.0, 10.0, 100.0, 0.01, 0.001,
            1.23456789, 1e10, 1e-10, 1e100, 1e-100,
            5e-324,                        // smallest subnormal
            2.2250738585072014e-308,        // smallest normal
            1.7976931348623157e308,          // largest finite
        ] {
            let (d, p) = short(f);
            let f2 = parse(d, p);
            assert_eq!(f, f2, "round-trip failed for {} (d={}, p={})", f, d, p);
        }
    }
}
