use std::f64::consts::{E, PI};
use std::fmt::Write as _;

use criterion::{Criterion, black_box, criterion_group, criterion_main};

#[allow(clippy::approx_constant)]
const VALUES: [f64; 8] = [
    1.0,
    0.1,
    3.14,
    PI,
    E,
    1e23,
    5e-324,                 // smallest subnormal
    1.7976931348623157e308, // largest finite
];

fn bench_format(c: &mut Criterion) {
    let mut group = c.benchmark_group("format");

    group.bench_function("fpfmt", |b| {
        b.iter(|| {
            let mut buf = [0u8; 32];
            for &f in &VALUES {
                let (d, p) = fpfmt::short(black_box(f));
                let nd = fpfmt::digits(d);
                let _ = fpfmt::fmt_float(&mut buf, d, p, nd);
            }
        });
    });

    group.bench_function("ryu", |b| {
        b.iter(|| {
            let mut buf = ryu::Buffer::new();
            for &f in &VALUES {
                buf.format(black_box(f));
            }
        });
    });

    group.bench_function("stdlib", |b| {
        b.iter(|| {
            let mut buf = String::with_capacity(32);
            for &f in &VALUES {
                buf.clear();
                write!(buf, "{}", black_box(f)).unwrap();
            }
        });
    });

    group.finish();
}

fn bench_parse(c: &mut Criterion) {
    let strings: Vec<String> = VALUES.iter().map(|f| f.to_string()).collect();

    let mut group = c.benchmark_group("parse");

    group.bench_function("fpfmt", |b| {
        b.iter(|| {
            for s in &strings {
                let _ = fpfmt::parse_text(black_box(s.as_bytes()));
            }
        });
    });

    group.bench_function("stdlib", |b| {
        b.iter(|| {
            for s in &strings {
                black_box(s).parse::<f64>().unwrap();
            }
        });
    });

    group.finish();
}

criterion_group!(benches, bench_format, bench_parse);
criterion_main!(benches);
