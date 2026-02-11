#[unsafe(no_mangle)]
pub extern "C" fn short(f: f64) -> u64 {
    let (d, _p) = fpfmt::short(f);
    d
}

#[unsafe(no_mangle)]
pub extern "C" fn parse(d: u64, p: i32) -> f64 {
    fpfmt::parse(d, p)
}
