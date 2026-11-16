#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let mut s = 0.0f64;
    for k in 0..12 {
        let (a, b) = (i.u32() as f64 / 7.0, i.u16() as f64 - 300.5);
        s = s * 0.5 + a * b - (if b != 0.0 { a / b } else { 1.0 });
        out(s.to_bits()); out((a < b) as u64); out((s as i64) as u64); out((k as f64 + a).to_bits());
    }
    let mut r = 2.0f64; let x = i.u16() as f64 + 1.0;
    for _ in 0..8 { r = 0.5 * (r + x / r); }
    out(r.to_bits());
    out(f64::from_bits(i.u64()).to_bits()); out((f64::from_bits(i.u64()) + 1.0).to_bits());
}
