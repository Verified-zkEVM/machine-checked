#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let mut s = 1.0f32;
    for _ in 0..16 {
        let a = i.u16() as f32 * 0.37 - 5000.0; let b = i.u8() as f32 + 0.25;
        s = s + a * b; out(s.to_bits() as u64); s = s / b - a; out(s.to_bits() as u64);
        out((s as i32) as u64); out((a as f64 * 3.0).to_bits()); out((s > a) as u64);
    }
}
