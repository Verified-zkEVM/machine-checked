#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    fn f0(x: u64) -> u64 { x.wrapping_add(1) }
    fn f1(x: u64) -> u64 { x.wrapping_mul(3) }
    fn f2(x: u64) -> u64 { x ^ x >> 7 }
    fn f3(x: u64) -> u64 { x.rotate_right(11) }
    fn f4(x: u64) -> u64 { !x }
    fn f5(x: u64) -> u64 { x.swap_bytes() }
    fn f6(x: u64) -> u64 { x / 3 }
    let t: [fn(u64) -> u64; 7] = [f0, f1, f2, f3, f4, f5, f6];
    let mut x = 0x9e3779b97f4a7c15u64;
    for k in 0..40 { let b = i.u8() as usize; x = t[(b + k) % 7](x); if k % 4 == 0 { out(x); } }
    out(x);
}
