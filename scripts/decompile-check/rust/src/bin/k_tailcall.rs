#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    #[inline(never)] fn even(n: u64, acc: u64) -> u64 { if n == 0 { acc } else { odd(n - 1, acc.wrapping_mul(3) + 1) } }
    #[inline(never)] fn odd(n: u64, acc: u64) -> u64 { if n == 0 { !acc } else { even(n - 1, acc ^ n) } }
    #[inline(never)] fn pick(k: u8, x: u64) -> u64 { let f: fn(u64, u64) -> u64 = if k & 1 == 0 { even } else { odd }; f(x % 50, x) }
    out(even(i.u16() as u64 + 5000, 1)); out(odd(i.u8() as u64, 7));
    for _ in 0..6 { out(pick(i.u8(), i.u64())); }
}
