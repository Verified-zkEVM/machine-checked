#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let n = 200 + i.u8() as usize * 8;
    let mut s = vec![true; n + 1]; s[0] = false; s[1] = false;
    let mut k = 2;
    while k * k <= n { if s[k] { let mut j = k * k; while j <= n { s[j] = false; j += k; } } k += 1; }
    let primes: Vec<u32> = (0..=n).filter(|&k| s[k]).map(|k| k as u32).collect();
    out(primes.len() as u64); out(*primes.last().unwrap() as u64);
    out(primes.iter().fold(0u64, |h, &p| h.wrapping_mul(1000003) ^ p as u64));
    let g = |mut a: u64, mut b: u64| { while b != 0 { let t = a % b; a = b; b = t; } a };
    out(g(i.u64(), i.u64() | 1)); out(g(i.u32() as u64 * 12, 18));
}
