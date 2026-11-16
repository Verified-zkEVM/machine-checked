#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let mut a = i.a.clone();
    a.sort_unstable();
    outs(&a);
    let mut w: Vec<u32> = i.b.chunks(3).map(|c| c.iter().fold(0u32, |x, &y| x << 8 | y as u32)).collect();
    w.sort_by_key(|x| x.rotate_left(7) ^ 0x5bd1e995);
    for x in &w { out(*x as u64); }
    let mut s: Vec<(u8, usize)> = i.a.iter().copied().enumerate().map(|(k, v)| (v & 15, k)).collect();
    s.sort_by(|x, y| y.0.cmp(&x.0));
    out(s.iter().fold(0u64, |h, &(v, k)| h.wrapping_mul(31).wrapping_add(v as u64 * 257 + k as u64)));
}
