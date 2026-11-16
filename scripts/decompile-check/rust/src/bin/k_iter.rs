#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let a = &i.a; let b = &i.b;
    out(a.iter().zip(b.iter()).filter(|(x, y)| x > y).map(|(x, y)| (*x as u64) * (*y as u64)).sum());
    out(a.windows(3).filter(|w| w[0] < w[1] && w[1] < w[2]).count() as u64);
    out(a.chunks(5).map(|c| c.iter().map(|&x| x as u32).max().unwrap_or(0)).fold(0u64, |h, m| h * 257 + m as u64));
    out(a.iter().rev().skip(2).step_by(3).take(10).fold(1u64, |h, &x| h.wrapping_mul(x as u64 | 1)));
    out(a.iter().position(|&x| x == 0xff).unwrap_or(1234) as u64);
    out(a.iter().copied().min().unwrap_or(42) as u64);
    let (ev, od): (Vec<u8>, Vec<u8>) = b.iter().partition(|&&x| x % 2 == 0);
    out(ev.len() as u64 * 1000 + od.len() as u64);
    out(b.iter().scan(0u8, |s, &x| { *s = s.wrapping_add(x); Some(*s) }).filter(|s| *s > 128).count() as u64);
    out(a.iter().flat_map(|&x| [x, x ^ 0x55]).any(|x| x == 0) as u64);
    let mut dd = a.clone(); dd.dedup_by_key(|x| *x >> 4); out(dd.len() as u64);
}
