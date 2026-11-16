#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let mut v: Vec<u16> = i.a.chunks(2).map(|c| c[0] as u16 | (*c.get(1).unwrap_or(&0) as u16) << 8).collect();
    v.sort();
    out(v.binary_search(&(i.u16())).unwrap_or_else(|e| e + 1000) as u64);
    v.dedup(); out(v.len() as u64);
    v.retain(|x| x % 3 != 1); out(v.len() as u64);
    if v.len() > 3 { v.rotate_left(2); let h = v.len() / 2; let (l, r) = v.split_at_mut(h); l[0] ^= r[0]; r.reverse(); }
    for x in v.iter().take(12) { out(*x as u64); }
    let mut w: Vec<(u8, u8)> = i.b.iter().map(|&b| (b >> 5, b)).collect();
    w.sort_by_key(|p| p.0);
    out(w.iter().fold(0u64, |h, p| h.wrapping_mul(263) + p.1 as u64));
    out(w.iter().map(|p| p.1).max().unwrap_or(1) as u64); out(v.concat_check());
    trait C { fn concat_check(&self) -> u64; }
    impl C for Vec<u16> { fn concat_check(&self) -> u64 { [&self[..], &self[..]].concat().len() as u64 } }
}
