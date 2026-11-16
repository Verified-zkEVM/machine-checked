// SP1 only: `HashMap` needs the standard library
#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    use std::collections::HashMap; use std::hash::{BuildHasherDefault, Hasher};
    #[derive(Default)] struct Fnv(u64);
    impl Hasher for Fnv { fn finish(&self) -> u64 { self.0 } fn write(&mut self, b: &[u8]) { for &x in b { self.0 = (self.0 ^ x as u64).wrapping_mul(0x100000001b3); } } }
    let mut m: HashMap<u16, Vec<u8>, BuildHasherDefault<Fnv>> = HashMap::default();
    for _ in 0..150 { let k = i.u8() as u16 % 40; let v = i.u8(); if v % 7 == 0 { m.remove(&k); } else { m.entry(k).or_default().push(v); } }
    let mut keys: Vec<_> = m.keys().copied().collect(); keys.sort();
    for k in keys { out((k as u64) << 32 | m[&k].len() as u64); }
    out(m.values().flatten().map(|&x| x as u64).sum()); out(m.contains_key(&7) as u64);
}
