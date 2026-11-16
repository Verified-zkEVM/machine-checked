#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    use std::collections::BTreeMap;
    let mut m: BTreeMap<u16, u32> = BTreeMap::new();
    for k in 0..120u32 {
        let key = i.u8() as u16 * 3 % 97;
        if k % 5 == 4 { if let Some(v) = m.remove(&key) { out(v as u64); } } else { *m.entry(key).or_insert(k) += key as u32; }
    }
    for (k, v) in &m { out((*k as u64) << 32 | *v as u64); }
    out(m.range(20..60).count() as u64);
    out(m.keys().next_back().copied().unwrap_or(0) as u64);
}
