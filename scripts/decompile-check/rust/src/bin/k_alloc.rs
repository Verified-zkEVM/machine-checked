#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let mut vs: Vec<Vec<u8>> = Vec::new();
    for k in 0..60usize {
        let b = i.u8() as usize;
        match b % 5 {
            0 => vs.push(vec![b as u8; b * 3 + 1]), 1 => { if !vs.is_empty() { let j = b % vs.len(); vs.swap_remove(j); } }
            2 => { if let Some(v) = vs.last_mut() { v.extend_from_slice(&[k as u8; 37]); v.shrink_to_fit(); } }
            3 => { let s: String = "xy".repeat(b); vs.push(s.into_bytes()); }
            _ => { let mut v = Vec::with_capacity(1); for x in 0..b { v.push(x as u8); } vs.insert(0, v); }
        }
    }
    out(vs.len() as u64); out(vs.iter().map(|v| v.len() as u64).sum());
    out(vs.iter().flatten().fold(0u64, |h, &x| h.wrapping_mul(1099511628211) ^ x as u64));
    let b = Box::new([i.u64(); 64]); out(b[63]); let bs: Box<[u8]> = i.a.clone().into_boxed_slice(); out(bs.len() as u64);
}
