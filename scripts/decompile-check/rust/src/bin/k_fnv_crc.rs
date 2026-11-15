#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let mut h = 0xcbf29ce484222325u64;
    for &b in &i.a { h = (h ^ b as u64).wrapping_mul(0x100000001b3); }
    out(h);
    let mut c = !0u32;
    for &b in &i.b {
        c ^= b as u32;
        for _ in 0..8 { c = if c & 1 != 0 { c >> 1 ^ 0xedb88320 } else { c >> 1 }; }
    }
    out(!c as u64);
}
