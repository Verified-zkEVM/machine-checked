#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let t = [3u64, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5, 8, 9, 7, 9, 3];
    let mut s = 0u64;
    for _ in 0..12 { let k = i.u8() as usize; out(s); s += t[k % 20]; }
    out(s);
}
