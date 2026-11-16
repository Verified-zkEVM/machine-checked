#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let mut s = [i.u32(), i.u32(), i.u32(), i.u32(), 0x61707865, 0x3320646e, 0x79622d32, 0x6b206574];
    for r in 0..20 {
        let (a, b, c, d) = (r % 4, (r + 1) % 4 + 4, (r + 2) % 4, (r + 3) % 4 + 4);
        s[a] = s[a].wrapping_add(s[b]); s[d] = (s[d] ^ s[a]).rotate_left(16);
        s[c] = s[c].wrapping_add(s[d]); s[b] = (s[b] ^ s[c]).rotate_left(12);
        s[a] = s[a].wrapping_add(s[b]); s[d] = (s[d] ^ s[a]).rotate_left(8);
        s[c] = s[c].wrapping_add(s[d]); s[b] = (s[b] ^ s[c]).rotate_left(7);
    }
    for x in s { out(x as u64); }
    let mut x = i.u64() | 1;
    for _ in 0..30 { x ^= x << 13; x ^= x >> 7; x ^= x << 17; }
    out(x);
}
