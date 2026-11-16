#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let mut st = 0u32; let mut acc = 0u64;
    let data: Vec<u8> = i.a.iter().chain(i.b.iter()).copied().collect();
    for &b in &data {
        st = match (st, b & 7) {
            (0, 0) => 1, (0, 1) => 5, (0, _) => 2,
            (1, x) if x < 4 => { acc += x as u64; 3 }
            (1, _) => 0,
            (2, 7) => { acc = acc.wrapping_mul(17); 4 }
            (2, _) => 1,
            (3, 2) | (3, 3) => 6,
            (3, _) => { acc ^= 0xabcd; 0 }
            (4, x) => x as u32 % 7,
            (5, 5) => 5,
            (5, _) => { acc = acc.rotate_left(3); 2 }
            (6, 0) => 0,
            (_, x) => { acc += 1 << x; 4 }
        };
        acc = match b >> 3 {
            0 => acc + 1, 1 => acc ^ 2, 2 => acc.wrapping_mul(3), 3 => acc >> 1, 4 => acc | 16, 5 => acc.wrapping_sub(5),
            6 => !acc, 7 => acc << 2, 8 => acc.rotate_left(9), 9 => acc ^ acc >> 3, 10 => acc.wrapping_add(st as u64),
            11 => acc & 0xffff_ffff_0000_ffff, 12 => acc.swap_bytes(), 13 => acc + 13, 14 => acc.wrapping_mul(acc | 1),
            15 => acc.count_ones() as u64, 16 => acc.leading_zeros() as u64 + acc, 17 => acc % 1000003, _ => acc,
        };
    }
    out(st as u64); out(acc);
}
