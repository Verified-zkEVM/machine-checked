#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let mut a = [[0u64; 4]; 4]; let mut b = [[0i32; 4]; 4];
    for r in 0..4 { for c in 0..4 { a[r][c] = i.u64(); b[r][c] = i.u16() as i16 as i32; } }
    let mut p = [[0u64; 4]; 4]; let mut q = [[0i32; 4]; 4];
    for r in 0..4 { for c in 0..4 { for k in 0..4 {
        p[r][c] = p[r][c].wrapping_add(a[r][k].wrapping_mul(a[k][c]));
        q[r][c] = q[r][c].wrapping_add(b[r][k].wrapping_mul(b[k][c]));
    } } }
    for r in 0..4 { for c in 0..4 { out(p[r][c]); out(q[r][c] as u64); } }
    out(q.iter().flatten().map(|&x| x as i64).sum::<i64>() as u64);
}
