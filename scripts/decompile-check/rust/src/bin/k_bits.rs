#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    for _ in 0..8 {
        let x = i.u64(); let s = i.u8() as u32;
        out(x.count_ones() as u64); out(x.leading_zeros() as u64); out(x.trailing_zeros() as u64);
        out(x.rotate_left(s)); out(x.swap_bytes()); out(x.reverse_bits());
        out((x as u32).count_ones() as u64); out((x as u32).leading_zeros() as u64); out((x as u32).rotate_right(s) as u64);
        out((x as u32).swap_bytes() as u64); out((x as u16).reverse_bits() as u64); out((x as u8).rotate_left(s) as u64);
        out((x as i64).abs_diff(s as i64)); out((x as i8).saturating_mul(3) as u64); out((x as u16).saturating_add(s as u16 * 999) as u64);
        out((x as i32).pow(s % 5) as u32 as u64 & 0xff); out(x.checked_next_power_of_two().unwrap_or(1)); out((x as u32).isqrt() as u64);
    }
}
