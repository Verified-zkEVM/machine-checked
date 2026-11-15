#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    for _ in 0..10 {
        let (a, b, s) = (i.u64(), i.u64() >> (i.u8() % 64), i.u8() as u32);
        out((a as i32).wrapping_div(if b as i32 == 0 { 1 } else { b as i32 }) as u64);
        out((a as i32).wrapping_rem(if b as i32 == 0 { 1 } else { b as i32 }) as u64);
        out((a as u32).checked_div(b as u32).unwrap_or(5) as u64); out((a as u32).checked_rem(b as u32).unwrap_or(6) as u64);
        out((a as i64).wrapping_div(if b == 0 { 1 } else { b as i64 }) as u64); out((a as i64).wrapping_rem(if b == 0 { 2 } else { b as i64 }) as u64);
        out(a.checked_div(b).unwrap_or(8)); out(a.checked_rem(b).unwrap_or(9));
        out((a as i32).wrapping_shl(s) as u64); out((a as i32).wrapping_shr(s) as u64); out((a as u32).wrapping_shr(s) as u64);
        out((a as i32).wrapping_add(b as i32) as u64); out((a as i32).wrapping_sub(b as i32) as u64); out((a as i32).wrapping_mul(b as i32) as u64);
        out((a as i16).wrapping_div(if b as i16 == 0 { 1 } else { b as i16 }) as u64); out((a as u8 / (b as u8 | 1)) as u64);
        out(((a as i64 as i128 * b as i64 as i128) >> 64) as u64); out(((a as u128 * b as u128) >> 64) as u64);
    }
    out(i32::MIN.wrapping_div(-1) as u64); out(i64::MIN.wrapping_rem(-1) as u64);
}
