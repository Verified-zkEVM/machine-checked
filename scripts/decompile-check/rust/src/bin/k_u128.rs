#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    for _ in 0..6 {
        let (a, b) = (i.u128(), i.u128() >> (i.u8() % 100));
        out128(a.wrapping_mul(b)); out128(a.wrapping_add(b)); out128(a.wrapping_sub(b));
        out128(if b != 0 { a / b } else { 7 }); out128(if b != 0 { a % b } else { 9 });
        out128(a << (i.u8() % 128)); out128(a >> (i.u8() % 128)); out(a.leading_zeros() as u64);
    }
}
