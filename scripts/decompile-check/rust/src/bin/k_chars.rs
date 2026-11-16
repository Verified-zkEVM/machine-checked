#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let mut n = 0u64;
    for _ in 0..20 {
        let c = char::from_u32(i.u32() % 0x3000).unwrap_or('?');
        n = n * 7 + c.is_alphabetic() as u64 + 2 * c.is_numeric() as u64 + 4 * c.is_uppercase() as u64 + 8 * c.is_whitespace() as u64;
        out(c.to_lowercase().next().unwrap() as u64); out(c.len_utf8() as u64); out(c.to_digit(36).unwrap_or(99) as u64);
    }
    out(n);
    let s: String = (0..10).map(|_| char::from_u32(0x400 + i.u8() as u32).unwrap()).collect();
    outs(s.as_bytes()); out(s.chars().rev().map(|c| c as u64).sum());
}
