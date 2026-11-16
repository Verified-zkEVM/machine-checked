#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    fn fib(n: u32) -> u64 { if n < 2 { n as u64 } else { fib(n - 1).wrapping_add(fib(n - 2)) } }
    fn ack(m: u64, n: u64) -> u64 { if m == 0 { n + 1 } else if n == 0 { ack(m - 1, 1) } else { ack(m - 1, ack(m, n - 1)) } }
    fn depth(n: u32, a: &[u8]) -> u64 { if n == 0 { 1 } else { a[n as usize % a.len().max(1) % 1.max(a.len())..].len() as u64 + 3 * depth(n - 1, a) % 1000000007 } }
    out(fib(i.u8() as u32 % 18));
    out(ack(2, i.u8() as u64 % 9));
    let pad = [1u8, 2, 3];
    out(depth(i.u8() as u32 * 3, if i.a.is_empty() { &pad } else { &i.a }));
}
