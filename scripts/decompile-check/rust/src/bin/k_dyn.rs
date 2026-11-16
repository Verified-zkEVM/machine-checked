#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    trait Op { fn go(&self, x: u64) -> u64; fn name(&self) -> u8; }
    struct Add(u64); struct Mul(u64); struct Rot(u32); struct Mix; struct Neg;
    impl Op for Add { fn go(&self, x: u64) -> u64 { x.wrapping_add(self.0) } fn name(&self) -> u8 { b'a' } }
    impl Op for Mul { fn go(&self, x: u64) -> u64 { x.wrapping_mul(self.0 | 1) } fn name(&self) -> u8 { b'm' } }
    impl Op for Rot { fn go(&self, x: u64) -> u64 { x.rotate_left(self.0 & 63) } fn name(&self) -> u8 { b'r' } }
    impl Op for Mix { fn go(&self, x: u64) -> u64 { (x ^ x >> 29).wrapping_mul(0xbf58476d1ce4e5b9) } fn name(&self) -> u8 { b'x' } }
    impl Op for Neg { fn go(&self, x: u64) -> u64 { x.wrapping_neg() ^ 0xff } fn name(&self) -> u8 { b'n' } }
    let mut ops: Vec<Box<dyn Op>> = Vec::new();
    for k in 0..24 {
        let b = i.u8();
        ops.push(match (b as usize + k) % 5 {
            0 => Box::new(Add(i.u64())), 1 => Box::new(Mul(i.u32() as u64)), 2 => Box::new(Rot(b as u32)),
            3 => Box::new(Mix), _ => Box::new(Neg) });
    }
    let mut x = i.u64();
    let mut names = Vec::new();
    for o in &ops { x = o.go(x); names.push(o.name()); out(x); }
    outs(&names);
}
