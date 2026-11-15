#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    use std::collections::{BinaryHeap, VecDeque};
    let mut h = BinaryHeap::new(); let mut q = VecDeque::new();
    for k in 0..100u32 {
        let b = i.u8();
        match b % 4 { 0 => { if let Some(x) = h.pop() { out(x as u64); } } 1 => q.push_front(b), 2 => { if let Some(x) = q.pop_back() { h.push(x as u32 + k); } } _ => { h.push(b as u32 * 3); q.push_back(b ^ 0x3c); } }
    }
    out(h.len() as u64); out(q.len() as u64);
    out(h.into_sorted_vec().iter().fold(0u64, |a, &x| a * 3 + x as u64));
    out(q.iter().rev().fold(0u64, |a, &x| a.rotate_left(5) ^ x as u64));
}
