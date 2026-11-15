#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let a: Vec<u32> = (0..12).map(|_| i.u32()).collect();
    let b: Vec<u32> = (0..9).map(|_| i.u32()).collect();
    let mut p = vec![0u32; a.len() + b.len()];
    for (x, &ai) in a.iter().enumerate() {
        let mut carry = 0u64;
        for (y, &bj) in b.iter().enumerate() {
            let t = ai as u64 * bj as u64 + p[x + y] as u64 + carry;
            p[x + y] = t as u32; carry = t >> 32;
        }
        p[x + b.len()] = carry as u32;
    }
    for w in p.chunks(2) { out(w[0] as u64 | (w[1] as u64) << 32); }
    let mut rem = 0u64; let d = (i.u32() | 1) as u64;
    for w in p.iter_mut().rev() { let t = rem << 32 | *w as u64; *w = (t / d) as u32; rem = t % d; }
    out(rem); out(p[0] as u64);
}
