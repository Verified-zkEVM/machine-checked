#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    let mut v: Vec<u8> = i.a.iter().chain(i.b.iter()).copied().cycle().take(700).collect();
    if i.a.is_empty() { v = (0..700u32).map(|x| (x * 7) as u8).collect(); }
    for k in 0..24usize {
        let (s, d, n) = (i.u8() as usize * 2, i.u8() as usize * 2 + k, i.u8() as usize % (k * 9 + 1));
        v.copy_within(s..s + n, d);
        v[d + n..d + n + k].fill(k as u8);
    }
    out(v.iter().fold(0u64, |h, &x| h.wrapping_mul(0x100000001b3) ^ x as u64));
    let w = v.clone(); out((w == v) as u64); out((w[1..] < v[..699]) as u64);
    let mut big = vec![0u64; 300]; big[5..200].copy_from_slice(&[i.u64(); 195]); out(big.iter().sum());
    let z = [0u8; 513]; out(z.iter().map(|&x| x as u64).sum()); outs(&v[100..140]);
}
