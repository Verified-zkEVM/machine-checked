#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    for _ in 0..6 {
        let (a, b) = (i.u128() as i128, (i.u128() as i128) >> (i.u8() % 110));
        out128(a.wrapping_mul(b) as u128); out128(a.wrapping_div(if b == 0 { 3 } else { b }) as u128);
        out128(a.wrapping_rem(if b == 0 { -5 } else { b }) as u128); out128((a >> (i.u8() % 128)) as u128);
        out((a < b) as u64); out128(a.wrapping_abs() as u128); out128(a.signum() as u128);
    }
}
