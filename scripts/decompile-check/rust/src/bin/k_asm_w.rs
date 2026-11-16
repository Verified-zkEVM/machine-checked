// SP1 only: RISC-V assembly
#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    use core::arch::asm;
    macro_rules! op { ($name:literal, $a:expr, $b:expr) => {{ let r: u64; unsafe { asm!(concat!($name, " {0}, {1}, {2}"), out(reg) r, in(reg) $a, in(reg) $b); } out(r); }} }
    macro_rules! opi { ($name:literal, $a:expr, $n:literal) => {{ let r: u64; unsafe { asm!(concat!($name, " {0}, {1}, ", $n), out(reg) r, in(reg) $a); } out(r); }} }
    let edge = [0u64, 1, 2, 31, 32, 63, 0x7fffffff, 0x80000000, 0xffffffff, 0x100000000, 0x7fffffffffffffff, 0x8000000000000000, !0, 0xffffffff80000000, 0x123456789abcdef0];
    let mut pairs: Vec<(u64, u64)> = Vec::new();
    for &a in &edge { for &b in &edge { pairs.push((a, b)); } }
    for _ in 0..12 { pairs.push((i.u64(), i.u64() >> (i.u8() % 64))); }
    for (a, b) in pairs {
        op!("addw", a, b); op!("subw", a, b); op!("sllw", a, b); op!("srlw", a, b); op!("sraw", a, b);
        op!("mulw", a, b); op!("divw", a, b); op!("divuw", a, b); op!("remw", a, b); op!("remuw", a, b);
        opi!("addiw", a, "-7"); opi!("addiw", b, "2047"); opi!("slliw", a, "0"); opi!("slliw", a, "13"); opi!("slliw", b, "31");
        opi!("srliw", a, "0"); opi!("srliw", a, "5"); opi!("srliw", b, "31"); opi!("sraiw", a, "0"); opi!("sraiw", a, "9"); opi!("sraiw", b, "31");
    }
}
