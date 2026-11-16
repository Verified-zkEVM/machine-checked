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
    let edge = [0u64, 1, 2, 63, 64, 0x7fffffff, 0xffffffff, 0x7fffffffffffffff, 0x8000000000000000, !0, 0xfedcba9876543210];
    let mut pairs: Vec<(u64, u64)> = Vec::new();
    for &a in &edge { for &b in &edge { pairs.push((a, b)); } }
    for _ in 0..12 { pairs.push((i.u64(), i.u64() >> (i.u8() % 64))); }
    for (a, b) in pairs {
        op!("mul", a, b); op!("mulh", a, b); op!("mulhsu", a, b); op!("mulhu", a, b);
        op!("div", a, b); op!("divu", a, b); op!("rem", a, b); op!("remu", a, b);
        op!("add", a, b); op!("sub", a, b); op!("sll", a, b); op!("srl", a, b); op!("sra", a, b);
        op!("slt", a, b); op!("sltu", a, b); op!("xor", a, b); op!("or", a, b); op!("and", a, b);
        opi!("slti", a, "-1"); opi!("sltiu", a, "-1"); opi!("sltiu", b, "1"); opi!("xori", a, "-1"); opi!("ori", a, "1365"); opi!("andi", b, "-1366");
        opi!("slli", a, "63"); opi!("srli", a, "63"); opi!("srai", a, "63"); opi!("srai", b, "1"); opi!("addi", a, "-2048");
    }
}
