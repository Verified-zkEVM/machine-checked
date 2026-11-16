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
    #[repr(align(8))] struct Buf([u8; 64]);
    let mut buf = Buf([0; 64]);
    for k in 0..64 { buf.0[k] = i.u8() ^ (k as u8).wrapping_mul(37) | 0x80 * (k as u8 & 1); }
    let p = buf.0.as_mut_ptr();
    macro_rules! ld { ($name:literal, $off:literal) => {{ let r: u64; unsafe { asm!(concat!($name, " {0}, ", $off, "({1})"), out(reg) r, in(reg) p); } out(r); }} }
    macro_rules! sto { ($name:literal, $off:literal, $v:expr) => {{ unsafe { asm!(concat!($name, " {0}, ", $off, "({1})"), in(reg) $v, in(reg) p); } }} }
    ld!("lb", "1"); ld!("lbu", "1"); ld!("lh", "2"); ld!("lhu", "2"); ld!("lw", "4"); ld!("lwu", "4"); ld!("ld", "8");
    ld!("lb", "63"); ld!("lh", "62"); ld!("lw", "60"); ld!("ld", "56"); ld!("lbu", "0"); ld!("lhu", "30"); ld!("lwu", "28");
    let v = i.u64() | 0x8080808080808080;
    sto!("sb", "17", v); sto!("sh", "18", v); sto!("sw", "20", v); sto!("sd", "24", v); sto!("sb", "63", v); sto!("sh", "40", v); sto!("sw", "44", v);
    outs(&buf.0);
    let e = unsafe { p.add(64) };
    let r: u64; unsafe { asm!("ld {0}, -8({1})", out(reg) r, in(reg) e); } out(r);
    let r: u64; unsafe { asm!("lb {0}, -2048({1})", out(reg) r, in(reg) p.wrapping_add(2048 + 5)); } out(r);
}
