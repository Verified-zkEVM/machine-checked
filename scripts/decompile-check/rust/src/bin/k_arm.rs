#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

// AArch64 instructions the compiler does not choose for the other guests, each beside the
// same function in Rust: on AArch64 the instruction runs, elsewhere the Rust does, and the
// outputs are the same.

#[cfg(target_arch = "aarch64")]
mod ops {
    use core::arch::asm;

    #[inline(never)]
    pub fn ccmn(a: u64, b: u64) -> u64 {
        let r: u64;
        unsafe { asm!("nop", "cmp {a}, #5", "ccmn {a}, {b}, #2, hi", "cset {r}, eq", a = in(reg) a, b = in(reg) b, r = out(reg) r) };
        r
    }
    #[inline(never)]
    pub fn rev32(x: u64) -> u64 {
        let r: u64;
        unsafe { asm!("rev32 {r}, {x}", x = in(reg) x, r = out(reg) r) };
        r
    }
    #[inline(never)]
    pub fn cls(x: u64) -> u64 {
        let (r, s): (u64, u64);
        unsafe { asm!("cls {r}, {x}", "cls {s:w}, {x:w}", x = in(reg) x, r = out(reg) r, s = out(reg) s) };
        r << 8 | s
    }
    #[inline(never)]
    pub fn msubl(a: u64, b: u64, c: u64) -> (u64, u64) {
        let (r, s): (u64, u64);
        unsafe { asm!("smsubl {r}, {a:w}, {b:w}, {c}", "umsubl {s}, {a:w}, {b:w}, {c}", a = in(reg) a, b = in(reg) b, c = in(reg) c, r = out(reg) r, s = out(reg) s) };
        (r, s)
    }
    #[inline(never)]
    pub fn literals() -> (u64, u64, u64) {
        let (r, s, t): (u64, u64, u64);
        unsafe { asm!("ldr {r}, 2f", "ldrsw {s}, 3f", "ldr {t:w}, 3f", "b 4f", ".balign 8",
            "2: .quad 0x0123456789abcdef", "3: .word 0x80000001", ".balign 4", "4:",
            r = out(reg) r, s = out(reg) s, t = out(reg) t) };
        (r, s, t)
    }
    #[inline(never)]
    pub fn ldpsw(p: &[i32; 2]) -> (u64, u64) {
        let (r, s): (u64, u64);
        unsafe { asm!("ldpsw {r}, {s}, [{p}]", p = in(reg) p.as_ptr(), r = out(reg) r, s = out(reg) s) };
        (r, s)
    }
}

#[cfg(not(target_arch = "aarch64"))]
mod ops {
    #[inline(never)]
    pub fn ccmn(a: u64, b: u64) -> u64 { (a > 5 && a.wrapping_add(b) == 0) as u64 }
    #[inline(never)]
    pub fn rev32(x: u64) -> u64 { (x as u32).swap_bytes() as u64 | (((x >> 32) as u32).swap_bytes() as u64) << 32 }
    #[inline(never)]
    pub fn cls(x: u64) -> u64 {
        let r = (x ^ ((x as i64 >> 1) as u64)).leading_zeros() as u64 - 1;
        let w = x as u32;
        let s = (w ^ ((w as i32 >> 1) as u32)).leading_zeros() as u64 - 1;
        r << 8 | s
    }
    #[inline(never)]
    pub fn msubl(a: u64, b: u64, c: u64) -> (u64, u64) {
        (c.wrapping_sub((a as i32 as i64).wrapping_mul(b as i32 as i64) as u64),
         c.wrapping_sub((a as u32 as u64).wrapping_mul(b as u32 as u64)))
    }
    #[inline(never)]
    pub fn literals() -> (u64, u64, u64) { (0x0123456789abcdef, 0xffffffff80000001, 0x80000001) }
    #[inline(never)]
    pub fn ldpsw(p: &[i32; 2]) -> (u64, u64) { (p[0] as i64 as u64, p[1] as i64 as u64) }
}

pub fn main() {
    let mut i = In::new();
    for k in 0..8u64 {
        let (a, b, c) = (i.u64(), i.u64(), i.u64());
        out(ops::ccmn(a, b)); out(ops::ccmn(k + 3, (k + 3).wrapping_neg())); out(ops::ccmn(k, a));
        out(ops::rev32(a)); out(ops::cls(a)); out(ops::cls(a >> (b & 63))); out(ops::cls((a as i64 >> (c & 63)) as u64));
        let (r, s) = ops::msubl(a, b, c); out(r); out(s);
        let (r, s) = ops::ldpsw(&[a as i32, b as i32]); out(r); out(s);
    }
    let (r, s, t) = ops::literals(); out(r); out(s); out(t);
}
