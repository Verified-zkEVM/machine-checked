#![no_main]
#![cfg_attr(not(target_os = "zkvm"), no_std)]
guests::entry!(main);
#[allow(unused_imports)]
use guests::*;

// x86-64 instructions the compiler does not choose for the other guests, each beside the
// same function in Rust: on x86-64 the instruction runs, elsewhere the Rust does, and the
// outputs are the same.

#[cfg(target_arch = "x86_64")]
mod ops {
    use core::arch::asm;

    #[inline(never)]
    pub fn xchg(a: u64, b: u64, m: &mut u64) -> (u64, u64) {
        let (mut x, mut y) = (a, b);
        unsafe { asm!("xchg {x}, {y}", "xchg [{p}], {x}", "xchg {y:e}, {x:e}", x = inout(reg) x, y = inout(reg) y, p = in(reg) m) };
        (x, y)
    }
    /// The parity flag of the low byte of `a + b`, read five ways.
    #[inline(never)]
    pub fn parity(a: u64, b: u64) -> [u64; 5] {
        let (s, j, n, c, d): (u8, u64, u64, u64, u64);
        unsafe { asm!(
            "mov {t:e}, {a:e}", "add {t:e}, {b:e}", "setp {s}",
            "mov {j}, 1", "jp 2f", "mov {j}, 7", "2:",
            "add {t:e}, 0", "mov {n}, 2", "jnp 3f", "mov {n}, 9", "3:",
            "mov {c}, {b}", "add {t:e}, 0", "cmovp {c}, {a}",
            "mov {d}, {b}", "add {t:e}, 0", "cmovnp {d}, {a}",
            a = in(reg) a, b = in(reg) b, t = out(reg) _, s = out(reg_byte) s, j = out(reg) j,
            n = out(reg) n, c = out(reg) c, d = out(reg) d) };
        [s as u64, j, n, c, d]
    }
    #[inline(never)]
    pub fn bits(a: u64, i: u64) -> (u64, u64) {
        let (mut x, c, z): (u64, u64, u64);
        x = a;
        unsafe { asm!("btr {x}, {i}", "setc {c:l}", "movzx {c:e}, {c:l}", "lzcnt {z}, {x}", "btr {x:e}, 3",
            x = inout(reg) x, i = in(reg) i, c = out(reg_abcd) c, z = out(reg) z) };
        (x, c << 8 | z)
    }
    /// One `movsq` and one `stosb`, without `rep`; and a frame made and left with `leave`.
    #[inline(never)]
    pub fn strings(src: &u64, dst: &mut [u64; 2], v: u64) -> u64 {
        let r: u64;
        unsafe { asm!("cld", "movsq", "stosb", "push rbp", "mov rbp, rsp", "sub rsp, 32", "mov [rsp], rdi", "mov {r}, [rsp]", "leave",
            inout("rsi") src as *const u64 => _, inout("rdi") dst.as_mut_ptr() => _, in("rax") v, r = out(reg) r) };
        r.wrapping_sub(dst.as_ptr() as u64)
    }
}

#[cfg(not(target_arch = "x86_64"))]
mod ops {
    #[inline(never)]
    pub fn xchg(a: u64, b: u64, m: &mut u64) -> (u64, u64) {
        // x and y change places, then x and the memory, then the low halves of y and x
        let (x, y) = (*m, a);
        *m = b;
        (y as u32 as u64, x as u32 as u64)
    }
    #[inline(never)]
    pub fn parity(a: u64, b: u64) -> [u64; 5] {
        let p = ((a as u32).wrapping_add(b as u32) as u8).count_ones() % 2 == 0;
        [p as u64, if p { 1 } else { 7 }, if !p { 2 } else { 9 }, if p { a } else { b }, if !p { a } else { b }]
    }
    #[inline(never)]
    pub fn bits(a: u64, i: u64) -> (u64, u64) {
        let x = a & !(1 << (i & 63));
        ((x as u32 & !8) as u64, (a >> (i & 63) & 1) << 8 | x.leading_zeros() as u64)
    }
    #[inline(never)]
    pub fn strings(src: &u64, dst: &mut [u64; 2], v: u64) -> u64 {
        dst[0] = *src;
        dst[1] = dst[1] & !0xff | v & 0xff;
        9
    }
}

pub fn main() {
    let mut i = In::new();
    for k in 0..8u64 {
        let (a, b, c) = (i.u64(), i.u64(), i.u64());
        let mut m = c;
        let (x, y) = ops::xchg(a, b, &mut m); out(x); out(y); out(m);
        for v in ops::parity(a, b) { out(v); }
        for v in ops::parity(k, 0) { out(v); }
        let (x, y) = ops::bits(a, b); out(x); out(y);
        let (x, y) = ops::bits(k << 60, 63); out(x); out(y);
        let mut d = [b, c];
        out(ops::strings(&a, &mut d, c ^ k)); out(d[0]); out(d[1]);
    }
}
