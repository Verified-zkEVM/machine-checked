#![no_main]
sp1_zkvm::entrypoint!(main);
#[allow(unused_imports)]
use guests::*;

core::arch::global_asm!(
        ".globl k_table", "k_table:",                 // a jump table in code, through `jr`
    "andi a0, a0, 3", "slli a0, a0, 3", "la t1, 5f", "add t1, t1, a0", "ld t1, 0(t1)", "jr t1",
    "1: li a0, 11", "ret", "2: li a0, 22", "ret", "3: li a0, 33", "ret", "4: li a0, 44", "ret",
    ".section .rodata", ".p2align 3", "5: .quad 1b", ".quad 2b", ".quad 3b", ".quad 4b", ".text",
    ".globl k_alt", "k_alt:",                     // a call that links through t0, and back
    "mv t3, a0", "jal t0, 6f", "addi a0, t3, 1", "jal t0, 6f", "mv a0, t3", "ret",
    "6: slli t3, t3, 1", "xori t3, t3, 5", "jr t0",
    ".globl k_same", "k_same:",                   // jalr with one register as target and link
    "la t1, 7f", "jalr t1, 0(t1)", "7: la t2, 7b", "sub a0, t1, t2", "ret",
    ".globl k_branches", "k_branches:",           // each branch, taken and not
    "li t0, 0", "beq a0, a1, 1f", "ori t0, t0, 1", "1: bne a0, a1, 1f", "ori t0, t0, 2", "1: blt a0, a1, 1f", "ori t0, t0, 4",
    "1: bge a0, a1, 1f", "ori t0, t0, 8", "1: bltu a0, a1, 1f", "ori t0, t0, 16", "1: bgeu a0, a1, 1f", "ori t0, t0, 32", "1: mv a0, t0", "ret",
    ".globl k_ptr", "k_ptr:",                     // an indirect call and an indirect tail call
    "addi sp, sp, -16", "sd ra, 8(sp)", "mv t1, a0", "mv a0, a1", "jalr ra, 0(t1)", "ld ra, 8(sp)", "addi sp, sp, 16", "mv t1, a2", "jr t1",
);

pub fn main() {
    #[allow(unused_mut)]
    let mut i = In::new();
    use core::arch::asm;
    extern "C" { fn k_table(x: u64) -> u64; fn k_alt(x: u64) -> u64; fn k_same() -> u64; fn k_branches(a: u64, b: u64) -> u64;
                 fn k_ptr(f: extern "C" fn(u64) -> u64, x: u64, g: extern "C" fn(u64) -> u64) -> u64; }
    extern "C" fn inc(x: u64) -> u64 { x.wrapping_add(3) }
    extern "C" fn dbl(x: u64) -> u64 { x.wrapping_mul(2) }
    unsafe {
        for _ in 0..6 { out(k_table(i.u8() as u64)); out(k_alt(i.u64())); }
        out(k_same());
        for (a, b) in [(0u64, 0u64), (1, 2), (2, 1), (!0, 1), (1, !0), (1 << 63, 1), (i.u64(), i.u64())] { out(k_branches(a, b)); }
        out(k_ptr(inc, i.u64(), dbl)); out(k_ptr(dbl, 5, inc));
    }
    let x: u64; unsafe { asm!("auipc {0}, 0", "lui {1}, 0xfffff", "add {0}, {0}, {1}", "srli {0}, {0}, 40", out(reg) x, out(reg) _); } out(x);
}
