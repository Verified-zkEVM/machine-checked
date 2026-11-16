#!/usr/bin/env python3
"""Write test images of hand-assembled RISC-V code: every instruction the lift covers.

    gen_asm.py SEED COUNT OUTDIR

Flapjack's own code uses a small part of RV64IM in a few fixed shapes. These images are not
from Flapjack: each is a random straight run of instructions, with the control flow a
compiler that follows the calling convention would emit, in the layout of a Flapjack image
so that the same tools run it. A program

  1. reads 96 bytes of input into memory through FFI function 0 (`in`), and loads twelve
     registers from them; some registers are then set to edge values (0, 1, -1, the least
     and greatest signed values, 63, 64);
  2. runs 40 to 90 random instructions: arithmetic, logic, shifts by a register and by a
     constant, comparisons, the multiplications and divisions, `addiw`, loads and
     stores of every width into a scratch area, `lui`, `auipc`, each branch over a
     following instruction, `jal` and `jalr` with and without a link, and calls of a small
     subroutine that returns with `jalr x0, 0(ra)`;
  3. stores every register and writes them and the scratch area out through FFI function 1
     (`out`), then halts.

So the output shows the effect of every instruction. `image.fjimg` is the image and
`source.s` a listing. `expected.txt` is not written here: it comes from the reference
machine (`flip-check run`, see README.md).
"""
import os, random, sys

CODE = 0x80010000
WORK = [5, 6, 7, 9, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31]
BASE = 8  # x8 holds the heap base throughout


def R(f7, rs2, rs1, f3, rd, op=0x33): return (f7 << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op
def I(imm, rs1, f3, rd, op): return ((imm & 0xFFF) << 20) | (rs1 << 15) | (f3 << 12) | (rd << 7) | op
def S(imm, rs2, rs1, f3): return (((imm >> 5) & 0x7F) << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | ((imm & 31) << 7) | 0x23
def B(off, rs2, rs1, f3):
    return (((off >> 12) & 1) << 31) | (((off >> 5) & 0x3F) << 25) | (rs2 << 20) | (rs1 << 15) | (f3 << 12) | \
        (((off >> 1) & 0xF) << 8) | (((off >> 11) & 1) << 7) | 0x63
def U(imm20, rd, op): return ((imm20 & 0xFFFFF) << 12) | (rd << 7) | op
def J(off, rd):
    return (((off >> 20) & 1) << 31) | (((off >> 1) & 0x3FF) << 21) | (((off >> 11) & 1) << 20) | \
        (((off >> 12) & 0xFF) << 12) | (rd << 7) | 0x6F

RTYPE = {"add": (0, 0), "sub": (0x20, 0), "sll": (0, 1), "slt": (0, 2), "sltu": (0, 3), "xor": (0, 4),
         "srl": (0, 5), "sra": (0x20, 5), "or": (0, 6), "and": (0, 7), "mul": (1, 0), "mulh": (1, 1),
         "mulhsu": (1, 2), "mulhu": (1, 3), "div": (1, 4), "divu": (1, 5), "rem": (1, 6), "remu": (1, 7)}
ITYPE = {"addi": 0, "slti": 2, "sltiu": 3, "xori": 4, "ori": 6, "andi": 7}
LOAD = {"lb": (0, 1), "lh": (1, 2), "lw": (2, 4), "ld": (3, 8), "lbu": (4, 1), "lhu": (5, 2), "lwu": (6, 4)}
STORE = {"sb": (0, 1), "sh": (1, 2), "sw": (2, 4), "sd": (3, 8)}
BRANCH = {"beq": 0, "bne": 1, "blt": 4, "bge": 5, "bltu": 6, "bgeu": 7}
IMMS = [0, 1, -1, 2047, -2048, 63, 64, 255]


class Asm:
    def __init__(self):
        self.words, self.text = [], []

    def emit(self, w, t):
        self.words.append(w & 0xFFFFFFFF)
        self.text.append(t)

    def pc(self): return CODE + 4 * len(self.words)

    def jump(self, target, rd=0):
        self.emit(J(target - self.pc(), rd), f"jal x{rd}, {target:#x}")

    def ffi(self, index, off, length):
        """Call FFI function `index` on `length` bytes at heap offset `off`."""
        self.emit(I(0, BASE, 0, 10, 0x13), "addi x10, x8, 0")
        self.emit(I(0, 0, 0, 11, 0x13), "addi x11, x0, 0")
        self.emit(I(off, BASE, 0, 12, 0x13), f"addi x12, x8, {off}")
        self.emit(I(length, 0, 0, 13, 0x13), f"addi x13, x0, {length}")
        self.emit(U(0, 1, 0x17), "auipc x1, 0")
        self.emit(I(12, 1, 0, 1, 0x13), "addi x1, x1, 12")
        self.jump(CODE - 16 * (index + 3))


def program(rng):
    a = Asm()
    reg = lambda zero=0.1: 0 if rng.random() < zero else rng.choice(WORK)
    a.emit(I(0, 11, 0, BASE, 0x13), "addi x8, x11, 0")
    a.ffi(0, 0, 96)
    for i, r in enumerate(WORK[:12]):
        a.emit(I(8 * i, BASE, 3, r, 0x03), f"ld x{r}, {8 * i}(x8)")
    for r, kind in zip(WORK[12:], ["zero", "one", "neg1", "min", "max", "c63", "c64", "one", "neg1", "min"]):
        if kind == "zero": a.emit(I(0, 0, 0, r, 0x13), f"addi x{r}, x0, 0")
        elif kind == "one": a.emit(I(1, 0, 0, r, 0x13), f"addi x{r}, x0, 1")
        elif kind == "neg1": a.emit(I(-1, 0, 0, r, 0x13), f"addi x{r}, x0, -1")
        elif kind == "c63": a.emit(I(63, 0, 0, r, 0x13), f"addi x{r}, x0, 63")
        elif kind == "c64": a.emit(I(64, 0, 0, r, 0x13), f"addi x{r}, x0, 64")
        else:
            a.emit(I(1, 0, 0, r, 0x13), f"addi x{r}, x0, 1")
            a.emit(I(63, r, 1, r, 0x13), f"slli x{r}, x{r}, 63")
            if kind == "max": a.emit(I(-1, r, 0, r, 0x13), f"addi x{r}, x{r}, -1")
    # the subroutine, jumped over: x9 = x9 * 3 + x5, and return
    sub_at = a.pc() + 4
    a.jump(a.pc() + 4 * 4)
    a.emit(I(1, 9, 1, 30, 0x13), "slli x30, x9, 1")
    a.emit(R(0, 30, 9, 0, 9), "add x9, x9, x30")
    a.emit(I(0, 1, 0, 0, 0x67), "jalr x0, 0(x1)")
    for _ in range(rng.randint(40, 90)):
        k = rng.random()
        if k < 0.40:
            n = rng.choice(list(RTYPE)); f7, f3 = RTYPE[n]; rd, r1, r2 = reg(0.03), reg(), reg()
            a.emit(R(f7, r2, r1, f3, rd), f"{n} x{rd}, x{r1}, x{r2}")
        elif k < 0.52:
            n = rng.choice(list(ITYPE)); rd, r1 = reg(0.03), reg()
            imm = rng.choice(IMMS) if rng.random() < 0.5 else rng.randint(-2048, 2047)
            a.emit(I(imm, r1, ITYPE[n], rd, 0x13), f"{n} x{rd}, x{r1}, {imm}")
        elif k < 0.60:
            n, f3, hi = rng.choice([("slli", 1, 0), ("srli", 5, 0), ("srai", 5, 0x10)]); rd, r1 = reg(0.03), reg()
            sh = rng.choice([0, 1, 31, 32, 63, rng.randint(0, 63)])
            a.emit(I((hi << 6) | sh, r1, f3, rd, 0x13), f"{n} x{rd}, x{r1}, {sh}")
        elif k < 0.66:
            # `addiw` only: the reference machine does not decode `slliw`, `srliw`, `srlw`, `subw`
            rd, r1 = reg(0.03), reg(); imm = rng.choice(IMMS) if rng.random() < 0.5 else rng.randint(-2048, 2047)
            a.emit(I(imm, r1, 0, rd, 0x1B), f"addiw x{rd}, x{r1}, {imm}")
        elif k < 0.74:
            n = rng.choice(list(STORE)); f3, size = STORE[n]; r2 = reg()
            off = 256 + size * rng.randint(0, 128 // size - 1)
            a.emit(S(off, r2, BASE, f3), f"{n} x{r2}, {off}(x8)")
        elif k < 0.82:
            n = rng.choice(list(LOAD)); f3, size = LOAD[n]; rd = reg(0.03)
            off = 256 + size * rng.randint(0, 128 // size - 1)
            a.emit(I(off, BASE, f3, rd, 0x03), f"{n} x{rd}, {off}(x8)")
        elif k < 0.85:
            rd = reg(0.03); imm = rng.choice([0, 1, 0x7FFFF, 0x80000, 0xFFFFF, rng.randint(0, 0xFFFFF)])
            n, op = rng.choice([("lui", 0x37), ("auipc", 0x17)])
            a.emit(U(imm, rd, op), f"{n} x{rd}, {imm:#x}")
        elif k < 0.93:
            n = rng.choice(list(BRANCH)); r1, r2 = reg(), reg(); rd = reg(0)
            a.emit(B(8, r2, r1, BRANCH[n]), f"{n} x{r1}, x{r2}, +8")
            a.emit(I(rng.randint(1, 99), rd, 4, rd, 0x13), f"xori x{rd}, x{rd}, …   (skipped if taken)")
        elif k < 0.95:
            rd = reg(0.3)
            a.emit(J(8, rd), f"jal x{rd}, +8")
            a.emit(I(-1, 0, 0, reg(0), 0x13), "addi …, x0, -1   (skipped)")
        elif k < 0.97:
            r, rd = reg(0), reg(0.3)
            a.emit(U(0, r, 0x17), f"auipc x{r}, 0")
            a.emit(I(16, r, 0, r, 0x13), f"addi x{r}, x{r}, 16")
            a.emit(I(0, r, 0, rd, 0x67), f"jalr x{rd}, 0(x{r})")
            a.emit(I(-1, 0, 0, reg(0), 0x13), "addi …, x0, -1   (skipped)")
        else:
            a.jump(sub_at, rd=1)
    for i, r in enumerate(WORK):
        a.emit(S(512 + 8 * i, r, BASE, 3), f"sd x{r}, {512 + 8 * i}(x8)")
    a.ffi(1, 512, 8 * len(WORK))
    a.ffi(1, 256, 128)
    a.emit(I(0, 0, 0, 10, 0x13), "addi x10, x0, 0")
    a.jump(CODE - 16)
    return a


if __name__ == "__main__":
    seed, count, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    for n in range(count):
        a = program(random.Random(seed * 100003 + n))
        d = os.path.join(out, f"asm_{seed}_{n:03d}")
        os.makedirs(d, exist_ok=True)
        code = b"".join(w.to_bytes(4, "little") for w in a.words)
        with open(os.path.join(d, "image.fjimg"), "w") as f:
            f.write("flapjack-flip image v1\nffi in\nffi out\nbitmaps\ncode " + " ".join(f"{b:02x}" for b in code) + "\n")
        with open(os.path.join(d, "source.s"), "w") as f:
            f.write("".join(f"{CODE + 4 * i:#x}: {w:08x}  {t}\n" for i, (w, t) in enumerate(zip(a.words, a.text))))
