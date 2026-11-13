#!/usr/bin/env python3
"""Run a Flapjack image and print what it does.

    fjrun.py IMAGE.fjimg
    fjrun.py --coverage IMAGE.fjimg ...

A plain RV64IM interpreter with the installation and the test world of flapjack-flip
(`FlapjackFlip/Machine.lean`, `FlapjackFlip/Harness.lean`): the layout of the image, the
halt, cache-clear and FFI entries, riscv-zkvm's rule for which memory accesses are valid, an
FFI oracle that answers every call with the next bytes of an input stream, and the five test
inputs. The output is what `flip-check run IMAGE` prints, byte for byte, step counts included.

With `--coverage` it prints, for the images together, how many of their instructions some
test input runs.

It exists because riscv-zkvm's machine state holds memory as a function, so a run of a few
hundred thousand steps takes minutes there and under a second here. It is not trusted on
its own word: `check.sh --self-test` runs it on images whose behaviour flapjack-flip recorded
and compares.
"""
import sys

M = (1 << 64) - 1
CODE = 0x80010000
HALT, CCACHE = CODE - 16, CODE - 32
BITMAPS, HEAP, STACK, STACK_END = 0xA0000000, 0xA0100000, 0xA0500000, 0xA0900000
FUEL = 2_000_000


def sx(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


def valid(a):
    return 0x20 <= a <= 0x78000000 or 0x40000000 <= a <= 0x40002000 or 0xA0000000 <= a <= 0xC0000000


def range_valid(a, n):
    if n == 0:
        return True
    last = (a + n - 1) & M
    return a + n <= 1 << 64 and valid(a) and valid(last) and (last < 0x80000000) == (a < 0x80000000)


def lcg(seed, n):
    x, out = seed, []
    for _ in range(n):
        x = (x * 6364136223846793005 + 1442695040888963407) % (1 << 64)
        out.append(x >> 56)
    return out


INPUTS = [[], lcg(1, 16), lcg(2, 64), lcg(3, 256), [0xFF] * 64]


class Image:
    def __init__(self, text):
        lines = [l.strip() for l in text.split("\n") if l.strip()]
        assert lines[0] == "flapjack-flip image v1", "not an image"
        self.ffi, self.bitmaps, self.code = [], [], b""
        for l in lines[1:]:
            w = l.split()
            if w[0] == "ffi":
                self.ffi.append(w[1])
            elif w[0] == "bitmaps":
                self.bitmaps = [int(x, 16) for x in w[1:]]
            elif w[0] == "code":
                self.code = bytes(int(x, 16) for x in w[1:])


def run(img, inp, seen=None):
    """The events and the final status of `img` on the input stream `inp`, and the steps.
    The indices of the instructions run are added to `seen`."""
    code = img.code
    words = [int.from_bytes(code[i:i + 4], "little") for i in range(0, len(code) - len(code) % 4, 4)]
    r = [0] * 32
    r[10], r[11], r[12], r[13] = CODE, HEAP, STACK, STACK_END
    mem = {}
    for k, w in enumerate(img.bitmaps):
        mem[BITMAPS + 8 * k] = w
    bend, cend = BITMAPS + 8 * len(img.bitmaps), CODE + len(code)
    for k, w in enumerate([BITMAPS, bend, bend, cend, cend]):
        mem[HEAP + 8 * k] = w
    ffi_at = {(CODE - 16 * (i + 3)) & M: i for i in range(len(img.ffi))}
    inp = list(inp)
    events, pc, steps = [], CODE, 0

    def get(a, n):  # n bytes at a, little-endian
        v = 0
        for i in range(n):
            b = (a + i) & M
            v |= ((mem.get(b & ~7, 0) >> (8 * (b & 7))) & 0xFF) << (8 * i)
        return v

    def put(a, n, v):
        for i in range(n):
            b = (a + i) & M
            d, sh = b & ~7, 8 * (b & 7)
            mem[d] = (mem.get(d, 0) & ~(0xFF << sh) & M) | (((v >> (8 * i)) & 0xFF) << sh)

    while steps < FUEL:
        steps += 1
        if pc == HALT:
            return events, ("halted: success" if r[10] == 0 else "halted: out of memory"), steps
        if pc == CCACHE:
            break
        if pc in ffi_at:
            cp, cl, ap, al = r[10], r[11], r[12], r[13]
            if not (range_valid(cp, cl) and range_valid(ap, al)):
                break
            conf = [get(cp + i, 1) for i in range(cl)]
            arr = [get(ap + i, 1) for i in range(al)]
            new = inp[:al] + [0] * (al - len(inp))
            inp = inp[al:]
            events.append((img.ffi[ffi_at[pc]], conf, arr, new))
            for i, b in enumerate(new):
                put(ap + i, 1, b)
            pc = r[1]
            continue
        k = pc - CODE
        if k < 0 or k >= len(code) or k % 4 or k // 4 >= len(words):
            break
        w = words[k // 4]
        if seen is not None:
            seen.add(k // 4)
        op, rd, f3, rs1, rs2, f7 = w & 0x7F, (w >> 7) & 31, (w >> 12) & 7, (w >> 15) & 31, (w >> 20) & 31, w >> 25
        a, b = r[rs1], r[rs2]
        imm_i = sx(w >> 20, 12)
        npc = (pc + 4) & M
        val = None
        if op == 0x37:
            val = sx(w & 0xFFFFF000, 32) & M
        elif op == 0x17:
            val = (pc + sx(w & 0xFFFFF000, 32)) & M
        elif op == 0x6F:
            off = sx(((w >> 31) << 20) | (((w >> 12) & 0xFF) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3FF) << 1), 21)
            val, npc = npc, (pc + off) & M
        elif op == 0x67 and f3 == 0:
            val, npc = npc, (a + imm_i) & M & ~1
        elif op == 0x63:
            off = sx(((w >> 31) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 0x3F) << 5) | (((w >> 8) & 0xF) << 1), 13)
            sa, sb = sx(a, 64), sx(b, 64)
            taken = {0: a == b, 1: a != b, 4: sa < sb, 5: sa >= sb, 6: a < b, 7: a >= b}.get(f3)
            if taken is None:
                break
            if taken:
                npc = (pc + off) & M
            rd = 0
        elif op == 0x03:
            n = {0: 1, 1: 2, 2: 4, 3: 8, 4: 1, 5: 2, 6: 4}.get(f3)
            ad = (a + imm_i) & M
            if n is None or not valid(ad) or ad % n:
                break
            val = get(ad, n)
            if f3 < 3:
                val = sx(val, 8 * n) & M
        elif op == 0x23:
            n = {0: 1, 1: 2, 2: 4, 3: 8}.get(f3)
            ad = (a + sx((f7 << 5) | rd, 12)) & M
            if n is None or not valid(ad) or ad % n:
                break
            put(ad, n, b)
            rd = 0
        elif op == 0x13:
            sh = (w >> 20) & 63
            if f3 == 0: val = a + imm_i
            elif f3 == 2: val = int(sx(a, 64) < imm_i)
            elif f3 == 3: val = int(a < (imm_i & M))
            elif f3 == 4: val = a ^ imm_i
            elif f3 == 6: val = a | imm_i
            elif f3 == 7: val = a & imm_i
            elif f3 == 1 and w >> 26 == 0: val = a << sh
            elif f3 == 5 and w >> 26 == 0: val = a >> sh
            elif f3 == 5 and w >> 26 == 0x10: val = sx(a, 64) >> sh
            else: break
            val &= M
        elif op == 0x33:
            sa, sb, sh = sx(a, 64), sx(b, 64), b & 63
            key = (f7, f3)
            if key == (0, 0): val = a + b
            elif key == (0x20, 0): val = a - b
            elif key == (0, 1): val = a << sh
            elif key == (0, 2): val = int(sa < sb)
            elif key == (0, 3): val = int(a < b)
            elif key == (0, 4): val = a ^ b
            elif key == (0, 5): val = a >> sh
            elif key == (0x20, 5): val = sa >> sh
            elif key == (0, 6): val = a | b
            elif key == (0, 7): val = a & b
            elif key == (1, 0): val = a * b
            elif key == (1, 1): val = (sa * sb) >> 64
            elif key == (1, 2): val = (sa * b) >> 64
            elif key == (1, 3): val = (a * b) >> 64
            elif key == (1, 4): val = -1 if b == 0 else (abs(sa) // abs(sb)) * (-1 if (sa < 0) != (sb < 0) else 1)
            elif key == (1, 5): val = M if b == 0 else a // b
            elif key == (1, 6): val = a if b == 0 else (abs(sa) % abs(sb)) * (-1 if sa < 0 else 1)
            elif key == (1, 7): val = a if b == 0 else a % b
            else: break
            val &= M
        elif op == 0x1B:  # the 32-bit forms riscv-zkvm has: addiw, slliw, srliw
            sh = (w >> 20) & 31
            if f3 == 0: val = a + imm_i
            elif f3 == 1 and f7 == 0: val = a << sh
            elif f3 == 5 and f7 == 0: val = (a & 0xFFFFFFFF) >> sh
            else: break
            val = sx(val, 32) & M
        elif op == 0x3B:  # subw, srlw
            if (f7, f3) == (0x20, 0): val = a - b
            elif (f7, f3) == (0, 5): val = (a & 0xFFFFFFFF) >> (b & 31)
            else: break
            val = sx(val, 32) & M
        else:
            break
        if rd and val is not None:
            r[rd] = val
        pc = npc
    else:
        return events, "still running (out of fuel)", steps
    return events, "failed (trap, bad memory access or bad FFI arguments)", steps


def describe(img):
    hx = lambda bs: "".join(f"{b:02x}" for b in bs)
    out = []
    for inp in INPUTS:
        events, status, steps = run(img, inp)
        lines = [f"## input {hx(inp)}"]
        lines += [f"@{n} conf={hx(c)} in={hx(a)} out={hx(b)}" for n, c, a, b in events]
        out.append("\n".join(lines + [status, f"({steps} steps)"]))
    return "\n\n".join(out) + "\n"


if __name__ == "__main__":
    if sys.argv[1] == "--coverage":
        ran = total = 0
        for path in sys.argv[2:]:
            img, seen = Image(open(path).read()), set()
            for inp in INPUTS:
                run(img, inp, seen)
            ran, total = ran + len(seen), total + len(img.code) // 4
        print(f"{ran} of {total} instructions run ({100 * ran // max(1, total)}%)")
    else:
        sys.stdout.write(describe(Image(open(sys.argv[1]).read())))
