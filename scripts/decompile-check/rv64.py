"""A plain RV64IM interpreter, shared by the runners here (`fjrun.py`, `sp1run.py`).

`run` steps a machine until something ends the run. What is outside the instruction set is
the caller's: `stops` maps an address to what happens when the pc reaches it (the entries
of an environment), `ecall` is what `ecall` does, and `valid` says which addresses a load
or store may touch. A load or store must be aligned to its width, as in riscv-zkvm, unless
the caller says otherwise (`aligned`).

Memory is a dictionary from addresses that are multiples of eight to 64-bit words; a word
that is absent is zero.

It is not trusted on its own word: each runner is compared with a machine it did not write
(`README.md`).
"""

M = (1 << 64) - 1


def sx(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


def get(mem, a, n):
    """The `n` bytes at `a`, little-endian."""
    if n == 8 and not a & 7:
        return mem.get(a, 0)
    v = 0
    for i in range(n):
        b = (a + i) & M
        v |= ((mem.get(b & ~7, 0) >> (8 * (b & 7))) & 0xFF) << (8 * i)
    return v


def put(mem, a, n, v):
    if n == 8 and not a & 7:
        mem[a] = v & M
        return
    for i in range(n):
        b = (a + i) & M
        d, sh = b & ~7, 8 * (b & 7)
        mem[d] = (mem.get(d, 0) & ~(0xFF << sh) & M) | (((v >> (8 * i)) & 0xFF) << sh)


def div(sa, sb):
    """Signed division, rounding towards zero."""
    q = abs(sa) // abs(sb)
    return -q if (sa < 0) != (sb < 0) else q


def rem(sa, sb):
    m = abs(sa) % abs(sb)
    return -m if sa < 0 else m


def run(words, base, r, mem, pc, fuel, stops=None, ecall=None, valid=None, seen=None, w32=True,
        aligned=True):
    """Run from `pc`. `words` are the instructions at `base`. Returns the reason the run
    ended and the number of steps: `None` when the fuel ran out, "fault" for what the
    machine cannot do (no instruction at the pc, a bad or misaligned access, an `ecall`
    with no handler), and otherwise what a stop or the `ecall` handler returned.

    A stop is called with the registers and returns the next pc (an int) or a reason to
    end; reaching it counts as a step. `ecall` is called likewise and returns `None` to
    carry on. With `w32` false the nine 32-bit operations riscv-zkvm lacks are no
    instructions. With `aligned` false a load or store may be at any address. The indices of
    the instructions run are added to `seen`."""
    stops = stops or {}
    n_words = len(words)
    steps = 0
    while steps < fuel:
        steps += 1
        if pc in stops:
            nxt = stops[pc](r)
            if isinstance(nxt, int):
                pc = nxt
                continue
            return nxt, steps
        k = pc - base
        if k < 0 or k & 3 or (k >> 2) >= n_words:
            return "fault", steps
        w = words[k >> 2]
        if seen is not None:
            seen.add(k >> 2)
        op, rd, f3, rs1, rs2, f7 = w & 0x7F, (w >> 7) & 31, (w >> 12) & 7, (w >> 15) & 31, (w >> 20) & 31, w >> 25
        a, b = r[rs1], r[rs2]
        imm_i = sx(w >> 20, 12)
        npc = (pc + 4) & M
        val = None
        if op == 0x13:
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
            else: return "fault", steps
            val &= M
        elif op == 0x03:
            n = (1, 2, 4, 8, 1, 2, 4, 0)[f3]
            ad = (a + imm_i) & M
            if not n or (aligned and ad % n) or (valid and not valid(ad)):
                return "fault", steps
            val = get(mem, ad, n)
            if f3 < 3:
                val = sx(val, 8 * n) & M
        elif op == 0x23:
            n = (1, 2, 4, 8, 0, 0, 0, 0)[f3]
            ad = (a + sx((f7 << 5) | rd, 12)) & M
            if not n or (aligned and ad % n) or (valid and not valid(ad)):
                return "fault", steps
            put(mem, ad, n, b)
            rd = 0
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
            elif key == (1, 4): val = -1 if b == 0 else div(sa, sb)
            elif key == (1, 5): val = M if b == 0 else a // b
            elif key == (1, 6): val = a if b == 0 else rem(sa, sb)
            elif key == (1, 7): val = a if b == 0 else a % b
            else: return "fault", steps
            val &= M
        elif op == 0x63:
            off = sx(((w >> 31) << 12) | (((w >> 7) & 1) << 11) | (((w >> 25) & 0x3F) << 5) | (((w >> 8) & 0xF) << 1), 13)
            if f3 == 0: taken = a == b
            elif f3 == 1: taken = a != b
            elif f3 == 4: taken = sx(a, 64) < sx(b, 64)
            elif f3 == 5: taken = sx(a, 64) >= sx(b, 64)
            elif f3 == 6: taken = a < b
            elif f3 == 7: taken = a >= b
            else: return "fault", steps
            if taken:
                npc = (pc + off) & M
            rd = 0
        elif op == 0x37:
            val = sx(w & 0xFFFFF000, 32) & M
        elif op == 0x17:
            val = (pc + sx(w & 0xFFFFF000, 32)) & M
        elif op == 0x6F:
            off = sx(((w >> 31) << 20) | (((w >> 12) & 0xFF) << 12) | (((w >> 20) & 1) << 11) | (((w >> 21) & 0x3FF) << 1), 21)
            val, npc = npc, (pc + off) & M
        elif op == 0x67 and f3 == 0:
            val, npc = npc, (a + imm_i) & M & ~1
        elif op == 0x1B:
            sh = (w >> 20) & 31
            if f3 == 0: val = a + imm_i
            elif f3 == 1 and f7 == 0: val = a << sh
            elif f3 == 5 and f7 == 0: val = (a & 0xFFFFFFFF) >> sh
            elif f3 == 5 and f7 == 0x20 and w32: val = sx(a, 32) >> sh
            else: return "fault", steps
            val = sx(val, 32) & M
        elif op == 0x3B:
            key = (f7, f3)
            a32, b32, sa, sb, sh = a & 0xFFFFFFFF, b & 0xFFFFFFFF, sx(a, 32), sx(b, 32), b & 31
            if key == (0x20, 0): val = a - b
            elif key == (0, 5): val = a32 >> sh
            elif not w32: return "fault", steps
            elif key == (0, 0): val = a + b
            elif key == (0, 1): val = a << sh
            elif key == (0x20, 5): val = sa >> sh
            elif key == (1, 0): val = a * b
            elif key == (1, 4): val = -1 if b32 == 0 else div(sa, sb)
            elif key == (1, 5): val = M if b32 == 0 else a32 // b32
            elif key == (1, 6): val = sa if b32 == 0 else rem(sa, sb)
            elif key == (1, 7): val = a32 if b32 == 0 else a32 % b32
            else: return "fault", steps
            val = sx(val, 32) & M
        elif w == 0x73 and ecall is not None:
            r[0] = 0
            reason = ecall(r)
            if reason is not None:
                return reason, steps
            rd = 0
        elif op == 0x0F and f3 == 0:  # fence: nothing to do
            rd = 0
        else:
            return "fault", steps
        if rd and val is not None:
            r[rd] = val
        pc = npc
    return None, steps
