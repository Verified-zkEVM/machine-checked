#!/usr/bin/env python3
"""Return-address integrity, per function, by dataflow over llvm-objdump output.

    llvm-objdump -d --no-show-raw-insn -M no-aliases ELF > DIS
    llvm-nm -S --defined-only ELF > NM
    llvm-dwarfdump --eh-frame ELF > EH        (optional cross-check)
    ra-check.py DIS NM [EH]

The property: at every exit of a function (`ret`, a tail call, a jump out of the function),
`ra` holds the value it had at entry and `sp` is back at its entry value. The analysis
tracks, per instruction, the abstract state

    sp_d  : sp - sp_entry           (None when lost)
    s0_d  : s0 - sp_entry           (frame pointer, None when not derived from sp)
    ra_ok : ra = ra_entry
    slots : the offsets (from sp_entry) of stack words known to hold ra_entry

and joins at merge points. It is a prototype of a checker, NOT sound, and says so where it
is not: a store through a base other than sp/s0 is assumed not to hit a tracked slot, and a
callee is assumed to preserve sp, s0 and the caller's frame (the RISC-V calling
convention). Those two assumptions are exactly what a proof would have to supply.
"""
import re
import sys
from collections import defaultdict

INSN = re.compile(r"^\s*([0-9a-f]+):\s+(\S+)\s*(.*?)\s*(?:<.*)?$")
MEMOP = re.compile(r"^(-?(?:0x[0-9a-f]+|\d+))\((\w+)\)$")
HEX = re.compile(r"0x[0-9a-f]+")
BRANCHES = {"beq", "bne", "blt", "bge", "bltu", "bgeu"}
STORES = {"sd", "sw", "sh", "sb"}
NO_RD = BRANCHES | STORES | {"ecall", "ebreak", "fence", "unimp", "c.unimp"}


def sx20(v):
    return v - (1 << 20) if v >= (1 << 19) else v


def num(s):
    return int(s, 16) if s.lstrip("-").startswith("0x") else int(s)


def parse_insns(path):
    out = {}
    for line in open(path):
        m = INSN.match(line)
        if m and ":" not in m.group(2):
            ops = [o.strip() for o in m.group(3).split(",")] if m.group(3) else []
            out[int(m.group(1), 16)] = (m.group(2), ops)
    return out


def parse_funcs(path):
    funcs = []
    for line in open(path):
        p = line.split()
        if len(p) >= 4 and p[2] in ("t", "T") and not p[3].startswith(".L"):
            funcs.append((int(p[0], 16), int(p[1], 16), p[3]))
    return sorted(set(funcs))


def parse_eh(path):
    """FDE pc range -> CFA offset of the saved ra (X1), if the FDE records one."""
    fdes, cur = {}, None
    for line in open(path):
        m = re.search(r"FDE cie=\w+ pc=([0-9a-f]+)\.\.\.([0-9a-f]+)", line)
        if m:
            cur = (int(m.group(1), 16), int(m.group(2), 16))
            fdes[cur] = None
            continue
        m = re.search(r"DW_CFA_offset: X1 (-?\d+)", line)
        if m and cur:
            fdes[cur] = int(m.group(1))
    return fdes


def effect(st, op, ops, pc, notes):
    """The effect of one straight-line instruction on the abstract state."""
    sp_d, s0_d, ra_ok, slots = st
    rd = ops[0] if ops and op not in NO_RD else None

    def mem(o):
        m = MEMOP.match(o)
        if not m:
            return None, None
        base, off = m.group(2), num(m.group(1))
        if base == "sp" and sp_d is not None:
            return sp_d + off, base
        if base == "s0" and s0_d is not None:
            return s0_d + off, base
        return None, base

    if op in STORES:
        a, base = mem(ops[1])
        if a is not None:
            if op == "sd" and ops[0] == "ra" and ra_ok:
                slots = slots | {a}
            else:
                slots = frozenset(s for s in slots if not (s <= a < s + 8 or a <= s < a + 8))
        elif base not in ("sp", "s0"):
            notes.add("stores through non-frame bases assumed not to alias the ra slot")
        return (sp_d, s0_d, ra_ok, slots)
    # Register-writing instructions.
    if rd == "sp":
        if op == "addi" and ops[1] == "sp" and sp_d is not None:
            sp_d = sp_d + num(ops[2])
        elif op == "addi" and ops[1] == "s0" and s0_d is not None:
            sp_d = s0_d + num(ops[2])
        else:
            sp_d = None
            notes.add(f"sp lost at {pc:#x} ({op} {', '.join(ops)})")
    elif rd == "s0":
        s0_d = sp_d + num(ops[2]) if op == "addi" and ops[1] == "sp" and sp_d is not None else None
        if op == "ld":
            s0_d = None  # restored callee-saved s0: no longer an sp-relative frame pointer
    elif rd == "ra":
        if op == "ld":
            a, _ = mem(ops[1])
            ra_ok = a is not None and a in slots
        else:
            ra_ok = False
    return (sp_d, s0_d, ra_ok, slots)


def check(lo, size, insns):
    hi = lo + size
    entry = (0, None, True, frozenset())
    state = {lo: entry}
    work = [lo]
    issues, notes = [], set()
    exits = 0

    def flow(pc, st):
        if pc not in insns or not lo <= pc < hi:
            return
        old = state.get(pc)
        if old is None:
            state[pc] = st
            work.append(pc)
            return
        j = (old[0] if old[0] == st[0] else None, old[1] if old[1] == st[1] else None,
             old[2] and st[2], old[3] & st[3])
        if j != old:
            state[pc] = j
            work.append(pc)

    def at_exit(pc, st, kind):
        nonlocal exits
        exits += 1
        sp_d, _, ra_ok, _ = st
        if not ra_ok:
            issues.append(f"{pc:#x} {kind}: ra not the entry value")
        if sp_d != 0:
            issues.append(f"{pc:#x} {kind}: sp offset {sp_d}")

    while work:
        pc = work.pop()
        st = state[pc]
        op, ops = insns[pc]
        sp_d, s0_d, ra_ok, slots = st
        nxt = pc + 4 if not op.startswith("c.") else pc + 2
        if op in BRANCHES:
            flow(nxt, st)
            flow(num(ops[2]), st)
            continue
        if op == "jal":
            tgt = num(HEX.search(ops[1]).group(0))
            if ops[0] == "zero":
                if lo <= tgt < hi:
                    flow(tgt, st)
                else:
                    at_exit(pc, st, "tail jump")
            else:  # call: ra clobbered, callee assumed to keep sp/s0/our frame
                flow(nxt, (sp_d, s0_d, False, slots))
            continue
        if op == "jalr" and ops[0] == "t0":
            # A machine-outliner call: link in t0, ra untouched. Apply the outlined body's
            # straight-line effect (it ends in `jalr zero, 0(t0)`) to this frame.
            prev = insns.get(pc - 4)
            if prev and prev[0] == "auipc" and prev[1][0] == "t0":
                tgt = pc - 4 + (sx20(num(prev[1][1])) << 12) + num(MEMOP.match(ops[1]).group(1))
                q, ok = tgt, False
                while q in insns:
                    qop, qops = insns[q]
                    if qop == "jalr" and qops[0] == "zero" and qops[1] in ("0(t0)", "0x0(t0)"):
                        ok = True
                        break
                    st = effect(st, qop, qops, q, notes)
                    q += 4
                if ok:
                    flow(nxt, st)
                    continue
            notes.add(f"unresolved outlined call {pc:#x}")
            flow(nxt, st)
            continue
        if op == "jalr":
            if ops[0] == "zero":
                if ops[1] in ("0(ra)", "0x0(ra)"):
                    at_exit(pc, st, "ret")
                elif re.search(r"\((t1|t0)\)$", ops[1]) and pc - 4 in insns and insns[pc - 4][0] == "auipc":
                    at_exit(pc, st, "tail call")
                else:
                    notes.add(f"indirect jump {pc:#x} {ops[1]}")
            else:
                flow(nxt, (sp_d, s0_d, False, slots))
            continue
        if op in ("ecall", "ebreak", "fence"):
            flow(nxt, st)
            continue
        if op in ("unimp", "c.unimp"):
            continue
        flow(nxt, effect(st, op, ops, pc, notes))

    saved = sorted({s for (_, _, _, sl) in state.values() for s in sl})
    return issues, notes, exits, saved


def main():
    insns = parse_insns(sys.argv[1])
    funcs = parse_funcs(sys.argv[2])
    eh = parse_eh(sys.argv[3]) if len(sys.argv) > 3 else {}
    tally = defaultdict(int)
    bad, cfi_mismatch, cfi_covered = [], [], 0
    seen_fde = set()
    for lo, size, name in funcs:
        issues, notes, exits, saved = check(lo, size, insns)
        indirect = any(n.startswith("indirect") for n in notes)
        if issues:
            tally["violations"] += 1
            bad.append((name, lo, issues[:3]))
        elif exits == 0:
            tally["no exit (diverges / panics only)"] += 1
        elif indirect:
            tally["ok, but has indirect jumps (not followed)"] += 1
        else:
            tally["ok"] += 1
        for (a, b), off in eh.items():
            if a == lo and lo not in seen_fde:
                seen_fde.add(lo)
                cfi_covered += 1
                ours = saved[0] if saved else None
                if off is not None and ours != off:
                    cfi_mismatch.append((name, lo, off, ours))
    print(f"functions: {len(funcs)}")
    for k, v in sorted(tally.items(), key=lambda kv: -kv[1]):
        print(f"  {v:5d}  {k}")
    print(f"eh_frame FDEs matching a function start: {cfi_covered} of {len(eh)}; "
          f"ra-slot disagreements with CFI: {len(cfi_mismatch)}")
    for n, lo, off, ours in cfi_mismatch[:10]:
        print(f"  CFI says ra at CFA{off:+d}, analysis says {ours}: {lo:#x} {n[:90]}")
    for n, lo, iss in bad[:15]:
        print(f"  VIOLATION {lo:#x} {n[:90]}")
        for i in iss:
            print(f"      {i}")


if __name__ == "__main__":
    main()
