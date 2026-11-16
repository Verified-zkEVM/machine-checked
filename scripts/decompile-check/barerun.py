#!/usr/bin/env python3
"""Run a bare guest for AArch64 or x86-64 on Unicorn, and print what it does.

    barerun.py GUEST.elf
    barerun.py --coverage [--instructions OUT] GUEST.elf ...

Unicorn is QEMU's processor emulation as a library: a machine this repository did not
write, and the reference for what a bare guest does, as SP1's executor is for an SP1 guest.
It needs the Python package `unicorn`.

The guest is loaded as its ELF says, with every other byte of its memory zero, and started
at its entry. A system call (`svc #0`, or `syscall`) is one of the four of `rust/src/bare.rs`,
answered by the same world as an SP1 guest's (`sp1run.World`), on the same five inputs. The
output has one line for each system call, the final status and the number of instructions.

With `--coverage` it prints, for the guests together, how many of their instructions some
input runs, and with `--instructions` writes the distinct ones to OUT, each as its bytes in
hexadecimal (for `decompile --kinds`).
"""
import os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from unicorn import Uc, UcError, UC_ARCH_ARM64, UC_ARCH_X86, UC_MODE_ARM, UC_MODE_64, UC_HOOK_CODE, UC_HOOK_INTR, UC_HOOK_INSN
from unicorn import arm64_const as A, x86_const as X
from fjrun import INPUTS
from sp1run import World, streams

FUEL = 20_000_000
PAGE = 0x1000


class Memory:
    """Unicorn's memory, as the dictionary of words `World` reads and writes."""

    def __init__(self, uc):
        self.uc = uc

    def get(self, a, default=0):
        return int.from_bytes(self.uc.mem_read(a, 8), "little")

    def __setitem__(self, a, v):
        self.uc.mem_write(a, v.to_bytes(8, "little"))


class Elf:
    def __init__(self, data):
        assert data[:4] == b"\x7fELF" and data[4] == 2, "not an ELF64 file"
        u = lambda o, n: int.from_bytes(data[o:o + n], "little")
        self.machine, self.entry, self.segments = u(0x12, 2), u(0x18, 8), []
        phoff, phentsize, phnum = u(0x20, 8), u(0x36, 2), u(0x38, 2)
        for i in range(phnum):
            p = phoff + i * phentsize
            if u(p, 4) == 1:
                off, vaddr, filesz, memsz = u(p + 8, 8), u(p + 0x10, 8), u(p + 0x20, 8), u(p + 0x28, 8)
                self.segments.append((vaddr, data[off:off + filesz], memsz, bool(u(p + 4, 4) & 1)))


def run(elf, inp, seen=None):
    arm = elf.machine == 183
    uc = Uc(UC_ARCH_ARM64, UC_MODE_ARM) if arm else Uc(UC_ARCH_X86, UC_MODE_64)
    lo = min(v for v, _, _, _ in elf.segments) & ~(PAGE - 1)
    hi = (max(v + m for v, _, m, _ in elf.segments) + PAGE - 1) & ~(PAGE - 1)
    uc.mem_map(lo, hi - lo)
    for vaddr, data, _, _ in elf.segments:
        uc.mem_write(vaddr, data)
    world = World(Memory(uc), streams(inp))
    state = {"steps": 0, "reason": None}

    def call(number, a, b, c):
        """The system call; its result, or `None` if the run ends."""
        t0, a0, reason = world.call(number, a, b, c)
        if reason is not None:
            state["reason"] = reason
            uc.emu_stop()
            return None
        return t0 if number == 0xF0 else a0

    def code(uc, address, size, _):
        state["steps"] += 1
        if seen is not None:
            seen.add((address, size))
        if state["steps"] > FUEL:
            uc.emu_stop()

    def svc(uc, intno, _):
        if intno != 2:
            state["reason"] = "fault"
            uc.emu_stop()
            return
        r = call(uc.reg_read(A.UC_ARM64_REG_X8), uc.reg_read(A.UC_ARM64_REG_X0), uc.reg_read(A.UC_ARM64_REG_X1), uc.reg_read(A.UC_ARM64_REG_X2))
        if r is not None:
            uc.reg_write(A.UC_ARM64_REG_X0, r)

    def syscall(uc, _):
        r = call(uc.reg_read(X.UC_X86_REG_RAX), uc.reg_read(X.UC_X86_REG_RDI), uc.reg_read(X.UC_X86_REG_RSI), uc.reg_read(X.UC_X86_REG_RDX))
        if r is not None:
            uc.reg_write(X.UC_X86_REG_RAX, r)

    uc.hook_add(UC_HOOK_CODE, code)
    if arm:
        uc.hook_add(UC_HOOK_INTR, svc)
    else:
        uc.hook_add(UC_HOOK_INSN, syscall, None, 1, 0, X.UC_X86_INS_SYSCALL)
    try:
        uc.emu_start(elf.entry, 0)
    except UcError:
        state["reason"] = state["reason"] or "fault"
    status = {None: "still running (out of fuel)", "fault": "failed"}.get(state["reason"], state["reason"])
    return world.events, status, state["steps"]


def describe(path):
    elf = Elf(open(path, "rb").read())
    out = []
    for inp in INPUTS:
        events, status, steps = run(elf, inp)
        out.append("\n".join([f"## input {bytes(inp).hex()}", *events, status, f"({steps} steps)"]))
    return "\n\n".join(out) + "\n"


if __name__ == "__main__":
    if sys.argv[1] == "--coverage":
        paths, ran, total, distinct = sys.argv[2:], 0, 0, set()
        out = paths[1] if paths[0] == "--instructions" else None
        for path in paths[2:] if out else paths:
            elf, seen = Elf(open(path, "rb").read()), set()
            for inp in INPUTS:
                run(elf, inp, seen)
            for vaddr, data, _, x in elf.segments:
                if x:
                    total += len(data)
                    distinct |= {data[a - vaddr:a - vaddr + n].hex() for a, n in seen if vaddr <= a < vaddr + len(data)}
            ran += len(seen)
        if out:
            open(out, "w").write("".join(w + "\n" for w in sorted(distinct)))
        print(f"{ran} instructions run, of {total} bytes of code")
    else:
        sys.stdout.write(describe(sys.argv[1]))
