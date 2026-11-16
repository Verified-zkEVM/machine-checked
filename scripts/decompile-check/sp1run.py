#!/usr/bin/env python3
"""Run an SP1 guest, or the image `decompile --to pancake` and Flapjack make of one, and
print what it does.

    sp1run.py GUEST.elf
    sp1run.py IMAGE.fjimg [FUEL]
    sp1run.py --coverage [--instructions OUT] FILE ...

Both run on the RV64IM interpreter of `rv64.py`, in one world: SP1's system calls (`World`),
as riscv-zkvm models them (`RiscvZkvm/Rv64/StepOn.lean`, `sp1Ecall`), and five inputs, each
a stream of two hint vectors.

* The guest is loaded as SP1 loads it: its segments in memory, the registers zero, the pc
  at the ELF's entry. An `ecall` is a system call, with the number in `t0` and the arguments
  in `a0`, `a1` and `a2`.
* The image is installed as any Flapjack image is, in a layout whose heap is the guest's
  whole address space (`RiscV/Sp1/Pancake.lean`): it reads and writes the guest's addresses.
  Its FFI function `ecall` is the same system call, on the four values it is passed; the new
  `t0` and `a0` are left at `SCRATCH`. Its FFI function `trap` says the program gave up.
  The image of a bare guest (`barerun.py`) has the FFI function `syscall` instead: the
  same call with the one result its guest reads left at `SCRATCH`. Such an image may load
  and store at addresses that are not aligned, as its guest's processor does.
  An FFI function `mark` does nothing but have the run say `(marked)`: `check.py mutants`
  puts a call of it where it changes a program, to know whether the change was reached.

The output has one line for each system call (its number, its arguments, the bytes it read
from memory or wrote to it), the final status and the steps. For an image that is the
decompiled guest, everything but the steps is the same as for the guest.

A run of an image is cut off after FUEL steps (400,000,000 if not given).

With `--coverage` it prints, for the files together, how many of their instructions some
input runs, and with `--instructions` writes the distinct ones to OUT, each as its bytes in
hexadecimal (for `decompile --kinds`).
"""
import os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rv64
from rv64 import M
from fjrun import Image, INPUTS

SCRATCH = 0x100
# the image's layout: its heap is the guest's address space
HEAP, STACK, STACK_END = 0, 1 << 40, (1 << 40) + (1 << 30)
BITMAPS, CODE = 1 << 41, (1 << 41) + (1 << 28)
GUEST_FUEL, IMAGE_FUEL = 20_000_000, 400_000_000

HALT, WRITE, COMMIT, COMMIT_DEFERRED, HINT_LEN, HINT_READ = 0, 2, 0x10, 0x1A, 0xF0, 0xF1


def streams(inp):
    """The hint vectors of a test input: its bytes, and its bytes backwards."""
    return [bytes(inp), bytes(reversed(inp))]


class World:
    """SP1's system calls on a memory, and the record of them."""

    def __init__(self, mem, hints):
        self.mem, self.hints, self.events = mem, list(hints), []

    def call(self, t0, a0, a1, a2):
        """A system call: the new `t0` and `a0`, and a reason to end the run or `None`."""
        say = lambda name, *more: self.events.append(" ".join([name, f"{a0:x}", f"{a1:x}", f"{a2:x}", *more]))
        if t0 == HALT:
            say("halt")
            return t0, a0, f"halted: exit {a0 & 0xFF}"
        if t0 == WRITE:
            if a2 > 1 << 24:
                say("write", "(too long)")
                return t0, a0, "fault"
            say("write", bytes(rv64.get(self.mem, (a1 + i) & M, 1) for i in range(a2)).hex())
            return t0, a0, None
        if t0 in (COMMIT, COMMIT_DEFERRED):
            say("commit" if t0 == COMMIT else "commit_deferred")
            return t0, a0, None
        if t0 == HINT_LEN:
            n = len(self.hints[0]) if self.hints else M
            say("hint_len", f"-> {n:x}")
            return n, a0, None
        if t0 == HINT_READ:
            if not self.hints or a1 != len(self.hints[0]) or a0 % 8:
                say("hint_read", "(refused)")
                return t0, a0, "fault"
            data = self.hints.pop(0)
            say("hint_read", data.hex())
            # as SP1 writes it: whole words, and one more than the bytes need
            padded = data + bytes(8 * (len(data) // 8 + 1) - len(data))
            for i in range(0, len(padded), 8):
                self.mem[(a0 + i) & M] = int.from_bytes(padded[i:i + 8], "little")
            return t0, a0, None
        say(f"unknown:{t0:x}")
        return t0, a0, "fault"


class Elf:
    """The loaded segments of an ELF64 file, and its entry."""

    def __init__(self, data):
        assert data[:4] == b"\x7fELF" and data[4] == 2, "not an ELF64 file"
        u = lambda o, n: int.from_bytes(data[o:o + n], "little")
        self.entry, self.segments = u(0x18, 8), []
        phoff, phentsize, phnum = u(0x20, 8), u(0x36, 2), u(0x38, 2)
        for i in range(phnum):
            p = phoff + i * phentsize
            if u(p, 4) == 1:
                off, vaddr, filesz = u(p + 8, 8), u(p + 0x10, 8), u(p + 0x20, 8)
                self.segments.append((vaddr, data[off:off + filesz], bool(u(p + 4, 4) & 1)))


def status_of(reason):
    return {None: "still running (out of fuel)", "fault": "failed"}.get(reason, reason)


def run_guest(elf, inp, seen=None):
    mem = {}
    for vaddr, data, _ in elf.segments:
        for i, b in enumerate(data):
            if b:
                rv64.put(mem, vaddr + i, 1, b)
    (base, text, _), = [s for s in elf.segments if s[2]]
    words = [int.from_bytes(text[i:i + 4], "little") for i in range(0, len(text) - len(text) % 4, 4)]
    world = World(mem, streams(inp))

    def ecall(r):
        r[5], r[10], reason = world.call(r[5], r[10], r[11], r[12])
        return reason

    reason, steps = rv64.run(words, base, [0] * 32, mem, elf.entry, GUEST_FUEL, None, ecall, None, seen)
    return world.events, status_of(reason), steps


def run_image(img, inp, seen=None):
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
    world = World(mem, streams(inp))
    # what the guest's `halt` said, until the image itself halts
    said = []

    def ecall(r):
        t0, a0, reason = world.call(r[10], r[11], r[12], r[13])
        mem[SCRATCH], mem[SCRATCH + 8] = t0, a0
        if reason == "fault":
            return "fault"
        if reason is not None:
            said.append(reason)
        return r[1]

    def syscall(r):
        number = r[10]
        t0, a0, reason = world.call(number, r[11], r[12], r[13])
        mem[SCRATCH] = t0 if number == HINT_LEN else a0
        if reason == "fault":
            return "fault"
        if reason is not None:
            said.append(reason)
        return r[1]

    def halt(r):
        if r[10] != 0:
            return "fault"
        return said[0] if said else "returned without halting"

    marked = []

    def mark(r):
        marked.append(True)
        return r[1]

    stops = {(CODE - 16) & M: halt, (CODE - 32) & M: lambda r: "fault"}
    for i, name in enumerate(img.ffi):
        stops[(CODE - 16 * (i + 3)) & M] = {"ecall": ecall, "syscall": syscall, "mark": mark,
                                            "trap": lambda r: f"gave up (trap {r[10]})"}.get(name, lambda r: "fault")
    # a bare guest's processor loads and stores at any address, and so does its image
    reason, steps = rv64.run(words, CODE, r, mem, CODE, IMAGE_FUEL, stops, None, None, seen,
                             aligned="syscall" not in img.ffi)
    return world.events, status_of(reason) + ("\n(marked)" if marked else ""), steps


def load(path):
    data = open(path, "rb").read()
    if data[:4] == b"\x7fELF":
        return Elf(data), run_guest
    return Image(data.decode()), run_image


def describe(path, fuel=None):
    global IMAGE_FUEL
    if fuel:
        IMAGE_FUEL = fuel
    thing, run = load(path)
    out = []
    for inp in INPUTS:
        events, status, steps = run(thing, inp)
        out.append("\n".join([f"## input {bytes(inp).hex()}", *events, status, f"({steps} steps)"]))
    return "\n\n".join(out) + "\n"


if __name__ == "__main__":
    if sys.argv[1] == "--coverage":
        paths, ran, total, distinct = sys.argv[2:], 0, 0, set()
        out = paths[1] if paths[0] == "--instructions" else None
        for path in paths[2:] if out else paths:
            thing, run = load(path)
            seen = set()
            for inp in INPUTS:
                run(thing, inp, seen)
            code = [d for _, d, x in thing.segments if x][0] if isinstance(thing, Elf) else thing.code
            distinct |= {bytes(code[4 * k:4 * k + 4]).hex() for k in seen}
            ran, total = ran + len(seen), total + len(code) // 4
        if out:
            open(out, "w").write("".join(w + "\n" for w in sorted(distinct)))
        print(f"{ran} of {total} instructions run ({100 * ran // max(1, total)}%)")
    else:
        sys.stdout.write(describe(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else None))
