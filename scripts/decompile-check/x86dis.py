#!/usr/bin/env python3
"""Compare the x86-64 decoder of `decompile` with LLVM's disassembler.

    x86dis.py OBJDUMP GUEST.elf ...

OBJDUMP is `llvm-objdump`. For each ELF, the instructions `decompile --listing` reads
(address, length, kind) are compared with the ones `llvm-objdump -d` prints: where each
function's instructions start, and the name of each. The decoder reads a function from its
start, one instruction after another, so agreeing on where every instruction starts is
agreeing on every length.

Bytes the decoder does not read are counted and listed by LLVM's name for them, not
compared: the decoder says so itself, and the lift gives up there. Exit status 0 only if
every instruction it does read is at the same place under the same name.

The names are compared as LLVM writes them in Intel syntax, with `movabs` as `mov`, `pause`
as `nop`, and the string instructions without their size.
"""
import os, re, subprocess, sys
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
DECOMPILE = os.environ.get("DECOMPILE") or os.path.join(os.path.dirname(os.path.dirname(HERE)), ".lake", "build", "bin", "decompile")
LINE = re.compile(r"^\s*([0-9a-f]+):\s*\t(.*)$")
STRING = re.compile(r"^(movs|stos)[bwdq]$")


def theirs(objdump, path):
    """Address -> name, for every instruction LLVM prints."""
    out = subprocess.run([objdump, "-d", "--no-show-raw-insn", "--x86-asm-syntax=intel", path],
                         capture_output=True, text=True, check=True).stdout
    names = {}
    for l in out.split("\n"):
        m = LINE.match(l)
        if not m:
            continue
        words = m.group(2).split()
        if not words:
            continue
        rep = words[0] == "rep" and len(words) > 1
        name = STRING.sub(r"\1", words[1] if rep else words[0])
        name = {"movabs": "mov", "pause": "nop"}.get(name, name)
        names[int(m.group(1), 16)] = ("rep " if rep and name in ("movs", "stos") else "") + name
    return names


def ours(path):
    """(address, length, kind) for every instruction the decoder reads, in order."""
    out = subprocess.run([DECOMPILE, "--listing", path], capture_output=True, text=True, check=True).stdout
    return [(int(a, 16), int(n), k) for a, n, k in (l.split(" ", 2) for l in out.split("\n") if l)]


def main(objdump, paths):
    same = differ = 0
    unread = Counter()
    for path in paths:
        llvm = theirs(objdump, path)
        for addr, size, kind in ours(path):
            if kind.startswith("(bytes"):
                unread[llvm.get(addr, "?")] += 1
                continue
            name = kind.split(" (")[0]
            if llvm.get(addr) == name:
                same += 1
            else:
                differ += 1
                if differ <= 20:
                    print(f"DIFFERS {os.path.basename(path)} {addr:x}: {kind}, LLVM has {llvm.get(addr)}")
    print(f"{same} instructions at the same place under the same name; {differ} differ; "
          f"{sum(unread.values())} places where the decoder stops")
    for name, n in unread.most_common():
        print(f"  not read: {name} ({n})")
    return differ == 0


if __name__ == "__main__":
    sys.exit(0 if main(sys.argv[1], sys.argv[2:]) else 1)
