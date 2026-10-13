#!/usr/bin/env python3
"""List the address-taken functions of an image whose demangled name matches a pattern.

    cfi-candidates.py ELF NM DIS PATTERN

A function is address-taken if its entry address is materialized by an `auipc`/`addi`
pair in the code (and not then called through), or stored as a doubleword in a loaded
segment. PATTERN is a Python regular expression over llvm-cxxfilt's demangling.

Prints one line per candidate: hex address, then the demangled name. The output is the
candidate list of a control-flow premise (`Env.cfi`), a reviewed input like the hand-proof
registry: nothing trusts it, the kernel only checks that the analysed code uses it as
stated, and the reference run is its satisfiability witness.
"""
import re
import struct
import subprocess
import sys


def functions(nm_path):
    out = {}
    for line in open(nm_path):
        parts = line.split()
        if len(parts) >= 4 and parts[2].lower() == "t":
            out[int(parts[0], 16)] = parts[3]
    return out


def demangle(names):
    p = subprocess.run(["llvm-cxxfilt"], input="\n".join(names), capture_output=True, text=True)
    return p.stdout.splitlines()


AUIPC = re.compile(r"^([0-9a-f]+):\s+auipc\s+(\w+), (0x[0-9a-f]+)$")
ADDI = re.compile(r"^([0-9a-f]+):\s+addi\s+(\w+), (\w+), (-?0x[0-9a-f]+)$")
JALR = re.compile(r"^([0-9a-f]+):\s+jalr\s+\w+, (-?0x[0-9a-f]+)\((\w+)\)")


def from_code(dis_path, entries):
    taken = set()
    lines = [l.strip() for l in open(dis_path)]
    for i, line in enumerate(lines):
        m = AUIPC.match(line)
        if not m:
            continue
        pc, rd, hi = int(m.group(1), 16), m.group(2), int(m.group(3), 16)
        base = (pc + ((hi << 12) if hi < 0x80000 else ((hi - 0x100000) << 12))) & (2**64 - 1)
        for nxt in lines[i + 1:i + 3]:
            a = ADDI.match(nxt)
            if a and a.group(3) == rd:
                tgt = (base + int(a.group(4), 16)) & (2**64 - 1)
                if tgt in entries:
                    taken.add(tgt)
                break
            if JALR.match(nxt):
                break
    return taken


def from_data(elf_path, entries):
    data = open(elf_path, "rb").read()
    phoff, = struct.unpack_from("<Q", data, 0x20)
    phentsize, phnum = struct.unpack_from("<HH", data, 0x36)
    taken = set()
    for i in range(phnum):
        ptype, _, off, vaddr, _, filesz, _, _ = struct.unpack_from("<IIQQQQQQ", data, phoff + i * phentsize)
        if ptype != 1:
            continue
        seg = data[off:off + filesz]
        for j in range(0, len(seg) - 7, 4):
            w, = struct.unpack_from("<Q", seg, j)
            if w in entries:
                taken.add(w)
    return taken


def main():
    elf, nm, dis, pattern = sys.argv[1:5]
    fns = functions(nm)
    entries = set(fns)
    taken = from_code(dis, entries) | from_data(elf, entries)
    addrs = sorted(taken)
    names = demangle([fns[a] for a in addrs])
    rx = re.compile(pattern)
    for a, n in zip(addrs, names):
        if rx.search(n):
            print(f"{a:08x}\t{n}")


if __name__ == "__main__":
    main()
