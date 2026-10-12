#!/usr/bin/env python3
"""List the statics DWARF places in an address range, with their types and mutability.

    llvm-dwarfdump --debug-info ELF | dwarf-statics.py LO HI

Reads llvm-dwarfdump's text output (stdlib only). For every DW_TAG_variable whose
location is a single DW_OP_addr in [LO, HI), prints address, size, qualified name,
type, and whether the type contains an UnsafeCell anywhere inside it (the Rust
marker for interior mutability; `static mut` shows up as a mutable static with no
UnsafeCell, which this tool does not distinguish, see RESULTS.md).

The output is a hint: every address and size is meant to be checked against the
symbol table and the segment, never trusted.
"""
import re
import sys

DIE = re.compile(r"^0x([0-9a-f]+):(\s+)(DW_TAG_\w+|NULL)")
ATTR = re.compile(r"^\s+(DW_AT_\w+)\s+\((.*)\)\s*$")
REF = re.compile(r"^0x([0-9a-f]+)")
ADDR = re.compile(r"^DW_OP_addr 0x([0-9a-f]+)$")
STR = re.compile(r'^"(.*)"$')


def parse(stream):
    dies = {}
    stack = []  # (depth, offset)
    cur = None
    for line in stream:
        m = DIE.match(line)
        if m:
            off, indent, tag = int(m.group(1), 16), len(m.group(2)), m.group(3)
            if tag == "NULL":
                cur = None
                continue
            while stack and stack[-1][0] >= indent:
                stack.pop()
            parent = stack[-1][1] if stack else None
            cur = {"tag": tag, "parent": parent, "children": [], "attrs": {}}
            dies[off] = cur
            if parent is not None:
                dies[parent]["children"].append(off)
            stack.append((indent, off))
            continue
        if cur is not None:
            a = ATTR.match(line)
            if a:
                cur["attrs"][a.group(1)] = a.group(2)
    return dies


def name(d):
    v = d["attrs"].get("DW_AT_name")
    if v is None:
        return None
    m = STR.match(v)
    return m.group(1) if m else v


def ref(d, attr="DW_AT_type"):
    v = d["attrs"].get(attr)
    m = REF.match(v) if v else None
    return int(m.group(1), 16) if m else None


def qualname(dies, off):
    parts = []
    while off is not None:
        d = dies[off]
        if d["tag"] in ("DW_TAG_namespace", "DW_TAG_structure_type", "DW_TAG_variable",
                        "DW_TAG_subprogram") and name(d):
            parts.append(name(d))
        off = d["parent"]
    return "::".join(reversed(parts))


def type_name(dies, off):
    if off is None or off not in dies:
        return "?"
    d = dies[off]
    return name(d) or type_name(dies, ref(d)) if d["tag"] != "DW_TAG_pointer_type" else "*" + type_name(dies, ref(d))


def has_unsafecell(dies, off, seen=None):
    """True if the type at `off` contains UnsafeCell by value (not behind a pointer)."""
    seen = seen if seen is not None else set()
    if off is None or off in seen or off not in dies:
        return False
    seen.add(off)
    d = dies[off]
    if d["tag"] == "DW_TAG_pointer_type":
        return False
    if (name(d) or "").startswith("UnsafeCell"):
        return True
    if has_unsafecell(dies, ref(d), seen):
        return True
    for c in d["children"]:
        if dies[c]["tag"] in ("DW_TAG_member", "DW_TAG_variant_part", "DW_TAG_variant") \
                and (has_unsafecell(dies, ref(dies[c]), seen) or has_unsafecell(dies, c, seen)):
            return True
    return False


def byte_size(dies, off, depth=0):
    if off is None or off not in dies or depth > 20:
        return None
    d = dies[off]
    v = d["attrs"].get("DW_AT_byte_size")
    if v:
        return int(v, 16) if v.startswith("0x") else int(v)
    return byte_size(dies, ref(d), depth + 1)


def main():
    lo, hi = int(sys.argv[1], 16), int(sys.argv[2], 16)
    dies = parse(sys.stdin)
    rows = {}
    for off, d in dies.items():
        if d["tag"] != "DW_TAG_variable":
            continue
        loc = d["attrs"].get("DW_AT_location")
        m = ADDR.match(loc) if loc else None
        if not m:
            continue
        addr = int(m.group(1), 16)
        if not lo <= addr < hi:
            continue
        t = ref(d)
        # One static can be described in several CUs; keep the first.
        rows.setdefault(addr, (addr, byte_size(dies, t), qualname(dies, off), type_name(dies, t),
                               has_unsafecell(dies, t)))
    for addr, size, q, t, cell in sorted(rows.values()):
        print(f"0x{addr:08x}\t{size if size is not None else '?'}\t{'CELL' if cell else '-'}\t{q}\t{t}")


if __name__ == "__main__":
    main()
