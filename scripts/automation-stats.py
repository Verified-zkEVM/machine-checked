#!/usr/bin/env python3
"""automation-stats.py PROVED.lprog [DEFAULT.lprog]: the counts of `docs/design/Automation.md`
("zip-2005, counted"), from the Lprog text `decompile` writes.

    lake exe decompile --to lprog --proved GUEST.elf PROVED.lprog
    lake exe decompile --to lprog GUEST.elf DEFAULT.lprog
    python3 scripts/automation-stats.py PROVED.lprog DEFAULT.lprog

An instruction is a `label` and the commands after it. It is straight-line if its commands are
only `set`, `load` and `store`; a `trap` (a word that is no instruction) is counted, and ends
a block like any other command. A block is a run of straight-line instructions, one after
another in a function. A call is a `call` (it returns); a tail call is a `tail`; a computed one
of either has `via` and its candidates, `N` then `N` function indices. A loop is a backward
branch: an `if` or `goto` to a label at or before its own.
"""

import sys
from statistics import median


def functions(path):
    """Each function of the text: a list of instructions, each a list of its command lines."""
    fns, cur, ins = [], None, None
    for line in open(path):
        s = line.strip()
        if s.startswith("fn "):
            cur = []
            fns.append(cur)
            ins = None
        elif s.startswith("label "):
            ins = [s]
            cur.append(ins)
        elif s and ins is not None and not s.startswith("#"):
            ins.append(s)
    return fns


def cands(cmd):
    """The number of candidates of a computed call or tail call, or None."""
    if " via " not in f" {cmd} ":
        return None
    w = cmd.split()
    # `… N c1 … cN`: the count is the word N places before the end.
    for k in range(len(w) - 1, -1, -1):
        if w[k].isdigit() and int(w[k]) == len(w) - 1 - k:  # counts are decimal
            return int(w[k])
    return None


def stats(path):
    fns = functions(path)
    n = sum(len(f) for f in fns)
    straight = 0
    blocks = []
    calls = tails = 0
    computed = []
    loops = 0
    aborts = 0
    traps = 0
    for f in fns:
        run = 0
        for i, ins in enumerate(f):
            here = int(ins[0].split()[1], 0)
            cmds = ins[1:]
            if all(c.split()[0] in ("set", "load", "store") for c in cmds):
                straight += 1
                run += 1
            else:
                if run:
                    blocks.append(run)
                run = 0
            for c in cmds:
                op = c.split()[0]
                if op == "call":
                    calls += 1
                elif op == "tail":
                    tails += 1
                elif op == "abort":
                    aborts += 1
                elif op == "trap":
                    traps += 1
                if op in ("call", "tail") and cands(c) is not None:
                    computed.append(cands(c))
                if op in ("if", "goto") and int(c.split()[-1], 0) <= here:
                    loops += 1
        if run:
            blocks.append(run)
    return {
        "functions": len(fns),
        "instructions": n,
        "straight": straight,
        "in blocks of 8 or more": sum(b for b in blocks if b >= 8),
        "longest block": max(blocks, default=0),
        "calls": calls,
        "tail calls": tails,
        "computed calls and tail calls": len(computed),
        "of them with one candidate": sum(1 for c in computed if c == 1),
        "loops": loops,
        "aborts": aborts,
        "traps": traps,
        "median function": median(len(f) for f in fns),
        "largest function": max(len(f) for f in fns),
    }


def main():
    p = stats(sys.argv[1])
    s = p["straight"]
    print(f"{p['functions']} functions, {p['instructions']} instructions")
    print(f"straight-line: {s} ({100 * s / p['instructions']:.0f}%), "
          f"{100 * p['in blocks of 8 or more'] / s:.0f}% of that in blocks of 8 or more, "
          f"the longest {p['longest block']}")
    print(f"calls {p['calls']}, tail calls {p['tail calls']}; computed, of both: "
          f"{p['computed calls and tail calls']}, {p['of them with one candidate']} with one candidate")
    print(f"loops {p['loops']}, aborts {p['aborts']}, traps {p['traps']}")
    print(f"function size: median {p['median function']}, the largest {p['largest function']}")
    if len(sys.argv) > 2:
        d = stats(sys.argv[2])
        print(f"default lift: computed calls and tail calls {d['computed calls and tail calls']}, "
              f"{d['of them with one candidate']} with one candidate; aborts {d['aborts']}")


if __name__ == "__main__":
    main()
