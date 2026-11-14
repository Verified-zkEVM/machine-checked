#!/usr/bin/env python3
"""Run a Flapjack image and print what it does.

    fjrun.py IMAGE.fjimg
    fjrun.py --coverage IMAGE.fjimg ...

The RV64IM interpreter of `rv64.py` with the installation and the test world of flapjack-flip
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
import os, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import rv64
from rv64 import M

CODE = 0x80010000
HALT, CCACHE = CODE - 16, CODE - 32
BITMAPS, HEAP, STACK, STACK_END = 0xA0000000, 0xA0100000, 0xA0500000, 0xA0900000
FUEL = 2_000_000


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
    inp = list(inp)
    events = []

    def ffi(name):
        def call(r):
            nonlocal inp
            cp, cl, ap, al = r[10], r[11], r[12], r[13]
            if not (range_valid(cp, cl) and range_valid(ap, al)):
                return "fault"
            conf = [rv64.get(mem, cp + i, 1) for i in range(cl)]
            arr = [rv64.get(mem, ap + i, 1) for i in range(al)]
            new = inp[:al] + [0] * (al - len(inp))
            inp = inp[al:]
            events.append((name, conf, arr, new))
            for i, b in enumerate(new):
                rv64.put(mem, ap + i, 1, b)
            return r[1]
        return call

    stops = {HALT: lambda r: "halted: success" if r[10] == 0 else "halted: out of memory",
             CCACHE: lambda r: "fault"}
    for i, name in enumerate(img.ffi):
        stops[(CODE - 16 * (i + 3)) & M] = ffi(name)
    reason, steps = rv64.run(words, CODE, r, mem, CODE, FUEL, stops, None, valid, seen)
    status = {None: "still running (out of fuel)",
              "fault": "failed (trap, bad memory access or bad FFI arguments)"}.get(reason, reason)
    return events, status, steps


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
