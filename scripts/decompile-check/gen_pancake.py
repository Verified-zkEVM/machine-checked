#!/usr/bin/env python3
"""Write random Pancake test programs that use the whole language.

    gen_pancake.py SEED COUNT OUTDIR

writes OUTDIR/pan_SEED_NNN/source.pnk. flapjack-flip's own generator
(`scripts/gen_tests.py` there) makes programs of arithmetic, branches, bounded loops and
calls. These add what it leaves out, so that the code Flapjack emits for each is in the
tests: global variables, functions that return a pair, exceptions thrown and caught across
calls, recursion and tail calls a few hundred frames deep, `break` and `continue`, loads and
stores of bytes, words and 32 bits at addresses from the start of memory to 1.9 MiB into it,
several FFI names, and configuration bytes.

Every program reads its input through `@in`, shows what it computed through the other FFI
names, and ends. `flip-check build OUTDIR` (flapjack-flip) compiles each with Flapjack,
runs it on the reference machine, writes `image.fjimg` and `expected.txt`, and rejects a
program that does not end normally on every test input.
"""
import random, sys
from pathlib import Path

BINOPS = ["+", "-", "*", "&", "|", "^"]
SHIFTS = ["<<", ">>>", ">>", "#>>"]
CMPS = ["<", "<+", "==", "!=", ">=", ">=+", "<=", ">+"]
OUTS = ["out", "err", "log"]
FAR = [0, 4096, 0x10000, 0x100000, 0x1E0000]  # scratch areas, up to 1.9 MiB into memory


class Gen:
    def __init__(self, rng):
        self.rng = rng
        self.globals = [f"g{k}" for k in range(rng.randrange(0, 4))]
        self.exn = rng.random() < 0.6
        self.funcs = []  # (name, arity, kind)

    def lit(self):
        r = self.rng.random()
        if r < 0.5: return str(self.rng.randrange(0, 16))
        if r < 0.8: return str(self.rng.randrange(0, 1 << 16))
        if r < 0.9: return str(-self.rng.randrange(1, 1 << 31))
        return str(self.rng.randrange(0, 1 << 63))

    def expr(self, names, depth):
        r = self.rng.random()
        if depth == 0 or r < 0.3:
            return self.rng.choice(names + self.globals) if self.rng.random() < 0.75 else self.lit()
        a = self.expr(names, depth - 1)
        if r < 0.45: return f"({a} {self.rng.choice(SHIFTS)} {self.rng.randrange(0, 64)})"
        b = self.expr(names, depth - 1)
        if r < 0.6: return f"({a} {self.rng.choice(CMPS)} {b})"
        return f"({a} {self.rng.choice(BINOPS)} {b})"

    def cond(self, names):
        return f"{self.expr(names, 1)} {self.rng.choice(CMPS)} {self.expr(names, 1)}"

    def show(self, pad, e):
        """Send the value of `e` out, sometimes with configuration bytes."""
        name = self.rng.choice(OUTS)
        out = [f"{pad}st @base + 512, {e};"]
        if self.rng.random() < 0.3:
            out += [f"{pad}st8 @base + 600, {self.rng.randrange(0, 256)};",
                    f"{pad}@{name}(@base + 600, 1, @base + 512, 8);"]
        else:
            out += [f"{pad}@{name}(0, 0, @base + 512, 8);"]
        return out

    def memory(self, pad, names, target):
        """A store and a load back, of some width, somewhere in memory."""
        at = f"@base + {self.rng.choice(FAR) + 1024 + 8 * self.rng.randrange(0, 64)}"
        e = self.expr(names, 2)
        k = self.rng.random()
        if k < 0.35: return [f"{pad}st {at}, {e};", f"{pad}{target} = lds 1 ({at});"]
        if k < 0.7: return [f"{pad}st8 {at} + {self.rng.randrange(0, 8)}, {e};", f"{pad}{target} = lds 1 ({at});"]
        if k < 0.85: return [f"{pad}st {at}, {e};", f"{pad}{target} = ld32 ({at});"]
        return [f"{pad}st {at}, {e};", f"{pad}{target} = {target} + (ld8 ({at} + {self.rng.randrange(0, 8)}));"]

    def call(self, pad, names, target, fresh):
        name, arity, kind = self.rng.choice(self.funcs)
        args = ", ".join(self.expr(names, 2) for _ in range(arity))
        if kind == "rec":  # the first argument bounds the depth
            args = f"({self.expr(names, 1)}) & {self.rng.choice([15, 63, 255])}, {self.expr(names, 1)}"
        if kind == "pair":
            p = f"s{fresh()}"
            return [f"{pad}var {{1,1}} {p} = {name}({args});", f"{pad}{target} = {p}.0 - {p}.1;"]
        if kind == "throw":
            return [f"{pad}try", f"{pad}  {target} = {name}({args})", f"{pad}catch E => {target} {{"] + \
                self.show(pad + "  ", target) + [f"{pad}  {target} = {target} ^ 1;", f"{pad}}}"]
        return [f"{pad}{target} = {name}({args});"]

    def stmt(self, vars_, depth, indent, loops, fresh, in_fn):
        pad, r = "  " * indent, self.rng.random()
        names, target = vars_ + loops, self.rng.choice(vars_)
        if depth > 0 and r < 0.18:
            out = [f"{pad}if {self.cond(names)} {{"] + self.block(vars_, depth - 1, indent + 1, loops, fresh, in_fn)
            if self.rng.random() < 0.5:
                out += [f"{pad}}} else {{"] + self.block(vars_, depth - 1, indent + 1, loops, fresh, in_fn)
            return out + [f"{pad}}}"]
        if depth > 0 and r < 0.34:
            c = f"i{fresh()}"
            out = [f"{pad}var 1 {c} = 0;", f"{pad}while {c} < {self.rng.randrange(1, 12)} {{", f"{pad}  {c} = {c} + 1;"]
            if self.rng.random() < 0.4:
                out += [f"{pad}  if {self.cond(names + [c])} {{ {self.rng.choice(['break', 'continue'])}; }}"]
            return out + self.block(vars_, depth - 1, indent + 1, loops + [c], fresh, in_fn) + [f"{pad}}}"]
        if self.funcs and r < 0.52: return self.call(pad, names, target, fresh)
        if r < 0.62 and not in_fn: return self.show(pad, self.expr(names, 2))
        if r < 0.74: return self.memory(pad, names, target)
        if self.globals and r < 0.82: return [f"{pad}{self.rng.choice(self.globals)} = {self.expr(names, 2)};"]
        if r < 0.86 and not in_fn:
            return [f"{pad}@in(0, 0, @base + 520, 8);", f"{pad}{target} = lds 1 (@base + 520);"]
        return [f"{pad}{target} = {self.expr(names, 3)};"]

    def block(self, vars_, depth, indent, loops, fresh, in_fn=False):
        out = []
        for _ in range(self.rng.randrange(1, 4)):
            out += self.stmt(vars_, depth, indent, loops, fresh, in_fn)
        return out

    def function(self, name):
        kinds = ["plain", "plain", "rec", "tail", "pair"] + (["throw"] if self.exn else [])
        kind = self.rng.choice(kinds)
        counter = iter(range(10**6))
        fresh = lambda: next(counter)
        if kind in ("rec", "tail"):
            step = self.expr(["n", "a"], 2)
            body = [f"fun 1 {name}(1 n, 1 a) {{", f"  if n == 0 {{ return a; }}"]
            if kind == "tail": body += [f"  return {name}(n - 1, {step});", "}"]
            else: body += [f"  var 1 r = {name}(n - 1, {step});", f"  return r + {self.expr(['n', 'a'], 1)};", "}"]
            self.funcs.append((name, 2, "rec"))
            return body
        arity = self.rng.randrange(1, 6)
        params = [f"p{k}" for k in range(arity)]
        shape = "{1,1}" if kind == "pair" else "1"
        body = [f"fun {shape} {name}({', '.join('1 ' + p for p in params)}) {{", f"  var 1 t = {self.expr(params, 3)};"]
        body += self.block(params + ["t"], 1, 1, [], fresh, in_fn=True)
        if kind == "throw": body += [f"  if {self.cond(params + ['t'])} {{ throw E t; }}"]
        if kind == "pair": body += [f"  return <{self.expr(params + ['t'], 2)}, {self.expr(params + ['t'], 2)}>;", "}"]
        else: body += [f"  return {self.expr(params + ['t'], 2)};", "}"]
        self.funcs.append((name, arity, kind))
        return body

    def program(self):
        lines = ["exception E : 1;"] if self.exn else []
        lines += [f"var 1 {g} = {self.lit()};" for g in self.globals] + [""]
        for k in range(self.rng.randrange(1, 5)):
            lines += self.function(f"f{k}") + [""]
        vars_ = [f"v{k}" for k in range(5)]
        counter = iter(range(10**6))
        fresh = lambda: next(counter)
        lines += ["fun 1 main() {", "  @in(0, 0, @base, 64);"]
        lines += [f"  var 1 {v} = lds 1 (@base + {8 * k});" for k, v in enumerate(vars_)]
        for _ in range(3):
            lines += self.block(vars_, 2, 1, [], fresh)
        lines += [f"  st @base + {512 + 8 * k}, {v};" for k, v in enumerate(vars_ + self.globals)]
        lines += [f"  @out(0, 0, @base + 512, {8 * len(vars_ + self.globals)});", "  return 0;", "}"]
        return "\n".join(lines) + "\n"


if __name__ == "__main__":
    seed, count, out = int(sys.argv[1]), int(sys.argv[2]), Path(sys.argv[3])
    for n in range(count):
        d = out / f"pan_{seed}_{n:03d}"
        d.mkdir(parents=True, exist_ok=True)
        (d / "source.pnk").write_text(f"// generated: seed {seed}, program {n}\n" + Gen(random.Random(seed * 1000003 + n)).program())
