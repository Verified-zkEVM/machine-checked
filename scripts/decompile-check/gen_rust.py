#!/usr/bin/env python3
"""Random SP1 guests in Rust, for the check of `decompile --to pancake` (`README.md`).

    gen_rust.py SEED COUNT OUT

writes COUNT programs `g_SEED_NNN.rs` to OUT, the `src/bin` of a copy of `rust/`.

Each program reads its input (`guests::In`), computes with it and shows what it computes
(`guests::out`) as it goes, so that a wrong value on the way is a different run. What it
computes is chosen at random, typed, from what makes rustc emit different code:

* the integer types of every width, signed and unsigned, with casts between them: the
  32-bit instructions come from `u32` and `i32`, calls into compiler-builtins from `u128`;
* wrapping, checked and saturating arithmetic, division and remainder, shifts, rotations
  and bit counts, comparisons;
* `if`, bounded `while` and `for` loops with `break` and `continue`, nested loops left by a
  labelled `break`, and `match` on a small number, which becomes a jump table;
* functions that are not inlined, one of them recursive, with early returns;
* arrays and a vector; calls through function pointers and through trait objects;
* now and then an assertion or an index that only some inputs pass, so that some runs end
  in a panic.

A program is a function of the seed and its number, so a failure can be made again.
"""
import random, sys
from pathlib import Path

TYPES = ["u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "u128", "i128", "usize", "u32", "i32", "u64"]
BITS = {"u8": 8, "u16": 16, "u32": 32, "u64": 64, "i8": 8, "i16": 16, "i32": 32, "i64": 64, "u128": 128, "i128": 128, "usize": 64}


class Gen:
    def __init__(self, rng):
        self.rng = rng
        self.funcs = []     # (name, parameter types, result type)
        self.fresh = 0
        self.arrays = []    # (name, element type, length) in scope
        self.objs = False   # trait objects and function pointers in scope

    def name(self, p="v"):
        self.fresh += 1
        return f"{p}{self.fresh}"

    def lit(self, t):
        r, signed = self.rng, t[0] == "i"
        k = r.random()
        if k < 0.15: return f"{t}::MAX"
        if k < 0.3: return f"{t}::MIN"
        if k < 0.4 and signed: return f"(-{r.randrange(1, 100)}{t})"
        hi = (1 << (BITS[t] - (1 if signed else 0))) - 1
        return f"{r.choice([0, 1, 2, 3, 5, 7, 31, 32, 63, 64, 100, 127, r.randrange(1 << 16), r.randrange(1 << 40), hi]) & hi}{t}"

    def of_type(self, env, t):
        return [n for n, u in env if u == t]

    def expr(self, env, t, d):
        r = self.rng
        k = r.random()
        if d <= 0 or k < 0.12:
            vs = self.of_type(env, t)
            if vs and r.random() < 0.7: return r.choice(vs)
            if env and r.random() < 0.6: return f"({r.choice(env)[0]} as {t})"
            return self.lit(t)
        a = lambda: self.expr(env, t, d - 1)
        if k < 0.34:
            return f"{a()}.{r.choice(['wrapping_add', 'wrapping_sub', 'wrapping_mul', 'saturating_add', 'saturating_sub', 'max', 'min'])}({a()})"
        if k < 0.44: return f"({a()} {r.choice('^&|')} {a()})"
        if k < 0.54:
            return f"{a()}.{r.choice(['wrapping_shl', 'wrapping_shr', 'rotate_left', 'rotate_right'])}({self.expr(env, 'u32', d - 1)})"
        if k < 0.64:
            return f"{a()}.{r.choice(['checked_div', 'checked_rem', 'checked_add', 'checked_mul'])}({a()}).unwrap_or({self.lit(t)})"
        if k < 0.68: return f"{a()}.wrapping_div({a()} | 1)"
        if k < 0.72: return f"{a()}.wrapping_pow({self.expr(env, 'u32', d - 1)} % 6)"
        if k < 0.78:
            return r.choice([f"!{a()}", f"{a()}.wrapping_neg()", f"{a()}.swap_bytes()", f"{a()}.reverse_bits()",
                             f"({a()}.count_ones() as {t})", f"({a()}.leading_zeros() as {t})", f"({a()}.trailing_zeros() as {t})"])
        if k < 0.86: return f"({self.expr(env, r.choice(TYPES), d - 1)} as {t})"
        if k < 0.91: return f"(if {self.cond(env, d - 1)} {{ {a()} }} else {{ {a()} }})"
        if k < 0.95 and self.funcs:
            f, ps, rt = r.choice(self.funcs)
            return f"({f}({', '.join(self.expr(env, p, d - 1) for p in ps)}) as {t})"
        if k < 0.98 and self.arrays:
            n, et, ln = r.choice(self.arrays)
            # now and then an index that some values do not pass
            return f"({n}[({self.expr(env, 'usize', d - 1)}) % {ln + (1 if r.random() < 0.04 else 0)}] as {t})"
        if self.objs:
            x = self.expr(env, "u64", d - 1)
            if r.random() < 0.5: return f"(objs[({self.expr(env, 'usize', d - 1)}) % objs.len()].go({x}) as {t})"
            return f"(FNS[({self.expr(env, 'usize', d - 1)}) % FNS.len()]({x}) as {t})"
        return self.lit(t)

    def cond(self, env, d):
        r = self.rng
        t = r.choice(TYPES)
        c = f"{self.expr(env, t, d)} {r.choice(['<', '<=', '>', '>=', '==', '!='])} {self.expr(env, t, d)}"
        k = r.random()
        if k < 0.15 and d > 0: return f"({c}) && ({self.cond(env, d - 1)})"
        if k < 0.3 and d > 0: return f"({c}) || ({self.cond(env, d - 1)})"
        return c

    def show(self, env):
        n, t = self.rng.choice(env)
        return f"out128({n} as u128);" if BITS[t] == 128 else f"out({n} as u64);"

    def stmt(self, env, d, pad, loops, ret):
        """Statements, and the variables they leave in scope. `loops` are the labels of the
        loops around, `ret` the result type of the function around (`None` in `main`)."""
        r = self.rng
        k = r.random()
        t = r.choice(TYPES)
        block = lambda e, l=None: self.block(e, d - 1, pad + "    ", loops if l is None else l, ret)
        if k < 0.2 or not env:
            n = self.name()
            return [f"{pad}let mut {n}: {t} = {self.expr(env, t, 3)};"], [(n, t)]
        n, t = r.choice(env)
        if k < 0.4: return [f"{pad}{n} = {self.expr(env, t, 3)};"], []
        if k < 0.46: return [f"{pad}{n} {r.choice(['^=', '|=', '&='])} {self.expr(env, t, 2)};"], []
        if k < 0.56 and d > 0:
            out = [f"{pad}if {self.cond(env, 2)} {{"] + block(env)
            if r.random() < 0.6: out += [f"{pad}}} else {{"] + block(env)
            return out + [f"{pad}}}"], []
        if k < 0.63 and d > 0:
            c = self.name("c")
            return ([f"{pad}let mut {c} = 0u32;", f"{pad}while {c} < {r.randrange(1, 12)} && ({self.cond(env, 1)}) {{", f"{pad}    {c} += 1;"]
                    + block(env + [(c, "u32")], loops + [None]) + [f"{pad}}}"]), []
        if k < 0.7 and d > 0:
            i = self.name("k")
            return ([f"{pad}for mut {i} in 0..({self.expr(env, 'usize', 1)}) % {r.randrange(2, 10)} {{"]
                    + block(env + [(i, "usize")], loops + [None]) + [f"{pad}}}"]), []
        if k < 0.75 and d > 0:
            l, i, j = self.name("'l"), self.name("k"), self.name("k")
            return ([f"{pad}{l}: for mut {i} in 0..{r.randrange(2, 7)}usize {{", f"{pad}    for mut {j} in 0..{r.randrange(2, 7)}usize {{"]
                    + self.block(env + [(i, "usize"), (j, "usize")], d - 1, pad + "        ", loops + [l, None], ret)
                    + [f"{pad}    }}", f"{pad}    {self.show(env)}", f"{pad}}}"]), []
        if k < 0.82 and d > 0:
            arms = r.randrange(3, 10)
            out = [f"{pad}match ({self.expr(env, 'u8', 2)}) % {arms} {{"]
            for a in range(arms - 1):
                out += [f"{pad}    {a} => {{"] + self.block(env, d - 1, pad + "        ", loops, ret) + [f"{pad}    }}"]
            return out + [f"{pad}    _ => {{"] + self.block(env, d - 1, pad + "        ", loops, ret) + [f"{pad}    }}", f"{pad}}}"], []
        if k < 0.86 and loops:
            l = r.choice(loops)
            word = r.choice(["break", "continue"])
            return [f"{pad}if {self.cond(env, 1)} {{ {word}{' ' + l if l else ''}; }}"], []
        if k < 0.9 and self.arrays:
            a, et, ln = r.choice(self.arrays)
            return [f"{pad}{a}[({self.expr(env, 'usize', 2)}) % {ln}] = {self.expr(env, et, 2)};"], []
        if k < 0.93:
            return r.choice([[f"{pad}vs.push({self.expr(env, 'u64', 2)});"],
                             [f"{pad}if let Some(x) = vs.pop() {{ {n} = x as {t}; }}"],
                             [f"{pad}vs.sort();", f"{pad}out(vs.iter().fold(0u64, |h, &x| h.wrapping_mul(31).wrapping_add(x)));"]]), []
        if k < 0.95 and ret: return [f"{pad}if {self.cond(env, 1)} {{ return {self.expr(env, ret, 2)}; }}"], []
        if k < 0.96 and not ret: return [f"{pad}assert!({self.cond(env, 1)}, \"an assertion some inputs fail\");"], []
        return [f"{pad}{self.show(env)}"], []

    def block(self, env, d, pad, loops, ret):
        out, env = [], list(env)
        for _ in range(self.rng.randrange(1, 4)):
            ls, new = self.stmt(env, d, pad, loops, ret)
            out += ls
            env += new
        return out

    def function(self, k):
        r = self.rng
        name = f"f{k}"
        ps = [r.choice(TYPES) for _ in range(r.randrange(1, 5))]
        rt = r.choice(TYPES)
        rec = r.random() < 0.25
        env = [(f"p{i}", p) for i, p in enumerate(ps)]
        sig = ", ".join([f"mut {n}: {t}" for n, t in env] + ["vs: &mut Vec<u64>"] + (["d: u32"] if rec else []))
        out = ["#[inline(never)]", f"fn {name}({sig}) -> {rt} {{"]
        if rec:
            args = ", ".join(self.expr(env, p, 2) for p in ps)
            out += [f"    if d == 0 {{ return {self.expr(env, rt, 2)}; }}",
                    f"    let mut r0: {rt} = {name}({args}, vs, d - 1);"]
            env.append(("r0", rt))
        # calls from an expression cannot pass the vector along, so only the body sees it
        out += self.block(env, 2, "    ", [], rt) + self.block(env, 2, "    ", [], rt)
        out += [f"    {self.expr(env, rt, 3)}", "}", ""]
        return name, ps, rt, rec, out

    def program(self):
        r = self.rng
        lines = ["#![no_main]", "#![cfg_attr(not(target_os = \"zkvm\"), no_std)]", "#![allow(unused, arithmetic_overflow, unconditional_panic)]", "guests::entry!(main);", "use guests::*;", "",
                 "trait Go { fn go(&self, x: u64) -> u64; }"]
        kinds = []
        for k in range(r.randrange(2, 6)):
            body = self.expr([("x", "u64"), ("s", "u64")], "u64", 3).replace("s", "self.0") if False else self.expr([("x", "u64")], "u64", 3)
            lines += [f"struct D{k}(u64);", f"impl Go for D{k} {{ fn go(&self, x: u64) -> u64 {{ ({body}) ^ self.0 }} }}"]
            kinds.append(f"D{k}")
        fns = []
        for k in range(r.randrange(2, 6)):
            lines += ["#[inline(never)]", f"fn h{k}(x: u64) -> u64 {{ {self.expr([('x', 'u64')], 'u64', 3)} }}"]
            fns.append(f"h{k}")
        lines += [f"static FNS: [fn(u64) -> u64; {len(fns)}] = [{', '.join(fns)}];", ""]
        # functions: called from `main` with the vector, so their calls are statements there
        wrapped = []
        for k in range(r.randrange(2, 6)):
            name, ps, rt, rec, out = self.function(k)
            lines += out
            wrapped.append((name, ps, rt, rec))
        lines += ["pub fn main() {", "    let mut i = In::new();", "    let mut vs: Vec<u64> = Vec::new();",
                  f"    let objs: Vec<Box<dyn Go>> = vec![{', '.join(f'Box::new({k}(i.u64()))' for k in kinds)}];"]
        self.objs = True
        env = []
        for _ in range(r.randrange(3, 8)):
            n, t = self.name(), r.choice(TYPES)
            src = {8: "i.u8()", 16: "i.u16()", 32: "i.u32()", 64: "i.u64()", 128: "i.u128()"}[BITS[t]]
            lines.append(f"    let mut {n}: {t} = {src} as {t};")
            env.append((n, t))
        for _ in range(r.randrange(1, 3)):
            n, t, ln = self.name("a"), r.choice(TYPES), r.choice([4, 8, 16, 33])
            lines.append(f"    let mut {n}: [{t}; {ln}] = [{self.lit(t)}; {ln}];")
            self.arrays.append((n, t, ln))
        for _ in range(r.randrange(6, 14)):
            if wrapped and r.random() < 0.35:
                name, ps, rt, rec = r.choice(wrapped)
                args = [self.expr(env, p, 2) for p in ps] + ["&mut vs"] + ([f"({self.expr(env, 'u32', 1)}) % 7"] if rec else [])
                v = self.name()
                lines.append(f"    let mut {v}: {rt} = {name}({', '.join(args)});")
                env.append((v, rt))
            else:
                ls, new = self.stmt(env, 3, "    ", [], None)
                lines += ls
                env += new
            if r.random() < 0.5: lines.append(f"    {self.show(env)}")
        for n, t in env:
            lines.append(f"    out128({n} as u128);" if BITS[t] == 128 else f"    out({n} as u64);")
        for a, _, _ in self.arrays:
            lines.append(f"    for x in {a}.iter() {{ out128(*x as u128); }}")
        lines += ["    out(vs.len() as u64);", "}"]
        return "\n".join(lines) + "\n"


if __name__ == "__main__":
    seed, count, out = int(sys.argv[1]), int(sys.argv[2]), Path(sys.argv[3])
    for n in range(count):
        text = Gen(random.Random(seed * 1000003 + n)).program()
        (out / f"g_{seed}_{n:03d}.rs").write_text(f"// generated: seed {seed}, program {n}\n" + text)
