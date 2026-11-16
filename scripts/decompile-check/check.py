#!/usr/bin/env python3
"""Check `decompile --to pancake` on Flapjack images and on guests, by running.

    check.py build FJC TESTS
    check.py rust WORK TESTS [--seed N] [--count N] [--target sp1|aarch64|x86-64]
    check.py reference FLIP_CHECK TESTS
    check.py sp1-reference SP1REF TESTS
    check.py self-test TESTS
    check.py run FJC TESTS [--work DIR] [-j N]
    check.py mutants FJC TESTS [--work DIR] [-j N]
    check.py limits [--write]

TESTS holds one directory per test, each with `image.fjimg` (a Flapjack image) or
`guest.elf` (a guest: an SP1 guest, or a program without an operating system for AArch64
or x86-64), and `expected.txt` (what it does on each test input), as flapjack-flip's
`tests/` does. For a guest read "guest" for "image" below: its `expected.txt` is written by
`build` from `sp1run.py`, or from `barerun.py` (Unicorn) for a bare one.

`rust`: build the guests of `rust/`, with COUNT generated ones, for a target, into TESTS.
`sp1-reference`: compare the `expected.txt` of SP1 guests with SP1's own executor.
`limits`: compare the instruction table of each `LIMITS.md` with the generated one.

The decompiler is `.lake/build/bin/decompile`, or the file the variable `DECOMPILE` names.

`run`: for each test, decompile the image (`lake exe decompile --to pancake`), compile the
Pancake text with Flapjack (FJC SOURCE.pnk prints the image; see README.md), run the new
image (`fjrun.py`) and compare the FFI events and the final status with the original's on
every test input. Step counts differ, and are reported, not compared. A test passes only if
the two agree on every input; a decompiler that gives up, text Flapjack rejects and a run
that does not end the same way are all failures.

`build`: make tests from programs. For each `TESTS/*/source.pnk`, compile it (FJC) to
`image.fjimg`, and write what the image does (`fjrun.py`) to `expected.txt`; a directory
with an image and no source (hand-assembled code) keeps its image. A program is only a test
if it ends normally and makes FFI calls on every input; any other is reported and gets no
`expected.txt`.

`reference`: run each image on flapjack-flip's machine (`flip-check run IMAGE`) and compare
with `expected.txt`, step counts included. This is what makes an `expected.txt` that
`build` wrote, or that came with hand-assembled code, the reference machine's word.

`self-test`: run `fjrun.py` on each original image and compare with `expected.txt`, step
counts included. `expected.txt` was written by flapjack-flip's own machine (riscv-zkvm's
`step`), so this is what entitles `run` to use the fast interpreter.

`mutants`: how sharp `run` is. For each test, decompile, then flip the low bit of the value
one statement of the Pancake text assigns to a register or stores, compile and run as `run`
does, and count the changed programs that `run` would have failed. A change in code the
test never reaches, or to a value nothing reads, goes unnoticed, so the count is a floor on
what the tests see, not a pass or fail. For a guest the statement is one of the program's,
not of the functions that write its memory image, and it is marked
(`sp1run.py`), so the count is also given among the changes some input reaches: most of a
guest is its runtime, which one program runs little of.

Exit status 0 only if everything passes.
"""
import argparse, os, re, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
DECOMPILE = os.environ.get("DECOMPILE") or os.path.join(ROOT, ".lake", "build", "bin", "decompile")
FJRUN = [sys.executable, os.path.join(HERE, "fjrun.py")]
SP1RUN = [sys.executable, os.path.join(HERE, "sp1run.py")]
BARERUN = [sys.executable, os.path.join(HERE, "barerun.py")]
# the bare targets of the Rust guests, by the name `rust --target` takes
BARE = {"aarch64": "aarch64-unknown-none-softfloat", "x86-64": "x86_64-unknown-none"}
STEPS = re.compile(r"^\((\d+) steps\)$", re.M)


def original(d):
    """The binary of a test: a Flapjack image, or an SP1 guest."""
    for f in ("image.fjimg", "guest.elf"):
        if os.path.isfile(os.path.join(d, f)):
            return os.path.join(d, f)


def guest_runner(elf):
    """The runner for a guest: ours for an SP1 guest (RISC-V), Unicorn for a bare one."""
    return SP1RUN if open(elf, "rb").read(0x14)[0x12:] == bytes([243, 0]) else BARERUN


def runner(d):
    """The runner for a test's binary, and for what it decompiles and recompiles to."""
    return SP1RUN if original(d).endswith(".elf") else FJRUN


def tests(d):
    """The tests of a directory: those with a binary and what it is expected to do."""
    return sorted(t for t in os.listdir(d)
                  if original(os.path.join(d, t)) and os.path.isfile(os.path.join(d, t, "expected.txt")))


def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def self_test(args):
    def one(t):
        d = os.path.join(args.tests, t)
        got = sh(runner(d) + [original(d)]).stdout
        return t, got == open(os.path.join(args.tests, t, "expected.txt")).read()
    with ThreadPoolExecutor(args.j) as ex:
        res = list(ex.map(one, tests(args.tests)))
    for t, ok in res:
        if not ok:
            print(f"DIFFERS {t}")
    good = sum(ok for _, ok in res)
    print(f"self-test: fjrun.py agrees with expected.txt on {good}/{len(res)} images")
    return good == len(res)


def build(args):
    def one(t):
        d = os.path.join(args.tests, t)
        img, exp = os.path.join(d, "image.fjimg"), os.path.join(d, "expected.txt")
        if os.path.isfile(exp):
            os.remove(exp)
        if os.path.isfile(os.path.join(d, "source.pnk")):
            p = sh([args.fjc, os.path.join(d, "source.pnk")])
            if p.returncode:
                return t, "Flapjack rejects it: " + p.stderr.strip()[:200]
            open(img, "w").write(p.stdout)
        if os.path.isfile(os.path.join(d, "guest.elf")):
            got = sh(guest_runner(os.path.join(d, "guest.elf")) + [os.path.join(d, "guest.elf")]).stdout
            if not all("halted: exit" in r for r in got.split("\n\n")):
                return t, "does not halt on every input"
        else:
            got = sh(FJRUN + [img]).stdout
            if not all("halted: success" in r and "\n@" in r for r in got.split("\n\n")):
                return t, "does not end normally with FFI calls on every input"
        open(exp, "w").write(got)
        return t, None
    names = sorted(t for t in os.listdir(args.tests)
                   if any(os.path.isfile(os.path.join(args.tests, t, f)) for f in ("source.pnk", "image.fjimg", "guest.elf")))
    with ThreadPoolExecutor(args.j) as ex:
        res = list(ex.map(one, names))
    for t, err in res:
        if err:
            print(f"NOT A TEST {t}: {err}")
    print(f"build: {sum(e is None for _, e in res)}/{len(res)} programs are tests")
    return True


def rust(args):
    """Build the guests of `rust/` in WORK, with COUNT generated ones, into TESTS."""
    import shutil
    src = os.path.join(args.work, "rust")
    shutil.copytree(os.path.join(HERE, "rust"), src, dirs_exist_ok=True)
    if args.count:
        p = sh([sys.executable, os.path.join(HERE, "gen_rust.py"), str(args.seed), str(args.count),
                os.path.join(src, "src", "bin")])
        if p.returncode:
            print(p.stderr)
            return False
    names = sorted(f[:-3] for f in os.listdir(os.path.join(src, "src", "bin")) if f.endswith(".rs"))
    if args.target == "sp1":
        p = sh([os.path.expanduser("~/.sp1/bin/cargo-prove"), "prove", "build"], cwd=src)
        out = os.path.join(src, "target", "elf-compilation", "riscv64im-succinct-zkvm-elf", "release")
    else:
        # a bare program: not the guests that say they are for SP1 only
        names = [n for n in names
                 if not open(os.path.join(src, "src", "bin", n + ".rs")).readline().startswith("// SP1 only")]
        triple = BARE[args.target]
        p = sh(["cargo", "build", "--release", "--target", triple] + [a for n in names for a in ("--bin", n)],
               cwd=src, env=dict(os.environ, RUSTFLAGS="-C relocation-model=static"))
        out = os.path.join(src, "target", triple, "release")
    if p.returncode or not os.path.isdir(out):
        print((p.stdout + p.stderr)[-3000:])
        return False
    for n in names:
        os.makedirs(os.path.join(args.tests, n), exist_ok=True)
        shutil.copy(os.path.join(out, n), os.path.join(args.tests, n, "guest.elf"))
    print(f"rust: {len(names)} guests built into {args.tests}")
    return True


def reference(args):
    def one(t):
        got = sh([args.flip_check, "run", os.path.join(args.tests, t, "image.fjimg")]).stdout
        return t, got == open(os.path.join(args.tests, t, "expected.txt")).read()
    with ThreadPoolExecutor(args.j) as ex:
        res = list(ex.map(one, tests(args.tests)))
    for t, ok in res:
        if not ok:
            print(f"DIFFERS {t}")
    good = sum(ok for _, ok in res)
    print(f"reference: flapjack-flip's machine agrees with expected.txt on {good}/{len(res)} images")
    return good == len(res)


def sp1_reference(args):
    """Compare `expected.txt` of each guest with SP1's own executor (`sp1ref`): the public
    values (the bytes written to file 13), the exit code and the number of instructions."""
    names = [t for t in tests(args.tests) if original(os.path.join(args.tests, t)).endswith(".elf")]

    def ours(t):
        out = []
        for r in open(os.path.join(args.tests, t, "expected.txt")).read().strip().split("\n\n"):
            public = "".join(l.split()[4] for l in r.split("\n") if l.startswith("write d ") and len(l.split()) > 4)
            out.append(f"public={public} exit={re.search(r'halted: exit (\d+)', r).group(1)} "
                       f"instructions={STEPS.search(r).group(1)}")
        return out

    def theirs(batch):
        p = sh([args.sp1ref] + [os.path.join(args.tests, t, "guest.elf") for t in batch])
        runs = [l for l in p.stdout.split("\n") if l.startswith(("public=", "error:"))]
        return [runs[5 * k:5 * k + 5] for k in range(len(batch))]

    batches = [names[k:k + 8] for k in range(0, len(names), 8)]
    with ThreadPoolExecutor(max(1, args.j // 8)) as ex:
        got = [g for gs in ex.map(theirs, batches) for g in gs]
    good = 0
    for t, g in zip(names, got):
        if g == ours(t):
            good += 1
        else:
            print(f"DIFFERS {t}")
    print(f"sp1-reference: SP1's executor agrees with expected.txt on {good}/{len(names)} guests")
    return good == len(names)


def run(args):
    work = args.work or tempfile.mkdtemp(prefix="decompile-check-")

    def one(t):
        d = os.path.join(work, t)
        os.makedirs(d, exist_ok=True)
        src, img = os.path.join(d, "source.pnk"), os.path.join(d, "image.fjimg")
        expected = open(os.path.join(args.tests, t, "expected.txt")).read()
        p = sh([DECOMPILE, "--to", "pancake", original(os.path.join(args.tests, t)), src])
        if p.returncode:
            return t, "decompiler gave up: " + p.stderr.strip()[:200], 0, 0
        p = sh([args.fjc, src])
        if p.returncode:
            return t, "Flapjack rejects the text: " + p.stderr.strip()[:200], 0, 0
        open(img, "w").write(p.stdout)
        got = sh(runner(os.path.join(args.tests, t)) + [img]).stdout
        open(os.path.join(d, "got.txt"), "w").write(got)
        a, b = sum(map(int, STEPS.findall(expected))), sum(map(int, STEPS.findall(got)))
        if STEPS.sub("", got) != STEPS.sub("", expected):
            return t, "behaviour differs", a, b
        return t, None, a, b

    with ThreadPoolExecutor(args.j) as ex:
        res = list(ex.map(one, tests(args.tests)))
    for t, err, _, _ in res:
        if err:
            print(f"FAIL {t}: {err}")
    good = [r for r in res if r[1] is None]
    ratio = sum(r[3] for r in good) / max(1, sum(r[2] for r in good))
    print(f"{len(good)}/{len(res)} pass; the recompiled images take {ratio:.1f}x the steps; work in {work}")
    return len(good) == len(res)


GLOBAL = re.compile(r"^var 1 (\w+) = 0;$")


def assign(text):
    """What matches a statement of a decompiled program that writes a register or stores:
    the registers are its global variables, up to the lift's own (`lt0` and after)."""
    regs = []
    for l in text.split("\n"):
        m = GLOBAL.match(l)
        if m and m.group(1) == "lt0":
            break
        if m:
            regs.append(m.group(1))
    return re.compile(r"^(\s+)((?:%s) = |st(?:8|32)? .*?, )(.*);$" % "|".join(regs))


def mutants(args):
    import random
    work = args.work or tempfile.mkdtemp(prefix="decompile-mutants-")

    def one(t):
        """Whether the change to test `t` is reached (`None` if that is not known) and
        whether it is caught."""
        d = os.path.join(work, t)
        os.makedirs(d, exist_ok=True)
        src = os.path.join(d, "source.pnk")
        guest = original(os.path.join(args.tests, t)).endswith(".elf")
        if sh([DECOMPILE, "--to", "pancake", original(os.path.join(args.tests, t)), src]).returncode:
            return None
        lines = open(src).read().split("\n")
        ASSIGN = assign("\n".join(lines))
        rng = random.Random(t)
        # not in the functions that install a guest's memory: they are data, not translation
        fn, sites = "", []
        for i, l in enumerate(lines):
            if l.startswith("fun "):
                fn = l.split()[2]
            elif ASSIGN.match(l) and not fn.startswith("l_init"):
                sites.append(i)
        if not sites:
            return None
        i = rng.choice(sites)
        lines[i] = ASSIGN.sub(r"\1\2(\3 ^ 1);", lines[i])
        changed = lines[i].strip()
        if guest:
            lines.insert(i, ASSIGN.match(lines[i]).group(1) + "@mark(0, 0, 0, 0);")
        mut = os.path.join(d, "mutant.pnk")
        open(mut, "w").write("\n".join(lines))
        p = sh([args.fjc, mut])
        if p.returncode:
            return None, True
        img = os.path.join(d, "mutant.fjimg")
        open(img, "w").write(p.stdout)
        expected = open(os.path.join(args.tests, t, "expected.txt")).read()
        # a changed program that no longer ends is cut off at fifty times the longest run
        fuel = [str(50 * max(map(int, STEPS.findall(expected))) + 1_000_000)] if guest else []
        got = sh(runner(os.path.join(args.tests, t)) + [img] + fuel).stdout
        plain = got.replace("\n(marked)", "")
        reached, caught = ("(marked)" in got) if guest else None, STEPS.sub("", plain) != STEPS.sub("", expected)
        # for whoever traces a change that was not caught
        open(os.path.join(d, "result.txt"), "w").write(f"reached: {reached}\ncaught: {caught}\nchanged: {changed}\n")
        return reached, caught

    with ThreadPoolExecutor(args.j) as ex:
        res = [r for r in ex.map(one, tests(args.tests)) if r is not None]
    caught = sum(c for _, c in res)
    print(f"mutants: {caught}/{len(res)} one-bit changes are caught")
    known = [(r, c) for r, c in res if r is not None]
    if known:
        reached = [c for r, c in known if r]
        print(f"mutants: {len(reached)}/{len(known)} of the changes are reached by some input, "
              f"and {sum(reached)}/{len(reached)} of those are caught; "
              f"{sum(c for r, c in known if not r)} unreached ones are caught")
    return True


LIMITS = {"riscv": "RiscV", "aarch64": "ARM", "x86-64": "X86"}
TABLE = re.compile(r"(<!-- table: generated, do not edit -->\n).*?(<!-- end of table -->)", re.S)


def limits(args):
    """Compare the instruction table of each `LIMITS.md` with the one `decompile --table`
    makes from `run/ISA.txt`, the kinds of instruction the check runs; `--write` puts the
    generated table in."""
    ok = True
    for isa, d in LIMITS.items():
        path = os.path.join(ROOT, "MachineChecked", d, "LIMITS.md")
        p = sh([DECOMPILE, "--table", isa, os.path.join(HERE, "run", isa + ".txt")])
        if p.returncode:
            print(f"limits: {isa}: {p.stderr.strip()}")
            ok = False
            continue
        text = open(path).read()
        new = TABLE.sub(lambda m: m.group(1) + p.stdout + m.group(2), text)
        if TABLE.search(text) is None:
            print(f"limits: {path} has no table")
            ok = False
        elif new != text and args.write:
            open(path, "w").write(new)
            print(f"limits: wrote the table of {path}")
        elif new != text:
            print(f"limits: the table of {path} is not the generated one")
            ok = False
    if ok:
        print("limits: the tables are the generated ones")
    return ok


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("self-test"); s.add_argument("tests"); s.add_argument("-j", type=int, default=os.cpu_count())
    r = sub.add_parser("run"); r.add_argument("fjc"); r.add_argument("tests")
    r.add_argument("--work"); r.add_argument("-j", type=int, default=os.cpu_count())
    b = sub.add_parser("build"); b.add_argument("fjc"); b.add_argument("tests"); b.add_argument("-j", type=int, default=os.cpu_count())
    f = sub.add_parser("reference"); f.add_argument("flip_check"); f.add_argument("tests"); f.add_argument("-j", type=int, default=os.cpu_count())
    q = sub.add_parser("sp1-reference"); q.add_argument("sp1ref"); q.add_argument("tests"); q.add_argument("-j", type=int, default=os.cpu_count())
    g = sub.add_parser("rust"); g.add_argument("work"); g.add_argument("tests")
    g.add_argument("--seed", type=int, default=1); g.add_argument("--count", type=int, default=0)
    g.add_argument("--target", choices=["sp1", *BARE], default="sp1")
    m = sub.add_parser("mutants"); m.add_argument("fjc"); m.add_argument("tests")
    m.add_argument("--work"); m.add_argument("-j", type=int, default=os.cpu_count())
    l = sub.add_parser("limits"); l.add_argument("--write", action="store_true")
    a = ap.parse_args()
    sys.exit(0 if {"self-test": self_test, "run": run, "build": build, "reference": reference, "mutants": mutants, "rust": rust, "sp1-reference": sp1_reference, "limits": limits}[a.cmd](a) else 1)
