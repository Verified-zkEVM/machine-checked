#!/usr/bin/env python3
"""Check `decompile --to pancake` on Flapjack images, by running.

    check.py build FJC TESTS
    check.py reference FLIP_CHECK TESTS
    check.py self-test TESTS
    check.py run FJC TESTS [--work DIR] [-j N]
    check.py mutants FJC TESTS [--work DIR] [-j N]

TESTS holds one directory per test, each with `image.fjimg` (a Flapjack image) and
`expected.txt` (what the image does on each test input), as flapjack-flip's `tests/` does.

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
what the tests see, not a pass or fail.

Exit status 0 only if everything passes.
"""
import argparse, os, re, subprocess, sys, tempfile
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
DECOMPILE = os.path.join(ROOT, ".lake", "build", "bin", "decompile")
FJRUN = [sys.executable, os.path.join(HERE, "fjrun.py")]
STEPS = re.compile(r"^\((\d+) steps\)$", re.M)


def tests(d):
    """The tests of a directory: those with an image and what it is expected to do."""
    return sorted(t for t in os.listdir(d)
                  if all(os.path.isfile(os.path.join(d, t, f)) for f in ("image.fjimg", "expected.txt")))


def sh(cmd, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, **kw)


def self_test(args):
    def one(t):
        got = sh(FJRUN + [os.path.join(args.tests, t, "image.fjimg")]).stdout
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
        got = sh(FJRUN + [img]).stdout
        if not all("halted: success" in r and "\n@" in r for r in got.split("\n\n")):
            return t, "does not end normally with FFI calls on every input"
        open(exp, "w").write(got)
        return t, None
    names = sorted(t for t in os.listdir(args.tests)
                   if any(os.path.isfile(os.path.join(args.tests, t, f)) for f in ("source.pnk", "image.fjimg")))
    with ThreadPoolExecutor(args.j) as ex:
        res = list(ex.map(one, names))
    for t, err in res:
        if err:
            print(f"NOT A TEST {t}: {err}")
    print(f"build: {sum(e is None for _, e in res)}/{len(res)} programs are tests")
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


def run(args):
    work = args.work or tempfile.mkdtemp(prefix="decompile-check-")

    def one(t):
        d = os.path.join(work, t)
        os.makedirs(d, exist_ok=True)
        src, img = os.path.join(d, "source.pnk"), os.path.join(d, "image.fjimg")
        expected = open(os.path.join(args.tests, t, "expected.txt")).read()
        p = sh([DECOMPILE, "--to", "pancake", os.path.join(args.tests, t, "image.fjimg"), src])
        if p.returncode:
            return t, "decompiler gave up: " + p.stderr.strip()[:200], 0, 0
        p = sh([args.fjc, src])
        if p.returncode:
            return t, "Flapjack rejects the text: " + p.stderr.strip()[:200], 0, 0
        open(img, "w").write(p.stdout)
        got = sh(FJRUN + [img]).stdout
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


ASSIGN = re.compile(r"^(\s+)(x\d+ = |st8? .*?, )(.*);$")


def mutants(args):
    import random
    work = args.work or tempfile.mkdtemp(prefix="decompile-mutants-")

    def one(t):
        d = os.path.join(work, t)
        os.makedirs(d, exist_ok=True)
        src = os.path.join(d, "source.pnk")
        if sh([DECOMPILE, "--to", "pancake", os.path.join(args.tests, t, "image.fjimg"), src]).returncode:
            return None
        lines = open(src).read().split("\n")
        rng = random.Random(t)
        sites = [i for i, l in enumerate(lines) if ASSIGN.match(l)]
        if not sites:
            return None
        i = rng.choice(sites)
        lines[i] = ASSIGN.sub(r"\1\2(\3 ^ 1);", lines[i])
        mut = os.path.join(d, "mutant.pnk")
        open(mut, "w").write("\n".join(lines))
        p = sh([args.fjc, mut])
        if p.returncode:
            return True
        img = os.path.join(d, "mutant.fjimg")
        open(img, "w").write(p.stdout)
        expected = open(os.path.join(args.tests, t, "expected.txt")).read()
        return STEPS.sub("", sh(FJRUN + [img]).stdout) != STEPS.sub("", expected)

    with ThreadPoolExecutor(args.j) as ex:
        res = [r for r in ex.map(one, tests(args.tests)) if r is not None]
    print(f"mutants: {sum(res)}/{len(res)} one-bit changes are caught")
    return True


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("self-test"); s.add_argument("tests"); s.add_argument("-j", type=int, default=os.cpu_count())
    r = sub.add_parser("run"); r.add_argument("fjc"); r.add_argument("tests")
    r.add_argument("--work"); r.add_argument("-j", type=int, default=os.cpu_count())
    b = sub.add_parser("build"); b.add_argument("fjc"); b.add_argument("tests"); b.add_argument("-j", type=int, default=os.cpu_count())
    f = sub.add_parser("reference"); f.add_argument("flip_check"); f.add_argument("tests"); f.add_argument("-j", type=int, default=os.cpu_count())
    m = sub.add_parser("mutants"); m.add_argument("fjc"); m.add_argument("tests")
    m.add_argument("--work"); m.add_argument("-j", type=int, default=os.cpu_count())
    a = ap.parse_args()
    sys.exit(0 if {"self-test": self_test, "run": run, "build": build, "reference": reference, "mutants": mutants}[a.cmd](a) else 1)
