#!/usr/bin/env python3
"""Check `decompile --to pancake` on Flapjack images, by running.

    check.py self-test TESTS
    check.py run FJC TESTS [--work DIR] [-j N]

TESTS holds one directory per test, each with `image.fjimg` (a Flapjack image) and
`expected.txt` (what the image does on each test input), as flapjack-flip's `tests/` does.

`run`: for each test, decompile the image (`lake exe decompile --to pancake`), compile the
Pancake text with Flapjack (FJC SOURCE.pnk prints the image; see README.md), run the new
image (`fjrun.py`) and compare the FFI events and the final status with the original's on
every test input. Step counts differ, and are reported, not compared. A test passes only if
the two agree on every input; a decompiler that gives up, text Flapjack rejects and a run
that does not end the same way are all failures.

`self-test`: run `fjrun.py` on each original image and compare with `expected.txt`, step
counts included. `expected.txt` was written by flapjack-flip's own machine (riscv-zkvm's
`step`), so this is what entitles `run` to use the fast interpreter.

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
    return sorted(t for t in os.listdir(d) if os.path.isfile(os.path.join(d, t, "image.fjimg")))


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


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("self-test"); s.add_argument("tests"); s.add_argument("-j", type=int, default=os.cpu_count())
    r = sub.add_parser("run"); r.add_argument("fjc"); r.add_argument("tests")
    r.add_argument("--work"); r.add_argument("-j", type=int, default=os.cpu_count())
    a = ap.parse_args()
    sys.exit(0 if (self_test(a) if a.cmd == "self-test" else run(a)) else 1)
