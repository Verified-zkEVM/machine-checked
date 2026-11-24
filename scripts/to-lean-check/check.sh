#!/bin/bash
# check.sh: `decompile --to lean` end to end, on the small ELF of `Tools/Test/Elf.lean`.
#
# Writes the ELF, runs the three routes (`--proved`, the lift of whole programs, `--pancake`),
# and builds every module they write, so that the kernel checks each theorem in them. Then
# changes one number in each route's input or output and checks that the module no longer
# builds: a word (`Words.lean`), a byte (`Code.lean`), and lift 2's notes (`Pancake.lean`).
# Then the function list: an unsized `_start` that is the last symbol of `.text` is taken,
# a local label without a size inside a function is named but not left out, a label past
# `.text` is neither, and a function past `.text` is left out.
# Last, on the ELF with `addw` (a 32-bit operation the `--proved` lift does not take) in
# `_start`, it checks that the root module of `--proved` names the function left out, and that
# `--all` refuses it and the function past `.text`, and writes nothing, but takes the ELF whose
# local label is only a name. (The main ELF's `_start` ends in `unimp`, which is lifted as a
# trap: `--all` takes it.)
#
# Run from anywhere, after `lake build decompile Tools`. CI runs it.
set -euo pipefail
REPO="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO"
OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT

LP="$(lake env printenv LEAN_PATH)"
export LEAN_PATH="$LP:$OUT/build"

# Build module `$1` (a path under $OUT, without `.lean`); fail on an error or a warning.
build() {
  mkdir -p "$(dirname "$OUT/build/$1")"
  if ! lean --tstack=400000 --root="$OUT" -o "$OUT/build/$1.olean" "$OUT/$1.lean" > "$OUT/log" 2>&1; then
    cat "$OUT/log"; echo "to-lean-check: $1 does not build"; exit 1
  fi
  if grep -q 'warning' "$OUT/log"; then
    cat "$OUT/log"; echo "to-lean-check: $1 builds with warnings"; exit 1
  fi
}

# Module `$1`, with the first `$2` in it replaced by `$3`, must not build, and for the kernel's
# refusal, not some other error.
refused() {
  local m=$1
  cp "$OUT/$m.lean" "$OUT/$m.orig"
  python3 -c 'import sys; p, a, b = sys.argv[1:]; s = open(p).read(); assert a in s, a; open(p, "w").write(s.replace(a, b, 1))' "$OUT/$m.lean" "$2" "$3"
  if lean --tstack=400000 --root="$OUT" "$OUT/$m.lean" > "$OUT/log" 2>&1; then
    echo "to-lean-check: $m builds with $2 changed to $3"; exit 1
  fi
  if ! grep -q '(kernel)' "$OUT/log"; then
    cat "$OUT/log"; echo "to-lean-check: $m with $2 changed fails, but not in the kernel"; exit 1
  fi
  mv "$OUT/$m.orig" "$OUT/$m.lean"
  echo "  refused: $m with $2 changed to $3"
}

lake env lean --run scripts/to-lean-check/WriteElf.lean "$OUT/t.elf"
lake exe decompile --to lean --proved --all "$OUT/t.elf" "$OUT" P
lake exe decompile --to lean "$OUT/t.elf" "$OUT" W
lake exe decompile --to lean --pancake "$OUT/t.elf" "$OUT" K

build P/Words
for f in "$OUT"/P/F*.lean; do build "P/$(basename "$f" .lean)"; done
build P
build W/Code
for f in "$OUT"/W/F*.lean; do build "W/$(basename "$f" .lean)"; done
build W
build K/Code
build K/Pancake
build K
echo "to-lean-check: every module of the three routes builds"

refused P/Words '[5244179,' '[5244180,'
refused W/Code '[19, 5, 80,' '[19, 5, 81,'
refused K/Pancake '"f_main, after label 1:' '"f_main, after label 2:'
echo "to-lean-check: a changed word, byte or note is refused"

# Decompile the ELF `WriteElf $1` writes, as namespace `$2`; what it prints must contain each
# of the lines after.
listed() {
  local flag=$1 ns=$2; shift 2
  lake env lean --run scripts/to-lean-check/WriteElf.lean "$flag" "$OUT/$ns.elf"
  lake exe decompile --to lean --proved "$OUT/$ns.elf" "$OUT" "$ns" > "$OUT/log"
  for l in "$@"; do
    if ! grep -qF "$l" "$OUT/log"; then cat "$OUT/log"; echo "to-lean-check: $ns: no $l"; exit 1; fi
  done
}
listed --start-last S '3 functions, 4 instructions, 0 symbols left out' \
  'not a function: zz: a local label without a size'
listed --label-past X '3 functions, 4 instructions, 0 symbols left out'
listed --func-past Y '3 functions, 4 instructions, 1 symbols left out' \
  'left out: zz: outside its section'
echo "to-lean-check: last unsized _start taken; local label named; function past .text left out"

# what is left out is named in the root module; with `--all`, it is an error
if grep -q 'not functions of' "$OUT/P.lean"; then
  cat "$OUT/P.lean"; echo "to-lean-check: P.lean names a function left out"; exit 1
fi
lake env lean --run scripts/to-lean-check/WriteElf.lean --addw "$OUT/u.elf"
lake exe decompile --to lean --proved "$OUT/u.elf" "$OUT" U
if ! grep -q '^  \* "_start: `ADDW` at 0x1000c' "$OUT/U.lean"; then
  cat "$OUT/U.lean"; echo "to-lean-check: U.lean does not name _start as left out"; exit 1
fi
build U/Words
for f in "$OUT"/U/F*.lean; do build "U/$(basename "$f" .lean)"; done
build U
for e in u Y; do
  if lake exe decompile --to lean --proved --all "$OUT/$e.elf" "$OUT" V; then
    echo "to-lean-check: --all writes $e.elf, which has a symbol left out"; exit 1
  fi
  if [ -e "$OUT/V" ] || [ -e "$OUT/V.lean" ]; then
    echo "to-lean-check: --all failed on $e.elf, but wrote V"; exit 1
  fi
done
# a name that is not a function (here a local label inside `main`) leaves no code out
lake exe decompile --to lean --proved --all "$OUT/S.elf" "$OUT" N > /dev/null
echo "to-lean-check: what is left out is named in the root module, and refused by --all"
