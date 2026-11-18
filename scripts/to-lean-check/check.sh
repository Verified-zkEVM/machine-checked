#!/bin/bash
# check.sh: `decompile --to lean` end to end, on the small ELF of `Tools/Test/Elf.lean`.
#
# Writes the ELF, runs the three routes (`--proved`, the lift of whole programs, `--pancake`),
# and builds every module they write, so that the kernel checks each theorem in them. Then
# changes one number in each route's input or output and checks that the module no longer
# builds: a word (`Words.lean`), a byte (`Code.lean`), and lift 2's notes (`Pancake.lean`).
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
lake exe decompile --to lean --proved "$OUT/t.elf" "$OUT" P
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
