#!/usr/bin/env bash
# Time the kernel check `decodeWords words = prog` for image functions.
#
#   time-decode.sh MODE FN...     MODE: base | list | packed | rfl
#
# For each function `F_<addr>` (a module under Cases/Zip2005/Image, built first), writes a
# one-theorem file to $TMPDIR and elaborates it alone with `lake env lean`, printing wall
# time and peak RSS. `list`/`packed` close the goal with `decide +kernel` (the kernel
# evaluates the `Decidable` instance; no elaborator evaluation). `rfl` closes the list form
# with `rfl`, for comparison.
set -euo pipefail
cd "$(dirname "$0")/../.."
MODE="$1"; shift
TMP="${TMPDIR:-/tmp}/asmverif-time"; mkdir -p "$TMP"
for F in "$@"; do
  lake build "Cases.Zip2005.Image.$F" >/dev/null
  case "$MODE" in
    base)   lhs="True"; tac="trivial" ;;
    list)   lhs="decodeWords $F.words";              tac="decide +kernel" ;;
    packed) lhs="decodeWords (unpackWords $F.packed $F.len)"; tac="decide +kernel" ;;
    rfl)    lhs="decodeWords $F.words";              tac="rfl" ;;
  esac
  cat > "$TMP/T_$F.lean" <<LEAN
import Cases.Zip2005.Image.$F
open AsmVerif.RiscV Cases.Zip2005.Image
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem decode_ok : $( [[ $MODE == base ]] && echo True || echo "$lhs = $F.prog" ) := by $tac
LEAN
  n=$(grep -m1 "^$F" Cases/Zip2005/Image/INDEX.tsv | cut -f3)
  out=$( { /usr/bin/time -l lake env lean "$TMP/T_$F.lean" ; } 2>&1 ) && st=ok || st=FAIL
  real=$(echo "$out" | awk '/real/ {print $1}')
  rss=$(echo "$out" | awk '/maximum resident set size/ {printf "%.0f", $1/1048576}')
  printf '%-7s %-11s %6s words  %8ss  %6s MB  %s\n' "$MODE" "$F" "$n" "$real" "$rss" "$st"
  [[ $st == ok ]] || echo "$out" | grep -v '^ ' | head -5
done
