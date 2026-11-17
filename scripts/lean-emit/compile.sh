#!/bin/bash
# compile.sh OUT NS [JOBS]: compile the emitted modules, timing each; prints a summary.
set -u
OUT=$1; NS=$2; JOBS=${3:-8}
REPO="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$REPO"
LP=$(lake env printenv LEAN_PATH)
export LEAN_PATH="$LP:$OUT/build"
mkdir -p "$OUT/build/$NS" "$OUT/log"
one() {
  local m=$1
  local s=$(date +%s.%N 2>/dev/null || python3 -c 'import time;print(time.time())')
  /usr/bin/time -p lean --tstack=400000 --root="$OUT" -o "$OUT/build/$NS/$m.olean" "$OUT/$NS/$m.lean" > "$OUT/log/$m.out" 2> "$OUT/log/$m.time"
  local rc=$?
  echo "$m rc=$rc real=$(grep real "$OUT/log/$m.time" | awk '{print $2}') $(head -c 300 "$OUT/log/$m.out" | tr '\n' ' ')"
}
export -f one
export OUT NS
# the data module first (`Words` for `--proved`, `Code` otherwise), then the rest
for m in Words Code; do [ -f "$OUT/$NS/$m.lean" ] && one $m; done
ls "$OUT/$NS" | grep -E '^(F[0-9]+|Pancake)\.lean$' | sed 's/\.lean$//' | xargs -P "$JOBS" -I{} bash -c 'one {}' > "$OUT/log/summary.txt"
sort -t= -k3 -n -r "$OUT/log/summary.txt" | head -5
echo "failed: $(grep -vc 'rc=0' "$OUT/log/summary.txt")  of $(wc -l < "$OUT/log/summary.txt")"
awk '{split($3,a,"="); s+=a[2]} END {print "sum of times: " s " s"}' "$OUT/log/summary.txt"
