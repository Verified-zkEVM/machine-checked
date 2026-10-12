#!/usr/bin/env bash
# Per allocated section: size and sha256 in each of two ELFs, and whether they agree.
set -euo pipefail
a="$1"; b="$2"; d="$(mktemp -d)"
for s in .rodata .eh_frame .text .data; do
  for f in "$a" "$b"; do llvm-objcopy -O binary --only-section="$s" "$f" "$d/$(basename "$f").$s"; done
  ha=$(shasum -a 256 < "$d/$(basename "$a").$s" | cut -c1-12); hb=$(shasum -a 256 < "$d/$(basename "$b").$s" | cut -c1-12)
  sa=$(wc -c < "$d/$(basename "$a").$s"); sb=$(wc -c < "$d/$(basename "$b").$s")
  printf '%-10s %8s %8s  %s\n' "$s" "$sa" "$sb" "$([[ $ha == $hb ]] && echo same || echo DIFFERENT)"
done
rm -rf "$d"
