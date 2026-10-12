#!/usr/bin/env bash
# The digest of what the zkVM loads: entry point plus the bytes of every PT_LOAD segment
# (llvm-objcopy -O binary keeps exactly the allocated sections, laid out by address).
# Two ELFs with equal digests run identically, whatever their non-loaded sections say.
set -euo pipefail
for f in "$@"; do
  tmp="$(mktemp)"; llvm-objcopy -O binary "$f" "$tmp"
  entry="$(llvm-readelf -h "$f" | awk '/Entry point/ {print $4}')"
  echo "$(printf '%s ' "$entry"; shasum -a 256 "$tmp" | awk '{print $1}')  $f"
  rm -f "$tmp"
done
