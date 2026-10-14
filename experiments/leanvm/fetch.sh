#!/usr/bin/env bash
# The leanVM guest under study: `programs/blake2s/blake2s.elf` of leanEthereum/leanVM at the
# commit that merged PR 555 into `riscv-exploration` (BLAKE2s-256 in plain Rust, rv64im,
# built by `programs/build.sh` with the guest's pinned nightly). Fetched by content, pinned
# by digest; `llvm-nm` gives gen-image its function boundaries (an untrusted hint).
#
#     experiments/leanvm/fetch.sh
#     lake exe gen-image experiments/leanvm/out/blake2s.elf experiments/leanvm/out/blake2s.nm \
#       Cases/LeanVM/Blake2s/Image Cases.LeanVM.Blake2s.Image
set -euo pipefail
REPO=leanEthereum/leanVM
COMMIT=9255db3ea2a604898c8af4677f4707d5f671f83a
SHA256=6d83bc01bd396e5703de100a90e2b820d78f87b8cd1ea243c4775fa880acd70b
OUT="$(dirname "$0")/out"
mkdir -p "$OUT"
gh api -H "Accept: application/vnd.github.raw" \
  "repos/$REPO/contents/programs/blake2s/blake2s.elf?ref=$COMMIT" > "$OUT/blake2s.elf"
echo "$SHA256  $OUT/blake2s.elf" | shasum -a 256 -c -
llvm-nm -S --defined-only "$OUT/blake2s.elf" > "$OUT/blake2s.nm"
"$(dirname "$0")/../zip-2005/image-digest.sh" "$OUT/blake2s.elf"
