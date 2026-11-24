#!/bin/sh
# build.sh: the images of rustc's lean verifiers (docs/NativeVerifiers.md).
#
#   Examples/LeanVerifiers/build.sh            write the four images to Examples/elf/
#   Examples/LeanVerifiers/build.sh --check    the same, to a scratch directory, and compare
#
# The code is rustc's assembly for leanXMSS and leanSPHINCS (`signatures`) and the leanVM
# verifier (`vm`), for AArch64 and x86-64, as leanEthereum/leanVM#837 commits it (its
# `formal/native/rustc/build.sh` makes it: rustc 1.99.1, opt-level 3, fat LTO, no SIMD, panics
# as trap instructions). It is fetched at the commit below and checked against that pull
# request's SHA256SUMS. Each file is assembled by clang and linked by LLD, with a stub `_start`
# that loops, into a statically linked executable that is not position-independent, which is
# what `decompile` reads. `--no-relax` keeps x86-64's calls of `memcpy` and `memset` through
# the GOT as rustc wrote them; the GOT is then part of the image.
#
# A different clang or LLD may give different bytes, and proofs are about the images that are
# in the repository: SHA256SUMS, beside this file, pins them, and `--check` says if a build
# here gives others. Needs curl, clang with the two targets (CLANG) and LLD's `ld.lld` (LLD;
# rustup's `rust-lld -flavor gnu` is one).
set -eu
here=$(cd "$(dirname "$0")" && pwd)
COMMIT=1eb3a8f9a7ea3d63f9d2c69ef97543bfa8a03ae2
RAW=https://raw.githubusercontent.com/kevaundray/leanVM/$COMMIT/formal/native/rustc
CLANG=${CLANG:-clang}
LLD=${LLD:-ld.lld}
out=$here/../elf
[ "${1:-}" = --check ] && out=$(mktemp -d)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

# name, path of the assembly in the pull request, its sha256 there
sources="signatures_a64 asm/signatures-aarch64.s 02ada8aa56186203cfd04b38b1d5d6324ffd6ae498e81b96fb1e5a9c6d02565d
signatures_x64 asm/signatures-x86_64.s 455087031020ecfb3576d162285f97f9dd4a4faa0358a5f5afe1b3de6e174c86
vm_a64 vm/asm/vm-aarch64.s 15636eb734897392c63c0c05c7fd77a66ac9cf10c66f23ae3ee0e11152526e25
vm_x64 vm/asm/vm-x86_64.s 40a3122855a3f5fdd86b44f13421d0b8de791951071735599da6dad79ff42812"

printf '\t.text\n\t.globl _start\n\t.type _start,%%function\n_start:\n\tb _start\n\t.size _start, .-_start\n' > "$tmp/start_a64.s"
printf '\t.text\n\t.globl _start\n\t.type _start,@function\n_start:\n\tjmp _start\n\t.size _start, .-_start\n' > "$tmp/start_x64.s"

echo "$sources" | while read -r name path sum; do
  case $name in
    *_a64) target=aarch64-unknown-linux-musl start=start_a64 ;;
    *) target=x86_64-unknown-linux-musl start=start_x64 ;;
  esac
  curl -sSfL "$RAW/$path" -o "$tmp/$name.s"
  echo "$sum  $tmp/$name.s" | shasum -a 256 -c - > /dev/null
  "$CLANG" --target=$target -c "$tmp/$start.s" -o "$tmp/$start.o"
  "$CLANG" --target=$target -c "$tmp/$name.s" -o "$tmp/$name.o"
  # shellcheck disable=SC2086
  $LLD -static --no-pie --no-relax --strip-debug --build-id=none -e _start \
    "$tmp/$start.o" "$tmp/$name.o" -o "$out/lean_$name.elf"
done

(cd "$out" && shasum -a 256 lean_signatures_a64.elf lean_signatures_x64.elf lean_vm_a64.elf lean_vm_x64.elf) > "$tmp/sums"
if [ "${1:-}" = --check ]; then
  diff "$here/SHA256SUMS" "$tmp/sums" && echo "the images are those of SHA256SUMS"
  rm -rf "$out"
else
  cp "$tmp/sums" "$here/SHA256SUMS"; cat "$here/SHA256SUMS"
fi
