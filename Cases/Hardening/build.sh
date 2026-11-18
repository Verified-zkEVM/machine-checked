#!/bin/sh
# build.sh: the hardening examples' ELFs, from src/*.c, into elf/, and their Lean modules
# (`decompile --to lean --proved`) into Gen/. A source ending in _o0.c is built at -O0, the
# others at -O2. Needs clang with the RISC-V target and an ld.lld (LLD, or found on PATH).
# Run from the repository's root after `lake build decompile`.
set -eu
H=Cases/Hardening
CLANG=${CLANG:-clang}
LLD=${LLD:-ld.lld}
mkdir -p $H/elf
for c in $H/src/*.c; do
  n=$(basename "$c" .c)
  case $n in *_o0) O=-O0 ;; *) O=-O2 ;; esac
  $CLANG --target=riscv64-unknown-elf -march=rv64im -mabi=lp64 $O -ffreestanding -nostdlib \
    -fno-builtin -c "$c" -o "$H/elf/$n.o"
  $LLD -e _start -Ttext=0x1000 "$H/elf/$n.o" -o "$H/elf/$n.elf"
  rm "$H/elf/$n.o"
  M=$(echo "$n" | awk -F_ '{for (i = 1; i <= NF; i++) printf "%s", toupper(substr($i, 1, 1)) substr($i, 2)}')
  rm -rf "$H/Gen/$M" "$H/Gen/$M.lean"
  lake exe decompile --to lean --proved "$H/elf/$n.elf" . "Cases.Hardening.Gen.$M"
done
