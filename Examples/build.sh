#!/bin/sh
# build.sh: every example's ELF, from src/, into elf/, and its Image
# (`decompile --to lean --proved`), into <Module>/RiscV/.
#
#   Examples/build.sh                every module
#   Examples/build.sh Memory         one module
#   LIFT_ONLY=1 Examples/build.sh    do not compile: only write the Images, from the ELFs in elf/
#
# The modules are in three groups, compiled as each was when its proofs were written:
#
#   the ladder      clang -O1 (Rust through LLVM IR), linked by RV_LD at 0x10000
#   stress tests    clang -O2 (-O0 for a source ending in _o0), linked by LLD at 0x1000
#   guest code      Sp1Runtime: `memcmp.c` as a stress test, and five functions of an SP1
#                   guest, `elf/k_u128.elf`, which is not compiled here
#
# Compiling needs clang with the RISC-V target, a RISC-V linker (RV_LD), an ld.lld (LLD) and,
# for the Rust example, rustc with the target riscv64imac-unknown-none-elf. Run from the
# repository's root after `lake build decompile`. The ELFs and the Images are in the
# repository, so `lake build Examples` needs none of these. A different compiler or linker
# gives different code, and the proofs are about the ELFs that are here: use LIFT_ONLY=1
# unless you mean to change them.
set -eu
E=Examples
CLANG=${CLANG:-clang}
RV_LD=${RV_LD:-riscv64-elf-ld}
LLD=${LLD:-ld.lld}
DECOMPILE=${DECOMPILE:-.lake/build/bin/decompile}
LIFT_ONLY=${LIFT_ONLY:-}
TARGET="--target=riscv64-unknown-elf -march=rv64im -mabi=lp64"
CFLAGS="-O1 -fno-vectorize -ffreestanding -nostdlib -fno-builtin"
mkdir -p $E/elf $E/bin

# Write the Image of an ELF: name, Lean module of the Image (under Examples).
lift() {
  dir=$E/$(echo "$2" | tr . /)
  rm -rf "$dir" "$dir.lean"
  "$DECOMPILE" --to lean --proved "$E/elf/$1.elf" . "Examples.$2"
}

# A C source of the ladder: name, module.
ladder_c() {
  if [ -z "$LIFT_ONLY" ]; then
    # shellcheck disable=SC2086
    "$CLANG" $TARGET $CFLAGS -c "$E/src/c/$1.c" -o "$E/bin/$1.o"
    "$RV_LD" -Ttext=0x10000 --no-relax -e 0x10000 "$E/bin/$1.o" -o "$E/elf/$1.elf"
  fi
  lift "$1" "$2.RiscV.Image"
}

# A Rust source of the ladder: name, source, module. rustc writes LLVM IR, and clang compiles
# it for RV64IM, so that the code has no compressed instructions (rustc's own RISC-V targets
# without them need a standard library built for them).
ladder_rust() {
  if [ -z "$LIFT_ONLY" ]; then
    rustc --edition 2021 --target riscv64imac-unknown-none-elf -C opt-level=1 -C panic=abort \
      --crate-type=staticlib --emit=llvm-ir -o "$E/bin/$1.ll" "$2" 2>/dev/null
    sed -E 's/"target-features"="[^"]*"//g; s/"target-cpu"="[^"]*"//g; /^target datalayout/d;
            /^target triple/d' "$E/bin/$1.ll" > "$E/bin/$1.clean.ll"
    # shellcheck disable=SC2086
    "$CLANG" $TARGET -O1 -fno-vectorize -Wno-override-module -c "$E/bin/$1.clean.ll" -o "$E/bin/$1.o"
    "$RV_LD" -Ttext=0x10000 --no-relax -e 0x10000 "$E/bin/$1.o" -o "$E/elf/$1.elf"
  fi
  lift "$1" "$3.RiscV.Image"
}

# A stress test: name, Lean module of the Image. A source ending in _o0 is built at -O0, the
# others at -O2.
stress() {
  if [ -z "$LIFT_ONLY" ]; then
    case $1 in *_o0) O=-O0 ;; *) O=-O2 ;; esac
    # shellcheck disable=SC2086
    "$CLANG" $TARGET $O -ffreestanding -nostdlib -fno-builtin -c "$E/src/c/$1.c" -o "$E/bin/$1.o"
    "$LLD" -e _start -Ttext=0x1000 "$E/bin/$1.o" -o "$E/elf/$1.elf"
  fi
  lift "$1" "$2"
}

# The SP1 guest's runtime, from `elf/k_u128.elf`. The guest has 159 functions; the Image keeps
# the words and the functions that have proofs, and `Image.lean`, which is written by hand,
# imports them.
SP1_KEPT="Words F11 F24 F107 F158"
sp1runtime() {
  tmp=$(mktemp -d)
  "$DECOMPILE" --to lean --proved "$E/elf/k_u128.elf" "$tmp" Examples.Sp1Runtime.RiscV.Image
  dir=$E/Sp1Runtime/RiscV/Image
  rm -rf "$dir"
  mkdir -p "$dir"
  for f in $SP1_KEPT; do cp "$tmp/$dir/$f.lean" "$dir/$f.lean"; done
  rm -rf "$tmp"
}

want() { [ -z "$ONLY" ] || [ "$ONLY" = "$1" ]; }
ONLY=${1:-}

# the ladder
if want Basic; then ladder_c basic Basic; fi
if want Memory; then ladder_c memory Memory; fi
if want Bytes; then ladder_c bytes Bytes; fi
if want RustBasic; then ladder_rust rustbasic $E/src/rust/basic.rs RustBasic; fi
if want Mem; then ladder_c mem Mem; fi
if want Limbs; then ladder_c limbs Limbs; fi
if want Crc32; then ladder_c crc32 Crc32; fi
if want ChaCha20; then ladder_c chacha20 ChaCha20; fi
if want Sha256; then ladder_c sha256 Sha256; fi

# stress tests
if want Branches; then stress branches Branches.RiscV.Image; fi
if want BranchesO0; then stress branches_o0 BranchesO0.RiscV.Image; fi
if want Widths; then stress widths Widths.RiscV.Image; fi
if want Arith; then stress arith Arith.RiscV.Image; fi
if want Calls; then stress calls Calls.RiscV.Image; fi
if want CallsO0; then stress calls_o0 CallsO0.RiscV.Image; fi
if want Rec; then stress rec Rec.RiscV.Image; fi
if want Switch; then stress switch Switch.RiscV.Image; fi
if want Big; then stress big Big.RiscV.Image; fi

# guest code
if want Sp1Runtime; then
  stress memcmp Sp1Runtime.RiscV.MemcmpImage
  sp1runtime
fi
