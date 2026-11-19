#!/bin/sh
# build.sh: the examples' ELFs, from src/, into elf/, and their Lean modules
# (`decompile --to lean --proved`) into Gen/.
#
#   Examples/build.sh           every example
#   Examples/build.sh basic     one example
#
# Needs clang with the RISC-V target, a RISC-V linker (RV_LD) and, for the Rust example, rustc
# with the target riscv64imac-unknown-none-elf. Run from the repository's root after
# `lake build decompile`. The ELFs and the modules are in the repository, so `lake build
# Examples` needs none of these.
set -eu
E=Examples
CLANG=${CLANG:-clang}
RV_LD=${RV_LD:-riscv64-elf-ld}
DECOMPILE=${DECOMPILE:-.lake/build/bin/decompile}
TARGET="--target=riscv64-unknown-elf -march=rv64im -mabi=lp64"
CFLAGS="-O1 -fno-vectorize -ffreestanding -nostdlib -fno-builtin"
mkdir -p $E/elf $E/bin

# Link an object at 0x10000 and write its Lean modules: name, module.
link_and_lift() {
  name=$1; module=$2
  "$RV_LD" -Ttext=0x10000 --no-relax -e 0x10000 "$E/bin/$name.o" -o "$E/elf/$name.elf"
  rm -rf "$E/Gen/$module" "$E/Gen/$module.lean"
  "$DECOMPILE" --to lean --proved "$E/elf/$name.elf" . "Examples.Gen.$module"
}

# A C source: name, module.
lift_c() {
  # shellcheck disable=SC2086
  "$CLANG" $TARGET $CFLAGS -c "$E/src/c/$1.c" -o "$E/bin/$1.o"
  link_and_lift "$1" "$2"
}

# A Rust source: name, source, module. rustc writes LLVM IR, and clang compiles it for RV64IM,
# so that the code has no compressed instructions (rustc's own RISC-V targets without them need
# a standard library built for them).
lift_rust() {
  rustc --edition 2021 --target riscv64imac-unknown-none-elf -C opt-level=1 -C panic=abort \
    --crate-type=staticlib --emit=llvm-ir -o "$E/bin/$1.ll" "$2" 2>/dev/null
  sed -E 's/"target-features"="[^"]*"//g; s/"target-cpu"="[^"]*"//g; /^target datalayout/d;
          /^target triple/d' "$E/bin/$1.ll" > "$E/bin/$1.clean.ll"
  # shellcheck disable=SC2086
  "$CLANG" $TARGET -O1 -fno-vectorize -Wno-override-module -c "$E/bin/$1.clean.ll" -o "$E/bin/$1.o"
  link_and_lift "$1" "$3"
}

want() { [ -z "${ONLY:-}" ] || [ "$ONLY" = "$1" ]; }
ONLY=${1:-}

if want basic; then lift_c basic Basic; fi
if want memory; then lift_c memory Memory; fi
if want bytes; then lift_c bytes Bytes; fi
if want rustbasic; then lift_rust rustbasic $E/src/rust/basic.rs RustBasic; fi
if want mem; then lift_c mem Mem; fi
if want limbs; then lift_c limbs Limbs; fi
if want crc32; then lift_c crc32 Crc32; fi
if want chacha20; then lift_c chacha20 ChaCha20; fi
if want sha256; then lift_c sha256 Sha256; fi
