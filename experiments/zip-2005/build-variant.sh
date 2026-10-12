#!/usr/bin/env bash
# Build one variant of zip-2005-asm's guest ELF from a copy of its workspace.
#
#   build-variant.sh NAME [RUSTFLAGS...]
#
# The workspace is copied (without `target/`) to $WORK, so zip-2005-asm and its pinned
# artifacts/zip-2005.elf are never touched. The ELF lands in out/NAME.elf, with its sha256
# and the build log beside it. Every variant reuses one copy, so dependencies are built once
# per distinct RUSTFLAGS.
set -euo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
SRC="${SRC:-$HERE/../../../zip-2005-asm/zip-2005}"
WORK="${WORK:-${TMPDIR:-/tmp}/asm-verif-zip2005-work}"
NAME="${1:?usage: build-variant.sh NAME [RUSTFLAGS...]}"; shift
FLAGS="$*"

[[ -d "$SRC/program" ]] || { echo "build-variant: no guest at $SRC" >&2; exit 2; }
mkdir -p "$WORK" "$HERE/out"
rsync -a --delete --exclude target "$SRC/" "$WORK/zip-2005/"

ARGS=(prove build --locked --output-directory "$HERE/out/$NAME.d" --elf-name zip-2005)
[[ -n "$FLAGS" ]] && ARGS+=("--rustflags=$FLAGS")
echo "build-variant: $NAME  rustflags='$FLAGS'"
( cd "$WORK/zip-2005/program" && "$HOME/.sp1/bin/cargo-prove" "${ARGS[@]}" ) > "$HERE/out/$NAME.log" 2>&1 \
  || { echo "build-variant: build failed, see out/$NAME.log" >&2; tail -20 "$HERE/out/$NAME.log" >&2; exit 1; }
cp "$HERE/out/$NAME.d/zip-2005" "$HERE/out/$NAME.elf"
shasum -a 256 "$HERE/out/$NAME.elf" | awk '{print $1}' > "$HERE/out/$NAME.elf.sha256"
echo "build-variant: out/$NAME.elf  $(wc -c < "$HERE/out/$NAME.elf") bytes  sha256 $(cat "$HERE/out/$NAME.elf.sha256")"
