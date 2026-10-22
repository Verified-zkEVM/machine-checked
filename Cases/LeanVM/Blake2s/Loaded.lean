/-
  Cases.LeanVM.Blake2s.Loaded

  The leanVM `blake2s` guest as its VM loads it: the layout is well-formed, and each
  function's words decode to its program. `gen-image` compared this loader's result with
  riscv-zkvm's `Interpreter.load`, entry by entry (963 code entries, 699 memory
  doublewords); that comparison is the executable glue between the ELF and these facts.

  The guest is `programs/blake2s/blake2s.elf` of leanEthereum/leanVM at
  `9255db3ea2a604898c8af4677f4707d5f671f83a` (see `Cases/LeanVM/README.md`): BLAKE2s-256
  of the bytes `0, 1, 2, …` (mod 251), as many as the advice's first word says, in plain
  Rust; the length and the digest are committed. The functions: `compress`
  (`F_10000038`), `main` (`F_10000a48`), the SDK's `finish` (`F_10000dd8`), `memset`
  (`F_10000e94`), and four panic stubs of one illegal instruction each (`F_10000db8` to
  `F_10000dd0`; the SDK makes a panic one `unimp`, which ends a run with no proof).
  `_start` (`0x10000000`, 14 words before `compress`) has no size in the symbol table, so
  it is the layout's gap chunk, not a function module.
-/

import Cases.LeanVM.Blake2s.Image.Layout

namespace Cases.LeanVM.Blake2s.Loaded

open RiscvZkvm.Rv64 MachineChecked.RiscV Cases.LeanVM.Blake2s.Image

noncomputable abbrev image : Image := Layout.image

/-- The code chunks are sorted, disjoint and in range. -/
theorem codeWF : image.codeWF = true := by decide +kernel

/-- The data chunks are sorted, disjoint, aligned and in range. -/
theorem dataWF : image.dataWF = true := by decide +kernel

/-- The entry point is `_start`, at the base of the text segment. -/
theorem entry : image.entry = 0x10000000#64 := rfl

/-! ## The functions' code -/

theorem compress_decode : decodeWords F_10000038.words = F_10000038.prog := by decide +kernel
theorem main_decode : decodeWords F_10000a48.words = F_10000a48.prog := by decide +kernel
theorem finish_decode : decodeWords F_10000dd8.words = F_10000dd8.prog := by decide +kernel
theorem memset_decode : decodeWords F_10000e94.words = F_10000e94.prog := by decide +kernel

/-- A panic stub decodes to nothing: `unimp` is not an instruction. -/
theorem panic_fmt_decode : decodeWords F_10000db8.words = [none, none] := by decide +kernel

end Cases.LeanVM.Blake2s.Loaded
