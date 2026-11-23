/-
  Examples.Sp1Runtime.RiscV.Image

  Written by hand, unlike the other modules' `Image.lean`: the modules of the SP1 guest
  `Examples/elf/k_u128.elf` that are kept. `decompile --to lean --proved` writes one module for
  each of the 156 functions of the guest that it lifts, and an index that imports them all. Only the functions
  that have proofs are in the repository, with the words they are checked against, so that
  `lake build Examples` does not build 152 modules nothing uses. `Examples/build.sh Sp1Runtime`
  writes these five again and leaves this file alone. The functions, by index (`f<i>`,
  `f<i>_eq`):

  * `Words`: the words of all 156 functions, checked against the ELF (`words_eq_elf`)
  * `F11`: `syscall_write`, at 0x780042ec (`WriteVectored.lean`)
  * `F24`: `sys_write`, at 0x78004eec (`WriteVectored.lean`)
  * `F104`: `write_vectored` of the standard error, at 0x7800c060 (`WriteVectored.lean`)
  * `F155`: `__udivti3`, at 0x7800ed88 (`Udivti3.lean`)

  Not functions of `fns` (`decompile` gives each with the reason): three functions that contain
  `unimp`,

  * `_RNvCsgG40wm8spDe_7___rustc10rust_panic`, at 0x7800b054
  * `_RNvNtCsaFPe17dgLU6_3std9panicking15panic_with_hook`, at 0x7800b47c
  * `_RINvNtNtCsaFPe17dgLU6_3std3sys9backtrace26___rust_end_short_backtraceNCNvNtB6_5alloc8rust_oom0zEB6_`,
    at 0x7800bdc0

  and twelve second names of functions it takes, at their addresses.

  `memcmp` is from an ELF of its own (`MemcmpImage.lean`).

  `hok`, that the functions' entries are aligned, is here, once, for `WriteVectored.lean` and
  `Udivti3.lean`.
-/

import Examples.Sp1Runtime.RiscV.Image.F11
import Examples.Sp1Runtime.RiscV.Image.F24
import Examples.Sp1Runtime.RiscV.Image.F104
import Examples.Sp1Runtime.RiscV.Image.F155
import MachineChecked.RiscV.Lift.Transfer

namespace Examples.Sp1Runtime.RiscV.Image

open MachineChecked.RiscV.Lift

/-- The functions' entries are aligned. -/
theorem hok : ProgOk fns := by
  have h : ∀ w ∈ words, w.2.1 % 4 = 0 := by decide +kernel
  intro f hf
  obtain ⟨⟨name, base, ws⟩, hw, rfl⟩ := List.mem_map.mp hf
  have hb : base % 4 = 0 := h _ hw
  simp only [BitVec.toNat_ofNat]; omega

end Examples.Sp1Runtime.RiscV.Image
