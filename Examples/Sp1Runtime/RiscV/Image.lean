/-
  Examples.Sp1Runtime.RiscV.Image

  Written by hand, unlike the other modules' `Image.lean`: the modules of the SP1 guest
  `Examples/elf/k_u128.elf` that are kept. `decompile --to lean --proved` writes one module for
  each of the 159 functions of the guest that it lifts, and an index that imports them all.
  Only the functions that have proofs are in the repository, with the words they are checked
  against, so that `lake build Examples` does not build 155 modules nothing uses.
  `Examples/build.sh Sp1Runtime` writes these five again and leaves this file alone. The
  functions, by index (`f<i>`, `f<i>_eq`):

  * `Words`: the words of all 159 functions, checked against the ELF (`words_eq_elf`)
  * `F11`: `syscall_write`, at 0x780042ec (`WriteVectored.lean`)
  * `F24`: `sys_write`, at 0x78004eec (`WriteVectored.lean`)
  * `F107`: `write_vectored` of the standard error, at 0x7800c060 (`WriteVectored.lean`)
  * `F158`: `__udivti3`, at 0x7800ed88 (`Udivti3.lean`)

  Nothing of the guest's code is left out of `fns`: its three functions that contain `unimp`
  (`rust_panic`, `panic_with_hook`, and `__rust_end_short_backtrace` of `rust_oom`) are lifted,
  with a trap there. Not functions of `fns`, though no code is left out: twelve second names of
  functions it takes, at their addresses (`decompile` gives each).

  `memcmp` is from an ELF of its own (`MemcmpImage.lean`).

  `hok`, that the functions' entries are aligned, is here, once, for `WriteVectored.lean` and
  `Udivti3.lean`.
-/

import Examples.Sp1Runtime.RiscV.Image.F11
import Examples.Sp1Runtime.RiscV.Image.F24
import Examples.Sp1Runtime.RiscV.Image.F107
import Examples.Sp1Runtime.RiscV.Image.F158
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
