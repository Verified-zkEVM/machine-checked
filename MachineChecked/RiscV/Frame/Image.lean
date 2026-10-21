/-
  MachineChecked.RiscV.Frame.Image

  The frame theorems' code premise, discharged from a loaded image.

  `Frame.integrity` assumes `CodeOk f s0` for the state the activation starts in. Code
  never changes under `stepSp1` (`Sym.code_stepSp1`), so it is the loaded image's code
  (`Image.codeAt`); and the image holds `f`'s words at `f.base` and they decode to `f.prog`
  (`Image.codeAt_prog`, plus the per-function kernel check `decodeWords ws = prog`).
-/

import MachineChecked.RiscV.Load
import MachineChecked.RiscV.Frame.Sound
import MachineChecked.RiscV.Sym.Core

namespace MachineChecked.RiscV.Frame

open RiscvZkvm.Rv64

/-- `f`'s code is in any state whose code is the image's, given `f`'s chunk, the decoding
    of its words, and the same for each outlined fragment it calls. -/
theorem codeOk_of_image {img : Image} {f : Fn} {s : MachineState} (hs : s.code = img.codeAt)
    (hwf : img.codeWF = true) {k : Nat} {ws : List (BitVec 32)}
    (hk : img.code[k]? = some (CodeChunk.mk f.base ws)) (hdec : decodeWords ws = f.prog)
    (hfr : ∀ fb fp, f.frags.lookup fb = some fp →
      ∃ (k' : Nat) (ws' : List (BitVec 32)), img.code[k']? = some (CodeChunk.mk fb ws') ∧
        decodeWords ws' = fp) :
    CodeOk f s := by
  refine ⟨fun j ins hj => ?_, fun fb fp hfp m ins hm => ?_⟩
  · rw [hs]
    have : f.prog[j]? = some (some ins) := by
      simp only [Fn.instrAt?, Option.join_eq_some_iff] at hj; exact hj
    exact Image.codeAt_prog hwf hk hdec this
  · rw [hs]
    obtain ⟨k', ws', hk', hdec'⟩ := hfr fb fp hfp
    exact Image.codeAt_prog hwf hk' hdec' hm

end MachineChecked.RiscV.Frame
