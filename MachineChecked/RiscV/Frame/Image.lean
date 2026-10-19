/-
  MachineChecked.RiscV.Frame.Image

  The frame theorems' code premise, discharged from a loaded image.

  `Frame.integrity` assumes `CodeOk f s0` for the state the activation starts in. Code
  never changes under `stepSp1` (`stepSp1_code`), so it is the loaded image's code
  (`Image.codeAt`); and the image holds `f`'s words at `f.base` and they decode to `f.prog`
  (`Image.codeAt_prog`, plus the per-function kernel check `decodeWords ws = prog`).
-/

import MachineChecked.RiscV.Load
import MachineChecked.RiscV.Frame.Sound

namespace MachineChecked.RiscV.Frame

open RiscvZkvm.Rv64

theorem hintRead_code {s s' : MachineState} (h : hintRead s = some s') : s'.code = s.code := by
  unfold hintRead at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · cases h; simp

theorem sp1Ecall_code {s s' : MachineState} (h : sp1Ecall s = some s') : s'.code = s.code := by
  unfold sp1Ecall at h
  dsimp only at h
  split at h
  · split at h
    · cases h; simp
    · cases h
  · split at h
    · cases h; simp [hintLen]
    · split at h
      · exact hintRead_code h
      · split at h
        · cases h; simp [MachineState.sp1Commit]
        · split at h
          · cases h; simp
          · split at h
            · exact code_step h
            · cases h

/-- No SP1 step changes code memory: not an instruction, not a syscall, not a precompile. -/
theorem stepSp1_code {s s' : MachineState} (h : stepSp1 s = some s') : s'.code = s.code := by
  unfold stepSp1 at h
  split at h
  · cases h
  · cases h
  · exact sp1Ecall_code h
  · cases h
  · split at h
    · split at h
      · cases h; simp
      · cases h
    · cases h; simp

theorem stepsSp1_code : ∀ {n : Nat} {s s' : MachineState}, stepsSp1 n s = some s' → s'.code = s.code
  | 0, s, s', h => by simp [stepsSp1] at h; rw [h]
  | n + 1, s, s', h => by
    obtain ⟨s1, h1, h2⟩ := stepsSp1_succ h
    rw [stepsSp1_code h2, stepSp1_code h1]

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
