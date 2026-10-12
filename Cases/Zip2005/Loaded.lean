/-
  Cases.Zip2005.Loaded

  The guest as the zkVM loads it, and the spike's integrity theorems restated from there.

  What `zip-2005-asm` checked with compiled code (`check-load`) is here a kernel-checked
  fact about `AsmVerif.RiscV.Load`'s loader: the layout is well-formed, and each function's
  words decode to its program. What stays executable glue is narrower: `gen-image` compared
  this loader's result with riscv-zkvm's `Interpreter.load`, entry by entry (41,780 code
  entries, 36,144 memory doublewords).
-/

import Cases.Zip2005.Image.Layout
import Cases.Zip2005.Frame.Memcpy
import Cases.Zip2005.Frame.PadNext
import Cases.Zip2005.Frame.DefaultHook
import AsmVerif.RiscV.Frame.Image

namespace Cases.Zip2005.Loaded

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Frame Cases.Zip2005.Image Cases.Zip2005.Frame

noncomputable abbrev image : Image := Layout.image

/-- The code chunks are sorted, disjoint and in range. -/
theorem codeWF : image.codeWF = true := by decide +kernel

/-- Any state an SP1 run of the loaded guest reaches has the image's code. -/
theorem code_of_run {input : List (BitVec 8)} {n : Nat} {s : MachineState}
    (h : stepsSp1 n (image.state input) = some s) : s.code = image.codeAt := by
  rw [stepsSp1_code h]; rfl

/-! ## The spike functions' code -/

theorem memcpy_decode : decodeWords F_7801b4d8.words = F_7801b4d8.prog := by decide +kernel
theorem padNext_decode : decodeWords F_78021720.words = F_78021720.prog := by decide +kernel
theorem defaultHook_decode : decodeWords F_7803b6ac.words = F_7803b6ac.prog := by decide +kernel
theorem outlined_decode : decodeWords F_7803c304.words = F_7803c304.prog := by decide +kernel

theorem memcpy_codeOk {s : MachineState} (hs : s.code = image.codeAt) : CodeOk Fns.memcpy s :=
  codeOk_of_image (k := 25) hs codeWF rfl memcpy_decode
    (fun _ _ h => by simp [Fns.memcpy] at h)

theorem padNext_codeOk {s : MachineState} (hs : s.code = image.codeAt) : CodeOk Fns.padNext s :=
  codeOk_of_image (k := 79) hs codeWF rfl padNext_decode
    (fun _ _ h => by simp [Fns.padNext] at h)

theorem defaultHook_codeOk {s : MachineState} (hs : s.code = image.codeAt) :
    CodeOk Fns.defaultHook s :=
  codeOk_of_image (k := 210) hs codeWF rfl defaultHook_decode fun fb fp h => by
    simp only [Fns.defaultHook, List.lookup] at h
    split at h
    · rename_i hb
      cases h
      rw [beq_iff_eq.mp hb]
      exact ⟨230, F_7803c304.words, rfl, outlined_decode⟩
    · cases h

/-! ## Integrity, from the loaded guest

Each theorem: run the loaded guest `n` SP1 steps to a state `s0` that enters the function
with entry registers `E`; then along that activation's run, every exit restores `ra` and
`sp`. The code premise of the `Frame` theorems is gone: it follows from the load. -/

variable {input : List (BitVec 8)} {n : Nat} (E : Reg → Word) {s0 s s' : MachineState}

theorem memcpy_integrity (hrun : stepsSp1 n (image.state input) = some s0)
    (hpc : s0.pc = Fns.memcpy.base) (hE : ∀ r, r ≠ .x0 → s0.getReg r = E r)
    (hr : Run Fns.memcpy Memcpy.anno E s0 s) {i : Nat} {ins : Instr}
    (hi : Fns.memcpy.idx? s.pc = some i) (hins : Fns.memcpy.instrAt? i = some ins)
    (hleave : ins = .JALR .x0 .x1 0 ∨
      (¬ IsCall ins ∧ ¬ IsOutlined ins ∧ Fns.memcpy.idx? s'.pc = none))
    (hst : stepSp1 s = some s') : s'.getReg .x1 = E .x1 ∧ s'.getReg .x2 = E .x2 :=
  Memcpy.integrity_of_run E hpc hE (memcpy_codeOk (code_of_run hrun)) hr hi hins hleave hst

theorem padNext_integrity (hrun : stepsSp1 n (image.state input) = some s0)
    (hpc : s0.pc = Fns.padNext.base) (hE : ∀ r, r ≠ .x0 → s0.getReg r = E r)
    (hreq : ∀ q ∈ Fns.padNext.collect PadNext.anno (·.reqs), q.Holds E)
    (hr : Run Fns.padNext PadNext.anno E s0 s) {i : Nat} {ins : Instr}
    (hi : Fns.padNext.idx? s.pc = some i) (hins : Fns.padNext.instrAt? i = some ins)
    (hleave : ins = .JALR .x0 .x1 0 ∨
      (¬ IsCall ins ∧ ¬ IsOutlined ins ∧ Fns.padNext.idx? s'.pc = none))
    (hst : stepSp1 s = some s') : s'.getReg .x1 = E .x1 ∧ s'.getReg .x2 = E .x2 :=
  PadNext.integrity_of_run E hpc hE (padNext_codeOk (code_of_run hrun)) hreq hr hi hins hleave hst

theorem defaultHook_integrity (hrun : stepsSp1 n (image.state input) = some s0)
    (hpc : s0.pc = Fns.defaultHook.base) (hE : ∀ r, r ≠ .x0 → s0.getReg r = E r)
    (hreq : ∀ q ∈ Fns.defaultHook.collect DefaultHook.anno (·.reqs), q.Holds E)
    (hres : ∀ s, Run Fns.defaultHook DefaultHook.anno E s0 s → ResOk Fns.defaultHook DefaultHook.anno E s)
    (hr : Run Fns.defaultHook DefaultHook.anno E s0 s) {i : Nat} {ins : Instr}
    (hi : Fns.defaultHook.idx? s.pc = some i) (hins : Fns.defaultHook.instrAt? i = some ins)
    (hleave : ins = .JALR .x0 .x1 0 ∨
      (¬ IsCall ins ∧ ¬ IsOutlined ins ∧ Fns.defaultHook.idx? s'.pc = none))
    (hst : stepSp1 s = some s') : s'.getReg .x1 = E .x1 ∧ s'.getReg .x2 = E .x2 :=
  DefaultHook.integrity_of_run E hpc hE (defaultHook_codeOk (code_of_run hrun)) hreq hres hr hi
    hins hleave hst

end Cases.Zip2005.Loaded
