import AsmVerif.RiscV.Sym
import AsmVerif.RiscV.Sym.Write
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Image.F_7801b3b0
import Cases.Zip2005.Image.Ro

/-!
# `syscall_write` (0x7801b3b0) to a descriptor other than 13

`WRITE` the bytes, then, for fd 13 only, feed them to the public-values hasher. The guest's one
call (`empty_input_stream_halt`, fd 2) takes the `bne` straight to the epilogue: the call leaves
the memory alone and returns. The `ecall` itself is a spec at its pc (`write_other_step`), the
executor not knowing `WRITE`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- The `WRITE` `ecall` at `0x7801b3d4`, fd ≠ 13: the pc advances. -/
theorem write_other_step {P : Prop} (u : MachineState) (fd r1 r11 r12 : Word)
    (hpc : u.pc = 0x7801b3d4#64) (hcode : CodeAt F_7801b3b0.base F_7801b3b0.prog u)
    (ht0 : u.getReg .x5 = 2#64) (h10 : u.getReg .x10 = fd) (hfd : fd ≠ 13#64)
    (h1 : u.getReg .x1 = r1) (h11 : u.getReg .x11 = r11) (h12 : u.getReg .x12 = r12)
    (hk : ∀ t, t.pc = 0x7801b3d8#64 → t.code = u.code → CalleeSaved u t → Unchanged [] u t →
      t.privateInput = u.privateInput → t.getReg .x1 = r1 → t.getReg .x10 = fd →
      t.getReg .x11 = r11 → t.getReg .x12 = r12 → Safe P t) :
    Safe P u := by
  have hf : u.code u.pc = some .ECALL := by rw [hpc]; exact hcode 9 (by decide)
  refine Safe.step (stepSp1_write_other hf ht0 (by rw [h10]; exact hfd))
    (hk _ ?_ rfl ?_ ?_ rfl ?_ ?_ ?_ ?_)
  · show u.pc + 4 = _; rw [hpc]; decide
  · intro r _; simp
  · intro a _; simp
  · simp only [MachineState.getReg_setPC]; exact h1
  · simp only [MachineState.getReg_setPC]; exact h10
  · simp only [MachineState.getReg_setPC]; exact h11
  · simp only [MachineState.getReg_setPC]; exact h12

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem syscall_write_other_spec {P : Prop} (s : MachineState) (ra sp fd : Word)
    (hpc : s.pc = 0x7801b3b0#64) (hcode : CodeAt F_7801b3b0.base F_7801b3b0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x30 sp)
    (ha0 : s.getReg .x10 = fd) (hfd : fd ≠ 13#64)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x30#64, 6)] s t → Safe P t) :
    Safe P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hstk.frame 6 (by decide)
  have hu := Unchanged.refl [(sp - 0x30#64, 6)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x30#64) 6 s
  sym_exec [write_other_step]
  · sym_close hk
  · simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hbr11
    exact absurd hbr11 hfd

end Cases.Zip2005
