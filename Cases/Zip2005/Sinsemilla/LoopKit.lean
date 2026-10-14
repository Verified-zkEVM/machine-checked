import AsmVerif.RiscV.Sym

/-!
# Shared pieces of the two `from_iter` loop proofs

The callee-saved registers neither loop touches (`Kept`), and membership in short literal lists.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- The registers the loop does not touch (callee-saved ones it neither uses nor saves). -/
def Kept (s t : MachineState) : Prop :=
  t.getReg .x3 = s.getReg .x3 ∧ t.getReg .x4 = s.getReg .x4 ∧
  t.getReg .x22 = s.getReg .x22 ∧ t.getReg .x23 = s.getReg .x23 ∧ t.getReg .x24 = s.getReg .x24 ∧
  t.getReg .x25 = s.getReg .x25 ∧ t.getReg .x26 = s.getReg .x26 ∧ t.getReg .x27 = s.getReg .x27

theorem Kept.refl (s : MachineState) : Kept s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Kept.trans {s₁ s₂ s₃ : MachineState} (h₁ : Kept s₁ s₂) (h₂ : Kept s₂ s₃) : Kept s₁ s₃ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.1.trans h₁.2.2.2.1,
   h₂.2.2.2.2.1.trans h₁.2.2.2.2.1, h₂.2.2.2.2.2.1.trans h₁.2.2.2.2.2.1,
   h₂.2.2.2.2.2.2.1.trans h₁.2.2.2.2.2.2.1, h₂.2.2.2.2.2.2.2.trans h₁.2.2.2.2.2.2.2⟩

theorem mem4 {α : Type} {r r1 r2 r3 r4 : α} (h : r ∈ [r1, r2, r3, r4]) :
    r = r1 ∨ r = r2 ∨ r = r3 ∨ r = r4 := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using h

theorem mem5 {α : Type} {r r1 r2 r3 r4 r5 : α} (h : r ∈ [r1, r2, r3, r4, r5]) :
    r = r1 ∨ r = r2 ∨ r = r3 ∨ r = r4 ∨ r = r5 := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using h

theorem mem6 {α : Type} {r r1 r2 r3 r4 r5 r6 : α} (h : r ∈ [r1, r2, r3, r4, r5, r6]) :
    r = r1 ∨ r = r2 ∨ r = r3 ∨ r = r4 ∨ r = r5 ∨ r = r6 := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using h

end Cases.Zip2005
