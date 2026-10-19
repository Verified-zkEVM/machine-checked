/-
  MachineChecked.RiscV.Sym.Regs

  The register file as one fact.

  `Regs s l` says register `i` of `s` holds `l[i]!`, for all 32 registers. The
  executor keeps one such fact per state instead of one fact per register, so a
  step that writes one register costs one lemma application and one `List.set`
  -- which is what keeps the proof term linear in the number of steps with a
  small constant.
-/

import MachineChecked.RiscV.Sym.Frame

namespace MachineChecked.RiscV.Sym

open RiscvZkvm.Rv64

/-- Register number `i`. -/
def regOf : Nat → Reg
  | 0 => .x0 | 1 => .x1 | 2 => .x2 | 3 => .x3 | 4 => .x4 | 5 => .x5 | 6 => .x6 | 7 => .x7
  | 8 => .x8 | 9 => .x9 | 10 => .x10 | 11 => .x11 | 12 => .x12 | 13 => .x13 | 14 => .x14
  | 15 => .x15 | 16 => .x16 | 17 => .x17 | 18 => .x18 | 19 => .x19 | 20 => .x20 | 21 => .x21
  | 22 => .x22 | 23 => .x23 | 24 => .x24 | 25 => .x25 | 26 => .x26 | 27 => .x27 | 28 => .x28
  | 29 => .x29 | 30 => .x30 | 31 => .x31 | _ => .x0

theorem regOf_ne_x0 : ∀ i, i < 32 → i ≠ 0 → regOf i ≠ .x0 := by decide

theorem regOf_inj : ∀ i, i < 32 → ∀ j, j < 32 → i ≠ j → regOf i ≠ regOf j := by decide

/-- The register file of `s` is `l`. -/
def Regs (s : MachineState) (l : List Word) : Prop :=
  ∀ i, i < 32 → s.getReg (regOf i) = l[i]!

theorem Regs.get {s : MachineState} {l : List Word} (h : Regs s l) (i : Nat) (hi : i < 32) :
    s.getReg (regOf i) = l[i]! := h i hi

/-- The trivial register file: every register holds what it holds. -/
def regsOf (s : MachineState) : List Word := (List.range 32).map fun i => s.getReg (regOf i)

theorem Regs.self (s : MachineState) : Regs s (regsOf s) := by
  intro i hi
  rw [getBang (by simp [regsOf]; omega)]
  simp [regsOf]

@[simp] theorem length_regsOf (s : MachineState) : (regsOf s).length = 32 := by simp [regsOf]

theorem Regs.update {s : MachineState} {l : List Word} (h : Regs s l) (hlen : l.length = 32)
    (i : Nat) (hi : i < 32) {v : Word} (hv : s.getReg (regOf i) = v) : Regs s (l.set i v) := by
  intro j hj
  by_cases hij : j = i
  · subst hij
    rw [hv, getBang (by simp; omega), List.getElem_set_self]
  · rw [h j hj, getBang (by omega), getBang (by simp; omega), List.getElem_set_ne (Ne.symm hij)]

theorem Regs.setReg {s : MachineState} {l : List Word} (h : Regs s l) (hlen : l.length = 32)
    (rd : Nat) (hrd : rd < 32) (hrd0 : rd ≠ 0) (v p : Word) :
    Regs ((s.setReg (regOf rd) v).setPC p) (l.set rd v) := by
  intro i hi
  rw [MachineState.getReg_setPC]
  by_cases hij : i = rd
  · subst hij
    rw [MachineState.getReg_setReg_eq (regOf_ne_x0 i hi hrd0), getBang (by simp; omega),
      List.getElem_set_self]
  · rw [MachineState.getReg_setReg_ne _ _ _ _ (regOf_inj rd hrd i hi (Ne.symm hij)), h i hi,
      getBang (by omega), getBang (by simp; omega), List.getElem_set_ne (Ne.symm hij)]

theorem Regs.setReg0 {s : MachineState} {l : List Word} (h : Regs s l) (v p : Word) :
    Regs ((s.setReg .x0 v).setPC p) l := by
  intro i hi
  rw [MachineState.getReg_setPC]
  exact h i hi

theorem Regs.setPC {s : MachineState} {l : List Word} (h : Regs s l) (p : Word) :
    Regs (s.setPC p) l := by
  intro i hi; rw [MachineState.getReg_setPC]; exact h i hi

theorem Regs.setMem {s : MachineState} {l : List Word} (h : Regs s l) (a v p : Word) :
    Regs ((s.setMem a v).setPC p) l := by
  intro i hi; rw [memShape_getReg]; exact h i hi

theorem Regs.writeWords {s : MachineState} {l : List Word} (h : Regs s l) (a : Word) (ws : List Word)
    (p : Word) : Regs ((s.writeWords a ws).setPC p) l := by
  intro i hi; rw [wwShape_getReg]; exact h i hi

theorem Regs.commit {s : MachineState} {l : List Word} (h : Regs s l) (p : Word) :
    Regs ((s.sp1Commit).setPC p) l := by
  intro i hi; rw [commitShape_getReg]; exact h i hi

theorem Regs.of_eq {s s' : MachineState} {l : List Word} (h : Regs s l) (heq : s = s') :
    Regs s' l := heq ▸ h

/-! ## Chained equations -/

theorem getMem_of_mem_eq {s sM : MachineState} (hmem : s.mem = sM.mem) {a v : Word}
    (h : sM.getMem a = v) : s.getMem a = v := by
  simp only [MachineState.getMem, hmem] at h ⊢; exact h

theorem mem_chain {s s' sM : MachineState} {shape : MachineState} (hdef : shape = s')
    (hshape : shape.mem = s.mem) (hmem : s.mem = sM.mem) : s'.mem = sM.mem := by
  subst hdef; exact hshape.trans hmem

theorem code_chain {s s' s₀ : MachineState} {shape : MachineState} (hdef : shape = s')
    (hshape : shape.code = s.code) (hcode : s.code = s₀.code) : s'.code = s₀.code := by
  subst hdef; exact hshape.trans hcode

theorem priv_chain {s s' : MachineState} {shape : MachineState} {v : List (BitVec 8)} (hdef : shape = s')
    (hshape : shape.privateInput = s.privateInput) (hpriv : s.privateInput = v) :
    s'.privateInput = v := by
  subst hdef; exact hshape.trans hpriv

theorem pc_chain {s' : MachineState} {shape : MachineState} {p : Word} (hdef : shape = s')
    (hshape : shape.pc = p) : s'.pc = p := by
  subst hdef; exact hshape

theorem Unchanged.of_mem_eq' {W : List (Word × Nat)} {s₀ s sM : MachineState}
    (h : Unchanged W s₀ sM) (hmem : s.mem = sM.mem) : Unchanged W s₀ s :=
  h.of_mem_eq hmem

theorem Region.of_mem_eq' {base : Word} {vs : List Word} {s sM : MachineState}
    (h : Region base vs sM) (hmem : s.mem = sM.mem) : Region base vs s :=
  h.of_mem_eq hmem

end MachineChecked.RiscV.Sym
