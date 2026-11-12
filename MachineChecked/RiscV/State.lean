/-
  MachineChecked.RiscV.State

  Reading riscv-zkvm's machine state after an update: the pc after `setPC`, a register after
  a register or memory write, memory after a write, and a normal form with one `setPC` outermost and register
  writes collapsed. Every tool in `MachineChecked/RiscV` and the lift read states through
  these.

  The normal-form lemmas are proved by `cases s` rather than `rfl` on purpose: `simp` applies a
  `rfl` lemma as a definitional change, and the kernel then re-checks it by unfolding the whole
  state term, which on a long straight-line run recurses too deep.

  None of these is a `simp` lemma here; the tools that want them as such say so.
-/

import RiscvZkvm.Rv64

namespace MachineChecked.RiscV

open RiscvZkvm.Rv64

theorem pc_setPC (s : MachineState) (v : Word) : (s.setPC v).pc = v := rfl

theorem setPC_setPC (s : MachineState) (a b : Word) : (s.setPC a).setPC b = s.setPC b := by
  cases s; rfl

theorem setReg_setPC (s : MachineState) (a : Word) (r : Reg) (v : Word) :
    (s.setPC a).setReg r v = (s.setReg r v).setPC a := by
  cases r <;> rfl

theorem setMem_setPC (s : MachineState) (a x v : Word) :
    (s.setPC a).setMem x v = (s.setMem x v).setPC a := by
  cases s; rfl

theorem setByte_setPC (s : MachineState) (a x : Word) (b : BitVec 8) :
    (s.setPC a).setByte x b = (s.setByte x b).setPC a := by
  cases s; rfl

theorem setHalfword_setPC (s : MachineState) (a x : Word) (b : BitVec 16) :
    (s.setPC a).setHalfword x b = (s.setHalfword x b).setPC a := by
  cases s; rfl

theorem setWord32_setPC (s : MachineState) (a x : Word) (b : BitVec 32) :
    (s.setPC a).setWord32 x b = (s.setWord32 x b).setPC a := by
  cases s; rfl

theorem setReg_setReg_same (s : MachineState) (r : Reg) (a b : Word) :
    (s.setReg r a).setReg r b = s.setReg r b := by
  cases r <;> simp only [MachineState.setReg] <;> congr 1 <;> funext r' <;> split <;> rfl

theorem setPC_self {s : MachineState} {p : Word} (h : s.pc = p) : s.setPC p = s := by
  subst h; rfl

/-- Writing `x0` does nothing. -/
theorem setReg_x0 (s : MachineState) (v : Word) : s.setReg .x0 v = s := rfl

theorem getReg_x0 (s : MachineState) : s.getReg .x0 = 0 := rfl

/-- A register after a register write: with literal registers, `simp` decides the condition. -/
theorem getReg_setReg (s : MachineState) (r r' : Reg) (v : Word) :
    (s.setReg r v).getReg r' = if r' = r ∧ r ≠ .x0 then v else s.getReg r' := by
  cases r <;> cases r' <;> rfl

theorem getReg_setMem {s : MachineState} {a v : Word} {r : Reg} :
    (s.setMem a v).getReg r = s.getReg r := by
  cases r <;> rfl

theorem getReg_setByte (s : MachineState) (a : Word) (b : BitVec 8) (r : Reg) :
    (s.setByte a b).getReg r = s.getReg r := by
  cases r <;> rfl

theorem getReg_setWord32 (s : MachineState) (a : Word) (b : BitVec 32) (r : Reg) :
    (s.setWord32 a b).getReg r = s.getReg r := by
  cases r <;> rfl

theorem getReg_setHalfword (s : MachineState) (a : Word) (b : BitVec 16) (r : Reg) :
    (s.setHalfword a b).getReg r = s.getReg r := by
  cases r <;> rfl

/-- Memory after a doubleword write, in `if` form. -/
theorem getMem_setMem {s : MachineState} {a v x : Word} :
    (s.setMem a v).getMem x = if x = a then v else s.getMem x := by
  by_cases h : x = a
  · subst h; simp
  · simp [h]

/-- Memory after writing a block of doublewords, away from every written cell. -/
theorem getMem_writeWords_of_ne {s : MachineState} {base a : Word} {ws : List Word}
    (h : ∀ i, i < ws.length → a ≠ base + BitVec.ofNat 64 (8 * i)) :
    (s.writeWords base ws).getMem a = s.getMem a := by
  induction ws generalizing s base with
  | nil => rfl
  | cons w ws ih =>
    simp only [MachineState.writeWords_cons]
    rw [ih (fun i hi => by
      have := h (i + 1) (by simp; omega)
      rw [show 8 * (i + 1) = 8 * i + 8 by omega, BitVec.ofNat_add] at this
      intro he; apply this; rw [he, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8 * i))]; rfl)]
    rw [getMem_setMem, ite_eq_right (by simpa using h 0 (by simp))]

/-- The 32 registers. -/
def allRegs : List Reg :=
  [.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
   .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29,
   .x30, .x31]

theorem mem_allRegs (r : Reg) : r ∈ allRegs := by
  cases r <;> simp [allRegs]

end MachineChecked.RiscV
