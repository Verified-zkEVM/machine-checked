/-
  LprogRiscV.Lsym

  RISC-V's definitions in the simp set of `lsym` (`Lprog/Tactic.lean`): the instance, how an
  operand and an immediate are read, the memory, and the translation of an instruction to an
  operation, so that `lsym` computes RISC-V's operations and their side conditions.
-/

import LprogRiscV.Instance
import Lprog.Tactic

namespace Lprog.RiscV

open RiscvZkvm.Rv64 Lprog.RiscV.Machine

attribute [lsym_simp] rvIsa rv opnd se12 sh addr opOf rvMem signExtend12

-- the machine state a register file builds, read: a contract's pre- and postcondition
attribute [lsym_simp] getReg_ofParts getMem_ofParts

/-! A memory access's check, in the form the lemmas about regions give it (`dwordOk`): a
  doubleword's as `isValidDwordAccessSp1`, a byte's as validity alone. -/

@[lsym_simp] theorem dword_check (a : Word) :
    (isValidMemAddrSp1 a && alignedFor 8 a) = isValidDwordAccessSp1 a := rfl

@[lsym_simp] theorem dword_check' (a : Word) :
    (isValidMemAddrSp1 a = true ∧ alignedFor 8 a = true) ↔ isValidDwordAccessSp1 a = true := by
  simp [isValidDwordAccessSp1, alignedFor]

/-- A store does not change the code, so not where the code is. -/
@[lsym_simp] theorem noCodeAt_setMem (m : MachineState) (a v b : Word) (w : Nat) :
    noCodeAt (m.setMem a v) b w = noCodeAt m b w := rfl

@[lsym_simp] theorem alignedFor_1 (a : Word) : alignedFor 1 a = true := rfl

/-- **The frame of a postcondition.** Every register outside `S` reads in the machine state
    built from `r'` as in `u0`, if `regs` agrees with `u0` outside `S` and `r'` with `regs`
    (`x0` reads zero in both). The second is what `lframe` proves of the register file `lsym`
    leaves. -/
theorem frame_ofParts {S : List Reg} {regs r' : Reg → BitVec 64} {u0 : MachineState}
    (hkept : ∀ r, r ∉ S → r ≠ .x0 → regs r = u0.getReg r)
    (hw : ∀ r, r ∉ S → r ≠ .x0 → r' r = regs r) (m : MachineState) :
    ∀ r, r ∉ S → (ofParts r' m).getReg r = u0.getReg r := by
  intro r hr
  by_cases h0 : r = .x0
  · subst h0; simp [getReg_x0]
  · rw [getReg_ofParts]; simp [h0, hw r hr h0, hkept r hr h0]

/-- **A contract stated over a machine state, as a contract over the register file**
    (`Isa.Contract`): a function's contract that holds from any machine state `u` the register
    file agrees with holds from the one built from the register file (`Agree.refl`), with the
    precondition and the postcondition read there. So a contract proved by stepping a machine
    state is one `lsym … using` takes, without proving it again. -/
theorem contract_of_agree {p : Lprog rvIsa.Op rvIsa.Reg} {E : Type} {c : Context rvIsa E} {f : Nat}
    {Pre : BitVec 64 → BitVec 64 → MachineState → Prop}
    {Post : BitVec 64 → BitVec 64 → MachineState → MachineState → Prop}
    (h : ∀ (G : State rvIsa → Prop) (n : Nat) (Q : State rvIsa → Prop) (ret top : BitVec 64)
      (rest : List Frame) (u : MachineState) (regs : Reg → BitVec 64) (m : MachineState),
      Agree (ofParts regs m) u → Pre ret top u →
      (∀ r' m', Post ret top u (ofParts r' m') → rvIsa.SafeN p c G n Q ⟨rest, r', m'⟩) →
      rvIsa.SafeN p c G n Q ⟨⟨f, 0, ret, top⟩ :: rest, regs, m⟩) :
    rvIsa.Contract p c f (fun ret top regs m => Pre ret top (ofParts regs m))
      (fun ret top regs m r' m' => Post ret top (ofParts regs m) (ofParts r' m')) :=
  fun G n Q ret top rest regs m hpre hk => h G n Q ret top rest _ regs m (Agree.refl _) hpre hk

end Lprog.RiscV
