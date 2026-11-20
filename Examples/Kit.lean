/-
  Examples.Kit

  What the examples share: the bytes of a region, and a byte read after a byte written.
-/

import MachineChecked.RiscV.Lift.Contract
import MachineChecked.RiscV.Lift.Rules
import LprogRiscV.Lsym

namespace Examples

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine

/-- `j + 1`, as addresses count it. -/
theorem ofNat_succ (j : Nat) : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 (j + 1) := by
  apply BitVec.eq_of_toNat_eq; simp

/-- The `n` bytes from address `a`. -/
def bytesAt (m : MachineState) (a : Word) (n : Nat) : List (BitVec 8) :=
  (List.range n).map fun i => m.getByte (a + BitVec.ofNat 64 i)

/-- Byte `q` of a doubleword whose byte `p` was replaced. -/
theorem extractByte_replaceByte (w p q : Word) (b : BitVec 8) (hp : p ≤ 7#64) (hq : q ≤ 7#64) :
    extractByte (replaceByte w p.toNat b) q.toNat = if q = p then b else extractByte w q.toNat := by
  have e : ∀ x : Word, x ≤ 7#64 → x.toNat * 8 = (x * 8#64).toNat := fun x hx => by bv_omega
  simp only [extractByte, replaceByte, e p hp, e q hq, ← BitVec.shiftLeft_eq',
    ← BitVec.ushiftRight_eq']
  split <;> bv_decide

/-- **A byte read after a byte written**: the byte written at that address, the old one elsewhere. -/
theorem getByte_setByte (m : MachineState) (a c : Word) (b : BitVec 8) :
    (m.setByte a b).getByte c = if c = a then b else m.getByte c := by
  simp only [MachineState.getByte, MachineState.setByte, getMem_setMem, byteOffset]
  by_cases h : alignToDword c = alignToDword a
  · have e : (c &&& 7#64 = a &&& 7#64) ↔ c = a := by
      unfold alignToDword at h; constructor <;> intro h' <;> bv_decide
    simp only [h, ↓reduceIte, extractByte_replaceByte _ _ _ _ (show a &&& 7#64 ≤ 7#64 by bv_decide)
      (show c &&& 7#64 ≤ 7#64 by bv_decide), e]
  · have hne : c ≠ a := fun h' => h (by rw [h'])
    simp only [h, hne, ↓reduceIte]

end Examples
