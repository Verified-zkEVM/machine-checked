/-
  AsmVerif.RiscV.Sym.ByteFold

  A sub-word read back from a doubleword built by sub-word stores: `extractByte` /
  `extractHalfword` / `extractWord32` through `replaceByte` / `replaceHalfword` /
  `replaceWord32` chains. `sym_exec` uses these, when `asmverif.sym.foldBytes` is set, to give a
  load from a store-assembled cell (a struct's length byte, a flag, a parameter field) the
  value that was stored, so a branch on it is decided and a constant stays a constant.
-/

import Lean
import RiscvZkvm.Rv64

namespace AsmVerif.RiscV.Sym

open RiscvZkvm.Rv64

register_option asmverif.sym.foldBytes : Bool := {
  defValue := false
  descr := "sym_exec: fold a sub-word load through the sub-word stores that built its cell" }

theorem lt_cases2 {k : Nat} (hk : k < 2) : k = 0 ∨ k = 1 := by omega

theorem lt_cases4 {k : Nat} (hk : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega

theorem lt_cases8 {k : Nat} (hk : k < 8) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega

theorem lt_cases32 {k : Nat} (hk : k < 32) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 ∨ k = 23 ∨ k = 24 ∨ k = 25 ∨ k = 26 ∨ k = 27 ∨ k = 28 ∨ k = 29 ∨ k = 30 ∨ k = 31 := by omega

theorem lt_cases16 {k : Nat} (hk : k < 16) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega

theorem extract1_replace1_self (w : Word) (q : Nat) (x : BitVec 8) (hq : q < 8) :
    extractByte (replaceByte w q x) q = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases8 hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases lt_cases8 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractByte, replaceByte]

theorem extract2_replace2_self (w : Word) (q : Nat) (x : BitVec 16) (hq : q < 4) :
    extractHalfword (replaceHalfword w q x) q = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases4 hq with rfl | rfl | rfl | rfl <;>
  rcases lt_cases16 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractHalfword, replaceHalfword]

theorem extract4_replace4_self (w : Word) (q : Nat) (x : BitVec 32) (hq : q < 2) :
    extractWord32 (replaceWord32 w q x) q = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases2 hq with rfl | rfl <;>
  rcases lt_cases32 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractWord32, replaceWord32]

theorem extract1_replace1_disj (w : Word) (q p : Nat) (x : BitVec 8) (hq : q < 8) (hp : p < 8)
    (h : 1 * q + 1 ≤ 1 * p ∨ 1 * p + 1 ≤ 1 * q) :
    extractByte (replaceByte w p x) q = extractByte w q := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases8 hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases lt_cases8 hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  (try (exfalso; omega)) <;>
  rcases lt_cases8 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractByte, replaceByte]

theorem extract1_replace2_disj (w : Word) (q p : Nat) (x : BitVec 16) (hq : q < 8) (hp : p < 4)
    (h : 1 * q + 1 ≤ 2 * p ∨ 2 * p + 2 ≤ 1 * q) :
    extractByte (replaceHalfword w p x) q = extractByte w q := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases8 hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases lt_cases4 hp with rfl | rfl | rfl | rfl <;>
  (try (exfalso; omega)) <;>
  rcases lt_cases8 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractByte, replaceHalfword]

theorem extract1_replace4_disj (w : Word) (q p : Nat) (x : BitVec 32) (hq : q < 8) (hp : p < 2)
    (h : 1 * q + 1 ≤ 4 * p ∨ 4 * p + 4 ≤ 1 * q) :
    extractByte (replaceWord32 w p x) q = extractByte w q := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases8 hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases lt_cases2 hp with rfl | rfl <;>
  (try (exfalso; omega)) <;>
  rcases lt_cases8 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractByte, replaceWord32]

theorem extract2_replace1_disj (w : Word) (q p : Nat) (x : BitVec 8) (hq : q < 4) (hp : p < 8)
    (h : 2 * q + 2 ≤ 1 * p ∨ 1 * p + 1 ≤ 2 * q) :
    extractHalfword (replaceByte w p x) q = extractHalfword w q := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases4 hq with rfl | rfl | rfl | rfl <;>
  rcases lt_cases8 hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  (try (exfalso; omega)) <;>
  rcases lt_cases16 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractHalfword, replaceByte]

theorem extract2_replace2_disj (w : Word) (q p : Nat) (x : BitVec 16) (hq : q < 4) (hp : p < 4)
    (h : 2 * q + 2 ≤ 2 * p ∨ 2 * p + 2 ≤ 2 * q) :
    extractHalfword (replaceHalfword w p x) q = extractHalfword w q := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases4 hq with rfl | rfl | rfl | rfl <;>
  rcases lt_cases4 hp with rfl | rfl | rfl | rfl <;>
  (try (exfalso; omega)) <;>
  rcases lt_cases16 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractHalfword, replaceHalfword]

theorem extract2_replace4_disj (w : Word) (q p : Nat) (x : BitVec 32) (hq : q < 4) (hp : p < 2)
    (h : 2 * q + 2 ≤ 4 * p ∨ 4 * p + 4 ≤ 2 * q) :
    extractHalfword (replaceWord32 w p x) q = extractHalfword w q := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases4 hq with rfl | rfl | rfl | rfl <;>
  rcases lt_cases2 hp with rfl | rfl <;>
  (try (exfalso; omega)) <;>
  rcases lt_cases16 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractHalfword, replaceWord32]

theorem extract4_replace1_disj (w : Word) (q p : Nat) (x : BitVec 8) (hq : q < 2) (hp : p < 8)
    (h : 4 * q + 4 ≤ 1 * p ∨ 1 * p + 1 ≤ 4 * q) :
    extractWord32 (replaceByte w p x) q = extractWord32 w q := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases2 hq with rfl | rfl <;>
  rcases lt_cases8 hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  (try (exfalso; omega)) <;>
  rcases lt_cases32 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractWord32, replaceByte]

theorem extract4_replace2_disj (w : Word) (q p : Nat) (x : BitVec 16) (hq : q < 2) (hp : p < 4)
    (h : 4 * q + 4 ≤ 2 * p ∨ 2 * p + 2 ≤ 4 * q) :
    extractWord32 (replaceHalfword w p x) q = extractWord32 w q := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases2 hq with rfl | rfl <;>
  rcases lt_cases4 hp with rfl | rfl | rfl | rfl <;>
  (try (exfalso; omega)) <;>
  rcases lt_cases32 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractWord32, replaceHalfword]

theorem extract4_replace4_disj (w : Word) (q p : Nat) (x : BitVec 32) (hq : q < 2) (hp : p < 2)
    (h : 4 * q + 4 ≤ 4 * p ∨ 4 * p + 4 ≤ 4 * q) :
    extractWord32 (replaceWord32 w p x) q = extractWord32 w q := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases2 hq with rfl | rfl <;>
  rcases lt_cases2 hp with rfl | rfl <;>
  (try (exfalso; omega)) <;>
  rcases lt_cases32 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractWord32, replaceWord32]

theorem extract1_replace2_in (w : Word) (q p : Nat) (x : BitVec 16) (hq : q < 8) (hp : p < 4)
    (h : 2 * p ≤ 1 * q ∧ 1 * q + 1 ≤ 2 * p + 2) :
    extractByte (replaceHalfword w p x) q = extractByte (x.zeroExtend 64) (q - 2 * p) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases8 hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases lt_cases4 hp with rfl | rfl | rfl | rfl <;>
  (try (exfalso; omega)) <;>
  rcases lt_cases8 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractByte, replaceHalfword]

theorem extract1_replace4_in (w : Word) (q p : Nat) (x : BitVec 32) (hq : q < 8) (hp : p < 2)
    (h : 4 * p ≤ 1 * q ∧ 1 * q + 1 ≤ 4 * p + 4) :
    extractByte (replaceWord32 w p x) q = extractByte (x.zeroExtend 64) (q - 4 * p) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases8 hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases lt_cases2 hp with rfl | rfl <;>
  (try (exfalso; omega)) <;>
  rcases lt_cases8 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractByte, replaceWord32]

theorem extract2_replace4_in (w : Word) (q p : Nat) (x : BitVec 32) (hq : q < 4) (hp : p < 2)
    (h : 4 * p ≤ 2 * q ∧ 2 * q + 2 ≤ 4 * p + 4) :
    extractHalfword (replaceWord32 w p x) q = extractHalfword (x.zeroExtend 64) (q - 2 * p) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rcases lt_cases4 hq with rfl | rfl | rfl | rfl <;>
  rcases lt_cases2 hp with rfl | rfl <;>
  (try (exfalso; omega)) <;>
  rcases lt_cases16 hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp [extractHalfword, replaceWord32]

theorem getElem!_replicate_word (n i : Nat) (x : Word) (h : i < n) : (List.replicate n x)[i]! = x := by
  simp [h]

end AsmVerif.RiscV.Sym
