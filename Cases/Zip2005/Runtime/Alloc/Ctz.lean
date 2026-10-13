/-
  Cases.Zip2005.Runtime.Alloc.Ctz

  The lowest set bit, as `alloc` finds it: a de Bruijn multiply and a table in `.rodata`
  (phase D4). `ctz_ok` is the table's correctness (`bv_decide`); `load_tbl` reads the table
  through the doubleword memory `lbu` uses.
-/

import AsmVerif.RiscV.Exec.Tactic

namespace Cases.Zip2005.Runtime.Alloc

open RiscvZkvm.Rv64

/-! ## Counting trailing zeros: a de Bruijn table in `.rodata`

`alloc` finds the lowest set bit of a bitmap `w` as `T[((w & -w) * K) >> 58]`: `K` is the
de Bruijn constant at `0x780003f8`, `T` the 64-byte table at `0x78001540`. -/

/-- The constant, and the table's doublewords. -/
def K : Word := 0x0218a392cd3d5dbf#64

def tblW (j : Word) : Word :=
  if j = 0#64 then 0x13080d0307020100#64 else if j = 1#64 then 0x281422091c0e1904#64 else if j = 2#64 then 0x301d2e0f261a1105#64 else if j = 3#64 then 0x3929321536231f0a#64 else if j = 4#64 then 0x27211b18120c063f#64 else if j = 5#64 then 0x3831351e2f2d2510#64 else if j = 6#64 then 0x37342c2420170b3e#64 else 0x3a3b2a3c332b163d#64

/-- The table's byte at `j`. -/
def tbl (j : Word) : Word := (tblW (j >>> 3) >>> ((j &&& 7#64) * 8#64)) &&& 0xff#64

/-- Memory holds the constant and the table. -/
def RoOk (m : Word → Word) : Prop :=
  m 0x780003f8#64 = K ∧ ∀ j : Word, j < 8#64 → m (0x78001540#64 + (j <<< 3)) = tblW j

/-- **The lookup finds a set bit.** -/
theorem ctz_ok (w : Word) (hw : w ≠ 0#64) :
    tbl (((w &&& 0#64 - w) * K) >>> 58) < 64#64 ∧
      (w >>> tbl (((w &&& 0#64 - w) * K) >>> 58)) &&& 1#64 = 1#64 := by
  have : ∀ w : BitVec 64, w ≠ 0#64 →
      tbl (((w &&& 0#64 - w) * K) >>> 58) < 64#64 ∧
        (w >>> tbl (((w &&& 0#64 - w) * K) >>> 58)) &&& 1#64 = 1#64 := by
    intro w hw
    simp only [tbl, tblW, K]
    bv_decide
  exact this w hw

/-- The byte `lbu` reads at `T + idx` is the table's. -/
theorem load_tbl {m : Word → Word} (hro : RoOk m) {idx : Word} (hidx : idx < 64#64) :
    BitVec.zeroExtend 64 (extractByte (m (alignToDword (0x78001540#64 + idx)))
      (byteOffset (0x78001540#64 + idx))) = tbl idx := by
  have ha : alignToDword (0x78001540#64 + idx) = 0x78001540#64 + ((idx >>> 3) <<< 3) := by
    unfold alignToDword
    have : ∀ idx : BitVec 64, idx < 64#64 →
        (0x78001540#64 + idx) &&& ~~~7#64 = 0x78001540#64 + ((idx >>> 3) <<< 3) := by
      intro idx h; bv_decide
    exact this idx hidx
  have hb : byteOffset (0x78001540#64 + idx) = ((idx &&& 7#64) * 8#64).toNat / 8 := by
    unfold byteOffset
    have : ∀ idx : BitVec 64, (0x78001540#64 + idx) &&& 7#64 = idx &&& 7#64 := by
      intro idx; bv_decide
    rw [this idx]
    have h7 : (idx &&& 7#64).toNat < 8 := by
      rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    generalize idx &&& 7#64 = v at *
    rw [BitVec.toNat_mul, show (8#64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
    omega
  have hj : idx >>> 3 < 8#64 := by
    have : ∀ idx : BitVec 64, idx < 64#64 → idx >>> 3 < 8#64 := by intro idx h; bv_decide
    exact this idx hidx
  rw [ha, hb, hro.2 _ hj]
  unfold extractByte tbl
  have h8 : ((idx &&& 7#64) * 8#64).toNat / 8 * 8 = ((idx &&& 7#64) * 8#64).toNat := by
    have h7 : (idx &&& 7#64).toNat < 8 := by
      rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      omega
    generalize idx &&& 7#64 = v at *
    rw [BitVec.toNat_mul, show (8#64).toNat = 8 from rfl, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [h8, ← BitVec.ushiftRight_eq']
  generalize tblW (idx >>> 3) >>> ((idx &&& 7#64) * 8#64) = v
  have : ∀ v : BitVec 64, BitVec.zeroExtend 64 (BitVec.truncate 8 v) = v &&& 0xff#64 := by
    intro v; bv_decide
  exact this v

end Cases.Zip2005.Runtime.Alloc
