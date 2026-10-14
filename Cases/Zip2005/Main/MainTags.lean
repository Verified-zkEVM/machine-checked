import Cases.Zip2005.Witness.InstanceVisitor
import Cases.Zip2005.Witness.WitnessModel

/-!
# The `Result` tags `main` tests after the instance read

`Result<Zip2005Instance, Box<ErrorKind>>` keeps its discriminant in byte 0 of the struct (the
instance's bytes are `align(1)`, so they follow at offset 1): `0` for `Ok`, `1` for `Err`. These
are the facts the executor needs to decide `main`'s `bne` on that byte.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 AsmVerif.RiscV.Sym

/-- The `Ok` struct's tag byte. -/
theorem instW_tag (O W : List Word) : extractByte (instW O W)[0]! 0 = 0#8 := by
  have h0 : (instW O W)[0]! = word8 (instByte W 0) (instByte W 1) (instByte W 2) (instByte W 3)
      (instByte W 4) (instByte W 5) (instByte W 6) (instByte W 7) := rfl
  rw [h0, word8, extractByte_replaceByte_ne _ _ _ _ (by decide) (by decide),
    extractByte_replaceByte_ne _ _ _ _ (by decide) (by decide),
    extractByte_replaceByte_ne _ _ _ _ (by decide) (by decide),
    extractByte_replaceByte_ne _ _ _ _ (by decide) (by decide),
    extractByte_replaceByte_ne _ _ _ _ (by decide) (by decide),
    extractByte_replaceByte_ne _ _ _ _ (by decide) (by decide),
    extractByte_replaceByte_ne _ _ _ _ (by decide) (by decide),
    extractByte_replaceByte _ _ (by decide)]
  simp [instByte]

/-- `Ok(witness)`'s byte 1391 is the `negate` bool; the witness `Result`'s niche there is `2`. -/
theorem witW_negate (W V : List Word) : extractByte (witW W V)[173]! 7 = inByte W (witO4 W) 0 := by
  rw [witW_getElem! W V 173 (by decide), word8, extractByte_replaceByte _ _ (by decide)]
  simp only [witByte]
  rfl

theorem witW_negate_lt (W V : List Word) (l : Nat) (h : witOkCond W l) :
    (extractByte (witW W V)[173]! 7).toNat < 2 := by
  rw [witW_negate]; exact h.2.2.2.1

/-- The same over the struct as the visitor's continuation states it (`V = witW W V`). -/
theorem witW_negate_lt' {W V : List Word} {l : Nat} (hV : V = witW W V) (h : witOkCond W l) :
    (extractByte V[173]! 7).toNat < 2 := by
  have := witW_negate_lt W V l h
  rwa [← hV] at this

/-- `x &&& ~7` rounds down to a multiple of 8 (the hint vector capacities). -/
theorem and_round8 (x : Word) : (x &&& 18446744073709551608#64).toNat = x.toNat / 8 * 8 := by
  have h : x &&& 18446744073709551608#64 = (x >>> 3) <<< 3 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    interval_cases i <;> simp (config := {decide := true})
  rw [h, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  have := x.isLt
  have := Nat.div_mul_le_self x.toNat 8
  simp only [show (2 : Nat) ^ 3 = 8 from rfl]
  omega

/-- A hint vector of at least 128 bytes has a nonzero (indeed ≥ 128) rounded capacity. -/
theorem round8_ge (L : Word) (h : 128 ≤ L.toNat) (h' : L.toNat < 2 ^ 60) :
    128 ≤ (L + 7#64 &&& 18446744073709551608#64).toNat := by
  rw [and_round8, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- A nonempty hint vector has a nonzero rounded capacity. -/
theorem round8_pos (L : Word) (h : 1 ≤ L.toNat) (h' : L.toNat < 2 ^ 60) :
    8 ≤ (L + 7#64 &&& 18446744073709551608#64).toNat := by
  rw [and_round8, BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The `Err` struct's tag byte. -/
theorem errW_tag (w : Word) : extractByte (replaceByte w 0 1#8) 0 = 1#8 :=
  extractByte_replaceByte w 0 (by decide) 1#8

end Cases.Zip2005
