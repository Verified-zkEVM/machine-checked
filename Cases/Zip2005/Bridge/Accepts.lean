import Cases.Zip2005.Bridge.SpecGuestA2
import Cases.Zip2005.Bridge.InputBytes

/-!
# `GuestW` over the input records is `GuestAccepts`

`guestAccepts_of`: when every word `GuestW` names is the input's — the instance's `rk` and `nf`,
and the witness's `sk`, `ak`, `nk`, `rivk_ext`, `rivk`, `g_d`, `ρ`, `rseed` and `value`, each the
little-endian words at its bincode offset (`wordsAt`) — and `α` (Montgomery) and `negate` read back
to the witness's, then the input decodes (`Decodes`) and the guest's statement holds
(`GuestAccepts`). The instance's anchor and sighash, which the guest never checks, are taken as the
input has them.
-/

namespace Cases.Zip2005.Top

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel
open Zcash.Circuits (Fp Fq Point)

set_option autoImplicit false

theorem leos2ip_field (r : List (BitVec 8)) (o : ℕ) (h : o + 32 ≤ r.length) :
    Zip2005.leos2ip (field (inBytes r) o 32) = leLimbsToNat (wordsAt r o 4) := by
  rw [inBytes, field_wordsAt r o 4 (by omega), Cases.Zip2005.leos2ip_stateBytes]

theorem wordsAt_four (r : List (BitVec 8)) (o : ℕ) :
    wordsAt r o 4 = [(wordsAt r o 4)[0]!, (wordsAt r o 4)[1]!, (wordsAt r o 4)[2]!, (wordsAt r o 4)[3]!] :=
  four_eta _ (by simp [wordsAt])

/-- A scalar parsed by `from_repr` (Montgomery form, `natToLeLimbs`) reads back to its integer. -/
theorem fq_parse_val (a : ℕ) (ha : a < Cases.Zip2005.Fq.q) :
    (((leLimbsToNat (natToLeLimbs 4 (Cases.Zip2005.Fq.mul a Cases.Zip2005.Fq.R2)) * Cases.Zip2005.Fq.rInv % Cases.Zip2005.Fq.q : ℕ) : Fq)).val = a := by
  rw [fq_natToLe_val _ (by rw [fq_mul_R2]; exact Nat.mod_lt _ Cases.Zip2005.Fq.q_pos), fq_mul_R2, Cases.Zip2005.Fq.mont_back,
    Nat.mod_eq_of_lt ha, ZMod.val_natCast, Cases.Zip2005.Fq.q_card, Nat.mod_eq_of_lt ha]

/-- **The input decodes and the guest's statement holds.** `r1`, `r2`: the instance and witness
records' bytes. -/
theorem guestAccepts_of (I r1 r2 : List (BitVec 8)) (al : List Word) (neg : Word)
    (hI1 : instRec I = inBytes r1) (hI2 : witRec I = inBytes r2)
    (hl1 : 128 ≤ r1.length) (hl2 : 297 ≤ r2.length) (hwl : negOff (inBytes r2) + 1 ≤ r2.length)
    (htag : r2[0]! = 1#8)
    (hal : ((leLimbsToNat al * Cases.Zip2005.Fq.rInv % Cases.Zip2005.Fq.q : ℕ) : Fq).val = leLimbsToNat (wordsAt r2 33 4))
    (hnb : (inBytes r2)[negOff (inBytes r2)]!.toNat < 2)
    (hneg : (!(neg == 0#64)) = ((inBytes r2)[negOff (inBytes r2)]! == 1))
    (hG : GuestW (wordsAt r1 32 4) (wordsAt r1 64 4) (wordsAt r2 65 4) (wordsAt r2 97 4)
      (wordsAt r2 129 4) (wordsAt r2 161 4) (wordsAt r2 193 4) (wordsAt r2 225 4) (wordsAt r2 257 4) al
      (wordsAt r2 1 4)[0]! (wordsAt r2 1 4)[1]! (wordsAt r2 1 4)[2]! (wordsAt r2 1 4)[3]! neg
      (wordsAt r2 289 1)[0]!) :
    GuestAccepts I := by
  obtain ⟨rkP, akP, nk, rivkExt, rivk, gd, ρ, hrkv, hrkr, hf, hakv, hakr, hnk, hrx, hri, hgv, hgr, hρ, hall⟩ := hG
  let pi : Zip2005.PrimaryInput :=
    { rtOrchard := ((Zip2005.leos2ip (field (instRec I) 0 32) : ℕ) : Fp), rk := rkP,
      nf := ((leLimbsToNat (wordsAt r1 64 4) : ℕ) : Fp), sighash := field (instRec I) 96 32 }
  have hS := hall pi rfl rfl
  rw [← wordsAt_four] at hS
  refine ⟨pi, _, _, _, akP, nk, rivkExt, rivk, _, gd, _, ρ, ?_, hS⟩
  refine ⟨by rw [hI1]; simpa [inBytes] using hl1, rfl,
    ⟨hrkv, by rw [hrkr, hI1, leos2ip_field r1 32 (by omega)]⟩, ?_, rfl,
    ?_, ?_, ?_, ⟨hakv, by rw [hakr, hI2, leos2ip_field r2 65 (by omega)]⟩, ?_, ?_, ?_,
    ⟨hgv, by rw [hgr, hI2, leos2ip_field r2 193 (by omega)]⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show (((leLimbsToNat (wordsAt r1 64 4) : ℕ) : Fp)).val = _
    rw [ZMod.val_natCast, Fp.p_card, Nat.mod_eq_of_lt hf, hI1, leos2ip_field r1 64 (by omega)]
  · rw [hI2, inBytes, getElem!_pos _ 0 (by simp; omega), List.getElem_map, ← getElem!_pos r2 0 (by omega), htag]
    rfl
  · rw [hI2, inBytes, show (32 : ℕ) = 8 * 4 from rfl, field_wordsAt r2 1 4 (by omega)]
  · rw [hal, hI2, leos2ip_field r2 33 (by omega)]
  · rw [hnk, hI2, leos2ip_field r2 97 (by omega)]
  · rw [hrx, hI2, leos2ip_field r2 129 (by omega)]
  · rw [hri, hI2, leos2ip_field r2 161 (by omega)]
  · rw [hρ, hI2, leos2ip_field r2 225 (by omega)]
  · rw [hI2, inBytes, show (32 : ℕ) = 8 * 4 from rfl, field_wordsAt r2 257 4 (by omega)]
  · have h1 : wordsAt r2 289 1 = [(wordsAt r2 289 1)[0]!] := by simp [wordsAt]
    have h2 := field_wordsAt r2 289 1 (by omega)
    rw [Nat.mul_one] at h2
    rw [hI2, inBytes, h2, Cases.Zip2005.leos2ip_stateBytes, h1]
    simp
  · rw [hI2]; exact hnb
  · rw [hI2]; exact hneg
  · rw [hI2]; simpa [inBytes] using hwl

end Cases.Zip2005.Top
