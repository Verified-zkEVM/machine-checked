import Cases.Zip2005.Kit.Bytes
import Cases.Zip2005.Kit.ByteKit
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Field.Coordinates
import Cases.Zip2005.Sinsemilla.NoteBits

/-!
# Lemmas for `sinsemilla::Pad::next`

The arithmetic of one step of a `bitvec` cursor (`BitValIter`): the head bit `r < 64` as a
byte, the word pointer's carry, the `Take` count, `Pad`'s length, and the bit the step yields
as `wordsBit`. Shared by the `commit_ivk` and `NoteCommitment::derive` message iterators.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

set_option autoImplicit false

/-- The head byte after one step: `(r + 1) % 64`. -/
theorem headNext (r : Nat) (hr : r < 64) :
    BitVec.truncate 8 ((BitVec.zeroExtend 64 (BitVec.ofNat 8 r) &&& 255#64) + 1#64 &&& 63#64) =
      BitVec.ofNat 8 ((r + 1) % 64) := by
  interval_cases r <;> decide

/-- The word pointer's step: `8` when the head wraps, else `0`. -/
theorem ptrStep (r : Nat) (hr : r < 64) :
    ((BitVec.zeroExtend 64 (BitVec.ofNat 8 r) &&& 255#64) + 1#64) >>> 3 &&& 56#64 =
      if r = 63 then 8#64 else 0#64 := by
  interval_cases r <;> decide

/-- The `Take` count after one step. -/
theorem countNext (k : Nat) (hk : k ≤ 254) :
    BitVec.ofNat 64 (255 - k) + 18446744073709551615#64 = BitVec.ofNat 64 (255 - (k + 1)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, Bn.toNat_ofNat', Bn.toNat_ofNat', Bn.toNat_ofNat']
  omega

/-- `Pad`'s length after one step. -/
theorem lenNext (k : Nat) : BitVec.ofNat 64 k + 1#64 = BitVec.ofNat 64 (k + 1) := by
  rw [BitVec.ofNat_add]

/-- The low bit of a word as `bw` of the test the models use. -/
theorem bitVal (x : Word) : x &&& 1#64 = bw (decide (x &&& 1#64 = 1#64)) := by
  unfold bw
  by_cases h : x &&& 1#64 = 1#64
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    apply BitVec.eq_of_toNat_eq
    have h1 : (x &&& 1#64).toNat = x.toNat % 2 := by
      rw [BitVec.toNat_and, show (1#64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    have h3 : (x &&& 1#64).toNat ≠ 1 := fun e => h (BitVec.eq_of_toNat_eq (by rw [e]; rfl))
    simp only [BitVec.toNat_ofNat]
    omega

/-- The shift amount `srl` takes from the head byte. -/
theorem shiftAmt (r : Nat) (hr : r < 64) :
    (BitVec.zeroExtend 64 (BitVec.ofNat 8 r) &&& 255#64).toNat % 64 = r := by
  interval_cases r <;> decide

/-- The cursor's word pointer after one step from bit `k`: `base + 8 ((k + 1) / 64)`. -/
theorem ptrNext (sp c : Word) (k : Nat) :
    sp + (c + BitVec.ofNat 64 (8 * (k / 64))) + (if k % 64 = 63 then 8#64 else 0#64) =
      sp + c + BitVec.ofNat 64 (8 * ((k + 1) / 64)) := by
  rw [BitVec.add_assoc, BitVec.add_assoc, BitVec.add_assoc]
  congr 2
  split
  · rw [← BitVec.ofNat_add]
    congr 1; omega
  · rw [BitVec.add_zero]
    congr 2; omega

/-- The bit a step yields: word `k / 64` of the message shifted by `k % 64`, as `wordsBit`. -/
theorem bitNext (A : List Word) (k : Nat) :
    (A[k / 64]! >>> ((BitVec.zeroExtend 64 (BitVec.ofNat 8 (k % 64)) &&& 255#64).toNat % 64)) &&& 1#64 =
      bw (wordsBit A k) := by
  rw [shiftAmt (k % 64) (Nat.mod_lt _ (by decide)), wordsBit]
  exact bitVal _

/-- `seqz` of a cursor compared with its end: `0` when the pointers differ. -/
theorem seqz_or_xor (p e h : Word) (hpe : p ≠ e) :
    (if ((p ^^^ e) ||| h).ult 1#64 = true then 1#64 else 0#64) = 0#64 := by
  rw [if_neg]
  intro hlt
  have h0 : (p ^^^ e) ||| h = 0#64 := by
    apply BitVec.eq_of_toNat_eq
    have := BitVec.lt_def.mp (BitVec.ult_iff_lt.mp hlt)
    simp only [BitVec.toNat_ofNat] at this ⊢
    omega
  have h1 : p ^^^ e = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have := congrArg (fun w : Word => w.getLsbD i) h0
    simp only [BitVec.getLsbD_or, Bool.or_eq_false_iff, BitVec.getLsbD_zero] at this
    rw [this.1, BitVec.getLsbD_zero]
  apply hpe
  have := congrArg (fun w : Word => w ^^^ e) h1
  simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.zero_xor] using this

/-- A byte stored twice at the same position. -/
theorem replaceByte_replaceByte (w : Word) (k : Nat) (hk : k < 8) (a b : BitVec 8) :
    replaceByte (replaceByte w k a) k b = replaceByte w k b := by
  apply word_ext
  intro i hi
  by_cases h : k = i
  · subst h
    rw [extractByte_replaceByte _ _ hk, extractByte_replaceByte _ _ hk]
  · rw [extractByte_replaceByte_ne _ _ _ _ hi h, extractByte_replaceByte_ne _ _ _ _ hi h,
      extractByte_replaceByte_ne _ _ _ _ hi h]

/-- A bit value through `zext.b`: unchanged. -/
theorem bw_zext_trunc (b : Bool) : BitVec.zeroExtend 64 (BitVec.truncate 8 (bw b)) = bw b := by
  cases b <;> rfl

/-- A bit value through `andi 0xff`: unchanged. -/
theorem bw_and255 (b : Bool) : bw b &&& 255#64 = bw b := by
  cases b <;> rfl

/-- A bit value is never the iterator's `None` (2). -/
theorem bw_ne_two (b : Bool) : (bw b == 2#64) = false := by
  cases b <;> rfl

/-- A twelve-word list by its cells. -/
theorem list12_cells (I : List Word) (h : I.length = 12) : I = [I[0]!, I[1]!, I[2]!, I[3]!, I[4]!, I[5]!, I[6]!, I[7]!, I[8]!, I[9]!, I[10]!, I[11]!] := by
  match I, h with
  | [_, _, _, _, _, _, _, _, _, _, _, _], _ => rfl

end Cases.Zip2005
