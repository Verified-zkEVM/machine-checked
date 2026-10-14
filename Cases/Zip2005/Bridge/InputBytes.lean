import Cases.Zip2005.Kit.ByteKit
import Cases.Zip2005.Blake2b.SpecBridge
import Cases.Zip2005.Bridge.Decode
import Cases.Zip2005.Runtime.Hint
import Cases.Zip2005.Precompile

/-!
# Input bytes as the words the guest reads

The guest reads each 32-byte field of its input as four little-endian doublewords. `wordsAt r o n`
is the `n` doublewords at byte offset `o` of the byte string `r`, and `field_wordsAt` says that
the field's bytes are those words' bytes (`stateBytes`), so `leos2ip` of the field is `leLimbsToNat`
of the words. `inByte_overlay`: the words `read_vec_raw` leaves (`hintWords` of the record laid
over the read window) give back the record's bytes.
-/

namespace Cases.Zip2005.Top

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel

set_option autoImplicit false

/-- The `n` little-endian doublewords at byte offset `o` of `r`. -/
def wordsAt (r : List (BitVec 8)) (o n : ℕ) : List Word :=
  (List.range n).map fun j => word8 r[o + 8 * j]! r[o + 8 * j + 1]! r[o + 8 * j + 2]! r[o + 8 * j + 3]!
    r[o + 8 * j + 4]! r[o + 8 * j + 5]! r[o + 8 * j + 6]! r[o + 8 * j + 7]!

theorem wordsAt_succ (r : List (BitVec 8)) (o n : ℕ) :
    wordsAt r o (n + 1) = word8 r[o]! r[o + 1]! r[o + 2]! r[o + 3]! r[o + 4]! r[o + 5]! r[o + 6]! r[o + 7]! ::
      wordsAt r (o + 8) n := by
  unfold wordsAt
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp, show o + 8 * (j + 1) = o + 8 + 8 * j by omega]

theorem byte_ofNat (w : Word) (i : ℕ) :
    UInt8.ofNat (w.toNat >>> (8 * i) % 256) = UInt8.ofBitVec (extractByte w i) := by
  rw [show UInt8.ofNat (w.toNat >>> (8 * i) % 256) =
    UInt8.ofBitVec (BitVec.ofNat 8 (w.toNat >>> (8 * i) % 256)) from rfl]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, extractByte, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.mul_comm i 8]
  omega

theorem wordBytes_word8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    Zip2005.Blake2b.wordBytes (word8 b0 b1 b2 b3 b4 b5 b6 b7).toNat =
      [b0, b1, b2, b3, b4, b5, b6, b7].map UInt8.ofBitVec := by
  unfold Zip2005.Blake2b.wordBytes
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, byte_ofNat]
  simp (disch := decide) only [byte_simp]

theorem field_wordsAt (r : List (BitVec 8)) (o n : ℕ) (h : o + 8 * n ≤ r.length) :
    field (r.map UInt8.ofBitVec) o (8 * n) =
      Zip2005.Blake2b.stateBytes ((wordsAt r o n).map BitVec.toNat) := by
  induction n generalizing o with
  | zero => simp [field, wordsAt, Zip2005.Blake2b.stateBytes]
  | succ n ih =>
    rw [wordsAt_succ, List.map_cons]
    unfold Zip2005.Blake2b.stateBytes
    rw [List.flatMap_cons, ← Zip2005.Blake2b.stateBytes, ← ih (o + 8) (by omega), wordBytes_word8]
    unfold field
    rw [show 8 * (n + 1) = 8 + 8 * n by omega, List.take_add, List.drop_drop]
    congr 1
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp only [List.length_take, List.length_drop, List.length_map] at h1
      simp only [List.getElem_take, List.getElem_drop, List.getElem_map]
      have hi : i < 8 := by simp at h2; omega
      interval_cases i <;> simp <;> rw [List.getElem?_eq_getElem (by omega)] <;> rfl

/-! ## The hint words of a record -/
theorem extractByte_zext8_shl32 (b : BitVec 8) (k : Nat) (hk : k < 8) :
    extractByte (BitVec.zeroExtend 64 b <<< 32) k = if k = 4 then b else 0#8 :=
  extractByte_zext8_shl b 4 k (by decide) hk

theorem extractByte_zext8_shl40 (b : BitVec 8) (k : Nat) (hk : k < 8) :
    extractByte (BitVec.zeroExtend 64 b <<< 40) k = if k = 5 then b else 0#8 :=
  extractByte_zext8_shl b 5 k (by decide) hk

theorem extractByte_zext8_shl48 (b : BitVec 8) (k : Nat) (hk : k < 8) :
    extractByte (BitVec.zeroExtend 64 b <<< 48) k = if k = 6 then b else 0#8 :=
  extractByte_zext8_shl b 6 k (by decide) hk

theorem extractByte_zext8_shl56 (b : BitVec 8) (k : Nat) (hk : k < 8) :
    extractByte (BitVec.zeroExtend 64 b <<< 56) k = if k = 7 then b else 0#8 :=
  extractByte_zext8_shl b 7 k (by decide) hk

theorem bytesToWordLE_word8 (bs : List (BitVec 8)) :
    bytesToWordLE bs = word8 (bs[0]?.getD 0) (bs[1]?.getD 0) (bs[2]?.getD 0) (bs[3]?.getD 0)
      (bs[4]?.getD 0) (bs[5]?.getD 0) (bs[6]?.getD 0) (bs[7]?.getD 0) := by
  unfold bytesToWordLE
  simp only [BitVec.shiftLeft_eq', show (8 : Word).toNat = 8 from rfl, show (16 : Word).toNat = 16 from rfl,
    show (24 : Word).toNat = 24 from rfl, show (32 : Word).toNat = 32 from rfl, show (40 : Word).toNat = 40 from rfl,
    show (48 : Word).toNat = 48 from rfl, show (56 : Word).toNat = 56 from rfl]
  apply word_ext
  intro k hk
  interval_cases k <;> simp (disch := decide) only [byte_simp, extractByte_zext8_shl32, extractByte_zext8_shl40, extractByte_zext8_shl48,
    extractByte_zext8_shl56]

theorem extractByte_bytesToWordLE (bs : List (BitVec 8)) (j : ℕ) (hj : j < 8) :
    extractByte (bytesToWordLE bs) j = bs[j]?.getD 0 := by
  rw [bytesToWordLE_word8]
  interval_cases j <;> simp (disch := decide) only [byte_simp]

/-- The hint words of a record, laid over the read window, give back the record's bytes. -/
theorem inByte_overlay (r : List (BitVec 8)) (J : List Word) (k : ℕ) (hk : k < r.length)
    (hJ : k / 8 < J.length) :
    inByte (overlay (hintWords r) J) 0 k = r[k]! := by
  unfold inByte overlay
  rw [Nat.zero_add, getElem!_pos _ _ (by simpa using hJ)]
  simp only [List.getElem_map, List.getElem_range, hintWords_length, show k / 8 < r.length / 8 + 1 by omega,
    if_true]
  unfold hintWords
  rw [getElem!_pos _ _ (by simp; omega)]
  simp only [List.getElem_map, List.getElem_range]
  rw [extractByte_bytesToWordLE _ _ (Nat.mod_lt _ (by decide)), List.getElem?_take,
    if_pos (Nat.mod_lt _ (by decide)), List.getElem?_drop, show 8 * (k / 8) + k % 8 = k by omega,
    List.getElem?_eq_getElem hk, Option.getD_some, getElem!_pos r k hk]

/-! ## Records -/

theorem leos2ip_take8 (I : List (BitVec 8)) (h : 8 ≤ I.length) :
    Zip2005.leos2ip ((inBytes I).take 8) = (bytesToWordLE (I.take 8)).toNat := by
  have e : (inBytes I).take 8 = field (I.map UInt8.ofBitVec) 0 (8 * 1) := by simp [field, inBytes]
  have hw : wordsAt I 0 1 = [bytesToWordLE (I.take 8)] := by
    rw [bytesToWordLE_word8]
    simp only [wordsAt, List.range_one, List.map_cons, List.map_nil, Nat.mul_zero,
      Nat.zero_add, List.getElem?_take]
    simp [List.getElem?_eq_getElem (show 0 < I.length by omega), List.getElem?_eq_getElem (show 1 < I.length by omega),
      List.getElem?_eq_getElem (show 2 < I.length by omega), List.getElem?_eq_getElem (show 3 < I.length by omega),
      List.getElem?_eq_getElem (show 4 < I.length by omega), List.getElem?_eq_getElem (show 5 < I.length by omega),
      List.getElem?_eq_getElem (show 6 < I.length by omega), List.getElem?_eq_getElem (show 7 < I.length by omega),
      getElem!_pos I 0 (by omega), getElem!_pos I 1 (by omega),
      getElem!_pos I 2 (by omega), getElem!_pos I 3 (by omega),
      getElem!_pos I 4 (by omega), getElem!_pos I 5 (by omega),
      getElem!_pos I 6 (by omega), getElem!_pos I 7 (by omega)]
  rw [e, field_wordsAt I 0 1 (by omega), Cases.Zip2005.leos2ip_stateBytes, hw]
  simp

/-- The first record of the input and the stream after it, with `L` its length word. -/
theorem record_inBytes (I : List (BitVec 8)) (h : 8 ≤ I.length) :
    record (inBytes I) = (inBytes ((I.drop 8).take (bytesToWordLE (I.take 8)).toNat),
      inBytes (I.drop (8 + (bytesToWordLE (I.take 8)).toNat))) := by
  unfold record
  rw [leos2ip_take8 I h]
  simp [inBytes, List.map_drop, List.map_take]

end Cases.Zip2005.Top
