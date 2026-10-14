import Cases.Zip2005.Sinsemilla.SinsemillaModel
import Cases.Zip2005.Field.Coordinates

/-!
# The note-commitment message as the guest lays it out

`NoteCommitment::derive` hashes `g★_d ‖ pk★_d ‖ I2LEBSP_64(v) ‖ I2LEBSP_255(ρ) ‖ I2LEBSP_255(ψ)`
(1086 bits), padded by `Pad` with zero bits to 1090 = 109 · 10. `Vec<bool>::from_iter` materialises
it as 1090 bytes, each `0` or `1`, which `hash_to_point_inner` reads ten at a time. The `Vec`'s
spare capacity after byte 1090 is whatever the allocation held, so a contract about it fixes
the bytes below 1090 only (`byteAt … o = bw (bit o)`); `boolBytesToWords` is the canonical
image the models are stated over, and `chunks_ext` says the chunk fold sees no difference.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64

/-- Bit `i` (little-endian, `Lsb0`) of a byte string given as words. -/
def wordsBit (ws : List Word) (i : Nat) : Bool := (ws[i / 64]! >>> (i % 64)) &&& 1#64 = 1#64

/-- The message bit `i` of the note commitment: `g★_d` (256 bits of its 32-byte encoding),
`pk★_d`, `v` (64 bits), `ρ` (255 bits), `ψ` (255 bits), then zero padding. -/
def noteBit (gd pkd : List Word) (v : Word) (rho psi : List Word) (i : Nat) : Bool :=
  if i < 256 then wordsBit gd i
  else if i < 512 then wordsBit pkd (i - 256)
  else if i < 576 then (v >>> (i - 512)) &&& 1#64 = 1#64
  else if i < 831 then wordsBit rho (i - 576)
  else if i < 1086 then wordsBit psi (i - 831)
  else false

/-- Byte `k` of word `j` of a `0`/`1` byte string: bit `8 j + k` in place. -/
def bitByteW (b : Nat → Bool) (j k : Nat) : Word := if b (8 * j + k) then 1#64 <<< (8 * k) else 0#64

/-- Word `j` of a `0`/`1` byte string: its eight bytes. -/
def bitsWord (b : Nat → Bool) (j : Nat) : Word :=
  bitByteW b j 0 ||| bitByteW b j 1 ||| bitByteW b j 2 ||| bitByteW b j 3 |||
    bitByteW b j 4 ||| bitByteW b j 5 ||| bitByteW b j 6 ||| bitByteW b j 7

/-- `n` words of the `0`/`1` bytes `b i`, little-endian. -/
def boolBytesToWords (b : Nat → Bool) (n : Nat) : List Word := (List.range n).map (bitsWord b)

/-- The 1090 message bytes as 137 words (`noteBit` is `false` from bit 1086 on). -/
def noteBitsW (gd pkd : List Word) (v : Word) (rho psi : List Word) : List Word :=
  boolBytesToWords (noteBit gd pkd v rho psi) 137

theorem boolBytesToWords_length (b : Nat → Bool) (n : Nat) : (boolBytesToWords b n).length = n := by
  simp [boolBytesToWords]

theorem noteBitsW_length (gd pkd : List Word) (v : Word) (rho psi : List Word) :
    (noteBitsW gd pkd v rho psi).length = 137 := boolBytesToWords_length _ _

theorem getLsbD_bitByteW (b : Nat → Bool) (j k i : Nat) :
    (bitByteW b j k).getLsbD i = (b (8 * j + k) && decide (i = 8 * k) && decide (i < 64)) := by
  unfold bitByteW
  split
  · simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_one, Bool.true_and, *]
    by_cases h : i = 8 * k
    · subst h; simp
    · have : ¬ (i - 8 * k = 0 ∧ ¬ i < 8 * k) := by omega
      simp only [h, decide_false, Bool.false_and]
      by_cases h1 : i < 8 * k <;> by_cases h2 : i - 8 * k = 0 <;> simp_all
  · simp [*]

theorem getLsbD_ite01 (c : Prop) [Decidable c] (i : Nat) :
    (if c then 1#8 else 0#8).getLsbD i = (decide c && decide (i = 0)) := by
  split <;> simp [*]

theorem extractByte_bitsWord (b : Nat → Bool) (j k : Nat) (hk : k < 8) :
    extractByte (bitsWord b j) k = if b (8 * j + k) then 1#8 else 0#8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight, bitsWord, BitVec.getLsbD_or, getLsbD_bitByteW, hi, decide_true,
    Bool.true_and, getLsbD_ite01]
  interval_cases k <;> interval_cases i <;> simp

/-- Byte `o` of the canonical image is the bit. -/
theorem byteAt_boolBytesToWords (b : Nat → Bool) (n o : Nat) (ho : o < 8 * n) :
    byteAt (boolBytesToWords b n) o = bw (b o) := by
  unfold byteAt boolBytesToWords
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  rw [extractByte_bitsWord _ _ _ (Nat.mod_lt _ (by omega)), Nat.div_add_mod]
  unfold bw
  split <;> rfl

theorem chunkVal_ext {A B : List Word} (j : Nat)
    (h : ∀ k, k < 10 → byteAt A (10 * j + k) = byteAt B (10 * j + k)) : chunkVal A j = chunkVal B j := by
  unfold chunkVal
  rw [show List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from rfl]
  simp only [List.foldl]
  rw [h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega), h 6 (by omega), h 7 (by omega), h 8 (by omega), h 9 (by omega)]

/-- Two byte strings agreeing below `10 n` have the same first `n` chunks. -/
theorem chunks_ext {A B : List Word} (n : Nat) (h : ∀ o, o < 10 * n → byteAt A o = byteAt B o) :
    chunks A n = chunks B n := by
  unfold chunks
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  exact chunkVal_ext j (fun k hk => h _ (by omega))

end Cases.Zip2005
