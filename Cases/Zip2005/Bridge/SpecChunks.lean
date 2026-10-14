import Cases.Zip2005.Bridge.SpecMul
import Cases.Zip2005.Sinsemilla.NoteBits
import Cases.Zip2005.Orchard.CommitIvk
import Cases.Zip2005.Orchard.NoteCommitDerive
import Cases.Zip2005.Spec.Zip2005.Imported

/-!
# The guest's message bytes are the spec's chunks

`Vec<bool>::from_iter` lays a Sinsemilla message out as one `0`/`1` byte per bit
(`boolBytesToWords`), and `hash_to_point` reads ten at a time (`chunks`). `chunks_eq_chunksOf`:
for bytes spelling the bits of `M`, those chunks are the spec's `chunksOf M` (`bitrange` of `K = 10`
bits). Instances: `ivk_chunks` (`CommitIvk`, `ak ‖ nk`) and `note_chunks` (`NoteCommit`,
`g★_d ‖ pk★_d ‖ v ‖ ρ ‖ ψ`), each against ironwood's `commitIvkChunks` / `noteCommitChunks`.
-/

namespace Cases.Zip2005.SpecMul

open RiscvZkvm.Rv64
open Zcash.Circuits.Specs (bitrange K)
open Zcash.Circuits.Specs.Sinsemilla (chunksOf commitIvkChunks commitIvkMessage noteCommitChunks
  noteCommitMessage)

set_option autoImplicit false

theorem bitsVal_congr {f g : ℕ → Bool} : ∀ (m i : ℕ), (∀ k, k < m → f (i + k) = g (i + k)) →
    bitsVal f i m = bitsVal g i m
  | 0, _, _ => rfl
  | m + 1, i, h => by
    have h0 := h 0 (by omega)
    rw [Nat.add_zero] at h0
    have ih := bitsVal_congr (f := f) (g := g) m (i + 1) (fun k hk => by
      have := h (k + 1) (by omega); rw [show i + (k + 1) = i + 1 + k by omega] at this; exact this)
    rw [bitsVal, bitsVal, h0, ih]

theorem toNat_bw (b : Bool) : (bw b).toNat = if b then 1 else 0 := by
  cases b <;> rfl

/-- A chunk of a `0`/`1` byte string is the ten bits it covers. -/
theorem chunkVal_bits (b : ℕ → Bool) (W j : ℕ) (h : 10 * j + 10 ≤ 8 * W) :
    chunkVal (boolBytesToWords b W) j = bitsVal b (10 * j) 10 := by
  unfold chunkVal
  rw [show List.range 10 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] from rfl]
  simp only [List.foldl, bitsVal, Nat.add_zero]
  rw [byteAt_boolBytesToWords b W _ (by omega), byteAt_boolBytesToWords b W _ (by omega),
    byteAt_boolBytesToWords b W _ (by omega), byteAt_boolBytesToWords b W _ (by omega),
    byteAt_boolBytesToWords b W _ (by omega), byteAt_boolBytesToWords b W _ (by omega),
    byteAt_boolBytesToWords b W _ (by omega), byteAt_boolBytesToWords b W _ (by omega),
    byteAt_boolBytesToWords b W _ (by omega), byteAt_boolBytesToWords b W _ (by omega)]
  simp only [toNat_bw, show 10 * j + 1 + 1 = 10 * j + 2 by omega, show 10 * j + 2 + 1 = 10 * j + 3 by omega,
    show 10 * j + 3 + 1 = 10 * j + 4 by omega, show 10 * j + 4 + 1 = 10 * j + 5 by omega,
    show 10 * j + 5 + 1 = 10 * j + 6 by omega, show 10 * j + 6 + 1 = 10 * j + 7 by omega,
    show 10 * j + 7 + 1 = 10 * j + 8 by omega, show 10 * j + 8 + 1 = 10 * j + 9 by omega]
  ring

theorem bitrange_eq_bitsVal (M s n : ℕ) : bitrange M s n = bitsVal (fun j => M.testBit j) s n := by
  rw [bitsVal_testBit, bitrange, Nat.shiftRight_eq_div_pow]

/-- The guest's chunks of a `0`/`1` byte string spelling the bits of `M` are `chunksOf M`. -/
theorem chunks_eq_chunksOf (b : ℕ → Bool) (W n M : ℕ) (hW : 10 * n ≤ 8 * W)
    (hb : ∀ i, i < 10 * n → b i = M.testBit i) : chunks (boolBytesToWords b W) n = chunksOf M n := by
  unfold chunks chunksOf
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  rw [chunkVal_bits b W j (by omega), bitrange_eq_bitsVal, show K * j = 10 * j by simp [K],
    show K = 10 from rfl]
  exact bitsVal_congr 10 _ (fun k hk => hb _ (by omega))

theorem wbit (x : Word) (k : ℕ) :
    decide ((x >>> k) &&& 1#64 = 1#64) = x.toNat.testBit k := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  congr 1
  rw [← BitVec.toNat_inj, BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]

theorem wordsBit_natToLeLimbs (v i : ℕ) (hi : i < 256) :
    wordsBit (Accel.natToLeLimbs 4 v) i = v.testBit i := by
  unfold wordsBit
  rw [natToLeLimbs_getElem! (by omega), wbit _ _, BitVec.toNat_ofNat,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  have : i % 64 < 64 := Nat.mod_lt _ (by decide)
  simp only [this, decide_true, Bool.true_and]
  congr 1
  omega

theorem testBit_lt_two_pow {x k : ℕ} (hx : x < 2 ^ k) (i : ℕ) (hi : k ≤ i) : x.testBit i = false :=
  Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hi))

/-- 's message bits as the guest lays them out are . -/
theorem ivk_chunks (a n : ℕ) (ha : a < 2 ^ 255) :
    chunks (boolBytesToWords (ivkBit (Accel.natToLeLimbs 4 a) (Accel.natToLeLimbs 4 n)) 65) 51 =
      commitIvkChunks a n := by
  unfold commitIvkChunks
  refine chunks_eq_chunksOf _ 65 51 _ (by decide) (fun i hi => ?_)
  rw [commitIvkMessage, add_comm, Nat.testBit_two_pow_mul_add _ ha, ivkBit]
  split
  · exact wordsBit_natToLeLimbs _ _ (by omega)
  · exact wordsBit_natToLeLimbs _ _ (by omega)

/-- The note commitment's message as the guest lays it out ('s bits) is
, for the points' 256-bit encodings ,  (). -/
theorem note_chunks (gx gy kx ky rho psi : ℕ) (v : Word) (hgx : gx < 2 ^ 255) (hgy : gy < 2)
    (hkx : kx < 2 ^ 255) (hky : ky < 2) (hr : rho < 2 ^ 255) (hp : psi < 2 ^ 255) :
    chunks (boolBytesToWords (noteBit (Accel.natToLeLimbs 4 (gx + 2 ^ 255 * gy))
      (Accel.natToLeLimbs 4 (kx + 2 ^ 255 * ky)) v (Accel.natToLeLimbs 4 rho)
      (Accel.natToLeLimbs 4 psi)) 137) 109 =
      noteCommitChunks gx gy kx ky v.toNat rho psi := by
  unfold noteCommitChunks
  refine chunks_eq_chunksOf _ 137 109 _ (by decide) (fun i hi => ?_)
  have hG : gx + 2 ^ 255 * gy < 2 ^ 256 := by omega
  have hK : kx + 2 ^ 255 * ky < 2 ^ 256 := by omega
  have hv : v.toNat < 2 ^ 64 := v.isLt
  have e : noteCommitMessage gx gy kx ky v.toNat rho psi =
      2 ^ 256 * (2 ^ 256 * (2 ^ 64 * (2 ^ 255 * psi + rho) + v.toNat) + (kx + 2 ^ 255 * ky)) +
        (gx + 2 ^ 255 * gy) := by
    unfold noteCommitMessage
    rw [show (2 : ℕ) ^ 511 = 2 ^ 256 * 2 ^ 255 by rw [← pow_add],
      show (2 : ℕ) ^ 512 = 2 ^ 256 * 2 ^ 256 by rw [← pow_add],
      show (2 : ℕ) ^ 576 = 2 ^ 256 * 2 ^ 256 * 2 ^ 64 by rw [← pow_add, ← pow_add],
      show (2 : ℕ) ^ 831 = 2 ^ 256 * 2 ^ 256 * 2 ^ 64 * 2 ^ 255 by rw [← pow_add, ← pow_add, ← pow_add]]
    ring
  rw [e, Nat.testBit_two_pow_mul_add _ hG, noteBit]
  by_cases h1 : i < 256
  · rw [if_pos h1, if_pos h1]; exact wordsBit_natToLeLimbs _ _ h1
  rw [if_neg h1, if_neg h1, Nat.testBit_two_pow_mul_add _ hK]
  by_cases h2 : i < 512
  · rw [if_pos h2, if_pos (by omega : i - 256 < 256)]; exact wordsBit_natToLeLimbs _ _ (by omega)
  rw [if_neg h2, if_neg (by omega : ¬ i - 256 < 256), Nat.testBit_two_pow_mul_add _ hv]
  by_cases h3 : i < 576
  · rw [if_pos h3, if_pos (by omega : i - 256 - 256 < 64), wbit, show i - 256 - 256 = i - 512 by omega]
  rw [if_neg h3, if_neg (by omega : ¬ i - 256 - 256 < 64), Nat.testBit_two_pow_mul_add _ hr]
  by_cases h4 : i < 831
  · rw [if_pos h4, if_pos (by omega : i - 256 - 256 - 64 < 255), show i - 256 - 256 - 64 = i - 576 by omega]
    exact wordsBit_natToLeLimbs _ _ (by omega)
  rw [if_neg h4, if_neg (by omega : ¬ i - 256 - 256 - 64 < 255)]
  by_cases h5 : i < 1086
  · rw [if_pos h5, show i - 256 - 256 - 64 - 255 = i - 831 by omega]
    exact wordsBit_natToLeLimbs _ _ (by omega)
  · rw [if_neg h5, testBit_lt_two_pow hp _ (by omega)]

end Cases.Zip2005.SpecMul
