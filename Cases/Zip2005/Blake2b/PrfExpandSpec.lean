import Cases.Zip2005.Blake2b.Blake2bSpec
import Cases.Zip2005.Spec.Zip2005.Prf
import Mathlib.Tactic.IntervalCases

/-!
# `PRF^expand` on one block, against the specification

`PrfExpand::with` / `apply` hash `sk ‖ [d] ‖ ts` (33, 65 or 97 bytes, always one block) with
BLAKE2b-512 personalised `"Zcash_ExpandSeed"`. The machine side (`Proof/PrfExpand*.lean`) leaves the
eight words `Cases.Zip2005.B2b.compress prfH M L 0 (all ones) 0` in the output, `M` the message words as the
compression loop assembles them. This file shows those words serialise to
`Zip2005.prfExpand sk (d :: ts)`:

* `blake2b_one_block`: for `1 ≤ |msg| ≤ 128`, BLAKE2b is a single final compression;
* `prfH_toNat`: the parameter block for 64-byte output, no key, the personalisation;
* `leos2ip_wordBytes`: a word's eight little-endian bytes read back to the word;
* `prfExpand33_eq` (and the 65/97-byte forms): the machine words' bytes are the spec's output.
-/

namespace Cases.Zip2005.B2b

open RiscvZkvm.Rv64 _root_.Zip2005 _root_.Zip2005.Blake2b

set_option autoImplicit false

/-! ### BLAKE2b on one block -/

theorem blake2b_one_block (personal msg : List UInt8) (h1 : 1 ≤ msg.length) (h2 : msg.length ≤ 128) :
    blake2b personal 64 msg =
      stateBytes (Blake2b.compress (initialState 64 0 [] personal) (leWords msg 0 16) msg.length 0 true) := by
  have hdd : blockCount msg.length = 1 := by
    unfold blockCount blockBytes
    have : (msg.length + 128 - 1) / 128 = 1 := by omega
    rw [this]; rfl
  simp only [blake2b, hdd, Nat.sub_self, absorbAux, Nat.zero_mul]
  rw [List.take_of_length_le (by simp)]

/-! ### The parameter block -/

/-- The initial chaining state for `PRF^expand`: `IV` with the parameter block for 64-byte output,
    no key, fanout and depth 1, and the personalisation `"Zcash_ExpandSeed"` in words 6 and 7. -/
def prfH : List Word :=
  [0x6A09E667F3BCC908#64 ^^^ 0x01010040#64, 0xBB67AE8584CAA73B#64, 0x3C6EF372FE94F82B#64,
   0xA54FF53A5F1D36F1#64, 0x510E527FADE682D1#64, 0x9B05688C2B3E6C1F#64,
   0x1F83D9ABFB41BD6B#64 ^^^ 0x78455f687361635a#64, 0x5BE0CD19137E2179#64 ^^^ 0x64656553646e6170#64]

theorem prfH_toNat : prfH.map BitVec.toNat = initialState 64 0 [] prfExpandPersonalisation := by
  decide

/-! ### Bytes and words -/

theorem leos2ip_wordBytes (w : Word) : leos2ip (wordBytes w.toNat) = w.toNat := by
  have hw := w.isLt
  simp only [wordBytes, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.map_cons, List.map_nil,
    leos2ip_cons, leos2ip_nil, UInt8.toNat_ofNat', Nat.reducePow, Nat.shiftRight_eq_div_pow]
  omega

theorem wordBytes_length (w : Nat) : (wordBytes w).length = 8 := by
  simp [wordBytes]

theorem leos2ip_byte (d : Word) :
    leos2ip [UInt8.ofNat d.toNat] = (BitVec.zeroExtend 64 (BitVec.truncate 8 d)).toNat := by
  simp only [leos2ip_cons, leos2ip_nil, UInt8.toNat_ofNat', Nat.reducePow, BitVec.toNat_setWidth,
    BitVec.truncate_eq_setWidth]
  omega

/-- `leWords` on a concrete byte list: `drop`/`take` by the eight-byte groups. -/
theorem leWords_16 (msg : List UInt8) :
    leWords msg 0 16 = (List.range 16).map (fun i => leos2ip ((msg.drop (8 * i)).take 8)) := by
  simp only [leWords, Nat.zero_add]

/-! ### `PRF^expand(sk, [d])`: 33 bytes -/

/-- The message of `PRF^expand(sk, [d])` for a 32-byte `sk`, as sixteen words. -/
theorem leWords33 (s0 s1 s2 s3 d : Word) :
    leWords (stateBytes ([s0, s1, s2, s3].map BitVec.toNat) ++ [UInt8.ofNat d.toNat]) 0 16 =
      [s0.toNat, s1.toNat, s2.toNat, s3.toNat, (BitVec.zeroExtend 64 (BitVec.truncate 8 d)).toNat,
       0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  rw [← leos2ip_wordBytes s0, ← leos2ip_wordBytes s1, ← leos2ip_wordBytes s2, ← leos2ip_wordBytes s3,
    ← leos2ip_byte d]
  simp only [leWords_16, stateBytes, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, wordBytes, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    show List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from rfl,
    List.cons_append, List.nil_append, Nat.reduceMul, List.drop_succ_cons, List.drop_zero, List.take_succ_cons,
    List.take_zero, List.drop_nil, List.take_nil, leos2ip_nil]

theorem prfExpand33_eq (s0 s1 s2 s3 d : Word) :
    stateBytes ((compress prfH [s0, s1, s2, s3, BitVec.zeroExtend 64 (BitVec.truncate 8 d),
      0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]
      33#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64).map BitVec.toNat) =
    prfExpand (stateBytes ([s0, s1, s2, s3].map BitVec.toNat)) [UInt8.ofNat d.toNat] := by
  have hb := compress_toNat (0x6A09E667F3BCC908#64 ^^^ 0x01010040#64) 0xBB67AE8584CAA73B#64 0x3C6EF372FE94F82B#64
    0xA54FF53A5F1D36F1#64 0x510E527FADE682D1#64 0x9B05688C2B3E6C1F#64
    (0x1F83D9ABFB41BD6B#64 ^^^ 0x78455f687361635a#64) (0x5BE0CD19137E2179#64 ^^^ 0x64656553646e6170#64)
    s0 s1 s2 s3 (BitVec.zeroExtend 64 (BitVec.truncate 8 d)) 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64
    33#64 0#64 true
  rw [if_pos rfl] at hb
  have hH := prfH_toNat
  unfold prfH at hH ⊢
  rw [hb, prfExpand, blake2b512]
  have hlen : (stateBytes ([s0, s1, s2, s3].map BitVec.toNat) ++ [UInt8.ofNat d.toNat]).length = 33 := by
    simp only [List.length_append, stateBytes_length, List.length_map, List.length_cons, List.length_nil]
  rw [blake2b_one_block _ _ (by omega) (by omega), hlen, leWords33]
  simp only [List.map_cons, List.map_nil] at hH
  rw [hH]
  rfl

/-! ### `PRF^expand(sk, [d] ‖ t…)`: 65 and 97 bytes

The machine shifts each 32-byte `t` up one byte behind `d`, so message word `i` is `(tᵢ <<< 8) ||| (tᵢ₋₁ >>> 56)`.
These read each such word byte by byte. -/

/-- A word's serialisation, byte `j` as `extractByte w j`. -/
theorem wordBytes_extract (w : Word) : wordBytes w.toNat =
    [UInt8.ofNat (extractByte w 0).toNat, UInt8.ofNat (extractByte w 1).toNat, UInt8.ofNat (extractByte w 2).toNat,
     UInt8.ofNat (extractByte w 3).toNat, UInt8.ofNat (extractByte w 4).toNat, UInt8.ofNat (extractByte w 5).toNat,
     UInt8.ofNat (extractByte w 6).toNat, UInt8.ofNat (extractByte w 7).toNat] := by
  simp [wordBytes, extractByte, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, Nat.shiftRight_eq_div_pow]

theorem u8_trunc (d : Word) : UInt8.ofNat (BitVec.truncate 8 d).toNat = UInt8.ofNat d.toNat := by
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofNat', BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  omega

theorem ext_up_0 (a b : Word) : extractByte ((a <<< 8) ||| (b >>> 56)) 0 = extractByte b 7 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_upd_0 (a d : Word) : extractByte ((a <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d)) 0 = BitVec.truncate 8 d := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_top_0 (b : Word) : extractByte (b >>> 56) 0 = extractByte b 7 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_up_1 (a b : Word) : extractByte ((a <<< 8) ||| (b >>> 56)) 1 = extractByte a 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_upd_1 (a d : Word) : extractByte ((a <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d)) 1 = extractByte a 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_top_1 (b : Word) : extractByte (b >>> 56) 1 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_up_2 (a b : Word) : extractByte ((a <<< 8) ||| (b >>> 56)) 2 = extractByte a 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_upd_2 (a d : Word) : extractByte ((a <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d)) 2 = extractByte a 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_top_2 (b : Word) : extractByte (b >>> 56) 2 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_up_3 (a b : Word) : extractByte ((a <<< 8) ||| (b >>> 56)) 3 = extractByte a 2 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_upd_3 (a d : Word) : extractByte ((a <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d)) 3 = extractByte a 2 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_top_3 (b : Word) : extractByte (b >>> 56) 3 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_up_4 (a b : Word) : extractByte ((a <<< 8) ||| (b >>> 56)) 4 = extractByte a 3 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_upd_4 (a d : Word) : extractByte ((a <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d)) 4 = extractByte a 3 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_top_4 (b : Word) : extractByte (b >>> 56) 4 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_up_5 (a b : Word) : extractByte ((a <<< 8) ||| (b >>> 56)) 5 = extractByte a 4 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_upd_5 (a d : Word) : extractByte ((a <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d)) 5 = extractByte a 4 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_top_5 (b : Word) : extractByte (b >>> 56) 5 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_up_6 (a b : Word) : extractByte ((a <<< 8) ||| (b >>> 56)) 6 = extractByte a 5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_upd_6 (a d : Word) : extractByte ((a <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d)) 6 = extractByte a 5 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_top_6 (b : Word) : extractByte (b >>> 56) 6 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_up_7 (a b : Word) : extractByte ((a <<< 8) ||| (b >>> 56)) 7 = extractByte a 6 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_upd_7 (a d : Word) : extractByte ((a <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d)) 7 = extractByte a 6 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem ext_top_7 (b : Word) : extractByte (b >>> 56) 7 = 0#8 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; interval_cases i <;> simp [extractByte]

theorem leWords65 (s0 s1 s2 s3 a0 a1 a2 a3 d : Word) :
    leWords (stateBytes ([s0, s1, s2, s3].map BitVec.toNat) ++ [UInt8.ofNat d.toNat] ++ stateBytes ([a0, a1, a2, a3].map BitVec.toNat)) 0 16 = ([s0, s1, s2, s3, (a0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d), (a1 <<< 8) ||| (a0 >>> 56), (a2 <<< 8) ||| (a1 >>> 56), (a3 <<< 8) ||| (a2 >>> 56), a3 >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]).map BitVec.toNat := by
  simp only [leWords_16, stateBytes, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, wordBytes_extract, List.cons_append, List.nil_append,
    show List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from rfl, Nat.reduceMul,
    List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, List.drop_nil, List.take_nil,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [leos2ip_nil, BitVec.toNat_ofNat, Nat.zero_mod]
  all_goals (conv_rhs => rw [← leos2ip_wordBytes, wordBytes_extract])
  all_goals (simp only [ext_up_0, ext_up_1, ext_up_2, ext_up_3, ext_up_4, ext_up_5, ext_up_6, ext_up_7, ext_upd_0, ext_upd_1, ext_upd_2, ext_upd_3, ext_upd_4, ext_upd_5, ext_upd_6, ext_upd_7, ext_top_0, ext_top_1, ext_top_2, ext_top_3, ext_top_4, ext_top_5, ext_top_6, ext_top_7, u8_trunc])
  all_goals (try simp only [leos2ip_cons, leos2ip_nil, UInt8.toNat_ofNat', BitVec.toNat_ofNat, Nat.reducePow,
    Nat.zero_mod, Nat.mul_zero, Nat.add_zero])

theorem prfExpand65_eq (s0 s1 s2 s3 a0 a1 a2 a3 d : Word) :
    stateBytes ((compress prfH [s0, s1, s2, s3, (a0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d), (a1 <<< 8) ||| (a0 >>> 56), (a2 <<< 8) ||| (a1 >>> 56), (a3 <<< 8) ||| (a2 >>> 56), a3 >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64).map BitVec.toNat) =
    prfExpand (stateBytes ([s0, s1, s2, s3].map BitVec.toNat)) ([UInt8.ofNat d.toNat] ++ stateBytes ([a0, a1, a2, a3].map BitVec.toNat)) := by
  have hb := compress_toNat (0x6A09E667F3BCC908#64 ^^^ 0x01010040#64) 0xBB67AE8584CAA73B#64 0x3C6EF372FE94F82B#64
    0xA54FF53A5F1D36F1#64 0x510E527FADE682D1#64 0x9B05688C2B3E6C1F#64
    (0x1F83D9ABFB41BD6B#64 ^^^ 0x78455f687361635a#64) (0x5BE0CD19137E2179#64 ^^^ 0x64656553646e6170#64)
    s0 s1 s2 s3 ((a0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d)) ((a1 <<< 8) ||| (a0 >>> 56)) ((a2 <<< 8) ||| (a1 >>> 56)) ((a3 <<< 8) ||| (a2 >>> 56)) (a3 >>> 56) 0#64 0#64 0#64 0#64 0#64 0#64 0#64
    65#64 0#64 true
  rw [if_pos rfl] at hb
  have hH := prfH_toNat
  unfold prfH at hH ⊢
  rw [hb, prfExpand, blake2b512]
  simp only [← List.append_assoc]
  have hlen : (stateBytes ([s0, s1, s2, s3].map BitVec.toNat) ++ [UInt8.ofNat d.toNat] ++ stateBytes ([a0, a1, a2, a3].map BitVec.toNat)).length = 65 := by
    simp only [List.length_append, stateBytes_length, List.length_map, List.length_cons, List.length_nil]
  rw [blake2b_one_block _ _ (by omega) (by omega), hlen, leWords65]
  simp only [List.map_cons, List.map_nil] at hH
  rw [hH]
  rfl

theorem leWords97 (s0 s1 s2 s3 a0 a1 a2 a3 b0 b1 b2 b3 d : Word) :
    leWords (stateBytes ([s0, s1, s2, s3].map BitVec.toNat) ++ [UInt8.ofNat d.toNat] ++ stateBytes ([a0, a1, a2, a3].map BitVec.toNat) ++ stateBytes ([b0, b1, b2, b3].map BitVec.toNat)) 0 16 = ([s0, s1, s2, s3, (a0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d), (a1 <<< 8) ||| (a0 >>> 56), (a2 <<< 8) ||| (a1 >>> 56), (a3 <<< 8) ||| (a2 >>> 56), (b0 <<< 8) ||| (a3 >>> 56), (b1 <<< 8) ||| (b0 >>> 56), (b2 <<< 8) ||| (b1 >>> 56), (b3 <<< 8) ||| (b2 >>> 56), b3 >>> 56, 0#64, 0#64, 0#64]).map BitVec.toNat := by
  simp only [leWords_16, stateBytes, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, wordBytes_extract, List.cons_append, List.nil_append,
    show List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from rfl, Nat.reduceMul,
    List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, List.drop_nil, List.take_nil,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [leos2ip_nil, BitVec.toNat_ofNat, Nat.zero_mod]
  all_goals (conv_rhs => rw [← leos2ip_wordBytes, wordBytes_extract])
  all_goals (simp only [ext_up_0, ext_up_1, ext_up_2, ext_up_3, ext_up_4, ext_up_5, ext_up_6, ext_up_7, ext_upd_0, ext_upd_1, ext_upd_2, ext_upd_3, ext_upd_4, ext_upd_5, ext_upd_6, ext_upd_7, ext_top_0, ext_top_1, ext_top_2, ext_top_3, ext_top_4, ext_top_5, ext_top_6, ext_top_7, u8_trunc])
  all_goals (try simp only [leos2ip_cons, leos2ip_nil, UInt8.toNat_ofNat', BitVec.toNat_ofNat, Nat.reducePow,
    Nat.zero_mod, Nat.mul_zero, Nat.add_zero])

theorem prfExpand97_eq (s0 s1 s2 s3 a0 a1 a2 a3 b0 b1 b2 b3 d : Word) :
    stateBytes ((compress prfH [s0, s1, s2, s3, (a0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d), (a1 <<< 8) ||| (a0 >>> 56), (a2 <<< 8) ||| (a1 >>> 56), (a3 <<< 8) ||| (a2 >>> 56), (b0 <<< 8) ||| (a3 >>> 56), (b1 <<< 8) ||| (b0 >>> 56), (b2 <<< 8) ||| (b1 >>> 56), (b3 <<< 8) ||| (b2 >>> 56), b3 >>> 56, 0#64, 0#64, 0#64] 97#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64).map BitVec.toNat) =
    prfExpand (stateBytes ([s0, s1, s2, s3].map BitVec.toNat)) ([UInt8.ofNat d.toNat] ++ stateBytes ([a0, a1, a2, a3].map BitVec.toNat) ++ stateBytes ([b0, b1, b2, b3].map BitVec.toNat)) := by
  have hb := compress_toNat (0x6A09E667F3BCC908#64 ^^^ 0x01010040#64) 0xBB67AE8584CAA73B#64 0x3C6EF372FE94F82B#64
    0xA54FF53A5F1D36F1#64 0x510E527FADE682D1#64 0x9B05688C2B3E6C1F#64
    (0x1F83D9ABFB41BD6B#64 ^^^ 0x78455f687361635a#64) (0x5BE0CD19137E2179#64 ^^^ 0x64656553646e6170#64)
    s0 s1 s2 s3 ((a0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d)) ((a1 <<< 8) ||| (a0 >>> 56)) ((a2 <<< 8) ||| (a1 >>> 56)) ((a3 <<< 8) ||| (a2 >>> 56)) ((b0 <<< 8) ||| (a3 >>> 56)) ((b1 <<< 8) ||| (b0 >>> 56)) ((b2 <<< 8) ||| (b1 >>> 56)) ((b3 <<< 8) ||| (b2 >>> 56)) (b3 >>> 56) 0#64 0#64 0#64
    97#64 0#64 true
  rw [if_pos rfl] at hb
  have hH := prfH_toNat
  unfold prfH at hH ⊢
  rw [hb, prfExpand, blake2b512]
  simp only [← List.append_assoc]
  have hlen : (stateBytes ([s0, s1, s2, s3].map BitVec.toNat) ++ [UInt8.ofNat d.toNat] ++ stateBytes ([a0, a1, a2, a3].map BitVec.toNat) ++ stateBytes ([b0, b1, b2, b3].map BitVec.toNat)).length = 97 := by
    simp only [List.length_append, stateBytes_length, List.length_map, List.length_cons, List.length_nil]
  rw [blake2b_one_block _ _ (by omega) (by omega), hlen, leWords97]
  simp only [List.map_cons, List.map_nil] at hH
  rw [hH]
  rfl

end Cases.Zip2005.B2b
