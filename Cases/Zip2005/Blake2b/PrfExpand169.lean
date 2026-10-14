import Cases.Zip2005.Blake2b.PrfExpandSpec

/-!
# `PRF^expand` on two blocks: 169 bytes

`RandomSeed::rcm_v3` hashes `rseed ‖ [0x0B] ‖ …` (32 + 137 bytes). Everything after the separator
reaches the BLAKE2b buffer one byte past alignment, so message word `i` is `(xᵢ <<< 8) ||| (xᵢ₋₁ >>> 56)`
over the seventeen words `x` of `repr(g_d) ‖ repr(pk_d) ‖ v ‖ rho ‖ psi`.

* `blake2b_two_blocks`: for `128 < |msg| ≤ 256`, BLAKE2b is one non-final compression and a final one;
* `leWords169a`, `leWords169b`: the two blocks' sixteen words;
* `prfExpand169_eq`: the machine's two compressions serialise to `Zip2005.prfExpand`.
-/

namespace Cases.Zip2005.B2b

open RiscvZkvm.Rv64 _root_.Zip2005 _root_.Zip2005.Blake2b

set_option autoImplicit false

theorem exists8 (l : List Word) (h : l.length = 8) :
    ∃ a b c d e f g i : Word, l = [a, b, c, d, e, f, g, i] := by
  match l, h with
  | [a, b, c, d, e, f, g, i], _ => exact ⟨a, b, c, d, e, f, g, i, rfl⟩

theorem blake2b_two_blocks (personal msg : List UInt8) (h1 : 128 < msg.length) (h2 : msg.length ≤ 256) :
    blake2b personal 64 msg =
      stateBytes (Blake2b.compress (Blake2b.compress (initialState 64 0 [] personal) (leWords msg 0 16) 128 0 false)
        (leWords msg 128 16) msg.length 0 true) := by
  have hdd : blockCount msg.length = 2 := by
    unfold blockCount blockBytes
    have : (msg.length + 128 - 1) / 128 = 2 := by omega
    rw [this]; rfl
  simp only [blake2b, hdd, absorbAux, Nat.zero_mul, Nat.zero_add, Nat.one_mul, blockBytes, Nat.add_one_sub_one]
  rw [List.take_of_length_le (by simp)]

set_option maxHeartbeats 4000000 in
theorem leWords169a (e0 e1 e2 e3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 d : Word) :
    leWords (stateBytes ([e0, e1, e2, e3].map BitVec.toNat) ++ [UInt8.ofNat d.toNat] ++ stateBytes ([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16].map BitVec.toNat)) 0 16 = ([e0, e1, e2, e3, (x0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d), (x1 <<< 8) ||| (x0 >>> 56), (x2 <<< 8) ||| (x1 >>> 56), (x3 <<< 8) ||| (x2 >>> 56), (x4 <<< 8) ||| (x3 >>> 56), (x5 <<< 8) ||| (x4 >>> 56), (x6 <<< 8) ||| (x5 >>> 56), (x7 <<< 8) ||| (x6 >>> 56), (x8 <<< 8) ||| (x7 >>> 56), (x9 <<< 8) ||| (x8 >>> 56), (x10 <<< 8) ||| (x9 >>> 56), (x11 <<< 8) ||| (x10 >>> 56)]).map BitVec.toNat := by
  simp only [leWords, stateBytes, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, wordBytes_extract, List.cons_append, List.nil_append,
    show List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from rfl, Nat.reduceMul,
    Nat.zero_add, List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals (conv_rhs => rw [← leos2ip_wordBytes, wordBytes_extract])
  all_goals (simp only [ext_up_0, ext_up_1, ext_up_2, ext_up_3, ext_up_4, ext_up_5, ext_up_6, ext_up_7, ext_upd_0, ext_upd_1, ext_upd_2, ext_upd_3, ext_upd_4, ext_upd_5, ext_upd_6, ext_upd_7, u8_trunc])

set_option maxHeartbeats 4000000 in
theorem leWords169b (e0 e1 e2 e3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 d : Word) :
    leWords (stateBytes ([e0, e1, e2, e3].map BitVec.toNat) ++ [UInt8.ofNat d.toNat] ++ stateBytes ([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16].map BitVec.toNat)) 128 16 = ([(x12 <<< 8) ||| (x11 >>> 56), (x13 <<< 8) ||| (x12 >>> 56), (x14 <<< 8) ||| (x13 >>> 56), (x15 <<< 8) ||| (x14 >>> 56), (x16 <<< 8) ||| (x15 >>> 56), x16 >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]).map BitVec.toNat := by
  simp only [leWords, stateBytes, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, wordBytes_extract, List.cons_append, List.nil_append,
    show List.range 16 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] from rfl, Nat.reduceMul, Nat.reduceAdd,
    List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero, List.drop_nil, List.take_nil,
    List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [leos2ip_nil, BitVec.toNat_ofNat, Nat.zero_mod]
  all_goals (conv_rhs => rw [← leos2ip_wordBytes, wordBytes_extract])
  all_goals (simp only [ext_up_0, ext_up_1, ext_up_2, ext_up_3, ext_up_4, ext_up_5, ext_up_6, ext_up_7, ext_top_0, ext_top_1, ext_top_2, ext_top_3, ext_top_4, ext_top_5, ext_top_6, ext_top_7])
  all_goals (try simp only [leos2ip_cons, leos2ip_nil, UInt8.toNat_ofNat', BitVec.toNat_ofNat, Nat.reducePow,
    Nat.zero_mod, Nat.mul_zero, Nat.add_zero])

/-- `PRF^expand_rseed(t)` for a 137-byte `t = [d] ‖ x`: two blocks. -/
theorem prfExpand169_eq (e0 e1 e2 e3 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 d : Word) :
    stateBytes ((compress (compress prfH [e0, e1, e2, e3, (x0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d), (x1 <<< 8) ||| (x0 >>> 56), (x2 <<< 8) ||| (x1 >>> 56), (x3 <<< 8) ||| (x2 >>> 56), (x4 <<< 8) ||| (x3 >>> 56), (x5 <<< 8) ||| (x4 >>> 56), (x6 <<< 8) ||| (x5 >>> 56), (x7 <<< 8) ||| (x6 >>> 56), (x8 <<< 8) ||| (x7 >>> 56), (x9 <<< 8) ||| (x8 >>> 56), (x10 <<< 8) ||| (x9 >>> 56), (x11 <<< 8) ||| (x10 >>> 56)] 128#64 0#64 0#64 0#64) [(x12 <<< 8) ||| (x11 >>> 56), (x13 <<< 8) ||| (x12 >>> 56), (x14 <<< 8) ||| (x13 >>> 56), (x15 <<< 8) ||| (x14 >>> 56), (x16 <<< 8) ||| (x15 >>> 56), x16 >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]
      169#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64).map BitVec.toNat) =
    prfExpand (stateBytes ([e0, e1, e2, e3].map BitVec.toNat)) ([UInt8.ofNat d.toNat] ++ stateBytes ([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16].map BitVec.toNat)) := by
  have hb1 := compress_toNat (0x6A09E667F3BCC908#64 ^^^ 0x01010040#64) 0xBB67AE8584CAA73B#64 0x3C6EF372FE94F82B#64 0xA54FF53A5F1D36F1#64 0x510E527FADE682D1#64 0x9B05688C2B3E6C1F#64 (0x1F83D9ABFB41BD6B#64 ^^^ 0x78455f687361635a#64) (0x5BE0CD19137E2179#64 ^^^ 0x64656553646e6170#64)
    e0 e1 e2 e3 ((x0 <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 d)) ((x1 <<< 8) ||| (x0 >>> 56)) ((x2 <<< 8) ||| (x1 >>> 56)) ((x3 <<< 8) ||| (x2 >>> 56)) ((x4 <<< 8) ||| (x3 >>> 56)) ((x5 <<< 8) ||| (x4 >>> 56)) ((x6 <<< 8) ||| (x5 >>> 56)) ((x7 <<< 8) ||| (x6 >>> 56)) ((x8 <<< 8) ||| (x7 >>> 56)) ((x9 <<< 8) ||| (x8 >>> 56)) ((x10 <<< 8) ||| (x9 >>> 56)) ((x11 <<< 8) ||| (x10 >>> 56)) 128#64 0#64 false
  rw [if_neg (by decide)] at hb1
  have hH := prfH_toNat
  unfold prfH at hH ⊢
  obtain ⟨o0, o1, o2, o3, o4, o5, o6, o7, hO⟩ := exists8 _ (compress_length _ _ 128#64 0#64 0#64 0#64)
  rw [hO] at hb1 ⊢
  have hb2 := compress_toNat o0 o1 o2 o3 o4 o5 o6 o7 ((x12 <<< 8) ||| (x11 >>> 56)) ((x13 <<< 8) ||| (x12 >>> 56)) ((x14 <<< 8) ||| (x13 >>> 56)) ((x15 <<< 8) ||| (x14 >>> 56)) ((x16 <<< 8) ||| (x15 >>> 56)) (x16 >>> 56) 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 169#64 0#64 true
  rw [if_pos rfl] at hb2
  rw [hb2, prfExpand, blake2b512]
  simp only [← List.append_assoc]
  have hlen : (stateBytes ([e0, e1, e2, e3].map BitVec.toNat) ++ [UInt8.ofNat d.toNat] ++ stateBytes ([x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15, x16].map BitVec.toNat)).length = 169 := by
    simp only [List.length_append, stateBytes_length, List.length_map, List.length_cons, List.length_nil]
  rw [blake2b_two_blocks _ _ (by omega) (by omega), hlen, leWords169a, leWords169b]
  simp only [List.map_cons, List.map_nil] at hb1 hH ⊢
  rw [show (128#64 : Word).toNat = 128 from rfl, show (0#64 : Word).toNat = 0 from rfl] at hb1
  rw [← hH, ← hb1]
  rfl

end Cases.Zip2005.B2b
