import Cases.Zip2005.Blake2b.Blake2bModel
import Cases.Zip2005.Spec.Zip2005.Blake2b

/-!
# The word-level BLAKE2b model against the specification

`Cases.Zip2005.B2b.compress` computes on 64-bit words in the association the compiler emits
(`(a + y) + b`); `Zip2005.Blake2b.compress` computes on `ℕ` modulo `2^64` as RFC 7693 writes
it. They agree word for word: `compress_toNat`. The proof is one mix at a time (`Gw_toNat`),
lifted to the sixteen-word vector for each of the eight mix positions (`G_toNat_*`), and then
both twelve-round loops are unfolded to the same nest of 96 mixes.

The spec's last-node flag word is never set (single-node hashing), so the model is
instantiated at `fn = 0`; the final-block flag word is all ones exactly when `f`.
-/

namespace Cases.Zip2005.B2b

open RiscvZkvm.Rv64

set_option autoImplicit false

theorem length16 {α : Type} (v : List α) (h : v.length = 16) :
    ∃ v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15,
      v = [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] :=
  match v, h with
  | [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15], _ =>
    ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, rfl⟩

/-! ### One mix -/

theorem add_toNat (a b : Word) : (a + b).toNat = (a.toNat + b.toNat) % Zip2005.Blake2b.M64 := by
  rw [BitVec.toNat_add]; rfl

theorem rotr_toNat (n : Nat) (x : Word) : (rotr n x).toNat = Zip2005.Blake2b.rotr n x.toNat := by
  simp only [rotr, Zip2005.Blake2b.rotr, Zip2005.Blake2b.M64, BitVec.toNat_or, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, Nat.or_mod_two_pow]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) x.isLt)]

theorem mod_add_add_mod (a b c n : Nat) : (a % n + b + c) % n = (a + b + c) % n := by
  rw [Nat.add_assoc, Nat.mod_add_mod, ← Nat.add_assoc]

/-- The spec's `G` arithmetic on four words (RFC 7693 § 3.1, `a + b + y` order). -/
def Gn (a b c d x y : Nat) : Nat × Nat × Nat × Nat :=
  let a := (a + b + x) % Zip2005.Blake2b.M64
  let d := Zip2005.Blake2b.rotr 32 (d ^^^ a)
  let c := (c + d) % Zip2005.Blake2b.M64
  let b := Zip2005.Blake2b.rotr 24 (b ^^^ c)
  let a := (a + b + y) % Zip2005.Blake2b.M64
  let d := Zip2005.Blake2b.rotr 16 (d ^^^ a)
  let c := (c + d) % Zip2005.Blake2b.M64
  let b := Zip2005.Blake2b.rotr 63 (b ^^^ c)
  (a, b, c, d)

theorem Gw_toNat (a b c d x y : Word) :
    ((Gw a b c d x y).1.toNat, (Gw a b c d x y).2.1.toNat, (Gw a b c d x y).2.2.1.toNat,
      (Gw a b c d x y).2.2.2.toNat) = Gn a.toNat b.toNat c.toNat d.toNat x.toNat y.toNat := by
  simp only [Gw, Gn, add_toNat, BitVec.toNat_xor, rotr_toNat, Nat.mod_add_mod,
    Nat.add_right_comm _ y.toNat, mod_add_add_mod]

theorem Gw_toNat_1 (a b c d x y : Word) :
    (Gw a b c d x y).1.toNat = (Gn a.toNat b.toNat c.toNat d.toNat x.toNat y.toNat).1 :=
  congrArg Prod.fst (Gw_toNat a b c d x y)
theorem Gw_toNat_2 (a b c d x y : Word) :
    (Gw a b c d x y).2.1.toNat = (Gn a.toNat b.toNat c.toNat d.toNat x.toNat y.toNat).2.1 :=
  congrArg (fun p => p.2.1) (Gw_toNat a b c d x y)
theorem Gw_toNat_3 (a b c d x y : Word) :
    (Gw a b c d x y).2.2.1.toNat = (Gn a.toNat b.toNat c.toNat d.toNat x.toNat y.toNat).2.2.1 :=
  congrArg (fun p => p.2.2.1) (Gw_toNat a b c d x y)
theorem Gw_toNat_4 (a b c d x y : Word) :
    (Gw a b c d x y).2.2.2.toNat = (Gn a.toNat b.toNat c.toNat d.toNat x.toNat y.toNat).2.2.2 :=
  congrArg (fun p => p.2.2.2) (Gw_toNat a b c d x y)

/-! ### The sixteen-word vector, per mix position -/

theorem G_length (v : List Word) (a b c d : Nat) (x y : Word) : (G v a b c d x y).length = v.length := by
  simp only [G, List.length_set]

theorem specG_0_4_8_12 (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 x y : Nat) :
    Zip2005.Blake2b.G [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15] 0 4 8 12 x y =
      [(Gn n0 n4 n8 n12 x y).1, n1, n2, n3, (Gn n0 n4 n8 n12 x y).2.1, n5, n6, n7, (Gn n0 n4 n8 n12 x y).2.2.1, n9, n10, n11, (Gn n0 n4 n8 n12 x y).2.2.2, n13, n14, n15] := rfl

theorem G_toNat_0_4_8_12 (v : List Word) (hv : v.length = 16) (x y : Word) :
    (G v 0 4 8 12 x y).map BitVec.toNat = Zip2005.Blake2b.G (v.map BitVec.toNat) 0 4 8 12 x.toNat y.toNat := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, rfl⟩ := length16 v hv
  simp only [G_pos_0_4_8_12, List.map_cons, List.map_nil, specG_0_4_8_12, Gw_toNat_1, Gw_toNat_2, Gw_toNat_3,
    Gw_toNat_4]

theorem specG_1_5_9_13 (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 x y : Nat) :
    Zip2005.Blake2b.G [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15] 1 5 9 13 x y =
      [n0, (Gn n1 n5 n9 n13 x y).1, n2, n3, n4, (Gn n1 n5 n9 n13 x y).2.1, n6, n7, n8, (Gn n1 n5 n9 n13 x y).2.2.1, n10, n11, n12, (Gn n1 n5 n9 n13 x y).2.2.2, n14, n15] := rfl

theorem G_toNat_1_5_9_13 (v : List Word) (hv : v.length = 16) (x y : Word) :
    (G v 1 5 9 13 x y).map BitVec.toNat = Zip2005.Blake2b.G (v.map BitVec.toNat) 1 5 9 13 x.toNat y.toNat := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, rfl⟩ := length16 v hv
  simp only [G_pos_1_5_9_13, List.map_cons, List.map_nil, specG_1_5_9_13, Gw_toNat_1, Gw_toNat_2, Gw_toNat_3,
    Gw_toNat_4]

theorem specG_2_6_10_14 (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 x y : Nat) :
    Zip2005.Blake2b.G [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15] 2 6 10 14 x y =
      [n0, n1, (Gn n2 n6 n10 n14 x y).1, n3, n4, n5, (Gn n2 n6 n10 n14 x y).2.1, n7, n8, n9, (Gn n2 n6 n10 n14 x y).2.2.1, n11, n12, n13, (Gn n2 n6 n10 n14 x y).2.2.2, n15] := rfl

theorem G_toNat_2_6_10_14 (v : List Word) (hv : v.length = 16) (x y : Word) :
    (G v 2 6 10 14 x y).map BitVec.toNat = Zip2005.Blake2b.G (v.map BitVec.toNat) 2 6 10 14 x.toNat y.toNat := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, rfl⟩ := length16 v hv
  simp only [G_pos_2_6_10_14, List.map_cons, List.map_nil, specG_2_6_10_14, Gw_toNat_1, Gw_toNat_2, Gw_toNat_3,
    Gw_toNat_4]

theorem specG_3_7_11_15 (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 x y : Nat) :
    Zip2005.Blake2b.G [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15] 3 7 11 15 x y =
      [n0, n1, n2, (Gn n3 n7 n11 n15 x y).1, n4, n5, n6, (Gn n3 n7 n11 n15 x y).2.1, n8, n9, n10, (Gn n3 n7 n11 n15 x y).2.2.1, n12, n13, n14, (Gn n3 n7 n11 n15 x y).2.2.2] := rfl

theorem G_toNat_3_7_11_15 (v : List Word) (hv : v.length = 16) (x y : Word) :
    (G v 3 7 11 15 x y).map BitVec.toNat = Zip2005.Blake2b.G (v.map BitVec.toNat) 3 7 11 15 x.toNat y.toNat := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, rfl⟩ := length16 v hv
  simp only [G_pos_3_7_11_15, List.map_cons, List.map_nil, specG_3_7_11_15, Gw_toNat_1, Gw_toNat_2, Gw_toNat_3,
    Gw_toNat_4]

theorem specG_0_5_10_15 (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 x y : Nat) :
    Zip2005.Blake2b.G [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15] 0 5 10 15 x y =
      [(Gn n0 n5 n10 n15 x y).1, n1, n2, n3, n4, (Gn n0 n5 n10 n15 x y).2.1, n6, n7, n8, n9, (Gn n0 n5 n10 n15 x y).2.2.1, n11, n12, n13, n14, (Gn n0 n5 n10 n15 x y).2.2.2] := rfl

theorem G_toNat_0_5_10_15 (v : List Word) (hv : v.length = 16) (x y : Word) :
    (G v 0 5 10 15 x y).map BitVec.toNat = Zip2005.Blake2b.G (v.map BitVec.toNat) 0 5 10 15 x.toNat y.toNat := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, rfl⟩ := length16 v hv
  simp only [G_pos_0_5_10_15, List.map_cons, List.map_nil, specG_0_5_10_15, Gw_toNat_1, Gw_toNat_2, Gw_toNat_3,
    Gw_toNat_4]

theorem specG_1_6_11_12 (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 x y : Nat) :
    Zip2005.Blake2b.G [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15] 1 6 11 12 x y =
      [n0, (Gn n1 n6 n11 n12 x y).1, n2, n3, n4, n5, (Gn n1 n6 n11 n12 x y).2.1, n7, n8, n9, n10, (Gn n1 n6 n11 n12 x y).2.2.1, (Gn n1 n6 n11 n12 x y).2.2.2, n13, n14, n15] := rfl

theorem G_toNat_1_6_11_12 (v : List Word) (hv : v.length = 16) (x y : Word) :
    (G v 1 6 11 12 x y).map BitVec.toNat = Zip2005.Blake2b.G (v.map BitVec.toNat) 1 6 11 12 x.toNat y.toNat := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, rfl⟩ := length16 v hv
  simp only [G_pos_1_6_11_12, List.map_cons, List.map_nil, specG_1_6_11_12, Gw_toNat_1, Gw_toNat_2, Gw_toNat_3,
    Gw_toNat_4]

theorem specG_2_7_8_13 (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 x y : Nat) :
    Zip2005.Blake2b.G [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15] 2 7 8 13 x y =
      [n0, n1, (Gn n2 n7 n8 n13 x y).1, n3, n4, n5, n6, (Gn n2 n7 n8 n13 x y).2.1, (Gn n2 n7 n8 n13 x y).2.2.1, n9, n10, n11, n12, (Gn n2 n7 n8 n13 x y).2.2.2, n14, n15] := rfl

theorem G_toNat_2_7_8_13 (v : List Word) (hv : v.length = 16) (x y : Word) :
    (G v 2 7 8 13 x y).map BitVec.toNat = Zip2005.Blake2b.G (v.map BitVec.toNat) 2 7 8 13 x.toNat y.toNat := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, rfl⟩ := length16 v hv
  simp only [G_pos_2_7_8_13, List.map_cons, List.map_nil, specG_2_7_8_13, Gw_toNat_1, Gw_toNat_2, Gw_toNat_3,
    Gw_toNat_4]

theorem specG_3_4_9_14 (n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14 n15 x y : Nat) :
    Zip2005.Blake2b.G [n0, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15] 3 4 9 14 x y =
      [n0, n1, n2, (Gn n3 n4 n9 n14 x y).1, (Gn n3 n4 n9 n14 x y).2.1, n5, n6, n7, n8, (Gn n3 n4 n9 n14 x y).2.2.1, n10, n11, n12, n13, (Gn n3 n4 n9 n14 x y).2.2.2, n15] := rfl

theorem G_toNat_3_4_9_14 (v : List Word) (hv : v.length = 16) (x y : Word) :
    (G v 3 4 9 14 x y).map BitVec.toNat = Zip2005.Blake2b.G (v.map BitVec.toNat) 3 4 9 14 x.toNat y.toNat := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, rfl⟩ := length16 v hv
  simp only [G_pos_3_4_9_14, List.map_cons, List.map_nil, specG_3_4_9_14, Gw_toNat_1, Gw_toNat_2, Gw_toNat_3,
    Gw_toNat_4]

/-! ### The rounds and the compression function -/

theorem getElem?_map_toNat (v : List Word) (i : Nat) :
    (v.map BitVec.toNat)[i]?.getD 0 = (v[i]?.getD 0).toNat := by
  simp only [List.getElem?_map]
  cases v[i]? <;> rfl

set_option maxHeartbeats 4000000 in
/-- The twelve rounds agree with the spec's `mixRounds`. -/
theorem roundsTo_toNat (h0 h1 h2 h3 h4 h5 h6 h7 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15
    t0 t1 : Word) (f : Bool) :
    (roundsTo [h0, h1, h2, h3, h4, h5, h6, h7] [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15]
      t0 t1 (if f then 0xFFFFFFFFFFFFFFFF#64 else 0#64) 0#64 12).map BitVec.toNat =
    Zip2005.Blake2b.mixRounds [h0.toNat, h1.toNat, h2.toNat, h3.toNat, h4.toNat, h5.toNat, h6.toNat, h7.toNat]
      [m0.toNat, m1.toNat, m2.toNat, m3.toNat, m4.toNat, m5.toNat, m6.toNat, m7.toNat, m8.toNat, m9.toNat,
       m10.toNat, m11.toNat, m12.toNat, m13.toNat, m14.toNat, m15.toNat] t0.toNat t1.toNat f := by
  unfold Zip2005.Blake2b.mixRounds
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Zip2005.Blake2b.rounds,
    List.range', List.forIn_cons, List.forIn_nil, Zip2005.Blake2b.mixTable, Zip2005.Blake2b.sigma,
    bind, pure, Id, Nat.reduceMod, Nat.reduceAdd, Nat.reduceDiv, Nat.reduceSub, List.getD_eq_getElem?_getD,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, Nat.reduceMul,
    Zip2005.Blake2b.IV, List.cons_append, List.nil_append, List.set_cons_zero, List.set_cons_succ]
  rw [roundsTo_12, roundsTo_8, roundsTo_4, initV_eq, round_eq_0, round_eq_1, round_eq_2, round_eq_3,
    round_eq_4, round_eq_5, round_eq_6, round_eq_7, round_eq_8, round_eq_9, round_eq_10, round_eq_11]
  simp only [G_toNat_0_4_8_12, G_toNat_1_5_9_13, G_toNat_2_6_10_14, G_toNat_3_7_11_15, G_toNat_0_5_10_15, G_toNat_1_6_11_12, G_toNat_2_7_8_13, G_toNat_3_4_9_14, G_length, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.map_cons, List.map_nil, BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Zip2005.Blake2b.M64]
  cases f <;> simp only [Bool.false_eq_true, if_true, if_false, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod,
    Nat.reduceSub, Nat.xor_zero]

/-- The compression function agrees with the spec's, word for word. -/
theorem compress_toNat (h0 h1 h2 h3 h4 h5 h6 h7 m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15
    t0 t1 : Word) (f : Bool) :
    (compress [h0, h1, h2, h3, h4, h5, h6, h7] [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15]
      t0 t1 (if f then 0xFFFFFFFFFFFFFFFF#64 else 0#64) 0#64).map BitVec.toNat =
    Zip2005.Blake2b.compress [h0.toNat, h1.toNat, h2.toNat, h3.toNat, h4.toNat, h5.toNat, h6.toNat, h7.toNat]
      [m0.toNat, m1.toNat, m2.toNat, m3.toNat, m4.toNat, m5.toNat, m6.toNat, m7.toNat, m8.toNat, m9.toNat,
       m10.toNat, m11.toNat, m12.toNat, m13.toNat, m14.toNat, m15.toNat] t0.toNat t1.toNat f := by
  unfold compress Zip2005.Blake2b.compress
  rw [← roundsTo_toNat]
  generalize roundsTo [h0, h1, h2, h3, h4, h5, h6, h7]
    [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] t0 t1
    (if f then 0xFFFFFFFFFFFFFFFF#64 else 0#64) 0#64 12 = v
  simp only [List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons, List.map_nil,
    BitVec.toNat_xor, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, Nat.reduceAdd, getElem?_map_toNat]

end Cases.Zip2005.B2b
