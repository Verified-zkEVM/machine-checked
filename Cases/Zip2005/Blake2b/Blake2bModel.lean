/-
  Cases.Zip2005.Blake2bModel

  BLAKE2b's compression function (RFC 7693) over 64-bit words, operation for operation as
  `Zip2005.Blake2b` states it over `ℕ`, so the executor's atoms can be matched one mix at a
  time (`G_step`) and the result related to the spec once (`Proof/Blake2b/Blake2bSpec.lean`).
-/

import Cases.Zip2005.Field.Limbs

namespace Cases.Zip2005.B2b

open RiscvZkvm.Rv64

/-- Rotate right, as compiled: `x >>> n ||| x <<< (64 - n)`. -/
def rotr (n : Nat) (x : Word) : Word := x >>> n ||| x <<< (64 - n)

/-- One `G` mix on four words with message words `x`, `y`: the new `(a, b, c, d)`. The second
    addition is written `a + y + b` (the compiled association); `Proof/Blake2b/Blake2bSpec.lean` relates
    it to RFC 7693's `a + b + y`. -/
def Gw (a b c d x y : Word) : Word × Word × Word × Word :=
  let a := a + b + x
  let d := rotr 32 (d ^^^ a)
  let c := c + d
  let b := rotr 24 (b ^^^ c)
  let a := a + y + b
  let d := rotr 16 (d ^^^ a)
  let c := c + d
  let b := rotr 63 (b ^^^ c)
  (a, b, c, d)

/-- `Gw`, one equation per machine step, in the association the compiler emits for the column
    mixes: `(a + b) + x` then `(a + y) + b`. Operand commutations are supplied by the caller
    (`BitVec.add_comm` and friends composed with the atom definitions). -/
theorem G_step {a b c d x y a1 a2 d1 d1r d1l d2 c1 b1 b1r b1l b2 a3 a4 d3 d3r d3l d4 c2 b3 b3r b3l b4 : Word}
    (h1 : a + b = a1) (h2 : a1 + x = a2) (h3 : d ^^^ a2 = d1)
    (h4 : d1 >>> 32 = d1r) (h5 : d1 <<< 32 = d1l) (h6 : d1r ||| d1l = d2)
    (h7 : c + d2 = c1) (h8 : b ^^^ c1 = b1)
    (h9 : b1 >>> 24 = b1r) (h10 : b1 <<< 40 = b1l) (h11 : b1r ||| b1l = b2)
    (h12 : a2 + y = a3) (h13 : a3 + b2 = a4) (h14 : d2 ^^^ a4 = d3)
    (h15 : d3 >>> 16 = d3r) (h16 : d3 <<< 48 = d3l) (h17 : d3r ||| d3l = d4)
    (h18 : c1 + d4 = c2) (h19 : b2 ^^^ c2 = b3)
    (h20 : b3 >>> 63 = b3r) (h21 : b3 <<< 1 = b3l) (h22 : b3r ||| b3l = b4) :
    Gw a b c d x y = (a4, b4, c2, d4) := by
  subst h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22
  rfl

/-- `G_step` with the first addition associated `(a + x) + b` (the diagonal mixes). -/
theorem G_step_xb {a b c d x y a1 a2 d1 d1r d1l d2 c1 b1 b1r b1l b2 a3 a4 d3 d3r d3l d4 c2 b3 b3r b3l b4 : Word}
    (h1 : a + x = a1) (h2 : a1 + b = a2) (h3 : d ^^^ a2 = d1)
    (h4 : d1 >>> 32 = d1r) (h5 : d1 <<< 32 = d1l) (h6 : d1r ||| d1l = d2)
    (h7 : c + d2 = c1) (h8 : b ^^^ c1 = b1)
    (h9 : b1 >>> 24 = b1r) (h10 : b1 <<< 40 = b1l) (h11 : b1r ||| b1l = b2)
    (h12 : a2 + y = a3) (h13 : a3 + b2 = a4) (h14 : d2 ^^^ a4 = d3)
    (h15 : d3 >>> 16 = d3r) (h16 : d3 <<< 48 = d3l) (h17 : d3r ||| d3l = d4)
    (h18 : c1 + d4 = c2) (h19 : b2 ^^^ c2 = b3)
    (h20 : b3 >>> 63 = b3r) (h21 : b3 <<< 1 = b3l) (h22 : b3r ||| b3l = b4) :
    Gw a b c d x y = (a4, b4, c2, d4) :=
  G_step rfl (by rw [← h2, ← h1]; ac_rfl) h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22

/-- `G_step` with the second addition associated `(a + b) + y`. -/
theorem G_step_by {a b c d x y a1 a2 d1 d1r d1l d2 c1 b1 b1r b1l b2 a3 a4 d3 d3r d3l d4 c2 b3 b3r b3l b4 : Word}
    (h1 : a + b = a1) (h2 : a1 + x = a2) (h3 : d ^^^ a2 = d1)
    (h4 : d1 >>> 32 = d1r) (h5 : d1 <<< 32 = d1l) (h6 : d1r ||| d1l = d2)
    (h7 : c + d2 = c1) (h8 : b ^^^ c1 = b1)
    (h9 : b1 >>> 24 = b1r) (h10 : b1 <<< 40 = b1l) (h11 : b1r ||| b1l = b2)
    (h12 : a2 + b2 = a3) (h13 : a3 + y = a4) (h14 : d2 ^^^ a4 = d3)
    (h15 : d3 >>> 16 = d3r) (h16 : d3 <<< 48 = d3l) (h17 : d3r ||| d3l = d4)
    (h18 : c1 + d4 = c2) (h19 : b2 ^^^ c2 = b3)
    (h20 : b3 >>> 63 = b3r) (h21 : b3 <<< 1 = b3l) (h22 : b3r ||| b3l = b4) :
    Gw a b c d x y = (a4, b4, c2, d4) :=
  G_step h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 rfl (by rw [← h13, ← h12]; ac_rfl) h14 h15 h16 h17 h18 h19 h20 h21 h22

/-- `G_step` with both additions in the other association. -/
theorem G_step_xb_by {a b c d x y a1 a2 d1 d1r d1l d2 c1 b1 b1r b1l b2 a3 a4 d3 d3r d3l d4 c2 b3 b3r b3l b4 : Word}
    (h1 : a + x = a1) (h2 : a1 + b = a2) (h3 : d ^^^ a2 = d1)
    (h4 : d1 >>> 32 = d1r) (h5 : d1 <<< 32 = d1l) (h6 : d1r ||| d1l = d2)
    (h7 : c + d2 = c1) (h8 : b ^^^ c1 = b1)
    (h9 : b1 >>> 24 = b1r) (h10 : b1 <<< 40 = b1l) (h11 : b1r ||| b1l = b2)
    (h12 : a2 + b2 = a3) (h13 : a3 + y = a4) (h14 : d2 ^^^ a4 = d3)
    (h15 : d3 >>> 16 = d3r) (h16 : d3 <<< 48 = d3l) (h17 : d3r ||| d3l = d4)
    (h18 : c1 + d4 = c2) (h19 : b2 ^^^ c2 = b3)
    (h20 : b3 >>> 63 = b3r) (h21 : b3 <<< 1 = b3l) (h22 : b3r ||| b3l = b4) :
    Gw a b c d x y = (a4, b4, c2, d4) :=
  G_step rfl (by rw [← h2, ← h1]; ac_rfl) h3 h4 h5 h6 h7 h8 h9 h10 h11 rfl (by rw [← h13, ← h12]; ac_rfl)
    h14 h15 h16 h17 h18 h19 h20 h21 h22

/-- `G` on the sixteen-word vector: positions `a b c d` replaced. -/
def G (v : List Word) (a b c d : Nat) (x y : Word) : List Word :=
  let r := Gw (v.getD a 0) (v.getD b 0) (v.getD c 0) (v.getD d 0) x y
  (((v.set a r.1).set b r.2.1).set c r.2.2.1).set d r.2.2.2

def IV : List Word :=
  [0x6A09E667F3BCC908#64, 0xBB67AE8584CAA73B#64, 0x3C6EF372FE94F82B#64, 0xA54FF53A5F1D36F1#64,
   0x510E527FADE682D1#64, 0x9B05688C2B3E6C1F#64, 0x1F83D9ABFB41BD6B#64, 0x5BE0CD19137E2179#64]

def sigma : List (List Nat) :=
  [[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15],
   [14,10,4,8,9,15,13,6,1,12,0,2,11,7,5,3],
   [11,8,12,0,5,2,15,13,10,14,3,6,7,1,9,4],
   [7,9,3,1,13,12,11,14,2,6,5,10,4,0,15,8],
   [9,0,5,7,2,4,10,15,14,1,11,12,6,8,3,13],
   [2,12,6,10,0,11,8,3,4,13,7,5,15,14,1,9],
   [12,5,1,15,14,13,4,10,0,7,6,3,9,2,8,11],
   [13,11,7,14,12,1,3,9,5,0,15,4,8,6,2,10],
   [6,15,14,9,11,3,0,8,12,2,13,7,1,4,10,5],
   [10,2,8,4,7,6,1,5,15,11,9,14,3,12,13,0]]

def mixTable : List (Nat × Nat × Nat × Nat) :=
  [(0,4,8,12), (1,5,9,13), (2,6,10,14), (3,7,11,15),
   (0,5,10,15), (1,6,11,12), (2,7,8,13), (3,4,9,14)]

/-- One round with message schedule `s`: the eight mixes of `mixTable`, written out. -/
def roundWith (v m : List Word) (s : List Nat) : List Word :=
  let mw := fun i => m.getD (s.getD i 0) 0
  let v := G v 0 4 8 12 (mw 0) (mw 1)
  let v := G v 1 5 9 13 (mw 2) (mw 3)
  let v := G v 2 6 10 14 (mw 4) (mw 5)
  let v := G v 3 7 11 15 (mw 6) (mw 7)
  let v := G v 0 5 10 15 (mw 8) (mw 9)
  let v := G v 1 6 11 12 (mw 10) (mw 11)
  let v := G v 2 7 8 13 (mw 12) (mw 13)
  G v 3 4 9 14 (mw 14) (mw 15)

/-- Round `r` uses permutation `sigma[r % 10]`. -/
def round (v m : List Word) (r : Nat) : List Word := roundWith v m (sigma.getD (r % 10) [])

/-- The work vector before the rounds: `h ‖ IV` with the counter words and the flag words
    (`fb` for the last block, `fn` for the last node; each `0` or all ones). -/
def initV (h : List Word) (t0 t1 fb fn : Word) : List Word :=
  let v := h ++ IV
  let v := v.set 12 (v.getD 12 0 ^^^ t0)
  let v := v.set 13 (v.getD 13 0 ^^^ t1)
  let v := v.set 14 (v.getD 14 0 ^^^ fb)
  v.set 15 (v.getD 15 0 ^^^ fn)

/-- The first `k` rounds. -/
def roundsTo (h m : List Word) (t0 t1 fb fn : Word) (k : Nat) : List Word :=
  (List.range k).foldl (fun v r => round v m r) (initV h t0 t1 fb fn)

/-- `F(h, m, t, f)`: the new chaining state. -/
def compress (h m : List Word) (t0 t1 fb fn : Word) : List Word :=
  let v := roundsTo h m t0 t1 fb fn 12
  (List.range 8).map (fun i => h.getD i 0 ^^^ v.getD i 0 ^^^ v.getD (i + 8) 0)

/-! ### Unfoldings for the machine side -/

theorem G_pos_0_4_8_12 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : Word) :
    G [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 0 4 8 12 x y =
      [(Gw v0 v4 v8 v12 x y).1, v1, v2, v3, (Gw v0 v4 v8 v12 x y).2.1, v5, v6, v7, (Gw v0 v4 v8 v12 x y).2.2.1, v9, v10, v11, (Gw v0 v4 v8 v12 x y).2.2.2, v13, v14, v15] := rfl
theorem G_pos_1_5_9_13 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : Word) :
    G [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 1 5 9 13 x y =
      [v0, (Gw v1 v5 v9 v13 x y).1, v2, v3, v4, (Gw v1 v5 v9 v13 x y).2.1, v6, v7, v8, (Gw v1 v5 v9 v13 x y).2.2.1, v10, v11, v12, (Gw v1 v5 v9 v13 x y).2.2.2, v14, v15] := rfl
theorem G_pos_2_6_10_14 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : Word) :
    G [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 2 6 10 14 x y =
      [v0, v1, (Gw v2 v6 v10 v14 x y).1, v3, v4, v5, (Gw v2 v6 v10 v14 x y).2.1, v7, v8, v9, (Gw v2 v6 v10 v14 x y).2.2.1, v11, v12, v13, (Gw v2 v6 v10 v14 x y).2.2.2, v15] := rfl
theorem G_pos_3_7_11_15 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : Word) :
    G [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 3 7 11 15 x y =
      [v0, v1, v2, (Gw v3 v7 v11 v15 x y).1, v4, v5, v6, (Gw v3 v7 v11 v15 x y).2.1, v8, v9, v10, (Gw v3 v7 v11 v15 x y).2.2.1, v12, v13, v14, (Gw v3 v7 v11 v15 x y).2.2.2] := rfl
theorem G_pos_0_5_10_15 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : Word) :
    G [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 0 5 10 15 x y =
      [(Gw v0 v5 v10 v15 x y).1, v1, v2, v3, v4, (Gw v0 v5 v10 v15 x y).2.1, v6, v7, v8, v9, (Gw v0 v5 v10 v15 x y).2.2.1, v11, v12, v13, v14, (Gw v0 v5 v10 v15 x y).2.2.2] := rfl
theorem G_pos_1_6_11_12 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : Word) :
    G [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 1 6 11 12 x y =
      [v0, (Gw v1 v6 v11 v12 x y).1, v2, v3, v4, v5, (Gw v1 v6 v11 v12 x y).2.1, v7, v8, v9, v10, (Gw v1 v6 v11 v12 x y).2.2.1, (Gw v1 v6 v11 v12 x y).2.2.2, v13, v14, v15] := rfl
theorem G_pos_2_7_8_13 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : Word) :
    G [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 2 7 8 13 x y =
      [v0, v1, (Gw v2 v7 v8 v13 x y).1, v3, v4, v5, v6, (Gw v2 v7 v8 v13 x y).2.1, (Gw v2 v7 v8 v13 x y).2.2.1, v9, v10, v11, v12, (Gw v2 v7 v8 v13 x y).2.2.2, v14, v15] := rfl
theorem G_pos_3_4_9_14 (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 x y : Word) :
    G [v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15] 3 4 9 14 x y =
      [v0, v1, v2, (Gw v3 v4 v9 v14 x y).1, (Gw v3 v4 v9 v14 x y).2.1, v5, v6, v7, v8, (Gw v3 v4 v9 v14 x y).2.2.1, v10, v11, v12, v13, (Gw v3 v4 v9 v14 x y).2.2.2, v15] := rfl

theorem round_eq_0 (v : List Word) (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Word) : round v [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] 0 =
    G (G (G (G (G (G (G (G v 0 4 8 12 m0 m1) 1 5 9 13 m2 m3) 2 6 10 14 m4 m5) 3 7 11 15 m6 m7) 0 5 10 15 m8 m9) 1 6 11 12 m10 m11) 2 7 8 13 m12 m13) 3 4 9 14 m14 m15 := by
  simp only [round, roundWith, sigma, Nat.reduceMod, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

theorem round_eq_1 (v : List Word) (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Word) : round v [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] 1 =
    G (G (G (G (G (G (G (G v 0 4 8 12 m14 m10) 1 5 9 13 m4 m8) 2 6 10 14 m9 m15) 3 7 11 15 m13 m6) 0 5 10 15 m1 m12) 1 6 11 12 m0 m2) 2 7 8 13 m11 m7) 3 4 9 14 m5 m3 := by
  simp only [round, roundWith, sigma, Nat.reduceMod, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

theorem round_eq_2 (v : List Word) (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Word) : round v [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] 2 =
    G (G (G (G (G (G (G (G v 0 4 8 12 m11 m8) 1 5 9 13 m12 m0) 2 6 10 14 m5 m2) 3 7 11 15 m15 m13) 0 5 10 15 m10 m14) 1 6 11 12 m3 m6) 2 7 8 13 m7 m1) 3 4 9 14 m9 m4 := by
  simp only [round, roundWith, sigma, Nat.reduceMod, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

theorem round_eq_3 (v : List Word) (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Word) : round v [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] 3 =
    G (G (G (G (G (G (G (G v 0 4 8 12 m7 m9) 1 5 9 13 m3 m1) 2 6 10 14 m13 m12) 3 7 11 15 m11 m14) 0 5 10 15 m2 m6) 1 6 11 12 m5 m10) 2 7 8 13 m4 m0) 3 4 9 14 m15 m8 := by
  simp only [round, roundWith, sigma, Nat.reduceMod, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

theorem round_eq_4 (v : List Word) (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Word) : round v [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] 4 =
    G (G (G (G (G (G (G (G v 0 4 8 12 m9 m0) 1 5 9 13 m5 m7) 2 6 10 14 m2 m4) 3 7 11 15 m10 m15) 0 5 10 15 m14 m1) 1 6 11 12 m11 m12) 2 7 8 13 m6 m8) 3 4 9 14 m3 m13 := by
  simp only [round, roundWith, sigma, Nat.reduceMod, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

theorem round_eq_5 (v : List Word) (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Word) : round v [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] 5 =
    G (G (G (G (G (G (G (G v 0 4 8 12 m2 m12) 1 5 9 13 m6 m10) 2 6 10 14 m0 m11) 3 7 11 15 m8 m3) 0 5 10 15 m4 m13) 1 6 11 12 m7 m5) 2 7 8 13 m15 m14) 3 4 9 14 m1 m9 := by
  simp only [round, roundWith, sigma, Nat.reduceMod, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

theorem round_eq_6 (v : List Word) (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Word) : round v [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] 6 =
    G (G (G (G (G (G (G (G v 0 4 8 12 m12 m5) 1 5 9 13 m1 m15) 2 6 10 14 m14 m13) 3 7 11 15 m4 m10) 0 5 10 15 m0 m7) 1 6 11 12 m6 m3) 2 7 8 13 m9 m2) 3 4 9 14 m8 m11 := by
  simp only [round, roundWith, sigma, Nat.reduceMod, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

theorem round_eq_7 (v : List Word) (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Word) : round v [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] 7 =
    G (G (G (G (G (G (G (G v 0 4 8 12 m13 m11) 1 5 9 13 m7 m14) 2 6 10 14 m12 m1) 3 7 11 15 m3 m9) 0 5 10 15 m5 m0) 1 6 11 12 m15 m4) 2 7 8 13 m8 m6) 3 4 9 14 m2 m10 := by
  simp only [round, roundWith, sigma, Nat.reduceMod, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

theorem round_eq_8 (v : List Word) (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Word) : round v [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] 8 =
    G (G (G (G (G (G (G (G v 0 4 8 12 m6 m15) 1 5 9 13 m14 m9) 2 6 10 14 m11 m3) 3 7 11 15 m0 m8) 0 5 10 15 m12 m2) 1 6 11 12 m13 m7) 2 7 8 13 m1 m4) 3 4 9 14 m10 m5 := by
  simp only [round, roundWith, sigma, Nat.reduceMod, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

theorem round_eq_9 (v : List Word) (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Word) : round v [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] 9 =
    G (G (G (G (G (G (G (G v 0 4 8 12 m10 m2) 1 5 9 13 m8 m4) 2 6 10 14 m7 m6) 3 7 11 15 m1 m5) 0 5 10 15 m15 m11) 1 6 11 12 m9 m14) 2 7 8 13 m3 m12) 3 4 9 14 m13 m0 := by
  simp only [round, roundWith, sigma, Nat.reduceMod, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

theorem round_eq_10 (v : List Word) (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Word) : round v [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] 10 =
    G (G (G (G (G (G (G (G v 0 4 8 12 m0 m1) 1 5 9 13 m2 m3) 2 6 10 14 m4 m5) 3 7 11 15 m6 m7) 0 5 10 15 m8 m9) 1 6 11 12 m10 m11) 2 7 8 13 m12 m13) 3 4 9 14 m14 m15 := by
  simp only [round, roundWith, sigma, Nat.reduceMod, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

theorem round_eq_11 (v : List Word) (m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 : Word) : round v [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15] 11 =
    G (G (G (G (G (G (G (G v 0 4 8 12 m14 m10) 1 5 9 13 m4 m8) 2 6 10 14 m9 m15) 3 7 11 15 m13 m6) 0 5 10 15 m1 m12) 1 6 11 12 m0 m2) 2 7 8 13 m11 m7) 3 4 9 14 m5 m3 := by
  simp only [round, roundWith, sigma, Nat.reduceMod, List.getD_eq_getElem?_getD, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some]

theorem initV_eq (h0 h1 h2 h3 h4 h5 h6 h7 t0 t1 fb fn : Word) :
    initV [h0, h1, h2, h3, h4, h5, h6, h7] t0 t1 fb fn =
      [h0, h1, h2, h3, h4, h5, h6, h7, 0x6A09E667F3BCC908#64, 0xBB67AE8584CAA73B#64,
       0x3C6EF372FE94F82B#64, 0xA54FF53A5F1D36F1#64, 0x510E527FADE682D1#64 ^^^ t0,
       0x9B05688C2B3E6C1F#64 ^^^ t1, 0x1F83D9ABFB41BD6B#64 ^^^ fb, 0x5BE0CD19137E2179#64 ^^^ fn] := rfl

theorem roundsTo_succ (h m : List Word) (t0 t1 fb fn : Word) (k : Nat) :
    roundsTo h m t0 t1 fb fn (k + 1) = round (roundsTo h m t0 t1 fb fn k) m k := by
  simp only [roundsTo, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem roundsTo_zero (h m : List Word) (t0 t1 fb fn : Word) :
    roundsTo h m t0 t1 fb fn 0 = initV h t0 t1 fb fn := rfl

theorem roundsTo_1 (h m : List Word) (t0 t1 fb fn : Word) :
    roundsTo h m t0 t1 fb fn 1 = round (initV h t0 t1 fb fn) m 0 := by
  simp only [roundsTo, List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem roundsTo_4 (h m : List Word) (t0 t1 fb fn : Word) :
    roundsTo h m t0 t1 fb fn 4 =
      round (round (round (round (initV h t0 t1 fb fn) m 0) m 1) m 2) m 3 := by
  simp only [roundsTo, List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem roundsTo_8 (h m : List Word) (t0 t1 fb fn : Word) :
    roundsTo h m t0 t1 fb fn 8 =
      round (round (round (round (roundsTo h m t0 t1 fb fn 4) m 4) m 5) m 6) m 7 := by
  simp only [roundsTo, List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem roundsTo_12 (h m : List Word) (t0 t1 fb fn : Word) :
    roundsTo h m t0 t1 fb fn 12 =
      round (round (round (round (roundsTo h m t0 t1 fb fn 8) m 8) m 9) m 10) m 11 := by
  simp only [roundsTo, List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem compress_length (h m : List Word) (t0 t1 fb fn : Word) : (compress h m t0 t1 fb fn).length = 8 := by
  simp only [compress, List.length_map, List.length_range]

theorem compress_eq {h0 h1 h2 h3 h4 h5 h6 h7 : Word} {m : List Word} {t0 t1 fb fn : Word}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : Word}
    (hv : roundsTo [h0, h1, h2, h3, h4, h5, h6, h7] m t0 t1 fb fn 12 =
      [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15]) :
    compress [h0, h1, h2, h3, h4, h5, h6, h7] m t0 t1 fb fn =
      [h0 ^^^ w0 ^^^ w8, h1 ^^^ w1 ^^^ w9, h2 ^^^ w2 ^^^ w10, h3 ^^^ w3 ^^^ w11,
       h4 ^^^ w4 ^^^ w12, h5 ^^^ w5 ^^^ w13, h6 ^^^ w6 ^^^ w14, h7 ^^^ w7 ^^^ w15] := by
  simp only [compress, hv]; rfl

end Cases.Zip2005.B2b
