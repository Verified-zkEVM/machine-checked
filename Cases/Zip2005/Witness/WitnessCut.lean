import Cases.Zip2005.Witness.WitnessModel

/-! # The visitor's read phase against its second part

The second part (`Cases.Zip2005.witness_mid_spec`, from pc `0x78018a6c`) sees the input from word `s`
on (`s = 32` with `sk` `None`, `36` with `Some`): `cutW WW s`. Its model `midW` and the whole
visitor's `witW` agree byte by byte: the bytes with a symbolic stream offset (from `sigma_qsk`
on) and the condition `witOkCond` are related here once; the other cells per cell, generated
(`Proof/WitnessVisitorCells_*.lean`). -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- The input from word `s` on, 138 words: the second part's stream (`qb = q + 8 s`). -/
def cutW (WW : List Word) (s : Nat) : List Word := (List.range 138).map fun k => WW[s + k]!

theorem cutW_getElem! (WW : List Word) (s k : Nat) (h : k < 138) : (cutW WW s)[k]! = WW[s + k]! := by
  simp [cutW, h]

theorem inByte_cutW (WW : List Word) (s o k : Nat) (h : o + k < 1104) :
    inByte WW (8 * s + o) k = inByte (cutW WW s) o k := by
  simp only [inByte]
  rw [cutW_getElem! _ _ _ (by omega), show (8 * s + o + k) / 8 = s + (o + k) / 8 by omega,
    show (8 * s + o + k) % 8 = (o + k) % 8 by omega]

theorem witOptByte_cutW (WW V : List Word) (s o j p : Nat) (h : o + j < 1104) :
    witOptByte WW V (8 * s + o) j p = witOptByte (cutW WW s) V o j p := by
  simp only [witOptByte]
  rw [inByte_cutW WW s o 0 (by omega), inByte_cutW WW s o j h]

theorem optLen_le (t : BitVec 8) : optLen t ≤ 33 := by
  unfold optLen; split <;> omega

theorem midO3_le (W : List Word) : midO3 W ≤ 1070 := by
  unfold midO3; have := optLen_le (inByte W 1037 0); omega

theorem midO4_le (W : List Word) : midO4 W ≤ 1103 := by
  unfold midO4; have := midO3_le W; have := optLen_le (inByte W (midO3 W) 0); omega

theorem witO2_cut (WW : List Word) (s : Nat) (h1 : witO1 WW + 255 = 8 * s) :
    witO2 WW = 8 * s + 1037 := by
  unfold witO2; omega

theorem witO3_cut (WW : List Word) (s : Nat) (h1 : witO1 WW + 255 = 8 * s) :
    witO3 WW = 8 * s + midO3 (cutW WW s) := by
  unfold witO3 midO3
  rw [witO2_cut WW s h1, inByte_cutW WW s 1037 0 (by omega)]
  omega

theorem witO4_cut (WW : List Word) (s : Nat) (h1 : witO1 WW + 255 = 8 * s) :
    witO4 WW = 8 * s + midO4 (cutW WW s) := by
  unfold witO4 midO4
  rw [witO3_cut WW s h1, inByte_cutW WW s (midO3 (cutW WW s)) 0 (by have := midO3_le (cutW WW s); omega)]
  omega

/-- From the `qk` tag on (`0x52d ≤ p`), where the stream offsets are symbolic. -/
theorem witByte_eq_midByte_hi (WW V Fr : List Word) (r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word)
    (s p : Nat) (h1 : witO1 WW + 255 = 8 * s) (hp : 0x52d ≤ p) :
    witByte WW V p = midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (cutW WW s) V p := by
  have h3 := midO3_le (cutW WW s)
  have h4 := midO4_le (cutW WW s)
  unfold witByte midByte
  split_ifs <;> first
    | omega
    | (rw [witO2_cut WW s h1]; exact witOptByte_cutW WW V s 1037 (p - 0x52d) p (by omega))
    | (rw [witO3_cut WW s h1]; exact witOptByte_cutW WW V s (midO3 (cutW WW s)) (p - 0x54e) p (by omega))
    | (rw [witO4_cut WW s h1]; exact inByte_cutW WW s (midO4 (cutW WW s)) 0 (by omega))

/-- The cells from word 166 on (bytes `0x530` on). -/
theorem midW_witW_cell_hi (WW V Fr : List Word) (r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word)
    (s i : Nat) (h1 : witO1 WW + 255 = 8 * s) (hi : 166 ≤ i) (hi' : i < 174) :
    (midW Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (cutW WW s) V)[i]! = (witW WW V)[i]! := by
  rw [midW_getElem! _ _ _ _ _ _ _ _ _ _ _ _ _ i hi', witW_getElem! _ _ i hi']
  have e := fun k (hk : 0x52d ≤ 8 * i + k) =>
    witByte_eq_midByte_hi WW V Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 s (8 * i + k) h1 hk
  have e0 := e 0 (by omega)
  rw [Nat.add_zero] at e0
  rw [e0, e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega),
    e 6 (by omega), e 7 (by omega)]

/-- A cell of `V = R` through a model `M` of `V`. -/
theorem ext_cell {V M R : List Word} (i : Nat) (h1 : i < V.length) (h2 : i < R.length)
    (hV : V = M) (hc : M[i]! = R[i]!) : V[i] = R[i] :=
  (getElem!_pos V i h1).symm.trans ((congrArg (fun L : List Word => L[i]!) hV).trans
    (hc.trans (getElem!_pos R i h2)))

theorem witOkCond_of_mid (WW : List Word) (s l : Nat) (h1 : witO1 WW + 255 = 8 * s)
    (h0 : (inByte WW 0 0).toNat < 2) (hl : 8 * s + 1 ≤ l)
    (h : midOkCond (cutW WW s) (l - 8 * s - 1)) : witOkCond WW l := by
  obtain ⟨a, b, c, d⟩ := h
  refine ⟨h0, ?_, ?_, ?_, ?_⟩
  · rw [witO2_cut WW s h1, inByte_cutW WW s 1037 0 (by omega)]; exact a
  · rw [witO3_cut WW s h1, inByte_cutW WW s (midO3 (cutW WW s)) 0 (by have := midO3_le (cutW WW s); omega)]
    exact b
  · rw [witO4_cut WW s h1, inByte_cutW WW s (midO4 (cutW WW s)) 0 (by have := midO4_le (cutW WW s); omega)]
    exact c
  · rw [witO4_cut WW s h1]; omega

attribute [byte_simp] cutW_getElem!

end Cases.Zip2005
