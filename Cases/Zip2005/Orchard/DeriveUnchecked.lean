import Cases.Zip2005.Orchard.TryFrom
import Cases.Zip2005.Field.FqReprOff
import Cases.Zip2005.Orchard.SpendingKeyFrom
import Cases.Zip2005.Field.FqNeg
import Cases.Zip2005.Image.F_7802233c
import Cases.Zip2005.Image.Ro

/-!
# `SpendAuthorizingKey::derive_unchecked` (0x7802233c)

`ask = ToScalar(PRF^expand_sk([6]))` (`PrfExpand::with`, `Fq::from_uniform_bytes`), negated when
the flag `neg` is set (the inline `Fq::neg`: `q - ask`, `0` for `0`), `to_repr`, then
`SigningKey::try_from` of those bytes, unwrapped (`unwrap_failed` otherwise), and its 160 bytes
copied out. With the flag set the bytes go through a frame buffer at byte offset 2.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym Cases.Zip2005.B2b

set_option autoImplicit false

/-- `ask` before the sign choice: `Fq::from_uniform_bytes(PrfExpand_sk([6]))`, a Montgomery
representative. -/
def askX (s0 s1 s2 s3 : Word) : Nat :=
  Fq.add
    (Fq.mul (leLimbsToNat [(prfExpandW 6#64 s0 s1 s2 s3)[0]!, (prfExpandW 6#64 s0 s1 s2 s3)[1]!,
      (prfExpandW 6#64 s0 s1 s2 s3)[2]!, (prfExpandW 6#64 s0 s1 s2 s3)[3]!]) Fq.R2)
    (Fq.mul (leLimbsToNat [(prfExpandW 6#64 s0 s1 s2 s3)[4]!, (prfExpandW 6#64 s0 s1 s2 s3)[5]!,
      (prfExpandW 6#64 s0 s1 s2 s3)[6]!, (prfExpandW 6#64 s0 s1 s2 s3)[7]!]) Fq.R3)

/-- `ask`, negated when `neg ≠ 0`. -/
def askK (neg s0 s1 s2 s3 : Word) : Nat :=
  if neg = 0#64 then askX s0 s1 s2 s3 else Fq.sub 0 (askX s0 s1 s2 s3)

/-- Its canonical representation (`to_repr`), as four words. -/
def askR (neg s0 s1 s2 s3 : Word) : List Word :=
  natToLeLimbs 4 (askK neg s0 s1 s2 s3 * Fq.rInv % Fq.q)

/-- The `SigningKey<SpendAuth>` `derive_unchecked` returns, for the basepoint `G`: the point
`[ask] G`, its bytes, the scalar. -/
def askW (neg s0 s1 s2 s3 : Word) (G : List Word) : List Word :=
  mulW G (skW (askR neg s0 s1 s2 s3)) ++ ptBytesW (mulW G (skW (askR neg s0 s1 s2 s3))) ++
    skW (askR neg s0 s1 s2 s3)

theorem askW_length (neg s0 s1 s2 s3 : Word) (G : List Word) : (askW neg s0 s1 s2 s3 G).length = 20 := by
  rw [askW, List.length_append, List.length_append, length_mulW, ptBytesW, toBytesW, skW,
    length_natToLeLimbs, length_natToLeLimbs]

/-- `try_from`'s words read back from the spliced cells are the limbs. -/
theorem unsplice_splice (W : List Word) (l0 l1 l2 l3 : Word) :
    [unsplice2 (splice2 W l0 l1 l2 l3)[0]! (splice2 W l0 l1 l2 l3)[1]!,
      unsplice2 (splice2 W l0 l1 l2 l3)[1]! (splice2 W l0 l1 l2 l3)[2]!,
      unsplice2 (splice2 W l0 l1 l2 l3)[2]! (splice2 W l0 l1 l2 l3)[3]!,
      unsplice2 (splice2 W l0 l1 l2 l3)[3]! (splice2 W l0 l1 l2 l3)[4]!] = [l0, l1, l2, l3] := by
  simp only [splice2, List.getElem!_cons_zero, List.getElem!_cons_succ, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [unsplice2, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
    interval_cases i <;> simp

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
set_option asmverif.sym.foldBytes true in
theorem derive_unchecked_spec {P : Prop} (s : MachineState) (ra sp out sk neg s0 s1 s2 s3 : Word)
    (cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (O IV G0 G1 G2 G3 : List Word)
    (hOl : O.length = 20) (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → Safe P u)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → Safe P u)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → Safe P u)
    (hprz : ∀ u : MachineState, u.pc = 0x7803de78#64 → u.code = s.code → Safe P u)
    (hpanic : ∀ u : MachineState, u.pc = 0x7803de40#64 → u.code = s.code → Safe P u)
    (hunwrap : ∀ u : MachineState, u.pc = 0x7803dc7c#64 → u.code = s.code → Safe P u)
    (hpc : s.pc = 0x7802233c#64) (hcode : CodeAt F_7802233c.base F_7802233c.prog s)
    -- `PrfExpand::with`
    (hcW : CodeAt F_78023308.base F_78023308.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    -- `Fq::from_uniform_bytes`, `to_repr`
    (hcodeFU : CodeAt F_7802f038.base F_7802f038.prog s) (hcodeU5 : CodeAt F_7802e5b4.base F_7802e5b4.prog s)
    -- `try_from` and its callees
    (hcodeTF : CodeAt F_78022f5c.base F_78022f5c.prog s)
    (hcodeFR : CodeAt F_7802ed10.base F_7802ed10.prog s)
    (hcodeBP : CodeAt F_78023278.base F_78023278.prog s)
    (hcodeU : CodeAt F_78026928.base F_78026928.prog s)
    (hcodeF : CodeAt F_78025a1c.base F_78025a1c.prog s)
    (hcodeMC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeP : CodeAt F_78029d94.base F_78029d94.prog s)
    (hcodeC : CodeAt F_7802f358.base F_7802f358.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeA : CodeAt F_780315c0.base F_780315c0.prog s)
    (hcodeR : CodeAt F_78028298.base F_78028298.prog s)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog s)
    (hcodeW : CodeAt F_7802827c.base F_7802827c.prog s)
    (hcodeMul : CodeAt F_78031be8.base F_78031be8.prog s)
    (hcodeMS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s)
    (hcodeCo : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeRq : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    (hcodeAs : CodeAt F_78035fe0.base F_78035fe0.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcodeD : CodeAt F_780360c8.base F_780360c8.prog s)
    (hcodeLn : CodeAt F_780360e0.base F_780360e0.prog s)
    (hcodeAF : CodeAt F_7803a110.base F_7803a110.prog s)
    (hcodeAFI : CodeAt F_7803dd28.base F_7803dd28.prog s)
    (hcodeTB : CodeAt F_78025654.base F_78025654.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0xb50 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = sk) (ha2 : s.getReg .x12 = neg)
    (hRS : Region sk [s0, s1, s2, s3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi sk 4)
    (hO : Region out O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi out 20)
    -- `FP_TABLES`, initialised (`Once` state byte 2 at 0x780488f0, padding zero)
    (hTB : Region 0x780488a8#64 [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx, 2#64] s)
    (hIV : Region iptr IV s) (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hG0 : Region g0 G0 s) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024)
    (hG1 : Region g1 G1 s) (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024)
    (hG2 : Region g2 G2 s) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024)
    (hG3 : Region g3 G3 s) (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hd0 : Disjoint (sp - 0xb50#64) 362 out 20) (hdS : Disjoint (sp - 0xb50#64) 362 sk 4)
    (hd_tb : Disjoint (sp - 0xb50#64) 362 0x780488a8#64 10)
    (hd_iptr : Disjoint (sp - 0xb50#64) 362 iptr 138)
    (hd_g0 : Disjoint (sp - 0xb50#64) 362 g0 1024) (hd_g1 : Disjoint (sp - 0xb50#64) 362 g1 1024)
    (hd_g2 : Disjoint (sp - 0xb50#64) 362 g2 1024) (hd_g3 : Disjoint (sp - 0xb50#64) 362 g3 516)
    (heS : Disjoint out 20 sk 4)
    (he_tb : Disjoint out 20 0x780488a8#64 10) (he_iptr : Disjoint out 20 iptr 138)
    (he_g0 : Disjoint out 20 g0 1024) (he_g1 : Disjoint out 20 g1 1024)
    (he_g2 : Disjoint out 20 g2 1024) (he_g3 : Disjoint out 20 g3 516)
    (hk : ∀ (t : MachineState) (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word),
      t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0xb50#64, 362), (out, 20)] s t →
      FromBytesPost 0x8d1a7284b875c963#64 0xc7f0ce37b70a10c#64 0x3b8d187c3e5f445f#64 0xb75523b328f1d606#64
          (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) 1#8 ∧
        leLimbsToNat [z0, z1, z2, z3] =
          (if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R) ∧
        mulFacts [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] (skW (askR neg s0 s1 s2 s3)) →
      Region out (askW neg s0 s1 s2 s3 [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3]) t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb50#64) 362 := hstk.frame 362 (by decide)
  -- the frame (`sp' = sp - 0x1d0`): [8, 0x28) `ask`, [0x28, 0x50) the bytes at offset 2,
  -- [0x50, 0xf0) the copied key, [0xf0, 0x110) `-ask` or the aligned bytes, [0x110, 0x1b8)
  -- `PrfExpand`'s output then `try_from`'s result, saved registers at 0x1b8
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1c8#64) 4 := hokW.sub' 305 4 (by decide) (by bv_omega)
  have hokB : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1a8#64) 5 := hokW.sub' 309 5 (by decide) (by bv_omega)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x180#64) 20 := hokW.sub' 314 20 (by decide) (by bv_omega)
  have hokN : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xe0#64) 4 := hokW.sub' 334 4 (by decide) (by bv_omega)
  have hokT : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xc0#64) 21 := hokW.sub' 338 21 (by decide) (by bv_omega)
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x18#64) 3 := hokW.sub' 359 3 (by decide) (by bv_omega)
  -- `PrfExpand`'s frame blocks below ours
  have hokP1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x650#64) 74 := hokW.sub' 160 74 (by decide) (by bv_omega)
  have hokP2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x400#64) 70 := hokW.sub' 234 70 (by decide) (by bv_omega)
  obtain ⟨FA, hFA, hFAl⟩ := Region.exists_junk (sp - 0x1c8#64) 4 s
  obtain ⟨FB, hFB, hFBl⟩ := Region.exists_junk (sp - 0x1a8#64) 5 s
  obtain ⟨FC, hFC, hFCl⟩ := Region.exists_junk (sp - 0x180#64) 20 s
  obtain ⟨FN, hFN, hFNl⟩ := Region.exists_junk (sp - 0xe0#64) 4 s
  obtain ⟨FT, hFT, hFTl⟩ := Region.exists_junk (sp - 0xc0#64) 21 s
  obtain ⟨FE, hFE, hFEl⟩ := Region.exists_junk (sp - 0x18#64) 3 s
  obtain ⟨F1, hF1, hF1l⟩ := Region.exists_junk (sp - 0x650#64) 74 s
  obtain ⟨F2, hF2, hF2l⟩ := Region.exists_junk (sp - 0x400#64) 70 s
  have hhF : Disjoint 0x78040620#64 14780694332 (sp - 0xb50#64) 362 := Disjoint.heap_frame (n := 362) hstk (by decide)
  have hlo := hstk.lo
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hu := Unchanged.refl [(sp - 0xb50#64, 362), (out, 20)] s
  sym_exec [prf_expand_with_spec, fq_from_uniform_bytes_spec] stop [0x78022424, 0x7802247c]
  · -- `neg = 0`: the bytes of `ask`, aligned
    sym_reframe
    sym_exec [fq_to_repr_spec, try_from_spec, memcpy160_spec, hunwrap, hpb, hpaf, hpp, hprz, hpanic]
    have hn0 : neg = 0#64 := beq_iff_eq.mp hbr18
    have hX : askX s0 s1 s2 s3 = acc17_0 := by rw [← acc17_0_def, ← acc12_0_def]; rfl
    have hXq : acc17_0 < Fq.q := by rw [← hX]; exact Nat.mod_lt _ Fq.q_pos
    have hX256 : acc17_0 < 2 ^ 256 := lt_trans hXq Fq.q_lt
    -- the representation `try_from` read is `askR`
    have hr : natToLeLimbs 4 acc4_0 = askR neg s0 s1 s2 s3 := by
      rw [← acc4_0_def, AsmVerif.RiscV.Sym.cells4', leLimbsToNat_natToLeLimbs 4 _ hX256, askR, askK, if_pos hn0, hX]
    rw [AsmVerif.RiscV.Sym.cells4'] at acc9_0_def post9_16
    have hcan' : leLimbsToNat (natToLeLimbs 4 acc4_0) < Fq.q := by
      rw [hr, askR, leLimbsToNat_natToLeLimbs 4 _ (lt_trans (Nat.mod_lt _ Fq.q_pos) Fq.q_lt)]
      exact Nat.mod_lt _ Fq.q_pos
    obtain ⟨hfb, hz, hmf⟩ := post9_16 hcan'
    rw [hr] at hmf acc9_0_def
    have hRo : Region out (askW neg s0 s1 s2 s3 [post9_0, post9_1, post9_2, post9_3, post9_4, post9_5, post9_6, post9_7, post9_8, post9_9, post9_10, post9_11]) s_30 := by
      rw [← acc9_0_def] at hR1
      unfold tryFromW at hR1
      rw [if_pos (by rw [← hr]; exact hcan')] at hR1
      simp only [List.getElem!_cons_succ] at hR1
      rw [askW, AsmVerif.RiscV.Sym.List.eq_map_range (mulW [post9_0, post9_1, post9_2, post9_3, post9_4, post9_5, post9_6, post9_7, post9_8, post9_9, post9_10, post9_11] (skW (askR neg s0 s1 s2 s3)) ++
        ptBytesW (mulW [post9_0, post9_1, post9_2, post9_3, post9_4, post9_5, post9_6, post9_7, post9_8, post9_9, post9_10, post9_11] (skW (askR neg s0 s1 s2 s3))) ++ skW (askR neg s0 s1 s2 s3)) (n := 20)
        (askW_length neg s0 s1 s2 s3 [post9_0, post9_1, post9_2, post9_3, post9_4, post9_5, post9_6, post9_7, post9_8, post9_9, post9_10, post9_11])]
      exact hR1
    clear hR1
    sym_close (hk _ post9_0 post9_1 post9_2 post9_3 post9_4 post9_5 post9_6 post9_7 post9_8 post9_9 post9_10 post9_11)
    exact ⟨hfb, hz, hmf⟩
  · -- `neg ≠ 0`: the bytes of `-ask`, at `sp' + 0x2a`
    sym_reframe
    have hTR := fq_to_repr_off2_spec (P := P) (b := sp - 0x1a8#64)
    have hTF := try_from_off2_spec (P := P) (b := sp - 0x1a8#64)
    sym_exec [hTR, hTF, memcpy160_spec, hunwrap, hpb, hpaf, hpp, hprz, hpanic]
    have hn0 : neg ≠ 0#64 := fun h => hbr18 (beq_iff_eq.mpr h)
    have hX : askX s0 s1 s2 s3 = acc17_0 := by rw [← acc17_0_def, ← acc12_0_def]; rfl
    have hXq : acc17_0 < Fq.q := by rw [← hX]; exact Nat.mod_lt _ Fq.q_pos
    have hX256 : acc17_0 < 2 ^ 256 := lt_trans hXq Fq.q_lt
    -- `-ask`, by the inline negation
    have hY : leLimbsToNat [v19, v20, v21, v22] = acc17_0 := by
      rw [← v19_def, ← v20_def, ← v21_def, ← v22_def, Nat.shiftRight_zero]
      exact cells4_decode _ hX256
    have hneg := fqneg_chain v27_def v28_def v29_def v32_def v33_def v34_def v36_def v37_def v38_def
      v39_def v40_def v41_def v42_def v46_def v47_def v48_def v49_def v50_def v52_def v53_def v54_def
      v55_def (hY ▸ hXq)
    rw [hY] at hneg
    -- the words `try_from` read back from the cells at offset 2 are `to_repr`'s limbs
    have hu : [unsplice2 acc4_0[0]! acc4_0[1]!, unsplice2 acc4_0[1]! acc4_0[2]!,
        unsplice2 acc4_0[2]! acc4_0[3]!, unsplice2 acc4_0[3]! acc4_0[4]!] =
        [post4_0, post4_1, post4_2, post4_3] := by
      rw [← acc4_0_def]; exact unsplice_splice _ _ _ _ _
    have hr : [unsplice2 acc4_0[0]! acc4_0[1]!, unsplice2 acc4_0[1]! acc4_0[2]!,
        unsplice2 acc4_0[2]! acc4_0[3]!, unsplice2 acc4_0[3]! acc4_0[4]!] = askR neg s0 s1 s2 s3 := by
      rw [hu, post4_8, hneg, askR, askK, if_neg hn0, hX]
    have hcan' : leLimbsToNat [unsplice2 acc4_0[0]! acc4_0[1]!, unsplice2 acc4_0[1]! acc4_0[2]!,
        unsplice2 acc4_0[2]! acc4_0[3]!, unsplice2 acc4_0[3]! acc4_0[4]!] < Fq.q := by
      rw [hr, askR, leLimbsToNat_natToLeLimbs 4 _ (lt_trans (Nat.mod_lt _ Fq.q_pos) Fq.q_lt)]
      exact Nat.mod_lt _ Fq.q_pos
    obtain ⟨hfb, hz, hmf⟩ := post9_16 hcan'
    rw [hr] at hmf acc9_0_def
    have hRo : Region out (askW neg s0 s1 s2 s3 [post9_0, post9_1, post9_2, post9_3, post9_4, post9_5, post9_6, post9_7, post9_8, post9_9, post9_10, post9_11]) s_30 := by
      rw [← acc9_0_def] at hR0
      unfold tryFromW at hR0
      rw [if_pos (by rw [← hr]; exact hcan')] at hR0
      simp only [List.getElem!_cons_succ] at hR0
      rw [askW, AsmVerif.RiscV.Sym.List.eq_map_range (mulW [post9_0, post9_1, post9_2, post9_3, post9_4, post9_5, post9_6, post9_7, post9_8, post9_9, post9_10, post9_11] (skW (askR neg s0 s1 s2 s3)) ++
        ptBytesW (mulW [post9_0, post9_1, post9_2, post9_3, post9_4, post9_5, post9_6, post9_7, post9_8, post9_9, post9_10, post9_11] (skW (askR neg s0 s1 s2 s3))) ++ skW (askR neg s0 s1 s2 s3)) (n := 20)
        (askW_length neg s0 s1 s2 s3 [post9_0, post9_1, post9_2, post9_3, post9_4, post9_5, post9_6, post9_7, post9_8, post9_9, post9_10, post9_11])]
      exact hR0
    clear hR0
    sym_close (hk _ post9_0 post9_1 post9_2 post9_3 post9_4 post9_5 post9_6 post9_7 post9_8 post9_9 post9_10 post9_11)
    exact ⟨hfb, hz, hmf⟩

end Cases.Zip2005
