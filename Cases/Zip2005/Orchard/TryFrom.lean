import Cases.Zip2005.Field.FqFromRepr
import Cases.Zip2005.Orchard.Randomize
import Cases.Zip2005.Orchard.NoteCommitDerive
import Cases.Zip2005.Image.F_78022f5c
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `TryFrom<[u8; 32]> for SigningKey<SpendAuth>` (0x78022f5c)

The 32 bytes reassembled into four little-endian words (byte loads, so the input may sit at any
address), `Fq::from_repr`; on a canonical scalar `sk`, `[sk] G_SpendAuth` (`spendauth_basepoint`,
`Ep::mul`), its `Ep::to_bytes`, and the result `Ok(SigningKey { vk: (point, bytes), sk })`: the
tag byte cleared, then the 160 bytes. Otherwise `Err` (the tag halfword `1`). A flag byte other
than `0`/`1` would `assert_failed` (it cannot: `from_repr` returns a `Choice`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- The scalar of a canonical representation, as `Fq::from_repr` leaves it (Montgomery limbs). -/
def skW (r : List Word) : List Word := natToLeLimbs 4 (Fq.mul (leLimbsToNat r) Fq.R2)

/-- `Ep::to_bytes` of a point given by its twelve words. -/
def ptBytesW (m : List Word) : List Word := toBytesW (ptX m, ptY m, ptZ m)

/-- The `Result<SigningKey<SpendAuth>, Error>` `try_from` writes over `O` (21 words) for the
representation `r` and the basepoint `G` (as `spendauth_basepoint` decodes it). -/
def tryFromW (O r G : List Word) : List Word :=
  if leLimbsToNat r < Fq.q then
    replaceByte O[0]! 0 0#8 :: (mulW G (skW r) ++ ptBytesW (mulW G (skW r)) ++ skW r)
  else replaceHalfword O[0]! 0 1#16 :: (List.range 20).map (fun i => O[i + 1]!)

@[simp] theorem tryFromW_length (O r G : List Word) : (tryFromW O r G).length = 21 := by
  unfold tryFromW
  split
  · rw [List.length_cons, List.length_append, List.length_append, length_mulW, ptBytesW, toBytesW, skW,
      length_natToLeLimbs, length_natToLeLimbs]
  · rw [List.length_cons, List.length_map, List.length_range]

/-- A word read at byte offset 2 of the cells `a`, `b`: bytes 2–7 of `a`, then 0–1 of `b`. -/
def unsplice2 (a b : Word) : Word := (a >>> 16) ||| (b <<< 48)

/-- The byte loads of a doubleword at byte offset 2, reassembled as `from_repr`'s caller does. -/
theorem bytes_word2 (a b : BitVec 64) :
    ((BitVec.zeroExtend 64 (extractByte b 1) <<< 24 ||| BitVec.zeroExtend 64 (extractByte b 0) <<< 16) |||
        (BitVec.zeroExtend 64 (extractByte a 7) <<< 8 ||| BitVec.zeroExtend 64 (extractByte a 6))) <<< 32 |||
      ((BitVec.zeroExtend 64 (extractByte a 5) <<< 24 ||| BitVec.zeroExtend 64 (extractByte a 4) <<< 16) |||
        (BitVec.zeroExtend 64 (extractByte a 3) <<< 8 ||| BitVec.zeroExtend 64 (extractByte a 2))) =
      unsplice2 a b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [unsplice2, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, extractByte, BitVec.truncate_eq_setWidth,
    BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
set_option asmverif.sym.foldBytes true in
/-- `try_from` on a representation held in four aligned words `r0 … r3`. -/
theorem try_from_spec {Gd : MachineState → Prop} {nb : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out a1 : Word)
    (r0 r1 r2 r3 : Word)
    (cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (O IV G0 G1 G2 G3 : List Word)
    (hOl : O.length = 21) (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN Gd nb P u)
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN Gd nb P u)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN Gd nb P u)
    (hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN Gd nb P u)
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN Gd nb P u)
    (hpc : s.pc = 0x78022f5c#64) (hcode : CodeAt F_78022f5c.base F_78022f5c.prog s)
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
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x980 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = a1)
    (hA : Region a1 [r0, r1, r2, r3] s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region out O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi out 21)
    (hbelow_out : out.toNat + 8 * 21 ≤ 0x78040620)
    -- `FP_TABLES`, initialised (`Once` state byte 2 at 0x780488f0, padding zero)
    (hTB : Region 0x780488a8#64 [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx, 2#64] s)
    (hIV : Region iptr IV s) (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hG0 : Region g0 G0 s) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024)
    (hG1 : Region g1 G1 s) (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024)
    (hG2 : Region g2 G2 s) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024)
    (hG3 : Region g3 G3 s) (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hd0 : Disjoint (sp - 0x980#64) 304 out 21) (hdA : Disjoint (sp - 0x980#64) 304 a1 4)
    (hd_tb : Disjoint (sp - 0x980#64) 304 0x780488a8#64 10)
    (hd_iptr : Disjoint (sp - 0x980#64) 304 iptr 138)
    (hd_g0 : Disjoint (sp - 0x980#64) 304 g0 1024) (hd_g1 : Disjoint (sp - 0x980#64) 304 g1 1024)
    (hd_g2 : Disjoint (sp - 0x980#64) 304 g2 1024) (hd_g3 : Disjoint (sp - 0x980#64) 304 g3 516)
    (heA : Disjoint out 21 a1 4)
    (he_tb : Disjoint out 21 0x780488a8#64 10) (he_iptr : Disjoint out 21 iptr 138)
    (he_g0 : Disjoint out 21 g0 1024) (he_g1 : Disjoint out 21 g1 1024)
    (he_g2 : Disjoint out 21 g2 1024) (he_g3 : Disjoint out 21 g3 516)
    (hk : ∀ (t : MachineState) (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word),
      t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x980#64, 304), (out, 21)] s t →
      (leLimbsToNat [r0, r1, r2, r3] < Fq.q →
        FromBytesPost 0x8d1a7284b875c963#64 0xc7f0ce37b70a10c#64 0x3b8d187c3e5f445f#64 0xb75523b328f1d606#64
          (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) 1#8 ∧
        leLimbsToNat [z0, z1, z2, z3] =
          (if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R) ∧
        mulFacts [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] (skW [r0, r1, r2, r3])) →
      Region out (tryFromW O [r0, r1, r2, r3] [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3]) t →
      SafeN Gd nb P t) :
    SafeN Gd nb P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x980#64) 304 := hstk.frame 304 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x160#64) 44 := hokW.sub' 260 44 (by decide) (by bv_omega)
  -- the frame: [8, 0x30) `from_repr`'s `CtOption<Fq>`, [0x30, 0x50) the scalar, [0x50, 0xf0) the
  -- words for `from_repr`, then the basepoint, the result's point, bytes and scalar,
  -- [0xf0, 0x150) `[sk] G`, saved registers at 0x150
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x158#64) 5 := hokF.sub' 1 5 (by decide) (by bv_omega)
  have hokK : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x130#64) 4 := hokF.sub' 6 4 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x110#64) 20 := hokF.sub' 10 20 (by decide) (by bv_omega)
  have hokM : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x70#64) 12 := hokF.sub' 30 12 (by decide) (by bv_omega)
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokF.sub' 42 2 (by decide) (by bv_omega)
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x158#64) 5 s
  obtain ⟨FK, hFK, hFKl⟩ := Region.exists_junk (sp - 0x130#64) 4 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x110#64) 20 s
  obtain ⟨FM, hFM, hFMl⟩ := Region.exists_junk (sp - 0x70#64) 12 s
  obtain ⟨FE, hFE, hFEl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hhF : Disjoint 0x78040620#64 14780694332 (sp - 0x980#64) 304 := Disjoint.heap_frame (n := 304) hstk (by decide)
  have hlo := hstk.lo
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hu := Unchanged.refl [(sp - 0x980#64, 304), (out, 21)] s
  sym_exec [fq_from_repr_spec] stop [0x780230e4]
  -- the four words, reassembled from their bytes
  have hw3 : v25 = r3 := by
    simp only [← v4_def, ← v5_def, ← v6_def, ← v7_def, ← v8_def, ← v9_def, ← v10_def, ← v11_def, ← v12_def, ← v13_def, ← v14_def, ← v15_def, ← v16_def, ← v17_def, ← v18_def, ← v19_def, ← v20_def, ← v21_def, ← v22_def, ← v23_def, ← v24_def, ← v25_def]
    exact bytes_word r3
  have hw2 : v47 = r2 := by
    simp only [← v26_def, ← v27_def, ← v28_def, ← v29_def, ← v30_def, ← v31_def, ← v32_def, ← v33_def, ← v34_def, ← v35_def, ← v36_def, ← v37_def, ← v38_def, ← v39_def, ← v40_def, ← v41_def, ← v42_def, ← v43_def, ← v44_def, ← v45_def, ← v46_def, ← v47_def]
    exact bytes_word r2
  have hw1 : v69 = r1 := by
    simp only [← v48_def, ← v49_def, ← v50_def, ← v51_def, ← v52_def, ← v53_def, ← v54_def, ← v55_def, ← v56_def, ← v57_def, ← v58_def, ← v59_def, ← v60_def, ← v61_def, ← v62_def, ← v63_def, ← v64_def, ← v65_def, ← v66_def, ← v67_def, ← v68_def, ← v69_def]
    exact bytes_word r1
  have hw0 : v91 = r0 := by
    simp only [← v70_def, ← v71_def, ← v72_def, ← v73_def, ← v74_def, ← v75_def, ← v76_def, ← v77_def, ← v78_def, ← v79_def, ← v80_def, ← v81_def, ← v82_def, ← v83_def, ← v84_def, ← v85_def, ← v86_def, ← v87_def, ← v88_def, ← v89_def, ← v90_def, ← v91_def]
    exact bytes_word r0
  rw [hw0, hw1, hw2, hw3] at hR10
  sym_reframe
  sym_exec [fq_from_repr_spec, spendauth_basepoint_spec, ep_mul_fq_spec, ep_to_bytes_spec,
    memcpy96_spec, memcpy160_spec, hpb, hpaf, hpp, hprz, hpanic]
  · -- `Err`: a non-canonical representation
    have hnq : ¬ leLimbsToNat [r0, r1, r2, r3] < Fq.q := by
      intro h; rw [if_pos h] at v3_def; rw [← v3_def] at hbr4; exact absurd hbr4 (by decide)
    have hRo : Region out (tryFromW O [r0, r1, r2, r3] (List.replicate 12 0#64)) s_11 := by
      unfold tryFromW
      rw [if_neg hnq]
      rw [← v6_def] at hR1
      exact hR1
    clear hR1
    sym_close (hk _ 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64)
  · -- `Ok`: `[sk] G`, its bytes, `sk`
    have hq : leLimbsToNat [r0, r1, r2, r3] < Fq.q := by
      refine Classical.byContradiction fun h => ?_
      rw [if_neg h] at v3_def; rw [← v3_def] at hbr4; exact hbr4 (by decide)
    have hk8 : [v8, v9, v10, v11] = skW [r0, r1, r2, r3] := by
      rw [skW, natToLeLimbs_cells4, ← v8_def, ← v9_def, ← v10_def, ← v11_def, Nat.shiftRight_zero]
    have hk37 : [v37, v38, v39, v40] = skW [r0, r1, r2, r3] := by
      rw [skW, natToLeLimbs_cells4, ← v37_def, ← v38_def, ← v39_def, ← v40_def, Nat.shiftRight_zero]
    rw [hk8] at post25_4 post25_6 acc25_0_def
    have hb : ptBytesW acc25_0 = natToLeLimbs 4 acc30_0 := by rw [← acc30_0_def]; rfl
    have hRo : Region out (tryFromW O [r0, r1, r2, r3] [post19_0, post19_1, post19_2, post19_3, post19_4, post19_5, post19_6, post19_7, post19_8, post19_9, post19_10, post19_11]) s_56 := by
      unfold tryFromW
      rw [if_pos hq, acc25_0_def, hb, ← hk37, natToLeLimbs_cells4,
        ← cells12_eq acc25_0 (acc25_0_def ▸ post25_4)]
      rw [← v51_def] at hR1
      exact hR1
    clear hR1
    sym_close (hk _ post19_0 post19_1 post19_2 post19_3 post19_4 post19_5 post19_6 post19_7 post19_8 post19_9 post19_10 post19_11)
    all_goals exact fun _ => ⟨post19_16, post19_17, post25_6⟩




set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
set_option asmverif.sym.foldBytes true in
/-- `try_from` on a representation at byte offset 2 of the five aligned words `c0 … c4` (as
`derive_unchecked` leaves `to_repr`'s bytes at `sp + 0x2a`). -/
theorem try_from_off2_spec {Gd : MachineState → Prop} {nb : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out b : Word)
    (c0 c1 c2 c3 c4 : Word)
    (cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (O IV G0 G1 G2 G3 : List Word)
    (hOl : O.length = 21) (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN Gd nb P u)
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN Gd nb P u)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN Gd nb P u)
    (hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN Gd nb P u)
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN Gd nb P u)
    (hpc : s.pc = 0x78022f5c#64) (hcode : CodeAt F_78022f5c.base F_78022f5c.prog s)
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
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x980 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = b + 2#64)
    (hA : Region b [c0, c1, c2, c3, c4] s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi b 5)
    (hO : Region out O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi out 21)
    (hbelow_out : out.toNat + 8 * 21 ≤ 0x78040620)
    -- `FP_TABLES`, initialised (`Once` state byte 2 at 0x780488f0, padding zero)
    (hTB : Region 0x780488a8#64 [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx, 2#64] s)
    (hIV : Region iptr IV s) (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hG0 : Region g0 G0 s) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024)
    (hG1 : Region g1 G1 s) (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024)
    (hG2 : Region g2 G2 s) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024)
    (hG3 : Region g3 G3 s) (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hd0 : Disjoint (sp - 0x980#64) 304 out 21) (hdA : Disjoint (sp - 0x980#64) 304 b 5)
    (hd_tb : Disjoint (sp - 0x980#64) 304 0x780488a8#64 10)
    (hd_iptr : Disjoint (sp - 0x980#64) 304 iptr 138)
    (hd_g0 : Disjoint (sp - 0x980#64) 304 g0 1024) (hd_g1 : Disjoint (sp - 0x980#64) 304 g1 1024)
    (hd_g2 : Disjoint (sp - 0x980#64) 304 g2 1024) (hd_g3 : Disjoint (sp - 0x980#64) 304 g3 516)
    (heA : Disjoint out 21 b 5)
    (he_tb : Disjoint out 21 0x780488a8#64 10) (he_iptr : Disjoint out 21 iptr 138)
    (he_g0 : Disjoint out 21 g0 1024) (he_g1 : Disjoint out 21 g1 1024)
    (he_g2 : Disjoint out 21 g2 1024) (he_g3 : Disjoint out 21 g3 516)
    (hk : ∀ (t : MachineState) (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word),
      t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x980#64, 304), (out, 21)] s t →
      (leLimbsToNat [unsplice2 c0 c1, unsplice2 c1 c2, unsplice2 c2 c3, unsplice2 c3 c4] < Fq.q →
        FromBytesPost 0x8d1a7284b875c963#64 0xc7f0ce37b70a10c#64 0x3b8d187c3e5f445f#64 0xb75523b328f1d606#64
          (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) 1#8 ∧
        leLimbsToNat [z0, z1, z2, z3] =
          (if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R) ∧
        mulFacts [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] (skW [unsplice2 c0 c1, unsplice2 c1 c2, unsplice2 c2 c3, unsplice2 c3 c4])) →
      Region out (tryFromW O [unsplice2 c0 c1, unsplice2 c1 c2, unsplice2 c2 c3, unsplice2 c3 c4] [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3]) t →
      SafeN Gd nb P t) :
    SafeN Gd nb P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x980#64) 304 := hstk.frame 304 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x160#64) 44 := hokW.sub' 260 44 (by decide) (by bv_omega)
  -- the frame: [8, 0x30) `from_repr`'s `CtOption<Fq>`, [0x30, 0x50) the scalar, [0x50, 0xf0) the
  -- words for `from_repr`, then the basepoint, the result's point, bytes and scalar,
  -- [0xf0, 0x150) `[sk] G`, saved registers at 0x150
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x158#64) 5 := hokF.sub' 1 5 (by decide) (by bv_omega)
  have hokK : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x130#64) 4 := hokF.sub' 6 4 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x110#64) 20 := hokF.sub' 10 20 (by decide) (by bv_omega)
  have hokM : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x70#64) 12 := hokF.sub' 30 12 (by decide) (by bv_omega)
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokF.sub' 42 2 (by decide) (by bv_omega)
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x158#64) 5 s
  obtain ⟨FK, hFK, hFKl⟩ := Region.exists_junk (sp - 0x130#64) 4 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x110#64) 20 s
  obtain ⟨FM, hFM, hFMl⟩ := Region.exists_junk (sp - 0x70#64) 12 s
  obtain ⟨FE, hFE, hFEl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hhF : Disjoint 0x78040620#64 14780694332 (sp - 0x980#64) 304 := Disjoint.heap_frame (n := 304) hstk (by decide)
  have hlo := hstk.lo
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hu := Unchanged.refl [(sp - 0x980#64, 304), (out, 21)] s
  sym_exec [fq_from_repr_spec] stop [0x780230e4]
  -- the four words, reassembled from their bytes
  have hw3 : v25 = unsplice2 c3 c4 := by
    simp only [← v4_def, ← v5_def, ← v6_def, ← v7_def, ← v8_def, ← v9_def, ← v10_def, ← v11_def, ← v12_def, ← v13_def, ← v14_def, ← v15_def, ← v16_def, ← v17_def, ← v18_def, ← v19_def, ← v20_def, ← v21_def, ← v22_def, ← v23_def, ← v24_def, ← v25_def]
    exact bytes_word2 c3 c4
  have hw2 : v47 = unsplice2 c2 c3 := by
    simp only [← v26_def, ← v27_def, ← v28_def, ← v29_def, ← v30_def, ← v31_def, ← v32_def, ← v33_def, ← v34_def, ← v35_def, ← v36_def, ← v37_def, ← v38_def, ← v39_def, ← v40_def, ← v41_def, ← v42_def, ← v43_def, ← v44_def, ← v45_def, ← v46_def, ← v47_def]
    exact bytes_word2 c2 c3
  have hw1 : v69 = unsplice2 c1 c2 := by
    simp only [← v48_def, ← v49_def, ← v50_def, ← v51_def, ← v52_def, ← v53_def, ← v54_def, ← v55_def, ← v56_def, ← v57_def, ← v58_def, ← v59_def, ← v60_def, ← v61_def, ← v62_def, ← v63_def, ← v64_def, ← v65_def, ← v66_def, ← v67_def, ← v68_def, ← v69_def]
    exact bytes_word2 c1 c2
  have hw0 : v91 = unsplice2 c0 c1 := by
    simp only [← v70_def, ← v71_def, ← v72_def, ← v73_def, ← v74_def, ← v75_def, ← v76_def, ← v77_def, ← v78_def, ← v79_def, ← v80_def, ← v81_def, ← v82_def, ← v83_def, ← v84_def, ← v85_def, ← v86_def, ← v87_def, ← v88_def, ← v89_def, ← v90_def, ← v91_def]
    exact bytes_word2 c0 c1
  rw [hw0, hw1, hw2, hw3] at hR10
  sym_reframe
  sym_exec [fq_from_repr_spec, spendauth_basepoint_spec, ep_mul_fq_spec, ep_to_bytes_spec,
    memcpy96_spec, memcpy160_spec, hpb, hpaf, hpp, hprz, hpanic]
  · -- `Err`: a non-canonical representation
    have hnq : ¬ leLimbsToNat [unsplice2 c0 c1, unsplice2 c1 c2, unsplice2 c2 c3, unsplice2 c3 c4] < Fq.q := by
      intro h; rw [if_pos h] at v3_def; rw [← v3_def] at hbr4; exact absurd hbr4 (by decide)
    have hRo : Region out (tryFromW O [unsplice2 c0 c1, unsplice2 c1 c2, unsplice2 c2 c3, unsplice2 c3 c4] (List.replicate 12 0#64)) s_11 := by
      unfold tryFromW
      rw [if_neg hnq]
      rw [← v6_def] at hR1
      exact hR1
    clear hR1
    sym_close (hk _ 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64 0#64)
  · -- `Ok`: `[sk] G`, its bytes, `sk`
    have hq : leLimbsToNat [unsplice2 c0 c1, unsplice2 c1 c2, unsplice2 c2 c3, unsplice2 c3 c4] < Fq.q := by
      refine Classical.byContradiction fun h => ?_
      rw [if_neg h] at v3_def; rw [← v3_def] at hbr4; exact hbr4 (by decide)
    have hk8 : [v8, v9, v10, v11] = skW [unsplice2 c0 c1, unsplice2 c1 c2, unsplice2 c2 c3, unsplice2 c3 c4] := by
      rw [skW, natToLeLimbs_cells4, ← v8_def, ← v9_def, ← v10_def, ← v11_def, Nat.shiftRight_zero]
    have hk37 : [v37, v38, v39, v40] = skW [unsplice2 c0 c1, unsplice2 c1 c2, unsplice2 c2 c3, unsplice2 c3 c4] := by
      rw [skW, natToLeLimbs_cells4, ← v37_def, ← v38_def, ← v39_def, ← v40_def, Nat.shiftRight_zero]
    rw [hk8] at post25_4 post25_6 acc25_0_def
    have hb : ptBytesW acc25_0 = natToLeLimbs 4 acc30_0 := by rw [← acc30_0_def]; rfl
    have hRo : Region out (tryFromW O [unsplice2 c0 c1, unsplice2 c1 c2, unsplice2 c2 c3, unsplice2 c3 c4] [post19_0, post19_1, post19_2, post19_3, post19_4, post19_5, post19_6, post19_7, post19_8, post19_9, post19_10, post19_11]) s_56 := by
      unfold tryFromW
      rw [if_pos hq, acc25_0_def, hb, ← hk37, natToLeLimbs_cells4,
        ← cells12_eq acc25_0 (acc25_0_def ▸ post25_4)]
      rw [← v51_def] at hR1
      exact hR1
    clear hR1
    sym_close (hk _ post19_0 post19_1 post19_2 post19_3 post19_4 post19_5 post19_6 post19_7 post19_8 post19_9 post19_10 post19_11)
    all_goals exact fun _ => ⟨post19_16, post19_17, post25_6⟩



end Cases.Zip2005
