import Cases.Zip2005.Poseidon.PoseidonPartial
import Cases.Zip2005.Poseidon.PoseidonPerm
import Cases.Zip2005.Poseidon.PoseidonTail
import Cases.Zip2005.Image.F_7801e26c
import AsmVerif.RiscV.Sym.Resume
import Cases.Zip2005.Image.Ro

/-!
# Poseidon's sponge step (`halo2_poseidon::poseidon_sponge`, `P128Pow5T3`, width 3, rate 2)

Absorb a padded block into the rate part of the state (`word += value.expect(..)`: two inline
`Fp` additions), permute (`halo2_poseidon::permute`: the round closures through their vtables,
driven by the chained `repeat(..).take(..)` iterator zipped with the round constants), and squeeze
the rate part into `Squeezing([Some(s0), Some(s1)])`.

The 64 rounds are executed in chunks (`AsmVerif.RiscV.Sym.Resume`), and the proof is cut after round 41
(`Cases.Zip2005.sponge_tail`, `Proof/Poseidon/PoseidonTail.lean`): one executor run over all of them does not fit
the memory budget.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
theorem sponge_spec {P : Prop} (s : MachineState) (ra sp out st inp mp rc : Word)
    (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) (t0 t1 i0 i1 i2 i3 i4 i5 i6 i7 : Word)
    (hpc : s.pc = 0x7801e26c#64) (hcode : CodeAt F_7801e26c.base F_7801e26c.prog s)
    (hcodeF : CodeAt F_7801f120.base F_7801f120.prog s) (hcodeP : CodeAt F_7801ed68.base F_7801ed68.prog s)
    (hcodeX : CodeAt F_7801e704.base F_7801e704.prog s) (hcodeB : CodeAt F_78023a18.base F_78023a18.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s) (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x300 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = st) (ha2 : s.getReg .x12 = inp)
    (ha3 : s.getReg .x13 = mp) (ha4 : s.getReg .x14 = rc) (ha5 : s.getReg .x15 = 64#64)
    (hX : Region st [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11] s) (hokX : RegionOk Ro.layout.roBase Ro.layout.textHi st 12)
    (hxl0 : leLimbsToNat [x0, x1, x2, x3] < Fp.p) (hxl1 : leLimbsToNat [x4, x5, x6, x7] < Fp.p) (hxl2 : leLimbsToNat [x8, x9, x10, x11] < Fp.p)
    (hI : Region inp [t0, i0, i1, i2, i3, t1, i4, i5, i6, i7] s) (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi inp 10)
    (hinp : (inp == 0#64) = false) (ht0 : t0 &&& 1#64 = 1#64) (ht1 : t1 &&& 1#64 = 1#64)
    (hil0 : leLimbsToNat [i0, i1, i2, i3] < Fp.p) (hil1 : leLimbsToNat [i4, i5, i6, i7] < Fp.p)
    (hM : Region mp Poseidon.mdsWords s) (hokM : RegionOk Ro.layout.roBase Ro.layout.textHi mp 36)
    (hC : Region rc Poseidon.rcWords s) (hokC : RegionOk Ro.layout.roBase Ro.layout.textHi rc 768)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 10)
    (hd0 : Disjoint (sp - 0x300#64) 96 st 12) (hd1 : Disjoint (sp - 0x300#64) 96 inp 10)
    (hd2 : Disjoint (sp - 0x300#64) 96 mp 36) (hd3 : Disjoint (sp - 0x300#64) 96 rc 768)
    (hd4 : Disjoint (sp - 0x300#64) 96 out 10)
    (hd5 : Disjoint st 12 inp 10) (hd6 : Disjoint st 12 mp 36) (hd7 : Disjoint st 12 rc 768)
    (hd8 : Disjoint st 12 out 10) (hd9 : Disjoint out 10 inp 10) (hd10 : Disjoint out 10 mp 36)
    (hd11 : Disjoint out 10 rc 768)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x300#64, 96), (st, 12), (out, 10)] s t → ∀ o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : Word,
      Region st [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11] t →
      Region out [1#64, o0, o1, o2, o3, 1#64, o4, o5, o6, o7] t →
      (leLimbsToNat [o0, o1, o2, o3], leLimbsToNat [o4, o5, o6, o7], leLimbsToNat [o8, o9, o10, o11]) =
        Poseidon.permute (Fp.add (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [i0, i1, i2, i3]), Fp.add (leLimbsToNat [x4, x5, x6, x7]) (leLimbsToNat [i4, i5, i6, i7]), leLimbsToNat [x8, x9, x10, x11]) →
      Safe P t) :
    Safe P s := by
  obtain ⟨O, hO, hOl⟩ := Region.exists_junk out 10 s
  -- the read-only image at any later state in the frame (as a function, so that the executor
  -- does not take it for its own image fact)
  have hro0 : ∀ u, Unchanged [(sp - 0x300#64, 96), (st, 12), (out, 10)] s u →
      (∀ q ∈ [(sp - 0x300#64, 96), (st, 12), (out, 10)],
        q.1.toNat + 8 * q.2 ≤ Ro.layout.roBase ∨ Ro.layout.roBase + Ro.layout.roBytes ≤ q.1.toNat) → RoImage Ro.layout u :=
    fun u hU hW => RoImage.of_unchanged hro hU hW
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x100#64) 32 s
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x100#64) 32 := hstk.frame 32 (by decide)
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x300#64) 96 := hstk.frame 96 (by decide)
  have hu := Unchanged.refl [(sp - 0x300#64, 96), (st, 12), (out, 10)] s
  have hlo := hstk.lo
  -- the write set outside the read-only segment, with its bounds as literals (as `omega` sees them)
  have hroSt : st.toNat + 8 * 12 ≤ 0x78000000 ∨ 0x78000000 + 88376 ≤ st.toNat := hokX.roOut
  have hroOut : out.toNat + 8 * 10 ≤ 0x78000000 ∨ 0x78000000 + 88376 ≤ out.toNat := hokO.roOut
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  sym_exec [full_round_spec, partial_round_spec] stop [0x7801e510]
  have ch0 := fadd_chain v41_def v42_def v43_def v44_def v45_def v46_def v47_def v50_def v51_def v52_def v53_def v54_def v55_def v56_def v58_def v60_def v61_def v62_def v64_def v65_def v67_def v68_def v69_def v70_def v71_def v72_def v73_def v74_def v76_def v77_def v79_def v80_def v81_def v82_def v83_def v84_def v85_def v86_def v87_def v88_def v89_def v91_def v92_def v93_def hxl0 hil0
  have D1 := fadd_limbs v108_def v109_def v110_def v111_def v112_def v113_def v114_def v115_def v116_def v117_def v118_def v119_def v120_def v121_def
    (padd_lt hxl1 hil1).1
  have R1 := padd_reduce (c0_def := v123_def) (e1_def := v125_def) (m0_def := v126_def) (c1a_def := v128_def) (u1_def := v130_def) (t1_def := v131_def) (c1b_def := v132_def) (w1_def := v133_def) (e2_def := v134_def) (m1_def := v135_def) (t2_def := v136_def) (c2_def := v137_def) (w2_def := v138_def) (e3_def := v139_def) (m2_def := v140_def) (c3a_def := v142_def) (u3_def := v144_def) (t3_def := v145_def) (c3b_def := v146_def) (M_def := v147_def) (t0_def := v148_def) (k0_def := v149_def) (r0_def := v150_def) (c4_def := v151_def) (t1'_def := v152_def) (k1_def := v153_def) (s1_def := v154_def) (c5_def := v155_def) (r1_def := v156_def) (c6_def := v157_def) (c7_def := v158_def) (t2'_def := v159_def) (r2_def := v160_def) (c8_def := v161_def) (k3_def := v162_def) (q3_def := v163_def)
    (by rw [D1]; exact (padd_lt hxl1 hil1).2)
  have ch1 : leLimbsToNat [v150, v156, v160, v164] =
      Fp.add (leLimbsToNat [x4, x5, x6, x7]) (leLimbsToNat [i4, i5, i6, i7]) := by
    rw [← v164_def, R1, D1]; rfl
  have lt0 : leLimbsToNat [v80, v85, v88, v93] < Fp.p := by rw [ch0]; exact fadd_lt _ _
  have lt1 : leLimbsToNat [v150, v156, v160, v164] < Fp.p := by rw [ch1]; exact fadd_lt _ _
  sym_forget
  sym_reframe
  sym_exec [full_round_spec, partial_round_spec] 300
  have R0 : (leLimbsToNat [post70_4, post70_5, post70_6, post70_7], leLimbsToNat [post70_8, post70_9, post70_10, post70_11], leLimbsToNat [post70_12, post70_13, post70_14, post70_15]) = Poseidon.round 0 (leLimbsToNat [v80, v85, v88, v93], leLimbsToNat [v150, v156, v160, v164], leLimbsToNat [x8, x9, x10, x11]) := by
    rw [post70_17, post70_18, post70_19]; rfl
  have R1 : (leLimbsToNat [post89_4, post89_5, post89_6, post89_7], leLimbsToNat [post89_8, post89_9, post89_10, post89_11], leLimbsToNat [post89_12, post89_13, post89_14, post89_15]) = Poseidon.round 1 (leLimbsToNat [post70_4, post70_5, post70_6, post70_7], leLimbsToNat [post70_8, post70_9, post70_10, post70_11], leLimbsToNat [post70_12, post70_13, post70_14, post70_15]) := by
    rw [post89_17, post89_18, post89_19]; rfl
  have R2 : (leLimbsToNat [post108_4, post108_5, post108_6, post108_7], leLimbsToNat [post108_8, post108_9, post108_10, post108_11], leLimbsToNat [post108_12, post108_13, post108_14, post108_15]) = Poseidon.round 2 (leLimbsToNat [post89_4, post89_5, post89_6, post89_7], leLimbsToNat [post89_8, post89_9, post89_10, post89_11], leLimbsToNat [post89_12, post89_13, post89_14, post89_15]) := by
    rw [post108_17, post108_18, post108_19]; rfl
  have R3 : (leLimbsToNat [post127_4, post127_5, post127_6, post127_7], leLimbsToNat [post127_8, post127_9, post127_10, post127_11], leLimbsToNat [post127_12, post127_13, post127_14, post127_15]) = Poseidon.round 3 (leLimbsToNat [post108_4, post108_5, post108_6, post108_7], leLimbsToNat [post108_8, post108_9, post108_10, post108_11], leLimbsToNat [post108_12, post108_13, post108_14, post108_15]) := by
    rw [post127_17, post127_18, post127_19]; rfl
  have R4 : (leLimbsToNat [post147_4, post147_5, post147_6, post147_7], leLimbsToNat [post147_8, post147_9, post147_10, post147_11], leLimbsToNat [post147_12, post147_13, post147_14, post147_15]) = Poseidon.round 4 (leLimbsToNat [post127_4, post127_5, post127_6, post127_7], leLimbsToNat [post127_8, post127_9, post127_10, post127_11], leLimbsToNat [post127_12, post127_13, post127_14, post127_15]) := by
    rw [post147_17, post147_18, post147_19]; rfl
  have R5 : (leLimbsToNat [post165_4, post165_5, post165_6, post165_7], leLimbsToNat [post165_8, post165_9, post165_10, post165_11], leLimbsToNat [post165_12, post165_13, post165_14, post165_15]) = Poseidon.round 5 (leLimbsToNat [post147_4, post147_5, post147_6, post147_7], leLimbsToNat [post147_8, post147_9, post147_10, post147_11], leLimbsToNat [post147_12, post147_13, post147_14, post147_15]) := by
    rw [post165_17, post165_18, post165_19]; rfl
  have R6 : (leLimbsToNat [post183_4, post183_5, post183_6, post183_7], leLimbsToNat [post183_8, post183_9, post183_10, post183_11], leLimbsToNat [post183_12, post183_13, post183_14, post183_15]) = Poseidon.round 6 (leLimbsToNat [post165_4, post165_5, post165_6, post165_7], leLimbsToNat [post165_8, post165_9, post165_10, post165_11], leLimbsToNat [post165_12, post165_13, post165_14, post165_15]) := by
    rw [post183_17, post183_18, post183_19]; rfl
  have R7 : (leLimbsToNat [post201_4, post201_5, post201_6, post201_7], leLimbsToNat [post201_8, post201_9, post201_10, post201_11], leLimbsToNat [post201_12, post201_13, post201_14, post201_15]) = Poseidon.round 7 (leLimbsToNat [post183_4, post183_5, post183_6, post183_7], leLimbsToNat [post183_8, post183_9, post183_10, post183_11], leLimbsToNat [post183_12, post183_13, post183_14, post183_15]) := by
    rw [post201_17, post201_18, post201_19]; rfl
  have R8 : (leLimbsToNat [post219_4, post219_5, post219_6, post219_7], leLimbsToNat [post219_8, post219_9, post219_10, post219_11], leLimbsToNat [post219_12, post219_13, post219_14, post219_15]) = Poseidon.round 8 (leLimbsToNat [post201_4, post201_5, post201_6, post201_7], leLimbsToNat [post201_8, post201_9, post201_10, post201_11], leLimbsToNat [post201_12, post201_13, post201_14, post201_15]) := by
    rw [post219_17, post219_18, post219_19]; rfl
  have R9 : (leLimbsToNat [post237_4, post237_5, post237_6, post237_7], leLimbsToNat [post237_8, post237_9, post237_10, post237_11], leLimbsToNat [post237_12, post237_13, post237_14, post237_15]) = Poseidon.round 9 (leLimbsToNat [post219_4, post219_5, post219_6, post219_7], leLimbsToNat [post219_8, post219_9, post219_10, post219_11], leLimbsToNat [post219_12, post219_13, post219_14, post219_15]) := by
    rw [post237_17, post237_18, post237_19]; rfl
  have R10 : (leLimbsToNat [post255_4, post255_5, post255_6, post255_7], leLimbsToNat [post255_8, post255_9, post255_10, post255_11], leLimbsToNat [post255_12, post255_13, post255_14, post255_15]) = Poseidon.round 10 (leLimbsToNat [post237_4, post237_5, post237_6, post237_7], leLimbsToNat [post237_8, post237_9, post237_10, post237_11], leLimbsToNat [post237_12, post237_13, post237_14, post237_15]) := by
    rw [post255_17, post255_18, post255_19]; rfl
  have R11 : (leLimbsToNat [post273_4, post273_5, post273_6, post273_7], leLimbsToNat [post273_8, post273_9, post273_10, post273_11], leLimbsToNat [post273_12, post273_13, post273_14, post273_15]) = Poseidon.round 11 (leLimbsToNat [post255_4, post255_5, post255_6, post255_7], leLimbsToNat [post255_8, post255_9, post255_10, post255_11], leLimbsToNat [post255_12, post255_13, post255_14, post255_15]) := by
    rw [post273_17, post273_18, post273_19]; rfl
  have R12 : (leLimbsToNat [post291_4, post291_5, post291_6, post291_7], leLimbsToNat [post291_8, post291_9, post291_10, post291_11], leLimbsToNat [post291_12, post291_13, post291_14, post291_15]) = Poseidon.round 12 (leLimbsToNat [post273_4, post273_5, post273_6, post273_7], leLimbsToNat [post273_8, post273_9, post273_10, post273_11], leLimbsToNat [post273_12, post273_13, post273_14, post273_15]) := by
    rw [post291_17, post291_18, post291_19]; rfl
  clear post70_17 post70_18 post70_19 post70_20 post70_21 post70_22 post89_17 post89_18 post89_19 post89_20 post89_21 post89_22 post108_17 post108_18 post108_19 post108_20 post108_21 post108_22 post127_17 post127_18 post127_19 post127_20 post127_21 post127_22 post147_17 post147_18 post147_19 post147_20 post147_21 post147_22 post165_17 post165_18 post165_19 post165_20 post165_21 post165_22 post183_17 post183_18 post183_19 post183_20 post183_21 post183_22 post201_17 post201_18 post201_19 post201_20 post201_21 post201_22 post219_17 post219_18 post219_19 post219_20 post219_21 post219_22 post237_17 post237_18 post237_19 post237_20 post237_21 post237_22 post255_17 post255_18 post255_19 post255_20 post255_21 post255_22 post273_17 post273_18 post273_19 post273_20 post273_21 post273_22 post291_17 post291_18 post291_19
  sym_forget
  sym_reframe
  sym_exec [full_round_spec, partial_round_spec] 500
  have R13 : (leLimbsToNat [post9_4, post9_5, post9_6, post9_7], leLimbsToNat [post9_8, post9_9, post9_10, post9_11], leLimbsToNat [post9_12, post9_13, post9_14, post9_15]) = Poseidon.round 13 (leLimbsToNat [post291_4, post291_5, post291_6, post291_7], leLimbsToNat [post291_8, post291_9, post291_10, post291_11], leLimbsToNat [post291_12, post291_13, post291_14, post291_15]) := by
    rw [post9_17, post9_18, post9_19]; rfl
  have R14 : (leLimbsToNat [post27_4, post27_5, post27_6, post27_7], leLimbsToNat [post27_8, post27_9, post27_10, post27_11], leLimbsToNat [post27_12, post27_13, post27_14, post27_15]) = Poseidon.round 14 (leLimbsToNat [post9_4, post9_5, post9_6, post9_7], leLimbsToNat [post9_8, post9_9, post9_10, post9_11], leLimbsToNat [post9_12, post9_13, post9_14, post9_15]) := by
    rw [post27_17, post27_18, post27_19]; rfl
  have R15 : (leLimbsToNat [post45_4, post45_5, post45_6, post45_7], leLimbsToNat [post45_8, post45_9, post45_10, post45_11], leLimbsToNat [post45_12, post45_13, post45_14, post45_15]) = Poseidon.round 15 (leLimbsToNat [post27_4, post27_5, post27_6, post27_7], leLimbsToNat [post27_8, post27_9, post27_10, post27_11], leLimbsToNat [post27_12, post27_13, post27_14, post27_15]) := by
    rw [post45_17, post45_18, post45_19]; rfl
  have R16 : (leLimbsToNat [post63_4, post63_5, post63_6, post63_7], leLimbsToNat [post63_8, post63_9, post63_10, post63_11], leLimbsToNat [post63_12, post63_13, post63_14, post63_15]) = Poseidon.round 16 (leLimbsToNat [post45_4, post45_5, post45_6, post45_7], leLimbsToNat [post45_8, post45_9, post45_10, post45_11], leLimbsToNat [post45_12, post45_13, post45_14, post45_15]) := by
    rw [post63_17, post63_18, post63_19]; rfl
  have R17 : (leLimbsToNat [post81_4, post81_5, post81_6, post81_7], leLimbsToNat [post81_8, post81_9, post81_10, post81_11], leLimbsToNat [post81_12, post81_13, post81_14, post81_15]) = Poseidon.round 17 (leLimbsToNat [post63_4, post63_5, post63_6, post63_7], leLimbsToNat [post63_8, post63_9, post63_10, post63_11], leLimbsToNat [post63_12, post63_13, post63_14, post63_15]) := by
    rw [post81_17, post81_18, post81_19]; rfl
  have R18 : (leLimbsToNat [post99_4, post99_5, post99_6, post99_7], leLimbsToNat [post99_8, post99_9, post99_10, post99_11], leLimbsToNat [post99_12, post99_13, post99_14, post99_15]) = Poseidon.round 18 (leLimbsToNat [post81_4, post81_5, post81_6, post81_7], leLimbsToNat [post81_8, post81_9, post81_10, post81_11], leLimbsToNat [post81_12, post81_13, post81_14, post81_15]) := by
    rw [post99_17, post99_18, post99_19]; rfl
  have R19 : (leLimbsToNat [post117_4, post117_5, post117_6, post117_7], leLimbsToNat [post117_8, post117_9, post117_10, post117_11], leLimbsToNat [post117_12, post117_13, post117_14, post117_15]) = Poseidon.round 19 (leLimbsToNat [post99_4, post99_5, post99_6, post99_7], leLimbsToNat [post99_8, post99_9, post99_10, post99_11], leLimbsToNat [post99_12, post99_13, post99_14, post99_15]) := by
    rw [post117_17, post117_18, post117_19]; rfl
  have R20 : (leLimbsToNat [post135_4, post135_5, post135_6, post135_7], leLimbsToNat [post135_8, post135_9, post135_10, post135_11], leLimbsToNat [post135_12, post135_13, post135_14, post135_15]) = Poseidon.round 20 (leLimbsToNat [post117_4, post117_5, post117_6, post117_7], leLimbsToNat [post117_8, post117_9, post117_10, post117_11], leLimbsToNat [post117_12, post117_13, post117_14, post117_15]) := by
    rw [post135_17, post135_18, post135_19]; rfl
  have R21 : (leLimbsToNat [post153_4, post153_5, post153_6, post153_7], leLimbsToNat [post153_8, post153_9, post153_10, post153_11], leLimbsToNat [post153_12, post153_13, post153_14, post153_15]) = Poseidon.round 21 (leLimbsToNat [post135_4, post135_5, post135_6, post135_7], leLimbsToNat [post135_8, post135_9, post135_10, post135_11], leLimbsToNat [post135_12, post135_13, post135_14, post135_15]) := by
    rw [post153_17, post153_18, post153_19]; rfl
  have R22 : (leLimbsToNat [post171_4, post171_5, post171_6, post171_7], leLimbsToNat [post171_8, post171_9, post171_10, post171_11], leLimbsToNat [post171_12, post171_13, post171_14, post171_15]) = Poseidon.round 22 (leLimbsToNat [post153_4, post153_5, post153_6, post153_7], leLimbsToNat [post153_8, post153_9, post153_10, post153_11], leLimbsToNat [post153_12, post153_13, post153_14, post153_15]) := by
    rw [post171_17, post171_18, post171_19]; rfl
  have R23 : (leLimbsToNat [post189_4, post189_5, post189_6, post189_7], leLimbsToNat [post189_8, post189_9, post189_10, post189_11], leLimbsToNat [post189_12, post189_13, post189_14, post189_15]) = Poseidon.round 23 (leLimbsToNat [post171_4, post171_5, post171_6, post171_7], leLimbsToNat [post171_8, post171_9, post171_10, post171_11], leLimbsToNat [post171_12, post171_13, post171_14, post171_15]) := by
    rw [post189_17, post189_18, post189_19]; rfl
  have R24 : (leLimbsToNat [post207_4, post207_5, post207_6, post207_7], leLimbsToNat [post207_8, post207_9, post207_10, post207_11], leLimbsToNat [post207_12, post207_13, post207_14, post207_15]) = Poseidon.round 24 (leLimbsToNat [post189_4, post189_5, post189_6, post189_7], leLimbsToNat [post189_8, post189_9, post189_10, post189_11], leLimbsToNat [post189_12, post189_13, post189_14, post189_15]) := by
    rw [post207_17, post207_18, post207_19]; rfl
  have R25 : (leLimbsToNat [post225_4, post225_5, post225_6, post225_7], leLimbsToNat [post225_8, post225_9, post225_10, post225_11], leLimbsToNat [post225_12, post225_13, post225_14, post225_15]) = Poseidon.round 25 (leLimbsToNat [post207_4, post207_5, post207_6, post207_7], leLimbsToNat [post207_8, post207_9, post207_10, post207_11], leLimbsToNat [post207_12, post207_13, post207_14, post207_15]) := by
    rw [post225_17, post225_18, post225_19]; rfl
  have R26 : (leLimbsToNat [post243_4, post243_5, post243_6, post243_7], leLimbsToNat [post243_8, post243_9, post243_10, post243_11], leLimbsToNat [post243_12, post243_13, post243_14, post243_15]) = Poseidon.round 26 (leLimbsToNat [post225_4, post225_5, post225_6, post225_7], leLimbsToNat [post225_8, post225_9, post225_10, post225_11], leLimbsToNat [post225_12, post225_13, post225_14, post225_15]) := by
    rw [post243_17, post243_18, post243_19]; rfl
  have R27 : (leLimbsToNat [post261_4, post261_5, post261_6, post261_7], leLimbsToNat [post261_8, post261_9, post261_10, post261_11], leLimbsToNat [post261_12, post261_13, post261_14, post261_15]) = Poseidon.round 27 (leLimbsToNat [post243_4, post243_5, post243_6, post243_7], leLimbsToNat [post243_8, post243_9, post243_10, post243_11], leLimbsToNat [post243_12, post243_13, post243_14, post243_15]) := by
    rw [post261_17, post261_18, post261_19]; rfl
  have R28 : (leLimbsToNat [post279_4, post279_5, post279_6, post279_7], leLimbsToNat [post279_8, post279_9, post279_10, post279_11], leLimbsToNat [post279_12, post279_13, post279_14, post279_15]) = Poseidon.round 28 (leLimbsToNat [post261_4, post261_5, post261_6, post261_7], leLimbsToNat [post261_8, post261_9, post261_10, post261_11], leLimbsToNat [post261_12, post261_13, post261_14, post261_15]) := by
    rw [post279_17, post279_18, post279_19]; rfl
  have R29 : (leLimbsToNat [post297_4, post297_5, post297_6, post297_7], leLimbsToNat [post297_8, post297_9, post297_10, post297_11], leLimbsToNat [post297_12, post297_13, post297_14, post297_15]) = Poseidon.round 29 (leLimbsToNat [post279_4, post279_5, post279_6, post279_7], leLimbsToNat [post279_8, post279_9, post279_10, post279_11], leLimbsToNat [post279_12, post279_13, post279_14, post279_15]) := by
    rw [post297_17, post297_18, post297_19]; rfl
  have R30 : (leLimbsToNat [post315_4, post315_5, post315_6, post315_7], leLimbsToNat [post315_8, post315_9, post315_10, post315_11], leLimbsToNat [post315_12, post315_13, post315_14, post315_15]) = Poseidon.round 30 (leLimbsToNat [post297_4, post297_5, post297_6, post297_7], leLimbsToNat [post297_8, post297_9, post297_10, post297_11], leLimbsToNat [post297_12, post297_13, post297_14, post297_15]) := by
    rw [post315_17, post315_18, post315_19]; rfl
  have R31 : (leLimbsToNat [post333_4, post333_5, post333_6, post333_7], leLimbsToNat [post333_8, post333_9, post333_10, post333_11], leLimbsToNat [post333_12, post333_13, post333_14, post333_15]) = Poseidon.round 31 (leLimbsToNat [post315_4, post315_5, post315_6, post315_7], leLimbsToNat [post315_8, post315_9, post315_10, post315_11], leLimbsToNat [post315_12, post315_13, post315_14, post315_15]) := by
    rw [post333_17, post333_18, post333_19]; rfl
  have R32 : (leLimbsToNat [post351_4, post351_5, post351_6, post351_7], leLimbsToNat [post351_8, post351_9, post351_10, post351_11], leLimbsToNat [post351_12, post351_13, post351_14, post351_15]) = Poseidon.round 32 (leLimbsToNat [post333_4, post333_5, post333_6, post333_7], leLimbsToNat [post333_8, post333_9, post333_10, post333_11], leLimbsToNat [post333_12, post333_13, post333_14, post333_15]) := by
    rw [post351_17, post351_18, post351_19]; rfl
  have R33 : (leLimbsToNat [post369_4, post369_5, post369_6, post369_7], leLimbsToNat [post369_8, post369_9, post369_10, post369_11], leLimbsToNat [post369_12, post369_13, post369_14, post369_15]) = Poseidon.round 33 (leLimbsToNat [post351_4, post351_5, post351_6, post351_7], leLimbsToNat [post351_8, post351_9, post351_10, post351_11], leLimbsToNat [post351_12, post351_13, post351_14, post351_15]) := by
    rw [post369_17, post369_18, post369_19]; rfl
  have R34 : (leLimbsToNat [post387_4, post387_5, post387_6, post387_7], leLimbsToNat [post387_8, post387_9, post387_10, post387_11], leLimbsToNat [post387_12, post387_13, post387_14, post387_15]) = Poseidon.round 34 (leLimbsToNat [post369_4, post369_5, post369_6, post369_7], leLimbsToNat [post369_8, post369_9, post369_10, post369_11], leLimbsToNat [post369_12, post369_13, post369_14, post369_15]) := by
    rw [post387_17, post387_18, post387_19]; rfl
  have R35 : (leLimbsToNat [post405_4, post405_5, post405_6, post405_7], leLimbsToNat [post405_8, post405_9, post405_10, post405_11], leLimbsToNat [post405_12, post405_13, post405_14, post405_15]) = Poseidon.round 35 (leLimbsToNat [post387_4, post387_5, post387_6, post387_7], leLimbsToNat [post387_8, post387_9, post387_10, post387_11], leLimbsToNat [post387_12, post387_13, post387_14, post387_15]) := by
    rw [post405_17, post405_18, post405_19]; rfl
  have R36 : (leLimbsToNat [post423_4, post423_5, post423_6, post423_7], leLimbsToNat [post423_8, post423_9, post423_10, post423_11], leLimbsToNat [post423_12, post423_13, post423_14, post423_15]) = Poseidon.round 36 (leLimbsToNat [post405_4, post405_5, post405_6, post405_7], leLimbsToNat [post405_8, post405_9, post405_10, post405_11], leLimbsToNat [post405_12, post405_13, post405_14, post405_15]) := by
    rw [post423_17, post423_18, post423_19]; rfl
  have R37 : (leLimbsToNat [post441_4, post441_5, post441_6, post441_7], leLimbsToNat [post441_8, post441_9, post441_10, post441_11], leLimbsToNat [post441_12, post441_13, post441_14, post441_15]) = Poseidon.round 37 (leLimbsToNat [post423_4, post423_5, post423_6, post423_7], leLimbsToNat [post423_8, post423_9, post423_10, post423_11], leLimbsToNat [post423_12, post423_13, post423_14, post423_15]) := by
    rw [post441_17, post441_18, post441_19]; rfl
  have R38 : (leLimbsToNat [post459_4, post459_5, post459_6, post459_7], leLimbsToNat [post459_8, post459_9, post459_10, post459_11], leLimbsToNat [post459_12, post459_13, post459_14, post459_15]) = Poseidon.round 38 (leLimbsToNat [post441_4, post441_5, post441_6, post441_7], leLimbsToNat [post441_8, post441_9, post441_10, post441_11], leLimbsToNat [post441_12, post441_13, post441_14, post441_15]) := by
    rw [post459_17, post459_18, post459_19]; rfl
  have R39 : (leLimbsToNat [post477_4, post477_5, post477_6, post477_7], leLimbsToNat [post477_8, post477_9, post477_10, post477_11], leLimbsToNat [post477_12, post477_13, post477_14, post477_15]) = Poseidon.round 39 (leLimbsToNat [post459_4, post459_5, post459_6, post459_7], leLimbsToNat [post459_8, post459_9, post459_10, post459_11], leLimbsToNat [post459_12, post459_13, post459_14, post459_15]) := by
    rw [post477_17, post477_18, post477_19]; rfl
  have R40 : (leLimbsToNat [post495_4, post495_5, post495_6, post495_7], leLimbsToNat [post495_8, post495_9, post495_10, post495_11], leLimbsToNat [post495_12, post495_13, post495_14, post495_15]) = Poseidon.round 40 (leLimbsToNat [post477_4, post477_5, post477_6, post477_7], leLimbsToNat [post477_8, post477_9, post477_10, post477_11], leLimbsToNat [post477_12, post477_13, post477_14, post477_15]) := by
    rw [post495_17, post495_18, post495_19]; rfl
  clear post291_20 post291_21 post291_22 post9_17 post9_18 post9_19 post9_20 post9_21 post9_22 post27_17 post27_18 post27_19 post27_20 post27_21 post27_22 post45_17 post45_18 post45_19 post45_20 post45_21 post45_22 post63_17 post63_18 post63_19 post63_20 post63_21 post63_22 post81_17 post81_18 post81_19 post81_20 post81_21 post81_22 post99_17 post99_18 post99_19 post99_20 post99_21 post99_22 post117_17 post117_18 post117_19 post117_20 post117_21 post117_22 post135_17 post135_18 post135_19 post135_20 post135_21 post135_22 post153_17 post153_18 post153_19 post153_20 post153_21 post153_22 post171_17 post171_18 post171_19 post171_20 post171_21 post171_22 post189_17 post189_18 post189_19 post189_20 post189_21 post189_22 post207_17 post207_18 post207_19 post207_20 post207_21 post207_22 post225_17 post225_18 post225_19 post225_20 post225_21 post225_22 post243_17 post243_18 post243_19 post243_20 post243_21 post243_22 post261_17 post261_18 post261_19 post261_20 post261_21 post261_22 post279_17 post279_18 post279_19 post279_20 post279_21 post279_22 post297_17 post297_18 post297_19 post297_20 post297_21 post297_22 post315_17 post315_18 post315_19 post315_20 post315_21 post315_22 post333_17 post333_18 post333_19 post333_20 post333_21 post333_22 post351_17 post351_18 post351_19 post351_20 post351_21 post351_22 post369_17 post369_18 post369_19 post369_20 post369_21 post369_22 post387_17 post387_18 post387_19 post387_20 post387_21 post387_22 post405_17 post405_18 post405_19 post405_20 post405_21 post405_22 post423_17 post423_18 post423_19 post423_20 post423_21 post423_22 post441_17 post441_18 post441_19 post441_20 post441_21 post441_22 post459_17 post459_18 post459_19 post459_20 post459_21 post459_22 post477_17 post477_18 post477_19 post477_20 post477_21 post477_22 post495_17 post495_18 post495_19
  sym_reframe
  have hk' : ∀ (u : MachineState) (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 : Word),
      u.pc = 0x7801e640#64 → u.code = s.code →
      CodeAt F_7801e26c.base F_7801e26c.prog u → CodeAt F_7801f120.base F_7801f120.prog u →
      CodeAt F_7801ed68.base F_7801ed68.prog u → CodeAt F_7801e704.base F_7801e704.prog u →
      CodeAt F_78023a18.base F_78023a18.prog u → CodeAt F_7801bf5c.base F_7801bf5c.prog u →
      CodeAt F_7803f57c.base F_7803f57c.prog u → CodeAt F_7801b4d8.base F_7801b4d8.prog u →
      CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      Unchanged [(sp - 0x300#64, 96), (st, 12), (out, 10)] s u →
      Region st [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11] u →
      Region out [O[0]!, O[1]!, O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!] u →
      Region (sp - 256#64) [F[0]!, out, mp, sp + 18446744073709551376#64, sp + 18446744073709551376#64, rc, rc + 6144#64, 0#64, 0#64, sp + 18446744073709551384#64, 2013271664#64, 4#64, sp + 18446744073709551392#64, 2013271712#64, 19#64, sp + 18446744073709551384#64, 2013271664#64, 0#64, v27, s.getReg Reg.x27, s.getReg Reg.x26, s.getReg Reg.x25, s.getReg Reg.x24, s.getReg Reg.x23, s.getReg Reg.x22, s.getReg Reg.x21, s.getReg Reg.x20, s.getReg Reg.x19, s.getReg Reg.x18, s.getReg Reg.x9, s.getReg Reg.x8, ra] u →
      Region mp Poseidon.mdsWords u → Region rc Poseidon.rcWords u →
      u.getReg .x2 = sp + 18446744073709551360#64 → u.getReg .x3 = s.getReg .x3 → u.getReg .x4 = s.getReg .x4 →
      u.getReg .x8 = rc + 3936#64 → u.getReg .x9 = st → u.getReg .x10 = 2#64 → u.getReg .x14 = rc + 3936#64 →
      u.getReg .x18 = sp + 18446744073709551440#64 → u.getReg .x19 = rc + 6144#64 → u.getReg .x20 = 19#64 →
      u.getReg .x21 = 4#64 → u.getReg .x22 = 2#64 → u.getReg .x23 = sp + 18446744073709551464#64 →
      u.getReg .x24 = 3#64 → u.getReg .x25 = sp + 18446744073709551488#64 → u.getReg .x26 = 0#64 → u.getReg .x27 = 2#64 →
      (leLimbsToNat [y0, y1, y2, y3], leLimbsToNat [y4, y5, y6, y7], leLimbsToNat [y8, y9, y10, y11]) =
        Poseidon.rounds 41 (Fp.add (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [i0, i1, i2, i3]), Fp.add (leLimbsToNat [x4, x5, x6, x7]) (leLimbsToNat [i4, i5, i6, i7]), leLimbsToNat [x8, x9, x10, x11]) →
      leLimbsToNat [y0, y1, y2, y3] < Fp.p → leLimbsToNat [y4, y5, y6, y7] < Fp.p → leLimbsToNat [y8, y9, y10, y11] < Fp.p →
      Safe P u := by
    intro u y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 upc ucode uc0 uc1 uc2 uc3 uc4 uc5 uc6 uc7 ucw uU uX uO uF uM uC rx2 rx3 rx4 rx8 rx9 rx10 rx14 rx18 rx19 rx20 rx21 rx22 rx23 rx24 rx25 rx26 rx27 hy hl0 hl1 hl2
    have hW : ∀ q ∈ [(sp - 0x300#64, 96), (st, 12), (out, 10)],
        q.1.toNat + 8 * q.2 ≤ Ro.layout.roBase ∨ Ro.layout.roBase + Ro.layout.roBytes ≤ q.1.toNat :=
      roW_cons (r := (sp - 0x300#64, 96))
        (by
          show (sp - 0x300#64).toNat + 8 * 96 ≤ Ro.layout.roBase ∨ Ro.layout.roBase + Ro.layout.roBytes ≤ (sp - 0x300#64).toNat
          have h1 := hstk.lo; have h2 := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
          simp only [Ro.layout_roBase, Ro.layout_roBytes]; left; bv_omega)
        (roW_cons (r := (st, 12)) (Or.imp_right (fun h => Nat.le_trans (by decide) h) hokX.offCode)
          (roW_cons (r := (out, 10)) (Or.imp_right (fun h => Nat.le_trans (by decide) h) hokO.offCode) (roW_nil Ro.layout)))
    have uro : RoImage Ro.layout u := hro0 u uU hW
    exact sponge_tail u ra sp out st mp rc y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 (O[0]!) (O[1]!) (O[2]!) (O[3]!) (O[4]!) (O[5]!) (O[6]!) (O[7]!) (O[8]!) (O[9]!) (F[0]!) v27 (s.getReg .x8) (s.getReg .x9) (s.getReg .x18) (s.getReg .x19) (s.getReg .x20) (s.getReg .x21) (s.getReg .x22) (s.getReg .x23) (s.getReg .x24) (s.getReg .x25) (s.getReg .x26) (s.getReg .x27)
      upc uc0 uc1 uc2 uc3 uc4 uc5 uc6 uc7 ucw uro hra1 hstk rx2 rx8 rx9 rx10 rx14 rx18 rx19 rx20 rx21 rx22 rx23 rx24 rx25 rx26 rx27
      uX hokX hl0 hl1 hl2 uO hokO uF uM hokM uC hokC hd0 hd2 hd3 hd4 hd6 hd7 hd8 hd10 hd11
      (fun v vpc vx2 vx3 vx4 vx8 vx9 vx18 vx19 vx20 vx21 vx22 vx23 vx24 vx25 vx26 vx27 vcode vU o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 vX vO heq =>
        hk v vpc
          (CalleeSaved.intro (vx2.trans hsp.symm) (vx3.trans rx3) (vx4.trans rx4) vx8 vx9 vx18 vx19 vx20
            vx21 vx22 vx23 vx24 vx25 vx26 vx27)
          (vcode.trans ucode) (uU.trans vU) o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 vX vO
          (by rw [heq, hy, ← Poseidon.rounds_add]; rfl))
  sym_close hk' _ post495_4 post495_5 post495_6 post495_7 post495_8 post495_9 post495_10 post495_11 post495_12 post495_13 post495_14 post495_15
  all_goals first
    | with_reducible assumption
    | simp only [Poseidon.rounds, R40, R39, R38, R37, R36, R35, R34, R33, R32, R31, R30, R29, R28, R27, R26, R25, R24, R23, R22, R21, R20, R19, R18, R17, R16, R15, R14, R13, R12, R11, R10, R9, R8, R7, R6, R5, R4, R3, R2, R1, R0, ch0, ch1]

end Cases.Zip2005
