import Cases.Zip2005.Curve.FromBytesUnchecked
import Cases.Zip2005.Curve.CondSelect
import Cases.Zip2005.Curve.IsIdentity
import Cases.Zip2005.Runtime.BlackBox
import Cases.Zip2005.Sinsemilla.SinsemillaCommit
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Image.F_7801fb1c
import Cases.Zip2005.Image.F_780232f4
import Cases.Zip2005.Image.Ro

/-!
# `NonIdentityPallasPoint::from_bytes` (0x7801fb1c)

`Ep::from_bytes` into a frame slot (`CtOption<Ep>`: twelve words and the flag byte), a zero
point by `memset`, `conditional_select(zero, point, flag)`, `is_identity` on the selection,
the selection copied to the output and the byte `flag ∧ ¬identity` stored at `out + 0x60`,
both through `black_box`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- `conditional_select` with the flag register holding a byte `f ∈ {0, 1}` (as `from_bytes`
leaves it), the choice stated as `f = 1#8`. -/
theorem conditional_select_spec_byte {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 a2 : Word)
    (f : BitVec 8)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : Word)
    (O : List Word) (hOl : O.length = 12)
    (hpc : s.pc = 0x78023d7c#64) (hcode : CodeAt F_78023d7c.base F_78023d7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x20 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1) (ha2 : s.getReg .x12 = a2)
    (ha3 : s.getReg .x13 = BitVec.zeroExtend 64 f) (hf : f = 1#8 ∨ f = 0#8)
    (hA : Region a1 [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11] s)
    (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hB : Region a2 [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11] s)
    (hok2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 12)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 12)
    (hd0 : Disjoint (sp - 0x20#64) 4 a0 12) (hd1 : Disjoint (sp - 0x20#64) 4 a1 12)
    (hd2 : Disjoint (sp - 0x20#64) 4 a2 12)
    (he1 : Disjoint a0 12 a1 12) (he2 : Disjoint a0 12 a2 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x20#64, 4), (a0, 12)] s t →
      Region a0 [if f = 1#8 then q0 else p0, if f = 1#8 then q1 else p1,
        if f = 1#8 then q2 else p2, if f = 1#8 then q3 else p3,
        if f = 1#8 then q4 else p4, if f = 1#8 then q5 else p5,
        if f = 1#8 then q6 else p6, if f = 1#8 then q7 else p7,
        if f = 1#8 then q8 else p8, if f = 1#8 then q9 else p9,
        if f = 1#8 then q10 else p10, if f = 1#8 then q11 else p11] t →
      SafeN G n P t) :
    SafeN G n P s :=
  conditional_select_spec s ra sp a0 a1 a2 (decide (f = 1#8)) p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    p10 p11 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 O hOl hpc hcode hcw hra hra1 hsp hstk ha0 ha1 ha2
    (by rw [ha3]; rcases hf with rfl | rfl <;> rfl) hA hok1 hB hok2 hO hok0 hd0 hd1 hd2 he1 he2
    (by simpa only [decide_eq_true_eq] using hk)

/-- `subtle::black_box::<u8>`, the `zip32` crate's instantiation (`0x780232f4`, the same five
instructions as `0x7803a0fc`). -/
theorem black_box_zip32_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp v : Word)
    (hpc : s.pc = 0x780232f4#64) (hcode : CodeAt F_780232f4.base F_780232f4.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x10 sp) (ha0 : s.getReg .x10 = v)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x10#64, 2)] s t →
      t.getReg .x10 = BitVec.zeroExtend 64 (BitVec.truncate 8 v) → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨F, hF, hFlen⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hstk.frame 2 (by decide)
  have hu := Unchanged.refl [(sp - 0x10#64, 2)] s
  sym_exec
  sym_close hk
  sym_subst
  rw [hx10, extractByte_replaceByte _ 7 (by decide)]

/-- The flag byte `NonIdentityPallasPoint::from_bytes` stores: `f ∧ ¬ identity`. -/
def nipFlag (f : BitVec 8) (z0 z1 z2 z3 : Word) : BitVec 8 :=
  if f = 1#8 ∧ ¬(z0 = 0#64 ∧ z1 = 0#64 ∧ z2 = 0#64 ∧ z3 = 0#64) then 1#8 else 0#8

/-- The byte the guest computes — `black_box(f & black_box(!is_identity & 1))` over the selected
point's `Z` — is `nipFlag`. -/
theorem nip_flag_eq (f : BitVec 8) (hf : f = 1#8 ∨ f = 0#8) (z0 z1 z2 z3 : Word) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 8 (BitVec.zeroExtend 64 f &&&
      BitVec.zeroExtend 64 (BitVec.truncate 8 ((bw (decide ((if f = 1#8 then z0 else 0#64) = 0#64 ∧
        (if f = 1#8 then z1 else 0#64) = 0#64 ∧ (if f = 1#8 then z2 else 0#64) = 0#64 ∧
        (if f = 1#8 then z3 else 0#64) = 0#64)) ^^^ 18446744073709551615#64) &&& 1#64))))) =
    nipFlag f z0 z1 z2 z3 := by
  rcases hf with rfl | rfl
  · by_cases h : z0 = 0#64 ∧ z1 = 0#64 ∧ z2 = 0#64 ∧ z3 = 0#64
    · simp [nipFlag, h, bw]
    · simp [nipFlag, h, bw]
  · simp [nipFlag, bw]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
theorem non_identity_pallas_point_from_bytes_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out a1 : Word)
    (b0 b1 b2 b3 cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (O IV G0 G1 G2 G3 : List Word)
    (hOl : O.length = 13) (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → SafeN G n P u)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → SafeN G n P u)
    (hprz : ∀ u : MachineState, u.pc = 0x7803de78#64 → u.code = s.code → SafeN G n P u)
    (hpc : s.pc = 0x7801fb1c#64) (hcode : CodeAt F_7801fb1c.base F_7801fb1c.prog s)
    (hcodeU : CodeAt F_78026928.base F_78026928.prog s)
    (hcodeF : CodeAt F_78025a1c.base F_78025a1c.prog s)
    (hcodeMC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeMS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeCS : CodeAt F_78023d7c.base F_78023d7c.prog s)
    (hcodeII : CodeAt F_78023ec4.base F_78023ec4.prog s)
    (hcodeBZ : CodeAt F_780232f4.base F_780232f4.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeP : CodeAt F_78029d94.base F_78029d94.prog s)
    (hcodeC : CodeAt F_7802f358.base F_7802f358.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeA : CodeAt F_780315c0.base F_780315c0.prog s)
    (hcodeR : CodeAt F_78028298.base F_78028298.prog s)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x8f0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = a1)
    (hB : Region a1 [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region out O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi out 13)
    -- `FP_TABLES`, initialised (`Once` state byte 2 at 0x780488f0, padding zero)
    (hTB : Region 0x780488a8#64 [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx, 2#64] s)
    (hIV : Region iptr IV s) (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hG0 : Region g0 G0 s) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024)
    (hG1 : Region g1 G1 s) (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024)
    (hG2 : Region g2 G2 s) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024)
    (hG3 : Region g3 G3 s) (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hd0 : Disjoint (sp - 0x8f0#64) 286 out 13) (hd_a1 : Disjoint (sp - 0x8f0#64) 286 a1 4)
    (hd_tb : Disjoint (sp - 0x8f0#64) 286 0x780488a8#64 10)
    (hd_iptr : Disjoint (sp - 0x8f0#64) 286 iptr 138)
    (hd_g0 : Disjoint (sp - 0x8f0#64) 286 g0 1024) (hd_g1 : Disjoint (sp - 0x8f0#64) 286 g1 1024)
    (hd_g2 : Disjoint (sp - 0x8f0#64) 286 g2 1024) (hd_g3 : Disjoint (sp - 0x8f0#64) 286 g3 516)
    (he_a1 : Disjoint out 13 a1 4) (he_tb : Disjoint out 13 0x780488a8#64 10)
    (he_iptr : Disjoint out 13 iptr 138)
    (he_g0 : Disjoint out 13 g0 1024) (he_g1 : Disjoint out 13 g1 1024)
    (he_g2 : Disjoint out 13 g2 1024) (he_g3 : Disjoint out 13 g3 516)
    (hk : ∀ (t : MachineState) (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word) (f : BitVec 8),
      t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x8f0#64, 286), (out, 13)] s t →
      FromBytesPost b0 b1 b2 b3 (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) f →
      leLimbsToNat [z0, z1, z2, z3] =
        (if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R) →
      Region out [if f = 1#8 then x0 else 0#64, if f = 1#8 then x1 else 0#64,
        if f = 1#8 then x2 else 0#64, if f = 1#8 then x3 else 0#64,
        if f = 1#8 then y0 else 0#64, if f = 1#8 then y1 else 0#64,
        if f = 1#8 then y2 else 0#64, if f = 1#8 then y3 else 0#64,
        if f = 1#8 then z0 else 0#64, if f = 1#8 then z1 else 0#64,
        if f = 1#8 then z2 else 0#64, if f = 1#8 then z3 else 0#64,
        replaceByte O[12]! 0 (nipFlag f z0 z1 z2 z3)] t →
      SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8f0#64) 286 := hstk.frame 286 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x150#64) 42 := hokW.sub' 244 42 (by decide) (by bv_omega)
  -- the frame: [8, 0x70) the `CtOption<Ep>`, [0x70, 0xd0) the selection, [0xd0, 0x130) the
  -- zero point, saved registers at 0x130..0x150
  obtain ⟨FC, hFC, hFCl⟩ := Region.exists_junk (sp - 0x148#64) 13 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0xe0#64) 12 s
  obtain ⟨FZ, hFZ, hFZl⟩ := Region.exists_junk (sp - 0x80#64) 12 s
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x148#64) 13 := hokF.sub' 1 13 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xe0#64) 12 := hokF.sub' 14 12 (by decide) (by bv_omega)
  have hokZ : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x80#64) 12 := hokF.sub' 26 12 (by decide) (by bv_omega)
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hokF.sub' 38 4 (by decide) (by bv_omega)
  have hok0' := hok0.toText
  have hok0'' : RegionOk Ro.layout.textLo Ro.layout.textHi out 12 := hok0'.sub' 0 12 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x8f0#64, 286), (out, 13)] s
  have hlo := hstk.lo
  sym_exec [ep_from_bytes_unchecked_spec, memset96_spec', hpb, hpp, hprz] stop [0x7801fb58]
  -- the flag byte, as `conditional_select` and the final `and` see it
  rw [extractByte_replaceByte _ _ (by decide)] at v16_def
  have hf01 := FromBytesPost.flag01 post9_18
  have hf16 := v16_def
  sym_reframe
  sym_exec [conditional_select_spec_byte, is_identity_spec, black_box_zip32_spec, memcpy96_spec]
  -- the stored byte is `nipFlag`
  have hflag : v27 = replaceByte O[12]! 0 (nipFlag post9_12 post9_8 post9_9 post9_10 post9_11) := by
    rw [← v27_def, ← v23_def, ← hf16, ← v16_def, ← v12_def, ← v11_def]
    exact congrArg _ (nip_flag_eq post9_12 hf01 _ _ _ _)
  rw [hflag] at hR1
  sym_close hk

end Cases.Zip2005
