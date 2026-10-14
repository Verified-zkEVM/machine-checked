import Cases.Zip2005.Orchard.NonIdentityFromBytes
import Cases.Zip2005.Image.F_7801d2ec
import Cases.Zip2005.Image.Ro

/-!
# `Zip2005Witness::parse_g_d` (0x7801d2ec)

`NonIdentityPallasPoint::from_bytes` on the 32 bytes at `w + 0x4a0` into a frame slot, then
`Option<NonIdentityPallasPoint>` at the output: the tag from the flag byte, and on `Some` the
twelve words of the point copied by `memcpy`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

theorem nipFlag_01 (f : BitVec 8) (z0 z1 z2 z3 : Word) :
    nipFlag f z0 z1 z2 z3 = 1#8 ∨ nipFlag f z0 z1 z2 z3 = 0#8 := by
  unfold nipFlag; split <;> simp

theorem nipFlag_one {f : BitVec 8} {z0 z1 z2 z3 : Word} (h : nipFlag f z0 z1 z2 z3 = 1#8) :
    f = 1#8 := by
  unfold nipFlag at h; split at h
  · exact (by assumption : f = 1#8 ∧ _).1
  · exact absurd h (by decide)

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
theorem parse_g_d_spec {P : Prop} (s : MachineState) (ra sp a0 w : Word)
    (b0 b1 b2 b3 cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (O IV G0 G1 G2 G3 : List Word)
    (hOl : O.length = 13) (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → Safe P u)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → Safe P u)
    (hprz : ∀ u : MachineState, u.pc = 0x7803de78#64 → u.code = s.code → Safe P u)
    (hpc : s.pc = 0x7801d2ec#64) (hcode : CodeAt F_7801d2ec.base F_7801d2ec.prog s)
    (hcodeN : CodeAt F_7801fb1c.base F_7801fb1c.prog s)
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
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x970 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = w)
    (hB : Region (w + 0x4a0#64) [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 0x4a0#64) 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 13)
    -- `FP_TABLES`, initialised (`Once` state byte 2 at 0x780488f0, padding zero)
    (hTB : Region 0x780488a8#64 [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx, 2#64] s)
    (hIV : Region iptr IV s) (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hG0 : Region g0 G0 s) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024)
    (hG1 : Region g1 G1 s) (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024)
    (hG2 : Region g2 G2 s) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024)
    (hG3 : Region g3 G3 s) (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hd0 : Disjoint (sp - 0x970#64) 302 a0 13) (hd_a1 : Disjoint (sp - 0x970#64) 302 (w + 0x4a0#64) 4)
    (hd_tb : Disjoint (sp - 0x970#64) 302 0x780488a8#64 10)
    (hd_iptr : Disjoint (sp - 0x970#64) 302 iptr 138)
    (hd_g0 : Disjoint (sp - 0x970#64) 302 g0 1024) (hd_g1 : Disjoint (sp - 0x970#64) 302 g1 1024)
    (hd_g2 : Disjoint (sp - 0x970#64) 302 g2 1024) (hd_g3 : Disjoint (sp - 0x970#64) 302 g3 516)
    (he_a1 : Disjoint a0 13 (w + 0x4a0#64) 4) (he_tb : Disjoint a0 13 0x780488a8#64 10)
    (he_iptr : Disjoint a0 13 iptr 138)
    (he_g0 : Disjoint a0 13 g0 1024) (he_g1 : Disjoint a0 13 g1 1024)
    (he_g2 : Disjoint a0 13 g2 1024) (he_g3 : Disjoint a0 13 g3 516)
    (hk : ∀ (t : MachineState) (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word) (f : BitVec 8)
      (tag : Word) (L : List Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x970#64, 302), (a0, 13)] s t →
      FromBytesPost b0 b1 b2 b3 (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) f →
      leLimbsToNat [z0, z1, z2, z3] =
        (if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R) →
      tag = BitVec.zeroExtend 64 (nipFlag f z0 z1 z2 z3) → L.length = 12 →
      (nipFlag f z0 z1 z2 z3 = 1#8 → L = [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3]) →
      Region a0 (tag :: L) t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x970#64) 302 := hstk.frame 302 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x80#64) 16 := hokW.sub' 286 16 (by decide) (by bv_omega)
  -- the frame: [0, 0x68) the `NonIdentityPallasPoint` with its flag byte, saved registers at
  -- 0x68..0x80
  obtain ⟨FC, hFC, hFCl⟩ := Region.exists_junk (sp - 0x80#64) 13 s
  obtain ⟨FR, hFR, hFRl⟩ := Region.exists_junk (sp - 0x18#64) 3 s
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x80#64) 13 := hokF.sub' 0 13 (by decide) (by bv_omega)
  have hokC' : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x80#64) 12 := hokF.sub' 0 12 (by decide) (by bv_omega)
  have hokR : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x18#64) 3 := hokF.sub' 13 3 (by decide) (by bv_omega)
  have hok0' := hok0.toText
  have hok0'' : RegionOk Ro.layout.textLo Ro.layout.textHi (a0 + 8#64) 12 := hok0'.sub' 1 12 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x970#64, 302), (a0, 13)] s
  have hlo := hstk.lo
  sym_exec [non_identity_pallas_point_from_bytes_spec, memcpy96_spec, hpb, hpp, hprz]
  all_goals rw [extractByte_replaceByte _ _ (by decide)] at v10_def
  · -- `None`: the flag byte is not 1, so it is 0
    have hf0 : nipFlag post9_12 post9_8 post9_9 post9_10 post9_11 = 0#8 := by
      rcases nipFlag_01 post9_12 post9_8 post9_9 post9_10 post9_11 with h | h
      · exact absurd (by rw [← v10_def, h]; rfl : v10 = 1#64) (bne_iff_ne.mp hbr12)
      · exact h
    sym_close (hk _ post9_0 post9_1 post9_2 post9_3 post9_4 post9_5 post9_6 post9_7 post9_8 post9_9 post9_10 post9_11 post9_12 0#64 [O[1]!, O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!, O[12]!])
    all_goals first
      | (intro h; rw [hf0] at h; exact absurd h (by decide))
      | (rw [hf0])
      | rfl
  · -- `Some`: the flag byte is 1, hence `f = 1` and the selection is the point
    have h1 : BitVec.zeroExtend 64 (nipFlag post9_12 post9_8 post9_9 post9_10 post9_11) = 1#64 := by
      rw [v10_def]; simpa using hbr12
    sym_close (hk _ post9_0 post9_1 post9_2 post9_3 post9_4 post9_5 post9_6 post9_7 post9_8 post9_9 post9_10 post9_11 post9_12 1#64 [(if post9_12 = 1#8 then post9_0 else 0#64), (if post9_12 = 1#8 then post9_1 else 0#64), (if post9_12 = 1#8 then post9_2 else 0#64), (if post9_12 = 1#8 then post9_3 else 0#64), (if post9_12 = 1#8 then post9_4 else 0#64), (if post9_12 = 1#8 then post9_5 else 0#64), (if post9_12 = 1#8 then post9_6 else 0#64), (if post9_12 = 1#8 then post9_7 else 0#64), (if post9_12 = 1#8 then post9_8 else 0#64), (if post9_12 = 1#8 then post9_9 else 0#64), (if post9_12 = 1#8 then post9_10 else 0#64), (if post9_12 = 1#8 then post9_11 else 0#64)])
    all_goals first
      | exact h1.symm
      | rfl
      | (intro h; rw [nipFlag_one h]; simp)

end Cases.Zip2005
