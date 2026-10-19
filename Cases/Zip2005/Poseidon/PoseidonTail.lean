import Cases.Zip2005.Poseidon.PoseidonPartial
import Cases.Zip2005.Poseidon.PoseidonPerm
import Cases.Zip2005.Image.F_7801e26c
import MachineChecked.RiscV.Sym.Resume
import Cases.Zip2005.Image.Ro

/-!
# Poseidon's sponge, from round 41 to the return

The second half of `poseidon_sponge` (`Proof/Poseidon/PoseidonSponge.lean`): the state at the sponge's
round loop after 41 rounds (pc `0x7801e640`, the iterator about to hand out the 42nd round
closure), through the remaining 23 rounds and the squeeze into `[Some(s0), Some(s1)]`. Cut here
because one executor run over all 64 rounds does not fit the memory budget.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
theorem sponge_tail {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out st mp rc : Word)
    (y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : Word)
    (f0 f18 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r26 r27 : Word)
    (hpc : s.pc = 0x7801e640#64) (hcode : CodeAt F_7801e26c.base F_7801e26c.prog s)
    (hcodeF : CodeAt F_7801f120.base F_7801f120.prog s) (hcodeP : CodeAt F_7801ed68.base F_7801ed68.prog s)
    (hcodeX : CodeAt F_7801e704.base F_7801e704.prog s) (hcodeB : CodeAt F_78023a18.base F_78023a18.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s) (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra1 : ra &&& ~~~1#64 = ra) (hstk : StackOk Ro.layout 0x300 sp)
    (hx2 : s.getReg .x2 = sp + 18446744073709551360#64) (hx8 : s.getReg .x8 = rc + 3936#64) (hx9 : s.getReg .x9 = st)
    (hx10 : s.getReg .x10 = 2#64) (hx14 : s.getReg .x14 = rc + 3936#64)
    (hx18 : s.getReg .x18 = sp + 18446744073709551440#64) (hx19 : s.getReg .x19 = rc + 6144#64)
    (hx20 : s.getReg .x20 = 19#64) (hx21 : s.getReg .x21 = 4#64) (hx22 : s.getReg .x22 = 2#64)
    (hx23 : s.getReg .x23 = sp + 18446744073709551464#64) (hx24 : s.getReg .x24 = 3#64) (hx25 : s.getReg .x25 = sp + 18446744073709551488#64)
    (hx26 : s.getReg .x26 = 0#64) (hx27 : s.getReg .x27 = 2#64)
    (hX : Region st [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11] s) (hokX : RegionOk Ro.layout.roBase Ro.layout.textHi st 12)
    (hyl0 : leLimbsToNat [y0, y1, y2, y3] < Fp.p) (hyl1 : leLimbsToNat [y4, y5, y6, y7] < Fp.p)
    (hyl2 : leLimbsToNat [y8, y9, y10, y11] < Fp.p)
    (hO : Region out [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9] s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 10)
    (hF : Region (sp - 256#64) [f0, out, mp, sp + 18446744073709551376#64, sp + 18446744073709551376#64, rc, rc + 6144#64, 0#64, 0#64, sp + 18446744073709551384#64, 2013271664#64, 4#64, sp + 18446744073709551392#64, 2013271712#64, 19#64, sp + 18446744073709551384#64, 2013271664#64, 0#64, f18, r27, r26, r25, r24, r23, r22, r21, r20, r19, r18, r9, r8, ra] s)
    (hM : Region mp Poseidon.mdsWords s) (hokM : RegionOk Ro.layout.roBase Ro.layout.textHi mp 36)
    (hC : Region rc Poseidon.rcWords s) (hokC : RegionOk Ro.layout.roBase Ro.layout.textHi rc 768)
    (hd0 : Disjoint (sp - 0x300#64) 96 st 12) (hd2 : Disjoint (sp - 0x300#64) 96 mp 36)
    (hd3 : Disjoint (sp - 0x300#64) 96 rc 768) (hd4 : Disjoint (sp - 0x300#64) 96 out 10)
    (hd6 : Disjoint st 12 mp 36) (hd7 : Disjoint st 12 rc 768) (hd8 : Disjoint st 12 out 10)
    (hd10 : Disjoint out 10 mp 36) (hd11 : Disjoint out 10 rc 768)
    (hk : ∀ u, u.pc = ra → u.getReg .x2 = sp → u.getReg .x3 = s.getReg .x3 → u.getReg .x4 = s.getReg .x4 →
      u.getReg .x8 = r8 → u.getReg .x9 = r9 → u.getReg .x18 = r18 → u.getReg .x19 = r19 →
      u.getReg .x20 = r20 → u.getReg .x21 = r21 → u.getReg .x22 = r22 → u.getReg .x23 = r23 →
      u.getReg .x24 = r24 → u.getReg .x25 = r25 → u.getReg .x26 = r26 → u.getReg .x27 = r27 →
      u.code = s.code → Unchanged [(sp - 0x300#64, 96), (st, 12), (out, 10)] s u →
      ∀ o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 : Word,
      Region st [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11] u →
      Region out [1#64, o0, o1, o2, o3, 1#64, o4, o5, o6, o7] u →
      (leLimbsToNat [o0, o1, o2, o3], leLimbsToNat [o4, o5, o6, o7], leLimbsToNat [o8, o9, o10, o11]) =
        Poseidon.roundsFrom 41 23 (leLimbsToNat [y0, y1, y2, y3], leLimbsToNat [y4, y5, y6, y7], leLimbsToNat [y8, y9, y10, y11]) →
      SafeN G n P u) :
    SafeN G n P s := by
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 256#64) 32 := hstk.frame 32 (by decide)
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x300#64) 96 := hstk.frame 96 (by decide)
  have hu := Unchanged.refl [(sp - 0x300#64, 96), (st, 12), (out, 10)] s
  have hlo := hstk.lo
  have hroSt : st.toNat + 8 * 12 ≤ 0x78000000 ∨ 0x78000000 + 88376 ≤ st.toNat := hokX.roOut
  have hroOut : out.toNat + 8 * 10 ≤ 0x78000000 ∨ 0x78000000 + 88376 ≤ out.toNat := hokO.roOut
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  sym_exec [full_round_spec, partial_round_spec] 300
  have R41 : (leLimbsToNat [post13_4, post13_5, post13_6, post13_7], leLimbsToNat [post13_8, post13_9, post13_10, post13_11], leLimbsToNat [post13_12, post13_13, post13_14, post13_15]) = Poseidon.round 41 (leLimbsToNat [y0, y1, y2, y3], leLimbsToNat [y4, y5, y6, y7], leLimbsToNat [y8, y9, y10, y11]) := by
    rw [post13_17, post13_18, post13_19]; rfl
  have R42 : (leLimbsToNat [post31_4, post31_5, post31_6, post31_7], leLimbsToNat [post31_8, post31_9, post31_10, post31_11], leLimbsToNat [post31_12, post31_13, post31_14, post31_15]) = Poseidon.round 42 (leLimbsToNat [post13_4, post13_5, post13_6, post13_7], leLimbsToNat [post13_8, post13_9, post13_10, post13_11], leLimbsToNat [post13_12, post13_13, post13_14, post13_15]) := by
    rw [post31_17, post31_18, post31_19]; rfl
  have R43 : (leLimbsToNat [post49_4, post49_5, post49_6, post49_7], leLimbsToNat [post49_8, post49_9, post49_10, post49_11], leLimbsToNat [post49_12, post49_13, post49_14, post49_15]) = Poseidon.round 43 (leLimbsToNat [post31_4, post31_5, post31_6, post31_7], leLimbsToNat [post31_8, post31_9, post31_10, post31_11], leLimbsToNat [post31_12, post31_13, post31_14, post31_15]) := by
    rw [post49_17, post49_18, post49_19]; rfl
  have R44 : (leLimbsToNat [post67_4, post67_5, post67_6, post67_7], leLimbsToNat [post67_8, post67_9, post67_10, post67_11], leLimbsToNat [post67_12, post67_13, post67_14, post67_15]) = Poseidon.round 44 (leLimbsToNat [post49_4, post49_5, post49_6, post49_7], leLimbsToNat [post49_8, post49_9, post49_10, post49_11], leLimbsToNat [post49_12, post49_13, post49_14, post49_15]) := by
    rw [post67_17, post67_18, post67_19]; rfl
  have R45 : (leLimbsToNat [post85_4, post85_5, post85_6, post85_7], leLimbsToNat [post85_8, post85_9, post85_10, post85_11], leLimbsToNat [post85_12, post85_13, post85_14, post85_15]) = Poseidon.round 45 (leLimbsToNat [post67_4, post67_5, post67_6, post67_7], leLimbsToNat [post67_8, post67_9, post67_10, post67_11], leLimbsToNat [post67_12, post67_13, post67_14, post67_15]) := by
    rw [post85_17, post85_18, post85_19]; rfl
  have R46 : (leLimbsToNat [post103_4, post103_5, post103_6, post103_7], leLimbsToNat [post103_8, post103_9, post103_10, post103_11], leLimbsToNat [post103_12, post103_13, post103_14, post103_15]) = Poseidon.round 46 (leLimbsToNat [post85_4, post85_5, post85_6, post85_7], leLimbsToNat [post85_8, post85_9, post85_10, post85_11], leLimbsToNat [post85_12, post85_13, post85_14, post85_15]) := by
    rw [post103_17, post103_18, post103_19]; rfl
  have R47 : (leLimbsToNat [post121_4, post121_5, post121_6, post121_7], leLimbsToNat [post121_8, post121_9, post121_10, post121_11], leLimbsToNat [post121_12, post121_13, post121_14, post121_15]) = Poseidon.round 47 (leLimbsToNat [post103_4, post103_5, post103_6, post103_7], leLimbsToNat [post103_8, post103_9, post103_10, post103_11], leLimbsToNat [post103_12, post103_13, post103_14, post103_15]) := by
    rw [post121_17, post121_18, post121_19]; rfl
  have R48 : (leLimbsToNat [post139_4, post139_5, post139_6, post139_7], leLimbsToNat [post139_8, post139_9, post139_10, post139_11], leLimbsToNat [post139_12, post139_13, post139_14, post139_15]) = Poseidon.round 48 (leLimbsToNat [post121_4, post121_5, post121_6, post121_7], leLimbsToNat [post121_8, post121_9, post121_10, post121_11], leLimbsToNat [post121_12, post121_13, post121_14, post121_15]) := by
    rw [post139_17, post139_18, post139_19]; rfl
  have R49 : (leLimbsToNat [post157_4, post157_5, post157_6, post157_7], leLimbsToNat [post157_8, post157_9, post157_10, post157_11], leLimbsToNat [post157_12, post157_13, post157_14, post157_15]) = Poseidon.round 49 (leLimbsToNat [post139_4, post139_5, post139_6, post139_7], leLimbsToNat [post139_8, post139_9, post139_10, post139_11], leLimbsToNat [post139_12, post139_13, post139_14, post139_15]) := by
    rw [post157_17, post157_18, post157_19]; rfl
  have R50 : (leLimbsToNat [post175_4, post175_5, post175_6, post175_7], leLimbsToNat [post175_8, post175_9, post175_10, post175_11], leLimbsToNat [post175_12, post175_13, post175_14, post175_15]) = Poseidon.round 50 (leLimbsToNat [post157_4, post157_5, post157_6, post157_7], leLimbsToNat [post157_8, post157_9, post157_10, post157_11], leLimbsToNat [post157_12, post157_13, post157_14, post157_15]) := by
    rw [post175_17, post175_18, post175_19]; rfl
  have R51 : (leLimbsToNat [post193_4, post193_5, post193_6, post193_7], leLimbsToNat [post193_8, post193_9, post193_10, post193_11], leLimbsToNat [post193_12, post193_13, post193_14, post193_15]) = Poseidon.round 51 (leLimbsToNat [post175_4, post175_5, post175_6, post175_7], leLimbsToNat [post175_8, post175_9, post175_10, post175_11], leLimbsToNat [post175_12, post175_13, post175_14, post175_15]) := by
    rw [post193_17, post193_18, post193_19]; rfl
  have R52 : (leLimbsToNat [post211_4, post211_5, post211_6, post211_7], leLimbsToNat [post211_8, post211_9, post211_10, post211_11], leLimbsToNat [post211_12, post211_13, post211_14, post211_15]) = Poseidon.round 52 (leLimbsToNat [post193_4, post193_5, post193_6, post193_7], leLimbsToNat [post193_8, post193_9, post193_10, post193_11], leLimbsToNat [post193_12, post193_13, post193_14, post193_15]) := by
    rw [post211_17, post211_18, post211_19]; rfl
  have R53 : (leLimbsToNat [post229_4, post229_5, post229_6, post229_7], leLimbsToNat [post229_8, post229_9, post229_10, post229_11], leLimbsToNat [post229_12, post229_13, post229_14, post229_15]) = Poseidon.round 53 (leLimbsToNat [post211_4, post211_5, post211_6, post211_7], leLimbsToNat [post211_8, post211_9, post211_10, post211_11], leLimbsToNat [post211_12, post211_13, post211_14, post211_15]) := by
    rw [post229_17, post229_18, post229_19]; rfl
  have R54 : (leLimbsToNat [post247_4, post247_5, post247_6, post247_7], leLimbsToNat [post247_8, post247_9, post247_10, post247_11], leLimbsToNat [post247_12, post247_13, post247_14, post247_15]) = Poseidon.round 54 (leLimbsToNat [post229_4, post229_5, post229_6, post229_7], leLimbsToNat [post229_8, post229_9, post229_10, post229_11], leLimbsToNat [post229_12, post229_13, post229_14, post229_15]) := by
    rw [post247_17, post247_18, post247_19]; rfl
  have R55 : (leLimbsToNat [post265_4, post265_5, post265_6, post265_7], leLimbsToNat [post265_8, post265_9, post265_10, post265_11], leLimbsToNat [post265_12, post265_13, post265_14, post265_15]) = Poseidon.round 55 (leLimbsToNat [post247_4, post247_5, post247_6, post247_7], leLimbsToNat [post247_8, post247_9, post247_10, post247_11], leLimbsToNat [post247_12, post247_13, post247_14, post247_15]) := by
    rw [post265_17, post265_18, post265_19]; rfl
  have R56 : (leLimbsToNat [post283_4, post283_5, post283_6, post283_7], leLimbsToNat [post283_8, post283_9, post283_10, post283_11], leLimbsToNat [post283_12, post283_13, post283_14, post283_15]) = Poseidon.round 56 (leLimbsToNat [post265_4, post265_5, post265_6, post265_7], leLimbsToNat [post265_8, post265_9, post265_10, post265_11], leLimbsToNat [post265_12, post265_13, post265_14, post265_15]) := by
    rw [post283_17, post283_18, post283_19]; rfl
  clear post13_17 post13_18 post13_19 post13_20 post13_21 post13_22 post31_17 post31_18 post31_19 post31_20 post31_21 post31_22 post49_17 post49_18 post49_19 post49_20 post49_21 post49_22 post67_17 post67_18 post67_19 post67_20 post67_21 post67_22 post85_17 post85_18 post85_19 post85_20 post85_21 post85_22 post103_17 post103_18 post103_19 post103_20 post103_21 post103_22 post121_17 post121_18 post121_19 post121_20 post121_21 post121_22 post139_17 post139_18 post139_19 post139_20 post139_21 post139_22 post157_17 post157_18 post157_19 post157_20 post157_21 post157_22 post175_17 post175_18 post175_19 post175_20 post175_21 post175_22 post193_17 post193_18 post193_19 post193_20 post193_21 post193_22 post211_17 post211_18 post211_19 post211_20 post211_21 post211_22 post229_17 post229_18 post229_19 post229_20 post229_21 post229_22 post247_17 post247_18 post247_19 post247_20 post247_21 post247_22 post265_17 post265_18 post265_19 post265_20 post265_21 post265_22 post283_17 post283_18 post283_19
  sym_reframe
  sym_exec [full_round_spec, partial_round_spec] 400
  have R57 : (leLimbsToNat [post1_4, post1_5, post1_6, post1_7], leLimbsToNat [post1_8, post1_9, post1_10, post1_11], leLimbsToNat [post1_12, post1_13, post1_14, post1_15]) = Poseidon.round 57 (leLimbsToNat [post283_4, post283_5, post283_6, post283_7], leLimbsToNat [post283_8, post283_9, post283_10, post283_11], leLimbsToNat [post283_12, post283_13, post283_14, post283_15]) := by
    rw [post1_17, post1_18, post1_19]; rfl
  have R58 : (leLimbsToNat [post19_4, post19_5, post19_6, post19_7], leLimbsToNat [post19_8, post19_9, post19_10, post19_11], leLimbsToNat [post19_12, post19_13, post19_14, post19_15]) = Poseidon.round 58 (leLimbsToNat [post1_4, post1_5, post1_6, post1_7], leLimbsToNat [post1_8, post1_9, post1_10, post1_11], leLimbsToNat [post1_12, post1_13, post1_14, post1_15]) := by
    rw [post19_17, post19_18, post19_19]; rfl
  have R59 : (leLimbsToNat [post37_4, post37_5, post37_6, post37_7], leLimbsToNat [post37_8, post37_9, post37_10, post37_11], leLimbsToNat [post37_12, post37_13, post37_14, post37_15]) = Poseidon.round 59 (leLimbsToNat [post19_4, post19_5, post19_6, post19_7], leLimbsToNat [post19_8, post19_9, post19_10, post19_11], leLimbsToNat [post19_12, post19_13, post19_14, post19_15]) := by
    rw [post37_17, post37_18, post37_19]; rfl
  have R60 : (leLimbsToNat [post53_4, post53_5, post53_6, post53_7], leLimbsToNat [post53_8, post53_9, post53_10, post53_11], leLimbsToNat [post53_12, post53_13, post53_14, post53_15]) = Poseidon.round 60 (leLimbsToNat [post37_4, post37_5, post37_6, post37_7], leLimbsToNat [post37_8, post37_9, post37_10, post37_11], leLimbsToNat [post37_12, post37_13, post37_14, post37_15]) := by
    rw [post53_17, post53_18, post53_19]; rfl
  have R61 : (leLimbsToNat [post69_4, post69_5, post69_6, post69_7], leLimbsToNat [post69_8, post69_9, post69_10, post69_11], leLimbsToNat [post69_12, post69_13, post69_14, post69_15]) = Poseidon.round 61 (leLimbsToNat [post53_4, post53_5, post53_6, post53_7], leLimbsToNat [post53_8, post53_9, post53_10, post53_11], leLimbsToNat [post53_12, post53_13, post53_14, post53_15]) := by
    rw [post69_17, post69_18, post69_19]; rfl
  have R62 : (leLimbsToNat [post85_4, post85_5, post85_6, post85_7], leLimbsToNat [post85_8, post85_9, post85_10, post85_11], leLimbsToNat [post85_12, post85_13, post85_14, post85_15]) = Poseidon.round 62 (leLimbsToNat [post69_4, post69_5, post69_6, post69_7], leLimbsToNat [post69_8, post69_9, post69_10, post69_11], leLimbsToNat [post69_12, post69_13, post69_14, post69_15]) := by
    rw [post85_17, post85_18, post85_19]; rfl
  have R63 : (leLimbsToNat [post101_4, post101_5, post101_6, post101_7], leLimbsToNat [post101_8, post101_9, post101_10, post101_11], leLimbsToNat [post101_12, post101_13, post101_14, post101_15]) = Poseidon.round 63 (leLimbsToNat [post85_4, post85_5, post85_6, post85_7], leLimbsToNat [post85_8, post85_9, post85_10, post85_11], leLimbsToNat [post85_12, post85_13, post85_14, post85_15]) := by
    rw [post101_17, post101_18, post101_19]; rfl
  have hcs : s_139.code = s.code := hcode.trans hcode0
  sym_close hk
  · simp only [Poseidon.roundsFrom, R63, R62, R61, R60, R59, R58, R57, R56, R55, R54, R53, R52, R51, R50, R49, R48, R47, R46, R45, R44, R43, R42, R41]

end Cases.Zip2005
