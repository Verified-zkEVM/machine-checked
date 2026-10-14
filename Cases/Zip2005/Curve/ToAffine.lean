/-
  Cases.Zip2005.ToAffine

  `Ep::to_affine` (`pasta_curves`): Jacobian `(X, Y, Z)` to affine
  `(X/Z², Y/Z³)`, with `Z = 1` (Montgomery `R`) copied through and the point
  at infinity (`Z = 0`) sent to `(0, 0)`.
-/

import Cases.Zip2005.Field.FpInvert
import Cases.Zip2005.Image.F_78025164
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

theorem xor_ult_one (x c : Word) : (x ^^^ c).ult 1#64 = decide (x = c) := by
  rw [ult_one]
  congr 1
  apply propext
  constructor
  · intro h
    have := congrArg (· ^^^ c) h
    simpa [BitVec.xor_assoc] using this
  · intro h; subst h; simp

theorem add_one_ult_one (x : Word) : (x + 1#64).ult 1#64 = decide (x = 18446744073709551615#64) := by
  rw [ult_one]
  congr 1
  apply propext
  constructor
  · intro h; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add, Bn.toNat_ofNat', Bn.toNat_ofNat'] at this
    rw [Bn.toNat_ofNat']
    have := x.isLt; omega
  · intro h; subst h; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, Bn.toNat_ofNat', Bn.toNat_ofNat', Bn.toNat_ofNat']
    decide

theorem eq_R_of_limbs {z0 z1 z2 z3 : Word} (h0 : z0 = 3780891978758094845#64)
    (h1 : z1 = 11037255111966004397#64) (h2 : z2 = 18446744073709551615#64)
    (h3 : z3 = 4611686018427387903#64) : leLimbsToNat [z0, z1, z2, z3] = Fp.R := by
  subst h0 h1 h2 h3; exact Fp.limbs_R

theorem mask_flag (w : Word) (c : Prop) [Decidable c] :
    (w &&& -BitVec.zeroExtend 64 (if c then 0#8 else 1#8)) = if c then 0#64 else w := by
  by_cases h : c
  · simp only [h, if_true]
    rw [show -BitVec.zeroExtend 64 (0#8) = 0#64 by decide, BitVec.and_zero]
  · simp only [h, if_false]
    rw [show -BitVec.zeroExtend 64 (1#8) = BitVec.allOnes 64 by decide, BitVec.and_allOnes]

theorem allOnes_and' (x : Word) : 18446744073709551615#64 &&& x = x := by
  rw [show (18446744073709551615#64 : Word) = BitVec.allOnes 64 by decide, BitVec.allOnes_and]

theorem ite_cell (c : Prop) [Decidable c] (I k : Nat) :
    (if c then 0#64 else BitVec.ofNat 64 (I >>> k)) = BitVec.ofNat 64 ((if c then 0 else I) >>> k) := by
  split <;> simp

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 10000 in
theorem to_affine_spec {P : Prop} (s : MachineState) (ra a0 a1 sp : Word) (pt : List Word)
    (hptl : pt.length = 12)
    (hpc : s.pc = 0x78025164#64) (hcode : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x230 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a1 pt s) (hokx : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 8)
    (hd0 : Disjoint (sp - 0x230#64) 70 a0 8) (hd1 : Disjoint (sp - 0x230#64) 70 a1 12)
    (hd : Disjoint a0 8 a1 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x230#64, 70), (a0, 8)] s t →
      Region a0 (natToLeLimbs 4 (Fp.toAffine (leLimbsToNat [pt[0]!, pt[1]!, pt[2]!, pt[3]!])
          (leLimbsToNat [pt[4]!, pt[5]!, pt[6]!, pt[7]!]) (leLimbsToNat [pt[8]!, pt[9]!, pt[10]!, pt[11]!])).1 ++
        natToLeLimbs 4 (Fp.toAffine (leLimbsToNat [pt[0]!, pt[1]!, pt[2]!, pt[3]!])
          (leLimbsToNat [pt[4]!, pt[5]!, pt[6]!, pt[7]!]) (leLimbsToNat [pt[8]!, pt[9]!, pt[10]!, pt[11]!])).2) t →
      Safe P t) :
    Safe P s := by
  obtain ⟨O, hO, hOlen⟩ := Region.exists_junk a0 8 s
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x120#64) 36 s
  obtain ⟨G, hG, hGl⟩ := Region.exists_junk (sp - 0x230#64) 34 s
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x230#64) 70 := hstk.frame 70 (by decide)
  have hokF1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x120#64) 36 := hokF.sub' 34 36 (by decide) (by bv_omega)
  have hokG : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x230#64) 34 := hokF.sub' 0 34 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x230#64, 70), (a0, 8)] s
  sym_exec [uint256_mulmod_spec, black_box_spec, fp_invert_spec]
  all_goals sym_close hk
  all_goals sym_subst
  · -- `Z ≠ 1`
    have hZR : leLimbsToNat [pt[8]!, pt[9]!, pt[10]!, pt[11]!] ≠ Fp.R := by
      intro hz
      have hl := natToLeLimbs_leLimbsToNat [pt[8]!, pt[9]!, pt[10]!, pt[11]!]
      rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons, List.length_nil, hz,
        show natToLeLimbs 4 Fp.R = [3780891978758094845#64, 11037255111966004397#64,
          18446744073709551615#64, 4611686018427387903#64] by decide] at hl
      simp only [List.cons.injEq, and_true] at hl
      obtain ⟨h0, h1, h2, h3⟩ := hl
      rw [← h0, ← h1, ← h2, ← h3] at hbr67
      exact absurd hbr67 (by decide)
    clear hbr67
    rw [show [F[15]!, F[16]!, F[17]!, F[18]!, F[19]!][4]! = F[19]! from rfl,
      extractByte_replaceByte _ 0 (by decide)]
    simp only [mask_flag, Fp.toAffine, hZR, if_false]
    have hinvlt := Fp.invert_lt (leLimbsToNat [pt[8]!, pt[9]!, pt[10]!, pt[11]!])
    generalize leLimbsToNat [pt[0]!, pt[1]!, pt[2]!, pt[3]!] = X at *
    generalize leLimbsToNat [pt[4]!, pt[5]!, pt[6]!, pt[7]!] = Y at *
    generalize Fp.invert (leLimbsToNat [pt[8]!, pt[9]!, pt[10]!, pt[11]!]) = I at *
    generalize leLimbsToNat [pt[8]!, pt[9]!, pt[10]!, pt[11]!] = Z at *
    simp only [ite_cell]
    have hZIlt : (if Z = 0 then 0 else I) < Fp.p := by split <;> [exact Fp.p_pos; exact hinvlt]
    generalize (if Z = 0 then 0 else I) = ZI at *
    have hZIl : leLimbsToNat (natToLeLimbs 4 ZI) = ZI :=
      leLimbsToNat_natToLeLimbs 4 ZI (lt_trans hZIlt Fp.p_lt)
    simp only [ult_one, cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod, hZIl]
    have hz : leLimbsToNat [BitVec.ofNat 64 (ZI >>> 0), BitVec.ofNat 64 (ZI >>> 64),
        BitVec.ofNat 64 (ZI >>> 128), BitVec.ofNat 64 (ZI >>> 192)] = ZI := hZIl
    have hz' : (BitVec.ofNat 64 (ZI >>> 0) = 0#64 ∧ BitVec.ofNat 64 (ZI >>> 64) = 0#64 ∧
        BitVec.ofNat 64 (ZI >>> 128) = 0#64 ∧ BitVec.ofNat 64 (ZI >>> 192) = 0#64) ↔ ZI = 0 := by
      rw [← leLimbs4_eq_zero, hz]
    by_cases hZI : ZI = 0
    · subst hZI
      simp only [Nat.zero_shiftRight, ↓reduceIte, decide_true, BitVec.truncate_eq_setWidth,
        BitVec.reduceSetWidth, BitVec.reduceAnd, BitVec.reduceAdd]
      simp only [BitVec.zero_and]
      decide
    · simp only [hZI, if_false]
      generalize hb0 : decide (BitVec.ofNat 64 (ZI >>> 0) = 0#64) = b0
      generalize hb1 : decide (BitVec.ofNat 64 (ZI >>> 64) = 0#64) = b1
      generalize hb2 : decide (BitVec.ofNat 64 (ZI >>> 128) = 0#64) = b2
      generalize hb3 : decide (BitVec.ofNat 64 (ZI >>> 192) = 0#64) = b3
      -- the flag is `ζ = 0`, limb by limb
      cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
        try simp only [↓reduceIte, Bool.false_eq_true, BitVec.truncate_eq_setWidth,
          BitVec.reduceSetWidth, BitVec.reduceAnd, BitVec.reduceAdd]
      all_goals first
        | exact absurd (hz'.mp ⟨of_decide_eq_true hb0, of_decide_eq_true hb1, of_decide_eq_true hb2,
            of_decide_eq_true hb3⟩) hZI
        | (simp only [allOnes_and']; rfl)
  · -- `Z = 1`: copied through
    simp only [xor_ult_one, add_one_ult_one] at hbr67
    have hz : leLimbsToNat [pt[8]!, pt[9]!, pt[10]!, pt[11]!] = Fp.R := by
      by_cases h0 : pt[8]! = 3780891978758094845#64 <;> by_cases h1 : pt[9]! = 11037255111966004397#64 <;>
        by_cases h2 : pt[10]! = 18446744073709551615#64 <;>
        by_cases h3 : pt[11]! = 4611686018427387903#64 <;>
        simp only [h0, h1, h2, h3, decide_true, decide_false] at hbr67 <;>
        first | exact eq_R_of_limbs h0 h1 h2 h3 | exact absurd hbr67 (by decide)
    simp only [Fp.toAffine, hz, if_true]
    rw [show ∀ (a b c d e f g h : Word), [a, b, c, d, e, f, g, h] = [a, b, c, d] ++ [e, f, g, h]
      from fun _ _ _ _ _ _ _ _ => rfl]
    exact congrArg₂ (· ++ ·) (natToLeLimbs_leLimbsToNat [_, _, _, _]).symm
      (natToLeLimbs_leLimbsToNat [_, _, _, _]).symm

end Cases.Zip2005
