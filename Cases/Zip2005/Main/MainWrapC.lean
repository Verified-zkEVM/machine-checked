import Cases.Zip2005.Witness.ParseRho
import Cases.Zip2005.Orchard.Psi
import Cases.Zip2005.Field.CtLimbs
import Cases.Zip2005.Curve.EpModel
import Cases.Zip2005.Main.MainAccept
import Cases.Zip2005.Orchard.CommitIvk
import Cases.Zip2005.Orchard.NonZeroScalar
import Cases.Zip2005.Image.Ro

/-!
# Wrappers for `main`'s segment C

`parse_rho` split on the canonicity of the witness bytes, and `RandomSeed::psi` with its output
limbs named: the next segment takes the canonicity of `ρ` and `ψ` as hypotheses, and the executor
discharges such a premise only from a fact about the very cells it reads.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym Cases.Zip2005.B2b

set_option autoImplicit false

/-- `parse_rho_spec` on canonical bytes: tag `1` and the limbs named, with their value and
canonicity as facts. -/
theorem parse_rho_ok_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 : Word) (b0 b1 b2 b3 : Word)
    (O : List Word) (hOl : O.length = 5)
    (hpc : s.pc = 0x7801d360#64) (hcode : CodeAt F_7801d360.base F_7801d360.prog s)
    (hcodeRho : CodeAt F_7801ddd8.base F_7801ddd8.prog s)
    (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x150 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hB : Region (a1 + 0x4c0#64) [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.roBase Ro.layout.textHi (a1 + 0x4c0#64) 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5)
    (hd0 : Disjoint (sp - 0x150#64) 42 a0 5) (hd_a1 : Disjoint (sp - 0x150#64) 42 (a1 + 0x4c0#64) 4)
    (he_a1 : Disjoint a0 5 (a1 + 0x4c0#64) 4)
    (hc : leLimbsToNat [b0, b1, b2, b3] < Fp.p)
    (hk : ∀ (t : MachineState) (r0 r1 r2 r3 : Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x150#64, 42), (a0, 5)] s t →
      leLimbsToNat [r0, r1, r2, r3] = Fp.mul (leLimbsToNat [b0, b1, b2, b3]) Fp.R2 → leLimbsToNat [r0, r1, r2, r3] < Fp.p →
      Region a0 [1#64, r0, r1, r2, r3] t → SafeN G n P t) :
    SafeN G n P s :=
  parse_rho_spec s ra sp a0 a1 b0 b1 b2 b3 O hOl hpc hcode hcodeRho hcodeR hcodeM hcodeB hcw hro hra hra1 hsp hstk ha0 ha1 hB hok_a1 hO hok0 hd0 hd_a1 he_a1 (fun t tag L h1 h2 h3 h4 htag _ hLeq hR => by
    rw [if_pos hc] at htag; subst htag
    have e := hLeq hc; subst e
    have hX := leLimbsToNat_natToLeLimbs 4 (Fp.mul (leLimbsToNat [b0, b1, b2, b3]) Fp.R2) (lt_trans (Fp.mul_lt _ _) Fp.p_lt)
    rw [natToLeLimbs_four] at hR hX
    exact hk t _ _ _ _ h1 h2 h3 h4 hX (by rw [hX]; exact Fp.mul_lt _ _) hR)

/-- `parse_rho_spec` on non-canonical bytes: tag `0` (`None`). -/
theorem parse_rho_bad_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 : Word) (b0 b1 b2 b3 : Word)
    (O : List Word) (hOl : O.length = 5)
    (hpc : s.pc = 0x7801d360#64) (hcode : CodeAt F_7801d360.base F_7801d360.prog s)
    (hcodeRho : CodeAt F_7801ddd8.base F_7801ddd8.prog s)
    (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x150 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hB : Region (a1 + 0x4c0#64) [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.roBase Ro.layout.textHi (a1 + 0x4c0#64) 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5)
    (hd0 : Disjoint (sp - 0x150#64) 42 a0 5) (hd_a1 : Disjoint (sp - 0x150#64) 42 (a1 + 0x4c0#64) 4)
    (he_a1 : Disjoint a0 5 (a1 + 0x4c0#64) 4)
    (hc : ¬ leLimbsToNat [b0, b1, b2, b3] < Fp.p)
    (hk : ∀ (t : MachineState) (L : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x150#64, 42), (a0, 5)] s t → L.length = 4 →
      Region a0 (0#64 :: L) t → SafeN G n P t) :
    SafeN G n P s :=
  parse_rho_spec s ra sp a0 a1 b0 b1 b2 b3 O hOl hpc hcode hcodeRho hcodeR hcodeM hcodeB hcw hro hra hra1 hsp hstk ha0 ha1 hB hok_a1 hO hok0 hd0 hd_a1 he_a1 (fun t tag L h1 h2 h3 h4 htag hL _ hR => by
    rw [if_neg hc] at htag; subst htag; exact hk t L h1 h2 h3 h4 hL hR)

/-- `psi_spec` with the output limbs named (their value and canonicity as facts) and its frame's
prior contents taken as junk, so a caller need not hold regions below its stack pointer. -/
theorem psi_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out rs rho s0 s1 s2 s3 p0 p1 p2 p3 : Word)
    (hpc : s.pc = 0x7801d51c#64) (hcP : CodeAt F_7801d51c.base F_7801d51c.prog s)
    (hcR : CodeAt F_78029468.base F_78029468.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcX : CodeAt F_7802e2b4.base F_7802e2b4.prog s) (hcX2 : CodeAt F_78028718.base F_78028718.prog s)
    (hcX3 : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x4d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = rs) (ha2 : s.getReg .x12 = rho)
    (hRS : Region rs [s0, s1, s2, s3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi rs 4)
    (hRP : Region rho [p0, p1, p2, p3] s) (hokP : RegionOk Ro.layout.roBase Ro.layout.textHi rho 4)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd1 : Disjoint (sp - 0x4d0#64) 154 rs 4) (hd2 : Disjoint (sp - 0x4d0#64) 154 out 4)
    (hd3 : Disjoint (sp - 0x4d0#64) 154 rho 4)
    (he1 : Disjoint out 4 rs 4) (he2 : Disjoint out 4 rho 4)
    (hk : ∀ (t : MachineState) (q0 q1 q2 q3 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x4d0#64, 154), (out, 4)] s t →
      leLimbsToNat [q0, q1, q2, q3] = psiX s0 s1 s2 s3 p0 p1 p2 p3 → leLimbsToNat [q0, q1, q2, q3] < Fp.p →
      Region out [q0, q1, q2, q3] t → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨F1, hRF1, hF1⟩ := Region.exists_junk (sp - 0x4d0#64) 74 s
  obtain ⟨F3, hRF3, hF3⟩ := Region.exists_junk (sp - 0x280#64) 12 s
  obtain ⟨F2, hRF2, hF2⟩ := Region.exists_junk (sp - 0x220#64) 68 s
  exact psi_spec s ra sp out rs rho s0 s1 s2 s3 p0 p1 p2 p3 F1 F3 F2 hF1 hF3 hF2 hpc hcP hcR hcT hcU hcF hcL hcM hcC hcX hcX2 hcX3 hcw hro hra hra1 hsp hstk ha0 ha1 ha2 hRF1 hRF3 hRF2 hRS hokS hRP hokP hokO hd1 hd2 hd3 he1 he2 (fun t h1 h2 h3 h4 hR => by
    have hX := leLimbsToNat_natToLeLimbs 4 (Fp.add (Fp.mul (leLimbsToNat [(compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[0]!, (compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[1]!, (compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[2]!, (compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[3]!]) Fp.R2) (Fp.mul (leLimbsToNat [(compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[4]!, (compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[5]!, (compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[6]!, (compress prfH [s0, s1, s2, s3, ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! <<< 8) ||| BitVec.zeroExtend 64 (BitVec.truncate 8 9#64), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[0]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[1]! >>> 56), ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! <<< 8) ||| ((natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[2]! >>> 56), (natToLeLimbs 4 (leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p))[3]! >>> 56, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] 65#64 0#64 0xFFFFFFFFFFFFFFFF#64 0#64)[7]!]) Fp.R3)) (lt_trans (Fp.add_lt _ _) Fp.p_lt)
    rw [natToLeLimbs_four] at hR hX
    exact hk t _ _ _ _ h1 h2 h3 h4 hX (by rw [hX]; exact Fp.add_lt _ _) hR)

/-- `rcm_v3_spec` with its ghost encodings discharged (the cells of `to_bytes` of the points and of
`ρ`, `ψ` out of Montgomery form) and the output related by `RcmRel`. -/
theorem rcm_v3_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out rs rho gd pkd v psi : Word)
    (e0 e1 e2 e3 r0 r1 r2 r3 q0 q1 q2 q3 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 : Word)
    (hpc : s.pc = 0x7801d92c#64) (hcP : CodeAt F_7801d92c.base F_7801d92c.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcB : CodeAt F_78025654.base F_78025654.prog s) (hcB2 : CodeAt F_78025164.base F_78025164.prog s)
    (hcB3 : CodeAt F_78028d04.base F_78028d04.prog s) (hcB4 : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcB5 : CodeAt F_7803a0fc.base F_7803a0fc.prog s) (hcR : CodeAt F_78029468.base F_78029468.prog s)
    (hcX : CodeAt F_7802f038.base F_7802f038.prog s) (hcX2 : CodeAt F_7802e5b4.base F_7802e5b4.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x510 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = rs) (ha2 : s.getReg .x12 = rho)
    (ha3 : s.getReg .x13 = gd) (ha4 : s.getReg .x14 = pkd) (ha5 : s.getReg .x15 = v)
    (ha6 : s.getReg .x16 = psi)
    (hRS : Region rs [e0, e1, e2, e3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi rs 4)
    (hRR : Region rho [r0, r1, r2, r3] s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi rho 4)
    (hRQ : Region psi [q0, q1, q2, q3] s) (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi psi 4)
    (hRGd : Region gd [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] s) (hokGd : RegionOk Ro.layout.roBase Ro.layout.textHi gd 12)
    (hRK : Region pkd [k0, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11] s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi pkd 12)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd1 : Disjoint (sp - 0x510#64) 162 rs 4) (hd2 : Disjoint (sp - 0x510#64) 162 rho 4)
    (hd3 : Disjoint (sp - 0x510#64) 162 psi 4) (hd4 : Disjoint (sp - 0x510#64) 162 gd 12)
    (hd5 : Disjoint (sp - 0x510#64) 162 pkd 12) (hd6 : Disjoint (sp - 0x510#64) 162 out 4)
    (he1 : Disjoint out 4 rs 4) (he2 : Disjoint out 4 rho 4) (he3 : Disjoint out 4 psi 4)
    (he4 : Disjoint out 4 gd 12) (he5 : Disjoint out 4 pkd 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x510#64, 162), (out, 4)] s t →
      ∀ x : Nat, Region out (natToLeLimbs 4 x) t →
      RcmRel e0 e1 e2 e3 r0 r1 r2 r3 q0 q1 q2 q3 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 v x → SafeN G n P t) :
    SafeN G n P s :=
  rcm_v3_spec s ra sp out rs rho gd pkd v psi e0 e1 e2 e3 r0 r1 r2 r3 q0 q1 q2 q3 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 (BitVec.ofNat 64 (tbX g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11)) (BitVec.ofNat 64 (tbX g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 >>> 64)) (BitVec.ofNat 64 (tbX g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 >>> 128)) (BitVec.ofNat 64 (tbX g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 >>> 192)) (BitVec.ofNat 64 (tbX k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11)) (BitVec.ofNat 64 (tbX k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 >>> 64)) (BitVec.ofNat 64 (tbX k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 >>> 128)) (BitVec.ofNat 64 (tbX k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 >>> 192)) (BitVec.ofNat 64 (leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p)) (BitVec.ofNat 64 ((leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p) >>> 64)) (BitVec.ofNat 64 ((leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p) >>> 128)) (BitVec.ofNat 64 ((leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p) >>> 192)) (BitVec.ofNat 64 (leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p)) (BitVec.ofNat 64 ((leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p) >>> 64)) (BitVec.ofNat 64 ((leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p) >>> 128)) (BitVec.ofNat 64 ((leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p) >>> 192)) (natToLeLimbs_four (tbX g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11)) (natToLeLimbs_four (tbX k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11)) (natToLeLimbs_four (leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p)) (natToLeLimbs_four (leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p)) hpc hcP hcT hcU hcF hcL hcM hcC hcB hcB2 hcB3 hcB4 hcB5 hcR hcX hcX2 hcw hro hra hra1 hsp hstk ha0 ha1 ha2 ha3 ha4 ha5 ha6 hRS hokS hRR hokR hRQ hokQ hRGd hokGd hRK hokK hokO hd1 hd2 hd3 hd4 hd5 hd6 he1 he2 he3 he4 he5 (fun t h1 h2 h3 h4 x hR hx => hk t h1 h2 h3 h4 x hR
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, natToLeLimbs_four (tbX g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11), natToLeLimbs_four (tbX k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11),
      natToLeLimbs_four (leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p), natToLeLimbs_four (leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p), hx⟩)

/-- `ep_to_bytes_spec` with the four output cells named. -/
theorem ep_to_bytes_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 : Word) (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 : Word)
    (O : List Word) (hOl : O.length = 4)
    (hpc : s.pc = 0x78025654#64) (hcode : CodeAt F_78025654.base F_78025654.prog s)
    (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeMS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x2f0 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hp : Region a1 [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 4)
    (hd0 : Disjoint (sp - 0x2f0#64) 94 a0 4) (hd1 : Disjoint (sp - 0x2f0#64) 94 a1 12)
    (he1 : Disjoint a0 4 a1 12)
    (hk : ∀ (t : MachineState) (c0 c1 c2 c3 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x2f0#64, 94), (a0, 4)] s t →
      [c0, c1, c2, c3] = natToLeLimbs 4 (tbX p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11) → Region a0 [c0, c1, c2, c3] t → SafeN G n P t) :
    SafeN G n P s :=
  ep_to_bytes_spec s ra sp a0 a1 p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 O hOl hpc hcode hcodeTA hcodeI hcodeM hcodeB hcodeMS hcodeT hcw hro hra hra1 hsp hstk ha0 ha1 hp hok1 hO hok0 hd0 hd1 he1 (fun t h1 h2 h3 h4 hR => hk t _ _ _ _ h1 h2 h3 h4 (natToLeLimbs_four (tbX p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11)).symm
    (by rw [natToLeLimbs_four] at hR; exact hR))

/-- `rivk_internal_spec` with the output cells named and the frame's prior contents taken as junk. -/
theorem rivk_internal_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out fvk SC k0 k1 k2 k3 n0 n1 n2 n3 r0 r1 r2 r3 : Word)
    (hpc : s.pc = 0x78022ca0#64) (hcR : CodeAt F_78022ca0.base F_78022ca0.prog s)
    (hcQ : CodeAt F_7802e9b8.base F_7802e9b8.prog s) (hcI : CodeAt F_78028ce8.base F_78028ce8.prog s)
    (hcI2 : CodeAt F_78029468.base F_78029468.prog s)
    (hcW : CodeAt F_7801d3d4.base F_7801d3d4.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcX : CodeAt F_7802f038.base F_7802f038.prog s) (hcX2 : CodeAt F_7802e5b4.base F_7802e5b4.prog s)
    (hcX3 : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x570 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = fvk) (ha2 : s.getReg .x12 = SC)
    (hK : Region (fvk + 0x60#64) [k0, k1, k2, k3, n0, n1, n2, n3, r0, r1, r2, r3] s)
    (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi (fvk + 0x60#64) 12)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd1 : Disjoint (sp - 0x570#64) 174 (fvk + 0x60#64) 12) (hd2 : Disjoint (sp - 0x570#64) 174 out 4)
    (hd3 : Disjoint out 4 (fvk + 0x60#64) 12)
    (hSC : SC = 1#64)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → SafeN G n P u)
    (hk : ∀ (t : MachineState) (c0 c1 c2 c3 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x570#64, 174), (out, 4)] s t →
      [c0, c1, c2, c3] = natToLeLimbs 4 (rivkIntX k0 k1 k2 k3 n0 n1 n2 n3 r0 r1 r2 r3) → Region out [c0, c1, c2, c3] t → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨Fr, hRF, hFr⟩ := Region.exists_junk (sp - 0xe0#64) 28 s
  exact rivk_internal_spec s ra sp out fvk SC k0 k1 k2 k3 n0 n1 n2 n3 r0 r1 r2 r3 Fr hFr hRF hpc hcR hcQ hcI hcI2 hcW hcT hcU hcF hcL hcM hcC hcX hcX2 hcX3 hcw hro hra hra1 hsp hstk ha0 ha1 ha2 hK hokK hokO hd1 hd2 hd3 hSC hpp (fun t h1 h2 h3 h4 hR => hk t _ _ _ _ h1 h2 h3 h4 (natToLeLimbs_four (rivkIntX k0 k1 k2 k3 n0 n1 n2 n3 r0 r1 r2 r3)).symm
    (by rw [natToLeLimbs_four] at hR; exact hR))

/-- `commit_ivk_spec` over the generic `from_iter` contract (any caller frame `sp0`, padding `J0`
and key words), instantiated inside: a caller passes its own hypothesis unchanged. -/
theorem commit_ivk_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out ak nk rivk : Word)
    (a0 a1 a2 a3 n0 n1 n2 n3 k0 k1 k2 k3 : Word)
    (O J : List Word) (hOl : O.length = 5) (hJl : J.length = 9)
    -- the sqrt/generator tables (`FP_TABLES`) in the heap, carried through: the allocator
    -- contracts below keep them (the allocator never writes a live block)
    (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word)
    (hIVl : IV.length = 138) (hG0l : G0.length = 1024) (hG1l : G1.length = 1024)
    (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hTB : Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] s)
    (hIVr : Region iptr IV s) (hG0 : Region tg0 G0 s) (hG1 : Region tg1 G1 s)
    (hG2 : Region tg2 G2 s) (hG3 : Region tg3 G3 s)
    (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024)
    (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024)
    (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516)
    (hlo_iptr : 0x78048980 ≤ iptr.toNat) (hlo_g0 : 0x78048980 ≤ tg0.toNat) (hlo_g1 : 0x78048980 ≤ tg1.toNat)
    (hlo_g2 : 0x78048980 ≤ tg2.toNat) (hlo_g3 : 0x78048980 ≤ tg3.toNat)
    (hhi_iptr : iptr.toNat + 8 * 138 ≤ 0x1c00000000)
    (hhi_g0 : tg0.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g1 : tg1.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g2 : tg2.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g3 : tg3.toNat + 8 * 516 ≤ 0x1c00000000)
    -- the caller's blocks lie below the heap (on its stack), so off the tables
    (hbelow_out : out.toNat + 8 * 5 ≤ 0x78040620)
    (hbelow_rivk : rivk.toNat + 8 * 4 ≤ 0x78040620)
    (hbelow_ak : ak.toNat + 8 * 4 ≤ 0x78040620)
    (hbelow_nk : nk.toNat + 8 * 4 ≤ 0x78040620)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → SafeN G n P u)
    (hpanic : ∀ u : MachineState, u.pc = 0x7803de40#64 → u.code = s.code → SafeN G n P u)
    (hunwrap : ∀ u : MachineState, u.pc = 0x7803dc7c#64 → u.code = s.code → SafeN G n P u)
    (hbounds : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → SafeN G n P u)
    (hpc : s.pc = 0x780203dc#64) (hcode : CodeAt F_780203dc.base F_780203dc.prog s)
    -- callees: cached_commit_domain (+ from_raw, from_xy, is_on_curve, mulmod, black_box,
    -- to_curve), to_le_bits (+ to_repr), commit (`0x78021238`) and its callees,
    -- extract_p_bottom (+ memset, conditional_select, to_affine, coordinates)
    (hcodeCD : CodeAt F_78020548.base F_78020548.prog s) (hcodeLB : CodeAt F_78029b18.base F_78029b18.prog s)
    (hcodeCm : CodeAt F_78021238.base F_78021238.prog s) (hcodeEB : CodeAt F_7802340c.base F_7802340c.prog s)
    (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s) (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeBB : CodeAt F_7803a0fc.base F_7803a0fc.prog s) (hcodeCo : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeP : CodeAt F_780237dc.base F_780237dc.prog s) (hcodeRp : CodeAt F_78029468.base F_78029468.prog s)
    (hcodeL : CodeAt F_780234cc.base F_780234cc.prog s) (hcodeIA : CodeAt F_780235e8.base F_780235e8.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s) (hcodeAA : CodeAt F_78035f88.base F_78035f88.prog s)
    (hcodeLR : CodeAt F_780360e0.base F_780360e0.prog s) (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcodeU : CodeAt F_78023864.base F_78023864.prog s) (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeXY : CodeAt F_78026878.base F_78026878.prog s) (hcodeOC : CodeAt F_78026258.base F_78026258.prog s)
    (hcodeFR : CodeAt F_78028298.base F_78028298.prog s) (hcodeTC : CodeAt F_78025854.base F_78025854.prog s)
    (hcodeF : CodeAt F_780239bc.base F_780239bc.prog s) (hcodeBt : CodeAt F_78023544.base F_78023544.prog s)
    (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcodeCS : CodeAt F_78023d7c.base F_78023d7c.prog s)
    (hcodeB : CodeAt F_78023594.base F_78023594.prog s) (hcodeW : CodeAt F_7802827c.base F_7802827c.prog s)
    (hcodeMul : CodeAt F_78031be8.base F_78031be8.prog s) (hcodeRq : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    (hcodeA : CodeAt F_78035fe0.base F_78035fe0.prog s) (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcodeD : CodeAt F_780360c8.base F_780360c8.prog s) (hcodeAF : CodeAt F_7803a110.base F_7803a110.prog s)
    (hcodeAFI : CodeAt F_7803dd28.base F_7803dd28.prog s) (hcodeEA : CodeAt F_78026b44.base F_78026b44.prog s)
    (hcodeED : CodeAt F_7802413c.base F_7802413c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0xaa0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = ak) (ha2 : s.getReg .x12 = nk)
    (ha3 : s.getReg .x13 = rivk)
    (hA : Region ak [a0, a1, a2, a3] s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi ak 4)
    (hN : Region nk [n0, n1, n2, n3] s) (hokN : RegionOk Ro.layout.roBase Ro.layout.textHi nk 4)
    (hK : Region rivk [k0, k1, k2, k3] s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi rivk 4)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 5)
    -- the frame's iterator block before the call: the struct's padding bytes keep these
    (hJ : Region (sp - 0xaa0#64 + 0x980#64) J s)
    (hd0 : Disjoint (sp - 0xaa0#64) 340 out 5) (hd1 : Disjoint (sp - 0xaa0#64) 340 ak 4)
    (hd2 : Disjoint (sp - 0xaa0#64) 340 nk 4) (hd3 : Disjoint (sp - 0xaa0#64) 340 rivk 4)
    (he0 : Disjoint out 5 ak 4) (he1 : Disjoint out 5 nk 4) (he2 : Disjoint out 5 rivk 4)
    (hh0 : Disjoint 0x78040620#64 14780694332 out 5) (hh1 : Disjoint 0x78040620#64 14780694332 rivk 4)
    -- `Vec<bool>::from_iter` of the padded bit iterator (ledger T2): the iterator block as
    -- `commit_ivk` builds it over the message words at `+0x9c8` (`ak`'s bits, then `nk`'s)
    -- yields 510 bytes, byte `o` the message bit `o`
    (hfrom : ∀ (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word) (sp0 : Word)
      (J0 : List Word) (a0 a1 a2 a3 n0 n1 n2 n3 : Word), O1.length = 3 →
      u.pc = 0x7801e110#64 → u.code = s.code → u.getReg .x1 = 0x780212ac#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x260 sp' → u.getReg .x10 = a0' → u.getReg .x11 = a1' →
      Region a0' O1 u → Region a1' [0#64, j] u →
      Region (a1' + 0x10#64) (iterIvkW sp0 J0) u →
      Region (a1' + 0x58#64) [0#64] u →
      Region (sp0 - 0xaa0#64 + 0x9c8#64) (ivkMsgW [a0, a1, a2, a3] [n0, n1, n2, n3]) u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 3 → RegionOk Ro.layout.roBase Ro.layout.textHi a1' 12 →
      Disjoint (sp' - 0x260#64) 76 a0' 3 → Disjoint (sp' - 0x260#64) 76 a1' 12 →
      Disjoint a0' 3 a1' 12 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      IV.length = 138 → G0.length = 1024 → G1.length = 1024 → G2.length = 1024 → G3.length = 516 →
      0x78048980 ≤ iptr.toNat → iptr.toNat + 8 * 138 ≤ 0x1c00000000 →
      0x78048980 ≤ tg0.toNat → tg0.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg1.toNat → tg1.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg2.toNat → tg2.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg3.toNat → tg3.toNat + 8 * 516 ≤ 0x1c00000000 →
      RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 → RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 →
      StackOk Ro.layout 0xaa0 sp0 →
      Disjoint (sp' - 0x260#64) 76 (sp0 - 0xaa0#64 + 0x9c8#64) 8 → Disjoint a0' 3 (sp0 - 0xaa0#64 + 0x9c8#64) 8 → Disjoint a1' 12 (sp0 - 0xaa0#64 + 0x9c8#64) 8 →
      Disjoint 0x78040620#64 14780694332 a0' 3 → Disjoint 0x78040620#64 14780694332 a1' 12 →
      (∀ (t : MachineState) (cap ptr : Word) (J Bv : List Word), t.pc = 0x780212ac#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x260#64, 76), (a0', 3), (a1', 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        J.length = 12 → Region a0' [cap, ptr, 510#64] t → cap ≠ 0#64 → Region a1' J t →
        Bv.length = 65 →
        (∀ o, o < 510 → byteAt Bv o = bw (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3]) o)) →
        Region ptr Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 65 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → SafeN G n P t) → SafeN G n P u)
    (hdealloc : ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word), C.length = 65 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780215d8#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap →
      u.getReg .x12 = 1#64 → Region ptr C u → 0x78048980 ≤ ptr.toNat →
      ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      (∀ t, t.pc = 0x780215d8#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → SafeN G n P t) → SafeN G n P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0xaa0#64, 340), (out, 5), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (extractPBottomW
        (ivkFlag qIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65))
        (ivkW qIvkW rIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65)
          [k0, k1, k2, k3]) ++
        [replaceByte O[4]! 0
          (ivkFlag qIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65))]) t →
      mulFacts rIvkW [k0, k1, k2, k3] →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
      Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → SafeN G n P t) :
    SafeN G n P s :=
  commit_ivk_spec s ra sp out ak nk rivk a0 a1 a2 a3 n0 n1 n2 n3 k0 k1 k2 k3 O J hOl hJl tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx IV G0 G1 G2 G3 hIVl hG0l hG1l hG2l hG3l hTB hIVr hG0 hG1 hG2 hG3 hok_iptr hok_g0 hok_g1 hok_g2 hok_g3 hlo_iptr hlo_g0 hlo_g1 hlo_g2 hlo_g3 hhi_iptr hhi_g0 hhi_g1 hhi_g2 hhi_g3 hbelow_out hbelow_rivk hbelow_ak hbelow_nk hpaf hpanic hunwrap hbounds hpc hcode hcodeCD hcodeLB hcodeCm hcodeEB hcodeC hcodeTA hcodeI hcodeM hcodeBB hcodeCo hcodeP hcodeRp hcodeL hcodeIA hcodeCmp hcodeAA hcodeLR hcodeAdd hcodeU hcodeR hcodeXY hcodeOC hcodeFR hcodeTC hcodeF hcodeBt hcodeS hcodeCS hcodeB hcodeW hcodeMul hcodeRq hcodeA hcodeDbl hcodeD hcodeAF hcodeAFI hcodeEA hcodeED hcw hro hra hra1 hsp hstk ha0 ha1 ha2 ha3 hA hokA hN hokN hK hokK hO hokO hJ hd0 hd1 hd2 hd3 he0 he1 he2 hh0 hh1 (fun u sp' a0' a1' j O1 => hfrom u sp' a0' a1' j O1 sp J a0 a1 a2 a3 n0 n1 n2 n3) hdealloc hk

/-- `commit_ivk_spec'` with the output cells named: `ivk`'s four limbs and the flag cell, each
with its model equation, so the executor never sizes `extractPBottomW` (an `if` over the
affine point). -/
theorem commit_ivk_spec'' {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out ak nk rivk : Word)
    (a0 a1 a2 a3 n0 n1 n2 n3 k0 k1 k2 k3 : Word)
    (O J : List Word) (hOl : O.length = 5) (hJl : J.length = 9)
    -- the sqrt/generator tables (`FP_TABLES`) in the heap, carried through: the allocator
    -- contracts below keep them (the allocator never writes a live block)
    (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word)
    (hIVl : IV.length = 138) (hG0l : G0.length = 1024) (hG1l : G1.length = 1024)
    (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hTB : Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] s)
    (hIVr : Region iptr IV s) (hG0 : Region tg0 G0 s) (hG1 : Region tg1 G1 s)
    (hG2 : Region tg2 G2 s) (hG3 : Region tg3 G3 s)
    (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024)
    (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024)
    (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516)
    (hlo_iptr : 0x78048980 ≤ iptr.toNat) (hlo_g0 : 0x78048980 ≤ tg0.toNat) (hlo_g1 : 0x78048980 ≤ tg1.toNat)
    (hlo_g2 : 0x78048980 ≤ tg2.toNat) (hlo_g3 : 0x78048980 ≤ tg3.toNat)
    (hhi_iptr : iptr.toNat + 8 * 138 ≤ 0x1c00000000)
    (hhi_g0 : tg0.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g1 : tg1.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g2 : tg2.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g3 : tg3.toNat + 8 * 516 ≤ 0x1c00000000)
    -- the caller's blocks lie below the heap (on its stack), so off the tables
    (hbelow_out : out.toNat + 8 * 5 ≤ 0x78040620)
    (hbelow_rivk : rivk.toNat + 8 * 4 ≤ 0x78040620)
    (hbelow_ak : ak.toNat + 8 * 4 ≤ 0x78040620)
    (hbelow_nk : nk.toNat + 8 * 4 ≤ 0x78040620)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → SafeN G n P u)
    (hpanic : ∀ u : MachineState, u.pc = 0x7803de40#64 → u.code = s.code → SafeN G n P u)
    (hunwrap : ∀ u : MachineState, u.pc = 0x7803dc7c#64 → u.code = s.code → SafeN G n P u)
    (hbounds : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → SafeN G n P u)
    (hpc : s.pc = 0x780203dc#64) (hcode : CodeAt F_780203dc.base F_780203dc.prog s)
    -- callees: cached_commit_domain (+ from_raw, from_xy, is_on_curve, mulmod, black_box,
    -- to_curve), to_le_bits (+ to_repr), commit (`0x78021238`) and its callees,
    -- extract_p_bottom (+ memset, conditional_select, to_affine, coordinates)
    (hcodeCD : CodeAt F_78020548.base F_78020548.prog s) (hcodeLB : CodeAt F_78029b18.base F_78029b18.prog s)
    (hcodeCm : CodeAt F_78021238.base F_78021238.prog s) (hcodeEB : CodeAt F_7802340c.base F_7802340c.prog s)
    (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s) (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeBB : CodeAt F_7803a0fc.base F_7803a0fc.prog s) (hcodeCo : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeP : CodeAt F_780237dc.base F_780237dc.prog s) (hcodeRp : CodeAt F_78029468.base F_78029468.prog s)
    (hcodeL : CodeAt F_780234cc.base F_780234cc.prog s) (hcodeIA : CodeAt F_780235e8.base F_780235e8.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s) (hcodeAA : CodeAt F_78035f88.base F_78035f88.prog s)
    (hcodeLR : CodeAt F_780360e0.base F_780360e0.prog s) (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcodeU : CodeAt F_78023864.base F_78023864.prog s) (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeXY : CodeAt F_78026878.base F_78026878.prog s) (hcodeOC : CodeAt F_78026258.base F_78026258.prog s)
    (hcodeFR : CodeAt F_78028298.base F_78028298.prog s) (hcodeTC : CodeAt F_78025854.base F_78025854.prog s)
    (hcodeF : CodeAt F_780239bc.base F_780239bc.prog s) (hcodeBt : CodeAt F_78023544.base F_78023544.prog s)
    (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcodeCS : CodeAt F_78023d7c.base F_78023d7c.prog s)
    (hcodeB : CodeAt F_78023594.base F_78023594.prog s) (hcodeW : CodeAt F_7802827c.base F_7802827c.prog s)
    (hcodeMul : CodeAt F_78031be8.base F_78031be8.prog s) (hcodeRq : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    (hcodeA : CodeAt F_78035fe0.base F_78035fe0.prog s) (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcodeD : CodeAt F_780360c8.base F_780360c8.prog s) (hcodeAF : CodeAt F_7803a110.base F_7803a110.prog s)
    (hcodeAFI : CodeAt F_7803dd28.base F_7803dd28.prog s) (hcodeEA : CodeAt F_78026b44.base F_78026b44.prog s)
    (hcodeED : CodeAt F_7802413c.base F_7802413c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0xaa0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = ak) (ha2 : s.getReg .x12 = nk)
    (ha3 : s.getReg .x13 = rivk)
    (hA : Region ak [a0, a1, a2, a3] s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi ak 4)
    (hN : Region nk [n0, n1, n2, n3] s) (hokN : RegionOk Ro.layout.roBase Ro.layout.textHi nk 4)
    (hK : Region rivk [k0, k1, k2, k3] s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi rivk 4)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 5)
    -- the frame's iterator block before the call: the struct's padding bytes keep these
    (hJ : Region (sp - 0xaa0#64 + 0x980#64) J s)
    (hd0 : Disjoint (sp - 0xaa0#64) 340 out 5) (hd1 : Disjoint (sp - 0xaa0#64) 340 ak 4)
    (hd2 : Disjoint (sp - 0xaa0#64) 340 nk 4) (hd3 : Disjoint (sp - 0xaa0#64) 340 rivk 4)
    (he0 : Disjoint out 5 ak 4) (he1 : Disjoint out 5 nk 4) (he2 : Disjoint out 5 rivk 4)
    (hh0 : Disjoint 0x78040620#64 14780694332 out 5) (hh1 : Disjoint 0x78040620#64 14780694332 rivk 4)
    -- `Vec<bool>::from_iter` of the padded bit iterator (ledger T2): the iterator block as
    -- `commit_ivk` builds it over the message words at `+0x9c8` (`ak`'s bits, then `nk`'s)
    -- yields 510 bytes, byte `o` the message bit `o`
    (hfrom : ∀ (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word) (sp0 : Word)
      (J0 : List Word) (a0 a1 a2 a3 n0 n1 n2 n3 : Word), O1.length = 3 →
      u.pc = 0x7801e110#64 → u.code = s.code → u.getReg .x1 = 0x780212ac#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x260 sp' → u.getReg .x10 = a0' → u.getReg .x11 = a1' →
      Region a0' O1 u → Region a1' [0#64, j] u →
      Region (a1' + 0x10#64) (iterIvkW sp0 J0) u →
      Region (a1' + 0x58#64) [0#64] u →
      Region (sp0 - 0xaa0#64 + 0x9c8#64) (ivkMsgW [a0, a1, a2, a3] [n0, n1, n2, n3]) u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 3 → RegionOk Ro.layout.roBase Ro.layout.textHi a1' 12 →
      Disjoint (sp' - 0x260#64) 76 a0' 3 → Disjoint (sp' - 0x260#64) 76 a1' 12 →
      Disjoint a0' 3 a1' 12 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      IV.length = 138 → G0.length = 1024 → G1.length = 1024 → G2.length = 1024 → G3.length = 516 →
      0x78048980 ≤ iptr.toNat → iptr.toNat + 8 * 138 ≤ 0x1c00000000 →
      0x78048980 ≤ tg0.toNat → tg0.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg1.toNat → tg1.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg2.toNat → tg2.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg3.toNat → tg3.toNat + 8 * 516 ≤ 0x1c00000000 →
      RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 → RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 →
      StackOk Ro.layout 0xaa0 sp0 →
      Disjoint (sp' - 0x260#64) 76 (sp0 - 0xaa0#64 + 0x9c8#64) 8 → Disjoint a0' 3 (sp0 - 0xaa0#64 + 0x9c8#64) 8 → Disjoint a1' 12 (sp0 - 0xaa0#64 + 0x9c8#64) 8 →
      Disjoint 0x78040620#64 14780694332 a0' 3 → Disjoint 0x78040620#64 14780694332 a1' 12 →
      (∀ (t : MachineState) (cap ptr : Word) (J Bv : List Word), t.pc = 0x780212ac#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x260#64, 76), (a0', 3), (a1', 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        J.length = 12 → Region a0' [cap, ptr, 510#64] t → cap ≠ 0#64 → Region a1' J t →
        Bv.length = 65 →
        (∀ o, o < 510 → byteAt Bv o = bw (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3]) o)) →
        Region ptr Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 65 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → SafeN G n P t) → SafeN G n P u)
    (hdealloc : ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word), C.length = 65 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780215d8#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap →
      u.getReg .x12 = 1#64 → Region ptr C u → 0x78048980 ≤ ptr.toNat →
      ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      (∀ t, t.pc = 0x780215d8#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → SafeN G n P t) → SafeN G n P u)
    (hk : ∀ (t : MachineState) (j0 j1 j2 j3 fl : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0xaa0#64, 340), (out, 5), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      [j0, j1, j2, j3] = extractPBottomW (ivkFlag qIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65))
        (ivkW qIvkW rIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65)
          [k0, k1, k2, k3]) →
      fl = replaceByte O[4]! 0 (ivkFlag qIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65)) →
      Region out [j0, j1, j2, j3, fl] t → mulFacts rIvkW [k0, k1, k2, k3] →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
      Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → SafeN G n P t) :
    SafeN G n P s :=
  commit_ivk_spec' s ra sp out ak nk rivk a0 a1 a2 a3 n0 n1 n2 n3 k0 k1 k2 k3 O J hOl hJl tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx IV G0 G1 G2 G3 hIVl hG0l hG1l hG2l hG3l hTB hIVr hG0 hG1 hG2 hG3 hok_iptr hok_g0 hok_g1 hok_g2 hok_g3 hlo_iptr hlo_g0 hlo_g1 hlo_g2 hlo_g3 hhi_iptr hhi_g0 hhi_g1 hhi_g2 hhi_g3 hbelow_out hbelow_rivk hbelow_ak hbelow_nk hpaf hpanic hunwrap hbounds hpc hcode hcodeCD hcodeLB hcodeCm hcodeEB hcodeC hcodeTA hcodeI hcodeM hcodeBB hcodeCo hcodeP hcodeRp hcodeL hcodeIA hcodeCmp hcodeAA hcodeLR hcodeAdd hcodeU hcodeR hcodeXY hcodeOC hcodeFR hcodeTC hcodeF hcodeBt hcodeS hcodeCS hcodeB hcodeW hcodeMul hcodeRq hcodeA hcodeDbl hcodeD hcodeAF hcodeAFI hcodeEA hcodeED hcw hro hra hra1 hsp hstk ha0 ha1 ha2 ha3 hA hokA hN hokN hK hokK hO hokO hJ hd0 hd1 hd2 hd3 he0 he1 he2 hh0 hh1 hfrom hdealloc (fun t h1 h2 h3 h4 hR hm b0 b1 b2 b3 b4 b5 => by
    generalize hL : extractPBottomW (ivkFlag qIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65))
      (ivkW qIvkW rIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65)
          [k0, k1, k2, k3]) = L at hR
    have hl : L.length = 4 := hL ▸ extractPBottomW_length _ _
    match L, hl, hL with
    | [j0, j1, j2, j3], _, hL =>
      exact hk t j0 j1 j2 j3 _ h1 h2 h3 h4 hL.symm rfl (by simpa using hR) hm b0 b1 b2 b3 b4 b5)

/-- `nonzero_scalar_spec` with the output cells named (`nzScalarW` is an `if` on canonicity). -/
theorem nonzero_scalar_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 a1 sp : Word)
    (x0 x1 x2 x3 : Word) (O : List Word) (hOl : O.length = 5)
    (hpc : s.pc = 0x7802018c#64) (hcode : CodeAt F_7802018c.base F_7802018c.prog s)
    (hcodeR : CodeAt F_7802ed10.base F_7802ed10.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeE : CodeAt F_7802e8ec.base F_7802e8ec.prog s)
    (hcodeZ : CodeAt F_780232f4.base F_780232f4.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x150 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a1 [x0, x1, x2, x3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5) (hd : Disjoint a0 5 a1 4)
    (hd0 : Disjoint (sp - 0x150#64) 42 a0 5) (hd1 : Disjoint (sp - 0x150#64) 42 a1 4)
    (hk : ∀ (t : MachineState) (i0 i1 i2 i3 fl : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x150#64, 42), (a0, 5)] s t →
      [i0, i1, i2, i3] = nzScalarW (leLimbsToNat [x0, x1, x2, x3]) → fl = replaceByte O[4]! 0 (nzScalarFlag (leLimbsToNat [x0, x1, x2, x3])) →
      Region a0 [i0, i1, i2, i3, fl] t → SafeN G n P t) :
    SafeN G n P s :=
  nonzero_scalar_spec s ra a0 a1 sp x0 x1 x2 x3 O hOl hpc hcode hcodeR hcodeM hcodeB hcodeE hcodeZ hcw hro hra hra1 hsp hstk ha0 ha1 hx hok1 hO hok0 hd hd0 hd1 (fun t h1 h2 h3 h4 hR => by
    generalize hL : nzScalarW (leLimbsToNat [x0, x1, x2, x3]) = L at hR
    have hl : L.length = 4 := by rw [← hL]; unfold nzScalarW; split <;> rfl
    match L, hl, hL with
    | [i0, i1, i2, i3], _, hL => exact hk t i0 i1 i2 i3 _ h1 h2 h3 h4 hL.symm rfl (by simpa using hR))

/-- The branch on `NonIdentityPallasPoint::from_bytes`'s tag: a non-zero zero-extended tag means
the flag is `1` (it is only ever `0` or `1`). -/
theorem nip_one_of {f : BitVec 8} {a b c d v : Word}
    (h1 : BitVec.zeroExtend 64 (nipFlag f a b c d) = v) (h2 : ¬(v == 0#64) = true) :
    nipFlag f a b c d = 1#8 := by
  unfold nipFlag at h1 ⊢
  split
  · rfl
  · rename_i hc
    rw [if_neg hc] at h1
    subst h1
    exact (h2 (by decide)).elim

end Cases.Zip2005

