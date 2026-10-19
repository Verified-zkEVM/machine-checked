import Cases.Zip2005.Main.MainAccept

/-!
# The hashes `main` names are the spec's

The models `main`'s accepting-path predicates carry, as the spec's PRF outputs (Montgomery form):
`psiX_correct` (`H^{ψ,Orchard}`), `rivkIntX_correct` (`H^{rivk,int}`), `rcmRel_correct`
(`H^{rcm,Orchard}`, from `RcmRel` and the points' encodings). The proofs are those of
`psi_correct`, `rivk_internal_correct`, `rcm_v3_correct`, stated over the models alone.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym Cases.Zip2005.B2b

set_option autoImplicit false

/-- `psiX` (`RandomSeed::psi`'s output) is the Montgomery form of `H^{ψ,Orchard}_rseed(ρ)`. -/
theorem psiX_correct (s0 s1 s2 s3 p0 p1 p2 p3 : Word) (ρ : Zcash.Circuits.Fp)
    (hp : leLimbsToNat [p0, p1, p2, p3] = ρ.val * Fp.R % Fp.p) :
    psiX s0 s1 s2 s3 p0 p1 p2 p3 =
      (Zip2005.hPsiOrchard (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat)) ρ).val *
        Fp.R % Fp.p := by
  unfold psiX
  have hpl : ρ.val < Fp.p := ZMod.val_lt ρ
  have eP : leLimbsToNat [p0, p1, p2, p3] * Fp.rInv % Fp.p = ρ.val := by
    rw [hp, Fp.mont_back, Nat.mod_eq_of_lt hpl]
  have eL : ∀ v, (natToLeLimbs 4 v).map BitVec.toNat =
      [(natToLeLimbs 4 v)[0]!.toNat, (natToLeLimbs 4 v)[1]!.toNat, (natToLeLimbs 4 v)[2]!.toNat,
        (natToLeLimbs 4 v)[3]!.toNat] := fun _ => rfl
  have hO := prfExpand65_eq s0 s1 s2 s3 (natToLeLimbs 4 ρ.val)[0]! (natToLeLimbs 4 ρ.val)[1]!
    (natToLeLimbs 4 ρ.val)[2]! (natToLeLimbs 4 ρ.val)[3]! 9#64
  simp only [List.map_cons, List.map_nil] at hO
  rw [eP, Fp.from_uniform_eq, leLimbsToNat_halves _ (compress_length _ _ _ _ _ _)]
  unfold Zip2005.hPsiOrchard Zip2005.rhoBytes
  rw [toBaseOrchard_val, Nat.mod_mul_mod, i2leosp256_limbs _ (by have := Fp.p_lt; omega), eL,
    show Zip2005.Sep.psiOrchard = UInt8.ofNat (9#64).toNat from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [← hO, leos2ip_stateBytes]

/-- `rivkIntX` (`FullViewingKey::rivk(Internal)`'s output) is the Montgomery form of
`H^{rivk,int}(rivk_ext, ak, nk)`. -/
theorem rivkIntX_correct (k0 k1 k2 k3 n0 n1 n2 n3 r0 r1 r2 r3 : Word) (rivkE : Zcash.Circuits.Fq)
    (ak nk : Zcash.Circuits.Fp)
    (hr : leLimbsToNat [r0, r1, r2, r3] = rivkE.val * Fq.R % Fq.q)
    (hn : leLimbsToNat [n0, n1, n2, n3] = nk.val * Fp.R % Fp.p)
    (hak : Zip2005.Blake2b.stateBytes ([k0, k1, k2, k3].map BitVec.toNat) = Zip2005.i2leosp 256 ak.val) :
    rivkIntX k0 k1 k2 k3 n0 n1 n2 n3 r0 r1 r2 r3 =
      (Zip2005.hRivkInt (Zip2005.i2leosp 256 rivkE.val) ak nk).val * Fq.R % Fq.q := by
  unfold rivkIntX
  have hq : rivkE.val < Fq.q := ZMod.val_lt rivkE
  have hp : nk.val < Fp.p := ZMod.val_lt nk
  have eK : leLimbsToNat [r0, r1, r2, r3] * Fq.rInv % Fq.q = rivkE.val := by
    rw [hr, Fq.mont_back, Nat.mod_eq_of_lt hq]
  have eN : leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p = nk.val := by
    rw [hn, Fp.mont_back, Nat.mod_eq_of_lt hp]
  have eL : ∀ v, (natToLeLimbs 4 v).map BitVec.toNat =
      [(natToLeLimbs 4 v)[0]!.toNat, (natToLeLimbs 4 v)[1]!.toNat, (natToLeLimbs 4 v)[2]!.toNat,
        (natToLeLimbs 4 v)[3]!.toNat] := fun _ => rfl
  have hO := prfExpand97_eq (natToLeLimbs 4 rivkE.val)[0]! (natToLeLimbs 4 rivkE.val)[1]!
    (natToLeLimbs 4 rivkE.val)[2]! (natToLeLimbs 4 rivkE.val)[3]! k0 k1 k2 k3
    (natToLeLimbs 4 nk.val)[0]! (natToLeLimbs 4 nk.val)[1]! (natToLeLimbs 4 nk.val)[2]! (natToLeLimbs 4 nk.val)[3]!
    0x83#64
  simp only [List.map_cons, List.map_nil] at hO
  rw [eK, eN, Fq.from_uniform_eq, leLimbsToNat_halves _ (compress_length _ _ _ _ _ _)]
  unfold Zip2005.hRivkInt
  rw [toScalarOrchard_val, Nat.mod_mul_mod, i2leosp256_limbs _ (by have := Fq.q_lt; omega),
    i2leosp256_limbs nk.val (by have := Fp.p_lt; omega), ← hak, eL, eL,
    show Zip2005.Sep.rivkInt = UInt8.ofNat (0x83#64).toNat from rfl]
  simp only [List.map_cons, List.map_nil]
  rw [← hO, leos2ip_stateBytes]

/-- `RcmRel`'s output (`RandomSeed::rcm_v3`) is the Montgomery form of
`H^{rcm,Orchard}_rseed(g★_d, pk★_d, v, ρ, ψ)`, given the points' encodings. -/
theorem rcmRel_correct (e0 e1 e2 e3 r0 r1 r2 r3 q0 q1 q2 q3 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
    k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 v : Word) (x : Nat)
    (gdP pkdP : Zcash.Circuits.Point Zcash.Circuits.Fp) (ρ ψ : Zcash.Circuits.Fp)
    (hgd : Zip2005.Blake2b.stateBytes ((natToLeLimbs 4 (tbX g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11)).map
      BitVec.toNat) = Zip2005.reprP gdP)
    (hpkd : Zip2005.Blake2b.stateBytes ((natToLeLimbs 4 (tbX k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11)).map
      BitVec.toNat) = Zip2005.reprP pkdP)
    (hr : leLimbsToNat [r0, r1, r2, r3] = ρ.val * Fp.R % Fp.p)
    (hq : leLimbsToNat [q0, q1, q2, q3] = ψ.val * Fp.R % Fp.p)
    (h : RcmRel e0 e1 e2 e3 r0 r1 r2 r3 q0 q1 q2 q3 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
      k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 k11 v x) :
    x = (Zip2005.hRcmOrchard (Zip2005.Blake2b.stateBytes ([e0, e1, e2, e3].map BitVec.toNat)) gdP pkdP
      v.toNat ρ ψ).val * Fq.R % Fq.q := by
  obtain ⟨G0, G1, G2, G3, K0, K1, K2, K3, R0, R1, R2, R3, Q0, Q1, Q2, Q3, hG, hK, hR, hQ, hx⟩ := h
  have hpl : ρ.val < Fp.p := ZMod.val_lt ρ
  have hql : ψ.val < Fp.p := ZMod.val_lt ψ
  have eρ : leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p = ρ.val := by
    rw [hr, Fp.mont_back, Nat.mod_eq_of_lt hpl]
  have eψ : leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p = ψ.val := by
    rw [hq, Fp.mont_back, Nat.mod_eq_of_lt hql]
  rw [eρ] at hR
  rw [eψ] at hQ
  have e11 : (11#64 : Word) = BitVec.zeroExtend 64 (BitVec.truncate 8 11#64) := by decide
  rw [hx]
  unfold rcmX
  rw [Fq.from_uniform_eq, leLimbsToNat_halves _ (compress_length _ _ _ _ _ _), e11, ← leos2ip_stateBytes,
    B2b.prfExpand169_eq]
  unfold Zip2005.hRcmOrchard Zip2005.preRcm Zip2005.rhoBytes
  rw [toScalarOrchard_val, Nat.mod_mul_mod, ← hgd, ← hpkd, i2leosp64_word, i2leosp256_limbs _ (by have := Fp.p_lt; omega),
    i2leosp256_limbs ψ.val (by have := Fp.p_lt; omega), hG, hK, hR, hQ,
    show Zip2005.Sep.rcmOrchard = UInt8.ofNat (11#64).toNat from rfl]
  simp only [Zip2005.Blake2b.stateBytes, List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil,
    List.append_assoc, List.append_nil, List.cons_append, List.nil_append]

end Cases.Zip2005
