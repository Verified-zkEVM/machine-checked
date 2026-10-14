import Cases.Zip2005.Poseidon.PrfNf
import RiscvZkvm.Rv64.Logic.ByteOps
import Cases.Zip2005.Field.FromRawRo
import Cases.Zip2005.Curve.FromXy
import Cases.Zip2005.Curve.ToCurve
import Cases.Zip2005.Field.FpRepr
import Cases.Zip2005.Field.FqFromRepr
import Cases.Zip2005.Curve.EpMulFq
import Cases.Zip2005.Curve.EpAdd
import Cases.Zip2005.Curve.ToAffine
import Cases.Zip2005.Field.Coordinates
import Cases.Zip2005.Field.Cells4
import Cases.Zip2005.Image.F_7801f780
import Cases.Zip2005.Image.Ro

/-!
# `orchard::note::nullifier::Nullifier::derive` (`0x7801f780`)

`Extract_ℙ([(PRF^nfOrchard_nk(ρ) + ψ) mod q_P] 𝒦^Orchard + cm)`: the constant `𝒦` from its raw
coordinates in the read-only segment (`from_raw` twice, `from_xy`, the `is_some` assertion,
`to_curve`), `prf_nf`, the inline `Fp::add` of `ψ`, `to_repr` and `Fq::from_repr` (the base-field
value read as a scalar; `q_P < r_P` so the `is_some` assertion holds), `[k] 𝒦` (`mul`), `+ cm`
(`Ep::add`), `to_affine`, `coordinates` and the `x` coordinate masked by `is_some` (the affine
identity is `(0, 0)`, so the result is `x` in every case).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-! ## The mul result's canonical coordinates -/

/-- The first four cells of `natToLeLimbs 4 A ++ rest` decode to `A`. -/
theorem leLimbsToNat_head4 (A : Nat) (hA : A < 2 ^ 256) (rest : List Word) :
    leLimbsToNat [(natToLeLimbs 4 A ++ rest)[0]!, (natToLeLimbs 4 A ++ rest)[1]!,
      (natToLeLimbs 4 A ++ rest)[2]!, (natToLeLimbs 4 A ++ rest)[3]!] = A := by
  have h := leLimbsToNat_natToLeLimbs 4 A hA
  simp only [natToLeLimbs_succ, natToLeLimbs_zero, List.cons_append, List.nil_append,
    List.getElem!_cons_zero, List.getElem!_cons_succ] at h ⊢
  exact h

theorem mulW_X_lt (pt k : List Word) :
    leLimbsToNat [(mulW pt k)[0]!, (mulW pt k)[1]!, (mulW pt k)[2]!, (mulW pt k)[3]!] < Fp.p := by
  unfold mulW
  split_ifs
  · decide
  · decide
  · rw [List.append_assoc, leLimbsToNat_head4 _ (lt_trans (Fp.mul_lt _ _) Fp.p_lt)]
    exact Fp.mul_lt _ _

theorem mulW_Z_lt (pt k : List Word) :
    leLimbsToNat [(mulW pt k)[8]!, (mulW pt k)[9]!, (mulW pt k)[10]!, (mulW pt k)[11]!] < Fp.p := by
  unfold mulW
  split_ifs
  · decide
  · decide
  · have h := leLimbsToNat_natToLeLimbs 4 Fp.R (lt_trans Fp.R_lt Fp.p_lt)
    simp only [natToLeLimbs_succ, natToLeLimbs_zero, List.cons_append, List.nil_append,
      List.getElem!_cons_zero, List.getElem!_cons_succ] at h ⊢
    rw [h]; exact Fp.R_lt

/-- A region off the image is disjoint from any read-only block. -/
theorem Disjoint.of_ro {b : Word} {n : Nat} (h : RegionOk Ro.layout.roBase Ro.layout.textHi b n) {a : Word} {m : Nat}
    (ha : Ro.layout.roBase ≤ a.toNat) (ha' : a.toNat + 8 * m ≤ Ro.layout.textHi) : Disjoint a m b n := by
  have h1 := h.offCode
  have h2 := h.nowrap
  simp only [Ro.layout_roBase, Ro.layout_textHi]at *
  exact ⟨by omega, by omega, h2⟩

/-! ## The model -/

/-- `𝒦^Orchard`'s raw `x` coordinate, the read-only words at `0x78001730`. -/
def kOrchardXRaw : Nat :=
  leLimbsToNat [0xd36f6aa7e447ca75#64, 0x5e7eb192ccb5db9b#64, 0x2e375571faf4c9cf#64, 0x25e7aa169ca8198d#64]

/-- `𝒦^Orchard`'s raw `y` coordinate, the read-only words at `0x780016f0`. -/
def kOrchardYRaw : Nat :=
  leLimbsToNat [0x2db8dce21ae001cc#64, 0x5fe0a49ec1c1b433#64, 0x880473442008ff75#64, 0x155c1f851b1a3384#64]

/-- `𝒦^Orchard` as the guest holds it after `from_raw`, `from_xy` and `to_curve`: Montgomery
coordinates, `Z = R`. -/
def kOrchardW : List Word :=
  natToLeLimbs 4 (Fp.mul kOrchardXRaw Fp.R2) ++ natToLeLimbs 4 (Fp.mul kOrchardYRaw Fp.R2) ++
    natToLeLimbs 4 Fp.R

/-- The scalar `(PRF^nfOrchard_nk(ρ) + ψ) mod q_P` as the guest holds it: the Montgomery sum,
taken out of Montgomery form by `to_repr`, read back as a scalar by `Fq::from_repr`
(Montgomery form over `r_P`). -/
def nullifierScalarW (nk rho psi : Nat) : List Word :=
  natToLeLimbs 4 (Fq.mul (Fp.add (Poseidon.hash2 nk rho) psi * Fp.rInv % Fp.p) Fq.R2)

/-- The affine `x` of a Jacobian triple. Kept behind a definition: `whnfCore` reduces a
projection of a computed structure by unfolding the structure with full delta, which on
`Fp.addJ (… mulW …)` evaluates the 255-step scalar multiplication symbolically (16 GB). -/
def affineX (A : Nat × Nat × Nat) : Nat := (Fp.toAffine A.1 A.2.1 A.2.2).1

theorem affineX_eq (A : Nat × Nat × Nat) : affineX A = (Fp.toAffine A.1 A.2.1 A.2.2).1 := rfl

/-- Folding the projection back: a goal or hypothesis must never carry `(Fp.toAffine …).1`
itself (a `rw` motive or `rfl` on it evaluates the inversion). -/
theorem affineX_cells' (A : Nat × Nat × Nat) : (Fp.toAffine A.1 A.2.1 A.2.2).1 = affineX A :=
  (affineX_eq A).symm

theorem ptX_eq (pt : List Word) : ptX pt = leLimbsToNat [pt[0]!, pt[1]!, pt[2]!, pt[3]!] := rfl
theorem ptY_eq (pt : List Word) : ptY pt = leLimbsToNat [pt[4]!, pt[5]!, pt[6]!, pt[7]!] := rfl
theorem ptZ_eq (pt : List Word) : ptZ pt = leLimbsToNat [pt[8]!, pt[9]!, pt[10]!, pt[11]!] := rfl

/-- `[k] 𝒦 + cm` in Jacobian coordinates (no `let`s: see `affineX`; the point's limbs behind
`ptX` … so that no `getElem!` on the computed point is exposed to the executor). -/
def nullifierJ (nk rho psi : Nat) (cm : List Word) : Nat × Nat × Nat :=
  Fp.addJ (ptX (mulW kOrchardW (nullifierScalarW nk rho psi))) (ptY (mulW kOrchardW (nullifierScalarW nk rho psi))) (ptZ (mulW kOrchardW (nullifierScalarW nk rho psi))) (ptX cm) (ptY cm) (ptZ cm)

theorem nullifierJ_eq (nk rho psi : Nat) (cm : List Word) : nullifierJ nk rho psi cm =
    Fp.addJ (ptX (mulW kOrchardW (nullifierScalarW nk rho psi))) (ptY (mulW kOrchardW (nullifierScalarW nk rho psi))) (ptZ (mulW kOrchardW (nullifierScalarW nk rho psi))) (ptX cm) (ptY cm) (ptZ cm) := rfl

/-- The nullifier's `x` coordinate: `[k] 𝒦 + cm` in Jacobian coordinates, then affine. -/
def nullifierX (nk rho psi : Nat) (cm : List Word) : Nat := affineX (nullifierJ nk rho psi cm)

theorem nullifierX_eq (nk rho psi : Nat) (cm : List Word) :
    nullifierX nk rho psi cm = affineX (nullifierJ nk rho psi cm) := rfl

/-! ## Glue -/

theorem Poseidon.row_lt (i : Nat) (y : Poseidon.St) : Poseidon.row i y < Fp.p := Fp.add_lt _ _

theorem Poseidon.hash2_lt (a b : Nat) : Poseidon.hash2 a b < Fp.p := by
  unfold Poseidon.hash2 Poseidon.permute
  show (Poseidon.round 63 _).1 < Fp.p
  unfold Poseidon.round
  split
  · exact Poseidon.row_lt _ _
  · exact Poseidon.row_lt _ _

theorem Fp.dblJ_lt (X Y Z : Nat) :
    (Fp.dblJ X Y Z).1 < 2 ^ 256 ∧ (Fp.dblJ X Y Z).2.1 < 2 ^ 256 ∧ (Fp.dblJ X Y Z).2.2 < 2 ^ 256 := by
  by_cases hZ : Z = 0
  · simp only [Fp.dblJ, hZ, if_true]
    exact ⟨Nat.two_pow_pos _, Nat.two_pow_pos _, Nat.two_pow_pos _⟩
  · simp only [Fp.dblJ, hZ, if_false]
    exact ⟨lt_trans (Fp.sub_lt _ _) Fp.p_lt, lt_trans (Fp.sub_lt _ _) Fp.p_lt,
      lt_trans (Fp.add_lt _ _) Fp.p_lt⟩

theorem Fp.addJ_main_lt (Z1 Z2 z1z1 z2z2 u1 u2 s1 s2 : Nat) :
    (Fp.addJ_main Z1 Z2 z1z1 z2z2 u1 u2 s1 s2).1 < 2 ^ 256 ∧
      (Fp.addJ_main Z1 Z2 z1z1 z2z2 u1 u2 s1 s2).2.1 < 2 ^ 256 ∧
      (Fp.addJ_main Z1 Z2 z1z1 z2z2 u1 u2 s1 s2).2.2 < 2 ^ 256 := by
  simp only [Fp.addJ_main]
  exact ⟨lt_trans (Fp.sub_lt _ _) Fp.p_lt, lt_trans (Fp.sub_lt _ _) Fp.p_lt,
    lt_trans (Fp.mul_lt _ _) Fp.p_lt⟩

/-- Every outcome of `addJ` fits in four limbs when the inputs do. -/
theorem Fp.addJ_lt {X1 Y1 Z1 X2 Y2 Z2 : Nat} (h1 : X1 < 2 ^ 256) (h2 : Y1 < 2 ^ 256) (h3 : Z1 < 2 ^ 256)
    (h4 : X2 < 2 ^ 256) (h5 : Y2 < 2 ^ 256) (h6 : Z2 < 2 ^ 256) :
    (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).1 < 2 ^ 256 ∧ (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.1 < 2 ^ 256 ∧
      (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.2 < 2 ^ 256 := by
  by_cases hZ1 : Z1 = 0
  · rw [Fp.addJ_z1_zero hZ1]; exact ⟨h4, h5, h6⟩
  by_cases hZ2 : Z2 = 0
  · rw [Fp.addJ_z2_zero hZ1 hZ2]; exact ⟨h1, h2, h3⟩
  by_cases hu : Fp.mul X1 (Fp.mul Z2 Z2) = Fp.mul X2 (Fp.mul Z1 Z1)
  · by_cases hs : Fp.mul (Fp.mul Y1 (Fp.mul Z2 Z2)) Z2 = Fp.mul (Fp.mul Y2 (Fp.mul Z1 Z1)) Z1
    · rw [Fp.addJ_double hZ1 hZ2 hu hs]; exact Fp.dblJ_lt _ _ _
    · rw [Fp.addJ_identity hZ1 hZ2 hu hs]
      exact ⟨Nat.two_pow_pos _, Nat.two_pow_pos _, Nat.two_pow_pos _⟩
  · rw [Fp.addJ_general hZ1 hZ2 hu]; exact Fp.addJ_main_lt _ _ _ _ _ _ _ _

/-- `to_affine` reads `Ep::add`'s twelve cells back as the three coordinates. -/
theorem Fp.toAffine_addJ_cells (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 e0 e1 e2 e3
    f0 f1 f2 f3 : Word) :
    Fp.toAffine
      (leLimbsToNat [BitVec.ofNat 64 (Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).1,
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).1 >>> 64),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).1 >>> 128),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).1 >>> 192)])
      (leLimbsToNat [BitVec.ofNat 64 (Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).2.1,
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).2.1 >>> 64),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).2.1 >>> 128),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).2.1 >>> 192)])
      (leLimbsToNat [BitVec.ofNat 64 (Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).2.2,
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).2.2 >>> 64),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).2.2 >>> 128),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).2.2 >>> 192)]) =
    Fp.toAffine (Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).1
      (Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).2.1
      (Fp.addJ (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [b0, b1, b2, b3])
          (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [d0, d1, d2, d3]) (leLimbsToNat [e0, e1, e2, e3])
          (leLimbsToNat [f0, f1, f2, f3])).2.2 := by
  have h := Fp.addJ_lt (leLimbsToNat4_lt a0 a1 a2 a3) (leLimbsToNat4_lt b0 b1 b2 b3)
    (leLimbsToNat4_lt c0 c1 c2 c3) (leLimbsToNat4_lt d0 d1 d2 d3) (leLimbsToNat4_lt e0 e1 e2 e3)
    (leLimbsToNat4_lt f0 f1 f2 f3)
  rw [cells4_decode _ h.1, cells4_decode _ h.2.1, cells4_decode _ h.2.2]

/-- `𝒦`'s Montgomery `x` has a non-zero low limb, so `to_curve` gives `Z = R`. -/
theorem kOrchard_x0_ne : BitVec.ofNat 64 (Fp.mul kOrchardXRaw Fp.R2 >>> 0) ≠ 0#64 := by
  decide +kernel

theorem kOrchard_cells {v50 v51 v52 v53 v42 v43 v44 v45 : Word}
    (h50 : BitVec.ofNat 64 (Fp.mul kOrchardXRaw Fp.R2 >>> 0) = v50)
    (h51 : BitVec.ofNat 64 (Fp.mul kOrchardXRaw Fp.R2 >>> 64) = v51)
    (h52 : BitVec.ofNat 64 (Fp.mul kOrchardXRaw Fp.R2 >>> 128) = v52)
    (h53 : BitVec.ofNat 64 (Fp.mul kOrchardXRaw Fp.R2 >>> 192) = v53)
    (h42 : BitVec.ofNat 64 (Fp.mul kOrchardYRaw Fp.R2 >>> 0) = v42)
    (h43 : BitVec.ofNat 64 (Fp.mul kOrchardYRaw Fp.R2 >>> 64) = v43)
    (h44 : BitVec.ofNat 64 (Fp.mul kOrchardYRaw Fp.R2 >>> 128) = v44)
    (h45 : BitVec.ofNat 64 (Fp.mul kOrchardYRaw Fp.R2 >>> 192) = v45) :
    [v50, v51, v52, v53, v42, v43, v44, v45,
      BitVec.ofNat 64 ((if v50 = 0#64 ∧ v51 = 0#64 ∧ v52 = 0#64 ∧ v53 = 0#64 ∧ v42 = 0#64 ∧ v43 = 0#64 ∧
          v44 = 0#64 ∧ v45 = 0#64 then 0 else Fp.R) >>> (64 * 0)),
      BitVec.ofNat 64 ((if v50 = 0#64 ∧ v51 = 0#64 ∧ v52 = 0#64 ∧ v53 = 0#64 ∧ v42 = 0#64 ∧ v43 = 0#64 ∧
          v44 = 0#64 ∧ v45 = 0#64 then 0 else Fp.R) >>> (64 * 1)),
      BitVec.ofNat 64 ((if v50 = 0#64 ∧ v51 = 0#64 ∧ v52 = 0#64 ∧ v53 = 0#64 ∧ v42 = 0#64 ∧ v43 = 0#64 ∧
          v44 = 0#64 ∧ v45 = 0#64 then 0 else Fp.R) >>> (64 * 2)),
      BitVec.ofNat 64 ((if v50 = 0#64 ∧ v51 = 0#64 ∧ v52 = 0#64 ∧ v53 = 0#64 ∧ v42 = 0#64 ∧ v43 = 0#64 ∧
          v44 = 0#64 ∧ v45 = 0#64 then 0 else Fp.R) >>> (64 * 3))] = kOrchardW := by
  have hne : ¬ (v50 = 0#64 ∧ v51 = 0#64 ∧ v52 = 0#64 ∧ v53 = 0#64 ∧ v42 = 0#64 ∧ v43 = 0#64 ∧
      v44 = 0#64 ∧ v45 = 0#64) := fun h => kOrchard_x0_ne (h50.trans h.1)
  subst h50 h51 h52 h53 h42 h43 h44 h45
  simp only [Nat.shiftRight_zero] at hne ⊢
  simp only [hne, if_false, kOrchardW, natToLeLimbs_cells4, List.cons_append, List.nil_append,
    Nat.reduceMul, Nat.shiftRight_zero]


/-- `to_affine` reads twelve cells back as the three coordinates (an opaque triple). -/
theorem Fp.toAffine_cells (A : Nat × Nat × Nat) (h : A.1 < 2 ^ 256 ∧ A.2.1 < 2 ^ 256 ∧ A.2.2 < 2 ^ 256) :
    Fp.toAffine
      (leLimbsToNat [BitVec.ofNat 64 A.1, BitVec.ofNat 64 (A.1 >>> 64), BitVec.ofNat 64 (A.1 >>> 128),
        BitVec.ofNat 64 (A.1 >>> 192)])
      (leLimbsToNat [BitVec.ofNat 64 A.2.1, BitVec.ofNat 64 (A.2.1 >>> 64), BitVec.ofNat 64 (A.2.1 >>> 128),
        BitVec.ofNat 64 (A.2.1 >>> 192)])
      (leLimbsToNat [BitVec.ofNat 64 A.2.2, BitVec.ofNat 64 (A.2.2 >>> 64), BitVec.ofNat 64 (A.2.2 >>> 128),
        BitVec.ofNat 64 (A.2.2 >>> 192)]) = Fp.toAffine A.1 A.2.1 A.2.2 := by
  rw [cells4_decode _ h.1, cells4_decode _ h.2.1, cells4_decode _ h.2.2]

/-! ## Cells of a twelve-word literal, as propositional rewrites

`simp only [List.getElem!_cons_zero, …] at h` rewrites *definitionally*; the kernel then checks
the old and new statements convertible, and on a statement with `(Fp.toAffine …).1` over cells
`ofNat (A.2.2 >>> 192)` that check evaluates the shift (`Nat.div` unfolding, 16 GB). `rw` with
these leaves only syntactic motives. -/

theorem list12_get_0 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11][0]! = x0 := rfl
theorem list12_get_1 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11][1]! = x1 := rfl
theorem list12_get_2 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11][2]! = x2 := rfl
theorem list12_get_3 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11][3]! = x3 := rfl
theorem list12_get_4 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11][4]! = x4 := rfl
theorem list12_get_5 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11][5]! = x5 := rfl
theorem list12_get_6 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11][6]! = x6 := rfl
theorem list12_get_7 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11][7]! = x7 := rfl
theorem list12_get_8 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11][8]! = x8 := rfl
theorem list12_get_9 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11][9]! = x9 := rfl
theorem list12_get_10 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11][10]! = x10 := rfl
theorem list12_get_11 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11][11]! = x11 := rfl

theorem list4_ext {a0 a1 a2 a3 b0 b1 b2 b3 : Word} (h0 : a0 = b0) (h1 : a1 = b1) (h2 : a2 = b2) (h3 : a3 = b3) :
    [a0, a1, a2, a3] = [b0, b1, b2, b3] := by rw [h0, h1, h2, h3]

/-- The `x` coordinate masked by `is_some`: the affine identity is `(0, 0)`, so the mask changes
nothing. -/
theorem mask_cells (x0 x1 x2 x3 : Word) (c : Prop) [Decidable c]
    (hc : c → x0 = 0#64 ∧ x1 = 0#64 ∧ x2 = 0#64 ∧ x3 = 0#64) (o m : Word)
    (hm : m = -BitVec.zeroExtend 64 (extractByte (replaceByte o 0 (if c then 0#8 else 1#8)) 0)) :
    [x0 &&& m, x1 &&& m, x2 &&& m, x3 &&& m] = [x0, x1, x2, x3] := by
  have e := extractByte_replaceByte_same o 0 (if c then 0#8 else 1#8)
  simp only [Fin.val_zero] at e
  subst hm
  simp only [e, mask_flag]
  by_cases h : c
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hc h
    simp only [ite_self]
  · simp only [h, if_false]

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
theorem nullifier_derive_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out nk rho psi cm : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 q0 q1 q2 q3 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : Word)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → SafeN G n P u)
    (hpanic : ∀ u : MachineState, u.pc = 0x7803de40#64 → u.code = s.code → SafeN G n P u)
    (hpc : s.pc = 0x7801f780#64) (hcode : CodeAt F_7801f780.base F_7801f780.prog s)
    -- callees: from_raw, from_xy (+ is_on_curve, mulmod, black_box), to_curve, prf_nf and its
    -- callees, to_repr, Fq::from_repr, mul and its callees, memcpy, Ep::add (+ double), to_affine
    -- (+ invert), coordinates
    (hcodeR : CodeAt F_78028298.base F_78028298.prog s) (hcodeXY : CodeAt F_78026878.base F_78026878.prog s)
    (hcodeOC : CodeAt F_78026258.base F_78026258.prog s) (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeBB : CodeAt F_7803a0fc.base F_7803a0fc.prog s) (hcodeTC : CodeAt F_78025854.base F_78025854.prog s)
    (hcodeN : CodeAt F_780207e8.base F_780207e8.prog s) (hcodeU : CodeAt F_78029ae8.base F_78029ae8.prog s)
    (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeG : CodeAt F_7801e26c.base F_7801e26c.prog s)
    (hcodeF : CodeAt F_7801f120.base F_7801f120.prog s) (hcodeP : CodeAt F_7801ed68.base F_7801ed68.prog s)
    (hcodeX : CodeAt F_7801e704.base F_7801e704.prog s) (hcodeB : CodeAt F_78023a18.base F_78023a18.prog s)
    (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcodeRp : CodeAt F_78029468.base F_78029468.prog s)
    (hcodeRq : CodeAt F_7802ed10.base F_7802ed10.prog s) (hcodeW : CodeAt F_7802827c.base F_7802827c.prog s)
    (hcodeMul : CodeAt F_78031be8.base F_78031be8.prog s) (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s) (hcodeCo : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeRq2 : CodeAt F_7802e9b8.base F_7802e9b8.prog s) (hcodeA : CodeAt F_78035fe0.base F_78035fe0.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s) (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s) (hcodeD : CodeAt F_780360c8.base F_780360c8.prog s)
    (hcodeL : CodeAt F_780360e0.base F_780360e0.prog s) (hcodeAF : CodeAt F_7803a110.base F_7803a110.prog s)
    (hcodeAFI : CodeAt F_7803dd28.base F_7803dd28.prog s) (hcodeEA : CodeAt F_78026b44.base F_78026b44.prog s)
    (hcodeED : CodeAt F_7802413c.base F_7802413c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0xb40 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = nk) (ha2 : s.getReg .x12 = rho)
    (ha3 : s.getReg .x13 = psi) (ha4 : s.getReg .x14 = cm)
    (hN : Region nk [n0, n1, n2, n3] s) (hokN : RegionOk Ro.layout.textLo Ro.layout.textHi nk 4)
    (hR : Region rho [r0, r1, r2, r3] s) (hokR : RegionOk Ro.layout.textLo Ro.layout.textHi rho 4)
    (hQ : Region psi [q0, q1, q2, q3] s) (hokQ : RegionOk Ro.layout.textLo Ro.layout.textHi psi 4)
    (hCm : Region cm [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] s) (hokCm : RegionOk Ro.layout.textLo Ro.layout.textHi cm 12)
    (hnl : leLimbsToNat [n0, n1, n2, n3] < Fp.p) (hrl : leLimbsToNat [r0, r1, r2, r3] < Fp.p)
    (hql : leLimbsToNat [q0, q1, q2, q3] < Fp.p) (hcz : leLimbsToNat [c8, c9, c10, c11] < Fp.p)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd0 : Disjoint (sp - 0xb40#64) 360 nk 4) (hd1 : Disjoint (sp - 0xb40#64) 360 rho 4)
    (hd2 : Disjoint (sp - 0xb40#64) 360 psi 4) (hd3 : Disjoint (sp - 0xb40#64) 360 cm 12)
    (hd4 : Disjoint (sp - 0xb40#64) 360 out 4)
    (he0 : Disjoint out 4 nk 4) (he1 : Disjoint out 4 rho 4) (he2 : Disjoint out 4 psi 4)
    (he3 : Disjoint out 4 cm 12)
    (hh0 : Disjoint 0x78040620#64 14780694332 nk 4) (hh1 : Disjoint 0x78040620#64 14780694332 rho 4)
    (hh2 : Disjoint 0x78040620#64 14780694332 psi 4) (hh3 : Disjoint 0x78040620#64 14780694332 cm 12)
    (hh4 : Disjoint 0x78040620#64 14780694332 out 4)
    -- the allocator contracts `prf_nf` needs (ledger T2)
    (hconst : ∀ (u : MachineState) (sp' a0' : Word) (O1 O2 O3 : List Word),
      O1.length = 3 → O2.length = 36 → O3.length = 36 →
      u.pc = 0x78023cbc#64 → u.code = s.code → u.getReg .x1 = 0x7802084c#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x60 sp' → u.getReg .x10 = a0' →
      Region a0' O1 u → Region (a0' + 0x18#64) O2 u → Region (a0' + 0x138#64) O3 u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 75 → Disjoint (sp' - 0x60#64) 12 a0' 75 →
      RoImage Ro.layout u → Disjoint 0x78040620#64 14780694332 a0' 75 →
      (∀ t, t.pc = 0x7802084c#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x60#64, 12), (a0', 75), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        ∀ (ptr : Word) (MI : List Word), MI.length = 36 →
        Region a0' [64#64, ptr, 64#64] t → Region (a0' + 0x18#64) Poseidon.mdsWords t →
        Region (a0' + 0x138#64) MI t →
        Region ptr Poseidon.rcWords t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 768 → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 768 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 → SafeN G n P t) → SafeN G n P u)
    (hdealloc : ∀ (u : MachineState) (sp' ptr : Word) (C : List Word), C.length = 768 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x78020c64#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = 6144#64 →
      u.getReg .x12 = 8#64 → Region ptr C u → 0x78048980 ≤ ptr.toNat →
      ptr.toNat + 8 * 768 ≤ 0x1c00000000 →
      (∀ t, t.pc = 0x78020c64#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → SafeN G n P t) → SafeN G n P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0xb40#64, 360), (out, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (natToLeLimbs 4 (nullifierX (leLimbsToNat [n0, n1, n2, n3])
        (leLimbsToNat [r0, r1, r2, r3]) (leLimbsToNat [q0, q1, q2, q3])
        [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11])) t →
      mulFacts kOrchardW (nullifierScalarW (leLimbsToNat [n0, n1, n2, n3])
        (leLimbsToNat [r0, r1, r2, r3]) (leLimbsToNat [q0, q1, q2, q3])) →
      SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb40#64) 360 := hstk.frame 360 (by decide)
  -- the frame (below it 0x9b0 bytes for the callees' frames): one cell, [0x8, 0x68), [0x68, 0xe8),
  -- [0xe8, 0x150), the save area
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb40#64 + 0x9b0#64) 1 := hokW.sub' 310 1 (by decide) (by bv_omega)
  have hokB : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb40#64 + 0x9b8#64) 12 := hokW.sub' 311 12 (by decide) (by bv_omega)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb40#64 + 0xa18#64) 16 := hokW.sub' 323 16 (by decide) (by bv_omega)
  have hokD : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb40#64 + 0xa98#64) 13 := hokW.sub' 339 13 (by decide) (by bv_omega)
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb40#64 + 0xb00#64) 8 := hokW.sub' 352 8 (by decide) (by bv_omega)
  obtain ⟨A, hA, hAl⟩ := Region.exists_junk (sp - 0xb40#64 + 0x9b0#64) 1 s
  obtain ⟨B, hB, hBl⟩ := Region.exists_junk (sp - 0xb40#64 + 0x9b8#64) 12 s
  obtain ⟨C, hC, hCl⟩ := Region.exists_junk (sp - 0xb40#64 + 0xa18#64) 16 s
  obtain ⟨D, hD, hDl⟩ := Region.exists_junk (sp - 0xb40#64 + 0xa98#64) 13 s
  obtain ⟨E, hE, hEl⟩ := Region.exists_junk (sp - 0xb40#64 + 0xb00#64) 8 s
  obtain ⟨O, hO, hOl⟩ := Region.exists_junk out 4 s
  -- `𝒦^Orchard`'s raw coordinates in the read-only segment
  have hKx : Region 0x78001730#64 _ s := (hro.get 11 (by decide)).sub 38 4 (by decide) rfl
  have hokKx : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001730#64 4 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 11 (by decide)).sub' 38 4 (by decide) (by decide)
  have hKy : Region 0x780016f0#64 _ s := (hro.get 11 (by decide)).sub 30 4 (by decide) rfl
  have hokKy : RegionOk Ro.layout.textLo Ro.layout.textHi 0x780016f0#64 4 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 11 (by decide)).sub' 30 4 (by decide) (by decide)
  have hokH : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hdKx : Disjoint 0x78001730#64 4 out 4 := Disjoint.of_ro hokO (by decide) (by decide)
  have hdKy : Disjoint 0x780016f0#64 4 out 4 := Disjoint.of_ro hokO (by decide) (by decide)
  have hlo := hstk.lo
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hu := Unchanged.refl [(sp - 0xb40#64, 360), (out, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  sym_exec [fp_from_raw_ro_spec, from_xy_spec, to_curve_spec, prf_nf_spec, fp_to_repr_spec,
    fq_from_repr_spec, ep_mul_fq_spec, memcpy96_spec, hconst, hdealloc, hpaf, hpanic] stop [0x7801fa28]
  -- `[k] 𝒦`'s `X` and `Z` are canonical (`Ep::add` asserts it of its first operand)
  have hmX : leLimbsToNat [acc172_0[0]!, acc172_0[1]!, acc172_0[2]!, acc172_0[3]!] < Fp.p :=
    acc172_0_def ▸ mulW_X_lt _ _
  have hmZ : leLimbsToNat [acc172_0[8]!, acc172_0[9]!, acc172_0[10]!, acc172_0[11]!] < Fp.p :=
    acc172_0_def ▸ mulW_Z_lt _ _
  sym_reframe
  sym_exec [ep_add_spec, to_affine_spec, coordinates_spec', hpaf]
  -- the inline `Fp::add` of `ψ`
  have ch0 := fadd_chain v77_def v78_def v79_def v80_def v81_def v82_def v83_def v84_def v85_def
    v86_def v87_def v88_def v89_def v90_def v96_def v100_def v101_def v102_def v104_def v105_def
    v107_def v108_def v109_def v110_def v111_def v112_def v113_def v114_def v118_def v119_def
    v127_def v128_def v129_def v130_def v131_def v132_def v133_def v134_def v135_def v136_def
    v137_def v139_def v140_def v141_def (by rw [post68_9]; exact Poseidon.hash2_lt _ _) hql
  -- the scalar
  have hacc : acc150_0 = Fp.add (Poseidon.hash2 (leLimbsToNat [n0, n1, n2, n3])
      (leLimbsToNat [r0, r1, r2, r3])) (leLimbsToNat [q0, q1, q2, q3]) * Fp.rInv % Fp.p := by
    rw [← acc150_0_def, ch0, post68_9]
  have hacc_lt : acc150_0 < 2 ^ 256 := by
    rw [← acc150_0_def]; exact lt_trans (Nat.mod_lt _ Fp.p_pos) Fp.p_lt
  have hsc : [v159, v160, v161, v162] = nullifierScalarW (leLimbsToNat [n0, n1, n2, n3])
      (leLimbsToNat [r0, r1, r2, r3]) (leLimbsToNat [q0, q1, q2, q3]) := by
    rw [← v159_def, ← v160_def, ← v161_def, ← v162_def]
    simp only [Nat.shiftRight_zero]
    rw [cells4_decode _ hacc_lt, hacc]
    simp only [nullifierScalarW, natToLeLimbs_cells4]
  -- `𝒦`
  rw [← acc20_0_def] at v50_def v51_def v52_def v53_def
  rw [← acc26_0_def] at v42_def v43_def v44_def v45_def
  have hK := kOrchard_cells v50_def v51_def v52_def v53_def v42_def v43_def v44_def v45_def
  have hmul : acc172_0 = mulW kOrchardW (nullifierScalarW (leLimbsToNat [n0, n1, n2, n3])
      (leLimbsToNat [r0, r1, r2, r3]) (leLimbsToNat [q0, q1, q2, q3])) := by
    rw [← acc172_0_def, hK, hsc]
  -- the masked `x`: the coordinates are the atoms `post15_0 …` (`coordinates_spec'`)
  have hm : [v22, v23, v24, v25] = [post15_0, post15_1, post15_2, post15_3] := by
    rw [← v22_def, ← v23_def, ← v24_def, ← v25_def]
    refine mask_cells post15_0 post15_1 post15_2 post15_3 _ ?_ _ v17
      (v17_def.symm.trans (congrArg Neg.neg v16_def.symm))
    exact fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩
  -- the Jacobian sum as one variable, then the atoms' equations in the model's terms
  generalize hA : Fp.addJ (leLimbsToNat [acc172_0[0]!, acc172_0[1]!, acc172_0[2]!, acc172_0[3]!])
      (leLimbsToNat [acc172_0[4]!, acc172_0[5]!, acc172_0[6]!, acc172_0[7]!])
      (leLimbsToNat [acc172_0[8]!, acc172_0[9]!, acc172_0[10]!, acc172_0[11]!])
      (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [c4, c5, c6, c7])
      (leLimbsToNat [c8, c9, c10, c11]) = A at post15_12 post15_13 post15_14 post15_15
  have hAlt : A.1 < 2 ^ 256 ∧ A.2.1 < 2 ^ 256 ∧ A.2.2 < 2 ^ 256 := by
    rw [← hA]
    exact Fp.addJ_lt (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)
      (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)
  -- the coordinates' cells, by `rw` only (see `list12_get_0`): `64 * k`, `>>> 0`, the twelve
  -- cells, then the point back to `A` and the projection to `affineX A`
  rw [Nat.mul_zero, Nat.mul_one, show (64 : Nat) * 2 = 128 from rfl, show (64 : Nat) * 3 = 192 from rfl]
    at post15_12 post15_13 post15_14 post15_15
  repeat rw [Nat.shiftRight_zero] at post15_12
  repeat rw [Nat.shiftRight_zero] at post15_13
  repeat rw [Nat.shiftRight_zero] at post15_14
  repeat rw [Nat.shiftRight_zero] at post15_15
  rw [list12_get_0, list12_get_1, list12_get_2, list12_get_3, list12_get_4, list12_get_5, list12_get_6,
    list12_get_7, list12_get_8, list12_get_9, list12_get_10, list12_get_11, Fp.toAffine_cells A hAlt,
    affineX_cells'] at post15_12 post15_13 post15_14 post15_15
  have e : [v22, v23, v24, v25] = natToLeLimbs 4 (nullifierX (leLimbsToNat [n0, n1, n2, n3])
      (leLimbsToNat [r0, r1, r2, r3]) (leLimbsToNat [q0, q1, q2, q3])
      [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11]) := by
    -- `← hmul` before the point's accessors: a `getElem!` on the computed point would make the
    -- unifier evaluate the scalar multiplication
    with_reducible rw [hm, natToLeLimbs_cells4, nullifierX_eq, nullifierJ_eq, ← hmul, ptX_eq, ptY_eq, ptZ_eq,
      ptX_eq, ptY_eq, ptZ_eq, list12_get_0, list12_get_1, list12_get_2, list12_get_3, list12_get_4,
      list12_get_5, list12_get_6, list12_get_7, list12_get_8, list12_get_9, list12_get_10, list12_get_11, hA]
    exact list4_ext post15_12.symm post15_13.symm post15_14.symm post15_15.symm
  have hR : Region out (natToLeLimbs 4 (nullifierX (leLimbsToNat [n0, n1, n2, n3])
      (leLimbsToNat [r0, r1, r2, r3]) (leLimbsToNat [q0, q1, q2, q3])
      [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11])) s_40 :=
    Eq.mp (congrArg (fun L => Region out L s_40) e) hR5
  have hM : mulFacts kOrchardW (nullifierScalarW (leLimbsToNat [n0, n1, n2, n3])
      (leLimbsToNat [r0, r1, r2, r3]) (leLimbsToNat [q0, q1, q2, q3])) := by
    with_reducible rw [← hK, ← hsc]
    exact post172_6
  have hcs : s_40.code = s.code := hcode.trans hcode0
  sym_close hk

end Cases.Zip2005
