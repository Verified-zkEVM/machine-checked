import Cases.Zip2005.Bridge.SpecNoteNf
import Cases.Zip2005.Bridge.SpecEncode
import Cases.Zip2005.Bridge.SpecCommitIvk
import Cases.Zip2005.Main.MainAccept
import Cases.Zip2005.Bridge.SpecHashes
import Cases.Zip2005.Orchard.Randomize
import Cases.Zip2005.Bridge.SpecKeys
import Cases.Zip2005.Precompile

/-!
# The accepting segments' facts, read in the spec's vocabulary

Each `acc*_spec` takes what one segment of `main` establishes on its accepting path
(`Cases.Zip2005.MainAccept`) and states it as the corresponding `Zip2005.GuestChecks` conjuncts.
-/

namespace Cases.Zip2005.SpecMul

open RiscvZkvm.Rv64 Cases.Zip2005.Precompile.Pallas
open Zcash.Circuits (Fp Fq Point)

set_option autoImplicit false

theorem reprP_G : Zip2005.reprPNat Zip2005.GOrchard =
    Accel.leLimbsToNat [10167565023098292579#64, 900452621665476876#64, 4291112941855392863#64,
      13210504334354273798#64] := by
  decide +kernel

/-- The spend-authorization basepoint the guest decodes from its read-only bytes is `𝒢^Orchard`. -/
theorem specPt_G (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word)
    (h : Cases.Zip2005.FromBytesPost 10167565023098292579#64 900452621665476876#64 4291112941855392863#64
      13210504334354273798#64 (Accel.leLimbsToNat [x0, x1, x2, x3]) (Accel.leLimbsToNat [y0, y1, y2, y3]) 1#8)
    (hz : Accel.leLimbsToNat [z0, z1, z2, z3] =
      if Accel.leLimbsToNat [x0, x1, x2, x3] = 0 ∧ Accel.leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R) :
    specPt [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] = Zip2005.GOrchard ∧
      Cases.Zip2005.Poseidon.JacW [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] := by
  obtain ⟨hj, hv, hr⟩ := fb_decode _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h hz
  refine ⟨reprPNat_inj hv (Or.inl Zcash.Circuits.Action.orchardBases.spendAuthG.onCurve) ?_, hj⟩
  rw [hr, reprP_G]

end Cases.Zip2005.SpecMul

namespace Cases.Zip2005.Top

open RiscvZkvm.Rv64 Cases.Zip2005.SpecMul Cases.Zip2005.Poseidon
open Zcash.Circuits (Fp Fq Point)

set_option autoImplicit false

/-- A field element's Montgomery limbs read back. -/
theorem D_of_mont {n : ℕ} {a : Fp} (h : n = a.val * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p) : D n = a := by
  rw [← castD, h, Fp.mont_back, Nat.mod_eq_of_lt (show a.val < Cases.Zip2005.Fp.p from ZMod.val_lt a)]
  exact ZMod.natCast_zmod_val a

theorem repr_of_mont {L : List Word} {a : Fp} (h : Accel.leLimbsToNat L = a.val * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p) :
    reprW L = Accel.natToLeLimbs 4 a.val := by
  unfold reprW; rw [h, Fp.mont_back, Nat.mod_eq_of_lt (show a.val < Cases.Zip2005.Fp.p from ZMod.val_lt a)]

theorem nat4_inj {a b : ℕ} (ha : a < 2 ^ 256) (hb : b < 2 ^ 256)
    (h : Accel.natToLeLimbs 4 a = Accel.natToLeLimbs 4 b) : a = b := by
  rw [← Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four ha, ← Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four hb, h]

theorem reprPNat_comm (P : Point Fp) : P.x.val + 2 ^ 255 * Zip2005.ytilde P = Zip2005.reprPNat P := by
  unfold Zip2005.reprPNat; ring

theorem nullifierX_lt (a b c : ℕ) (cm : List Word) : nullifierX a b c cm < 2 ^ 256 := by
  rw [nullifierX_eq, nullifierJ_eq, affineX_eq]
  have hb := Fp.addJ_lt (X1 := ptX (mulW kOrchardW (nullifierScalarW a b c)))
    (Y1 := ptY (mulW kOrchardW (nullifierScalarW a b c))) (Z1 := ptZ (mulW kOrchardW (nullifierScalarW a b c)))
    (X2 := ptX cm) (Y2 := ptY cm) (Z2 := ptZ cm)
    (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)
    (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)
  generalize Fp.addJ (ptX (mulW kOrchardW (nullifierScalarW a b c))) (ptY (mulW kOrchardW (nullifierScalarW a b c)))
    (ptZ (mulW kOrchardW (nullifierScalarW a b c))) (ptX cm) (ptY cm) (ptZ cm) = J at hb ⊢
  exact (toAffine_lt hb.1 hb.2.1).1

/-- **Segment E's accepting-path facts give the spec's note commitment and nullifier.** -/
theorem accE_spec (n r q g p k f : List Word) (v : Word) (nkF ρ ψ : Fp) (gd pkd : Point Fp)
    (hn : Accel.leLimbsToNat n = nkF.val * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p)
    (hr : Accel.leLimbsToNat r = ρ.val * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p)
    (hq : Accel.leLimbsToNat q = ψ.val * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p)
    (hg : g = Accel.natToLeLimbs 4 (Zip2005.reprPNat gd)) (hp : p = Accel.natToLeLimbs 4 (Zip2005.reprPNat pkd))
    (hflag : commitFlag qNoteW (noteMsgW g p v r q) = 1#8) (hfc : Accel.leLimbsToNat f < Cases.Zip2005.Fp.p)
    (hnf : Accel.natToLeLimbs 4 (nullifierX (Accel.leLimbsToNat n) (Accel.leLimbsToNat r) (Accel.leLimbsToNat q)
      (cmSel qNoteW rNoteW (noteMsgW g p v r q) k)) =
        Accel.natToLeLimbs 4 (Cases.Zip2005.Fp.mul (Accel.leLimbsToNat f) Cases.Zip2005.Fp.R2))
    (hm1 : mulFacts rNoteW k)
    (hm2 : mulFacts kOrchardW (nullifierScalarW (Accel.leLimbsToNat n) (Accel.leLimbsToNat r) (Accel.leLimbsToNat q))) :
    ∃ cm : Point Fp, Zip2005.noteCommit ((Accel.leLimbsToNat k * Cases.Zip2005.Fq.rInv % Cases.Zip2005.Fq.q : ℕ) : Fq)
        gd pkd v.toNat ρ ψ = some cm ∧
      ((Accel.leLimbsToNat f : ℕ) : Fp) = Zip2005.deriveNullifier nkF ρ ψ cm := by
  have hmsg : noteMsgW g p v r q = boolBytesToWords (noteBit
      (Accel.natToLeLimbs 4 (gd.x.val + 2 ^ 255 * Zip2005.ytilde gd))
      (Accel.natToLeLimbs 4 (pkd.x.val + 2 ^ 255 * Zip2005.ytilde pkd)) v
      (Accel.natToLeLimbs 4 ρ.val) (Accel.natToLeLimbs 4 ψ.val)) 137 := by
    rw [noteMsgW_eq, repr_of_mont hr, repr_of_mont hq, hg, hp, reprPNat_comm, reprPNat_comm]
  rw [hmsg] at hflag hnf
  obtain ⟨hcm, hok⟩ := note_spec gd pkd v ρ ψ k hflag hm1
  obtain ⟨L, hL⟩ : ∃ L, commitFold qNoteW (boolBytesToWords (noteBit
      (Accel.natToLeLimbs 4 (gd.x.val + 2 ^ 255 * Zip2005.ytilde gd))
      (Accel.natToLeLimbs 4 (pkd.x.val + 2 ^ 255 * Zip2005.ytilde pkd)) v
      (Accel.natToLeLimbs 4 ρ.val) (Accel.natToLeLimbs 4 ψ.val)) 137) = some L := by
    cases h : commitFold qNoteW (boolBytesToWords (noteBit
      (Accel.natToLeLimbs 4 (gd.x.val + 2 ^ 255 * Zip2005.ytilde gd))
      (Accel.natToLeLimbs 4 (pkd.x.val + 2 ^ 255 * Zip2005.ytilde pkd)) v
      (Accel.natToLeLimbs 4 ρ.val) (Accel.natToLeLimbs 4 ψ.val)) 137) with
    | none => rw [commitFlag_none h] at hflag; exact absurd hflag (by decide)
    | some L => exact ⟨L, rfl⟩
  rw [cmSel_some hL] at hnf
  refine ⟨_, hcm, ?_⟩
  have hnfs := nf_spec (Accel.leLimbsToNat n) (Accel.leLimbsToNat r) (Accel.leLimbsToNat q) _ hok hm2
  rw [D_of_mont hn, D_of_mont hr, D_of_mont hq] at hnfs
  rw [← hnfs]
  have hb := nat4_inj (nullifierX_lt _ _ _ _) (lt_trans (Cases.Zip2005.Fp.mul_lt _ _) Cases.Zip2005.Fp.p_lt) hnf
  rw [hb, mont_in_out _ hfc]


section
open RiscvZkvm.Rv64.Accel

/-- `extract_p_bottom` with flag `1`: its limbs are the affine `x` of the point. -/
theorem epb_val (W : List Word) :
    Accel.leLimbsToNat (extractPBottomW 1#8 W) = (Cases.Zip2005.Fp.toAffine (ptX W) (ptY W) (ptZ W)).1 := by
  have hA := Cases.Zip2005.toAffine_lt (X := ptX W) (Y := ptY W) (Z := ptZ W) (leLimbsToNat_lt _) (leLimbsToNat_lt _)
  unfold extractPBottomW selJ
  rw [if_pos rfl]
  dsimp only
  split
  · rename_i h; rw [h.1]; rfl
  · exact leLimbsToNat_natToLeLimbs 4 _ hA.1


theorem nz_of_flag (x : ℕ) (h : nzScalarFlag x = 1#8) : x < Fq.q ∧ x ≠ 0 := by
  unfold nzScalarFlag at h
  split at h
  · rename_i hc
    refine ⟨hc.1, ?_⟩
    rintro rfl
    exact hc.2 (by simp [Fq.mul])
  · exact absurd h (by decide)

theorem cast_ne_zero (x : ℕ) (hx : x < Fp.p) (h0 : x ≠ 0) : ((x : ℕ) : Zcash.Circuits.Fp) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff, Fp.p_card] at h
  exact h0 (Nat.eq_zero_of_dvd_of_lt h hx)

/-- Segment B on the spec side: `commit_ivk` gives `ivk = x`, not `⊥`, not zero, and the
scalar `pk_d` is derived with is `x` in Montgomery form over `F_q`. -/
theorem accB_ivk (n f rb sd w e rk ak gb : List Word) (v : Word)
    (h : AcceptB n f rb sd w e rk ak gb v) :
    ∃ (c0 c1 c2 c3 i0 i1 i2 i3 : Word) (x : ℕ),
      AcceptC n f rb sd [i0, i1, i2, i3] gb v ∧ x < Fp.p ∧ x < Fq.q ∧
      [i0, i1, i2, i3] = natToLeLimbs 4 (Fq.mul x Fq.R2) ∧
      Zip2005.commitIvk (((leLimbsToNat rk * Fq.rInv % Fq.q : ℕ)) : Zcash.Circuits.Fq)
        ((leLimbsToNat ak * Fp.rInv % Fp.p : ℕ) : Zcash.Circuits.Fp)
        ((leLimbsToNat n * Fp.rInv % Fp.p : ℕ) : Zcash.Circuits.Fp) = some (x : Zcash.Circuits.Fp) ∧
      (x : Zcash.Circuits.Fp) ≠ 0 ∧
      [c0, c1, c2, c3] = natToLeLimbs 4 (rivkIntX w[0]! w[1]! w[2]! w[3]! n[0]! n[1]! n[2]! n[3]!
        e[0]! e[1]! e[2]! e[3]!) ∧
      ((rk[0]! = c0 ∧ rk[1]! = c1 ∧ rk[2]! = c2 ∧ rk[3]! = c3) ∨
        (rk[0]! = e[0]! ∧ rk[1]! = e[1]! ∧ rk[2]! = e[2]! ∧ rk[3]! = e[3]!)) := by
  obtain ⟨c0, c1, c2, c3, j0, j1, j2, j3, i0, i1, i2, i3, x, hC, hm, hc, hj, hx, hi, hrk, hf, -, hnz⟩ := h
  have hxp : x < Fp.p := hx ▸ Nat.mod_lt _ Fp.p_pos
  have hx4 : leLimbsToNat [BitVec.ofNat 64 (x >>> (64 * 0)), BitVec.ofNat 64 (x >>> (64 * 1)),
      BitVec.ofNat 64 (x >>> (64 * 2)), BitVec.ofNat 64 (x >>> (64 * 3))] = x :=
    Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four (lt_trans hxp Fp.p_lt)
  rw [hx4] at hi hnz
  obtain ⟨hxq, hx0⟩ := nz_of_flag x hnz
  rw [nzScalarW, if_pos hxq] at hi
  refine ⟨c0, c1, c2, c3, i0, i1, i2, i3, x, hC, hxp, hxq, hi, ?_, cast_ne_zero x hxp hx0, hc, hrk⟩
  have hav : leLimbsToNat ak * Fp.rInv % Fp.p < Fp.p := Nat.mod_lt _ Fp.p_pos
  have hnv : leLimbsToNat n * Fp.rInv % Fp.p < Fp.p := Nat.mod_lt _ Fp.p_pos
  have key := ivk_spec _ _ hav hnv rk hf hm
  rw [key]
  rw [hf] at hj
  unfold reprW at hj
  rw [← hx, hj, epb_val, jacXY]

end

section
open RiscvZkvm.Rv64.Accel

theorem lebs2ip_i2lebsp (k n : ℕ) : Zip2005.lebs2ip (Zip2005.i2lebsp k n) = n % 2 ^ k := by
  induction k generalizing n with
  | zero => simp [Zip2005.i2lebsp, Zip2005.lebs2ip, Nat.mod_one]
  | succ k ih =>
    have e : Zip2005.lebs2ip (Zip2005.i2lebsp (k + 1) n) =
        (if (n % 2 == 1) = true then 1 else 0) + 2 * Zip2005.lebs2ip (Zip2005.i2lebsp k (n / 2)) := rfl
    rw [e, ih, pow_succ', Nat.mod_mul]
    congr 1
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem reprPNat_lt (P : Point Fp) : Zip2005.reprPNat P < 2 ^ 256 := by
  have hx : P.x.val < Cases.Zip2005.Fp.p := ZMod.val_lt P.x
  have hp : Cases.Zip2005.Fp.p < 2 ^ 255 := p_lt_255
  have hy : Zip2005.ytilde P < 2 := Nat.mod_lt _ (by decide)
  unfold Zip2005.reprPNat
  omega

theorem reprP_bytes (P : Point Fp) :
    Zip2005.reprP P = Zip2005.Blake2b.stateBytes ((natToLeLimbs 4 (Zip2005.reprPNat P)).map BitVec.toNat) := by
  unfold Zip2005.reprP Zip2005.lebs2osp Zip2005.reprPBits
  rw [Zip2005.i2lebsp_length, lebs2ip_i2lebsp, Nat.mod_eq_of_lt (reprPNat_lt P)]
  exact Cases.Zip2005.i2leosp256_limbs _ (reprPNat_lt P)

theorem fp_mul_R2 (a : ℕ) : Cases.Zip2005.Fp.mul a Cases.Zip2005.Fp.R2 = a * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p := by
  have h1 : Cases.Zip2005.Fp.R2 * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p = Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p := by decide +kernel
  unfold Cases.Zip2005.Fp.mul
  rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, h1, ← Nat.mul_mod]

theorem mont_of_lt (a : ℕ) (ha : a < Cases.Zip2005.Fp.p) :
    Cases.Zip2005.Fp.mul a Cases.Zip2005.Fp.R2 = ((a : ℕ) : Fp).val * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p := by
  rw [fp_mul_R2, ZMod.val_natCast, Fp.p_card, Nat.mod_eq_of_lt ha]

theorem fq_of_mont (y : ℕ) (a : Fq) (h : y = a.val * Cases.Zip2005.Fq.R % Cases.Zip2005.Fq.q) :
    (((leLimbsToNat (natToLeLimbs 4 y)) * Cases.Zip2005.Fq.rInv % Cases.Zip2005.Fq.q : ℕ) : Fq) = a := by
  have hy : y < 2 ^ 256 := h ▸ lt_trans (Nat.mod_lt _ Cases.Zip2005.Fq.q_pos) (by decide +kernel)
  rw [Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four hy, h, Cases.Zip2005.Fq.mont_back,
    Nat.mod_eq_of_lt (show a.val < Cases.Zip2005.Fq.q from ZMod.val_lt a)]
  exact ZMod.natCast_zmod_val a


theorem list12 {α : Type} (m : List α) (h : m.length = 12) :
    ∃ m0 m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 : α, m = [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11] := by
  match m, h with
  | [m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11], _ => exact ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, rfl⟩

/-- **Segment C's accepting-path facts, in the spec's vocabulary.** From the decoded `g_d`
(`l`, `from_bytes` with flag 1 of the bytes `b`), the scalar `x` (`ivk`) in Montgomery form
(`i`), `ρ` (`rb`), the seed (`sd`) and segment E's facts: `g_d` is a valid point with
encoding `b`, and the note commitment of `(g_d, [x] g_d, v, ρ, ψ)` under `rcm`, with `ψ` and
`rcm` the seed's PRF outputs, is some `cm` whose nullifier is the output `f`. -/
theorem accC_spec (n f rb sd : List Word) (i0 i1 i2 i3 v : Word) (x : ℕ) (nkF : Fp)
    (r0 r1 r2 r3 q0 q1 q2 q3 c0 c1 c2 c3 d0 d1 d2 d3 k0 k1 k2 k3 : Word)
    (l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 : Word) (m : List Word) (y : ℕ) (b0 b1 b2 b3 : Word)
    (hn : leLimbsToNat n = nkF.val * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p)
    (hxq : x < Cases.Zip2005.Fq.q) (hi : [i0, i1, i2, i3] = natToLeLimbs 4 (Cases.Zip2005.Fq.mul x Cases.Zip2005.Fq.R2))
    (hrb : leLimbsToNat rb < Cases.Zip2005.Fp.p)
    (hfb : Cases.Zip2005.FromBytesPost b0 b1 b2 b3 (leLimbsToNat [l0, l1, l2, l3]) (leLimbsToNat [l4, l5, l6, l7]) 1#8)
    (hz : leLimbsToNat [l8, l9, l10, l11] =
      if leLimbsToNat [l0, l1, l2, l3] = 0 ∧ leLimbsToNat [l4, l5, l6, l7] = 0 then 0 else Cases.Zip2005.Fp.R)
    (hml : mulFacts [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11] [i0, i1, i2, i3])
    (hE : AcceptE n [r0, r1, r2, r3] [q0, q1, q2, q3] [c0, c1, c2, c3] [d0, d1, d2, d3]
      [k0, k1, k2, k3] f v)
    (hR : leLimbsToNat [r0, r1, r2, r3] = Cases.Zip2005.Fp.mul (leLimbsToNat rb) Cases.Zip2005.Fp.R2)
    (hQ : leLimbsToNat [q0, q1, q2, q3] = psiX sd[0]! sd[1]! sd[2]! sd[3]! r0 r1 r2 r3)
    (hc : [c0, c1, c2, c3] = natToLeLimbs 4 (tbX l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11))
    (hm : mulW [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11] [i0, i1, i2, i3] = m)
    (hd : [d0, d1, d2, d3] = natToLeLimbs 4 (tbX m[0]! m[1]! m[2]! m[3]! m[4]! m[5]! m[6]! m[7]! m[8]! m[9]! m[10]! m[11]!))
    (hk : [k0, k1, k2, k3] = natToLeLimbs 4 y)
    (hrcm : RcmRel sd[0]! sd[1]! sd[2]! sd[3]! r0 r1 r2 r3 q0 q1 q2 q3 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11
      m[0]! m[1]! m[2]! m[3]! m[4]! m[5]! m[6]! m[7]! m[8]! m[9]! m[10]! m[11]! v y) :
    (specPt [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]).Valid ∧ Zip2005.reprPNat (specPt [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]) = leLimbsToNat [b0, b1, b2, b3] ∧
    ∃ cm : Point Fp,
      Zip2005.noteCommit
        (Zip2005.hRcmOrchard (Zip2005.Blake2b.stateBytes ([sd[0]!, sd[1]!, sd[2]!, sd[3]!].map BitVec.toNat))
          (specPt [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]) (Zip2005.smul (x : Fq) (specPt [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11])) v.toNat ((leLimbsToNat rb : ℕ) : Fp)
          (Zip2005.hPsiOrchard (Zip2005.Blake2b.stateBytes ([sd[0]!, sd[1]!, sd[2]!, sd[3]!].map BitVec.toNat))
            ((leLimbsToNat rb : ℕ) : Fp)))
        (specPt [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]) (Zip2005.smul (x : Fq) (specPt [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11])) v.toNat ((leLimbsToNat rb : ℕ) : Fp)
        (Zip2005.hPsiOrchard (Zip2005.Blake2b.stateBytes ([sd[0]!, sd[1]!, sd[2]!, sd[3]!].map BitVec.toNat))
          ((leLimbsToNat rb : ℕ) : Fp)) = some cm ∧
      ((leLimbsToNat f : ℕ) : Fp) = Zip2005.deriveNullifier nkF ((leLimbsToNat rb : ℕ) : Fp)
        (Zip2005.hPsiOrchard (Zip2005.Blake2b.stateBytes ([sd[0]!, sd[1]!, sd[2]!, sd[3]!].map BitVec.toNat))
          ((leLimbsToNat rb : ℕ) : Fp)) cm := by
  obtain ⟨hJ, hV, hrep⟩ := fb_decode l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 b0 b1 b2 b3 hfb hz
  refine ⟨hV, hrep, ?_⟩
  have hb : ptZ [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11] ≠ 0 → Cases.Zip2005.SpecMul.ValidA (Cases.Zip2005.mulBase [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]) := by
    intro hz0
    rcases hJ with h | h
    · exact absurd h hz0
    · exact validA_mulBase h.2
  have hpk := specPt_mulW _ _ hb hml hV
  rw [hm, hi, Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four (lt_trans (Cases.Zip2005.Fq.mul_lt _ _) (by decide +kernel)),
    Fq_mont_in_out x hxq] at hpk
  have hl : m.length = 12 := hm ▸ length_mulW _ _
  obtain ⟨m0, m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, rfl⟩ := list12 m hl
  have hρ : leLimbsToNat [r0, r1, r2, r3] = ((leLimbsToNat rb : ℕ) : Fp).val * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p := by
    rw [hR, mont_of_lt _ hrb]
  have hψ := hQ.trans (psiX_correct _ _ _ _ _ _ _ _ _ hρ)
  have hg : [c0, c1, c2, c3] = natToLeLimbs 4 (Zip2005.reprPNat (specPt [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11])) := by rw [hc, tbX_repr]
  have hp : [d0, d1, d2, d3] = natToLeLimbs 4 (Zip2005.reprPNat (Zip2005.smul (x : Fq) (specPt [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]))) := by
    rw [hd, ← hpk]
    simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
    rw [tbX_repr]
  have hy := rcmRel_correct _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ y
    (specPt [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]) (Zip2005.smul (x : Fq) (specPt [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11])) _ _
    (by rw [tbX_repr, reprP_bytes]) (by
      simp only [List.getElem!_cons_zero, List.getElem!_cons_succ]
      rw [tbX_repr, hpk, reprP_bytes]) hρ hψ hrcm
  obtain ⟨cm, hcm, hnf⟩ := accE_spec n [r0, r1, r2, r3] [q0, q1, q2, q3] [c0, c1, c2, c3] [d0, d1, d2, d3]
    [k0, k1, k2, k3] f v nkF _ _ (specPt [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11]) (Zip2005.smul (x : Fq) (specPt [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11])) hn hρ hψ hg hp
    hE.1 hE.2.1 hE.2.2.1 hE.2.2.2.1 hE.2.2.2.2
  rw [hk, fq_of_mont y _ hy] at hcm
  exact ⟨cm, hcm, hnf⟩

/-- `repr_ℙ` of a spec point read from cells, in terms of the affine Montgomery coordinates. -/
theorem repr_specPt (L : List Word) :
    Zip2005.reprPNat (specPt L) =
      (Cases.Zip2005.Fp.toAffine (ptX L) (ptY L) (ptZ L)).1 * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p +
        2 ^ 255 * ((Cases.Zip2005.Fp.toAffine (ptX L) (ptY L) (ptZ L)).2 * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p % 2) := by
  unfold Zip2005.reprPNat Zip2005.ytilde specPt jacXY
  simp only
  generalize Cases.Zip2005.Fp.toAffine (ptX L) (ptY L) (ptZ L) = T
  have hA : T.1 * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := Nat.mod_lt _ Cases.Zip2005.Fp.p_pos
  have hB : T.2 * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := Nat.mod_lt _ Cases.Zip2005.Fp.p_pos
  rw [ZMod.val_cast_of_lt hA, ZMod.val_cast_of_lt hB]
  ring

/-- `Ep::to_bytes` of a sum of two well-formed Jacobian points is `repr_ℙ` of the spec sum, and
the sum is a valid point. -/
theorem toBytes_addJ (A B : List Word) (hA : JacW A) (hB : JacW B) :
    leLimbsToNat (toBytesW (Cases.Zip2005.Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B))) =
      Zip2005.reprPNat (specPt A + specPt B) ∧ (specPt A + specPt B).Valid := by
  have b := Cases.Zip2005.Fp.addJ_lt (X1 := ptX A) (Y1 := ptY A) (Z1 := ptZ A) (X2 := ptX B) (Y2 := ptY B) (Z2 := ptZ B)
    (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)
    (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)
  obtain ⟨hs, hok⟩ := specPt_addJ_cells A B hA hB
  obtain ⟨cx, cy, cz⟩ := cells3 _ _ _ b.1 b.2.1 b.2.2
  rw [← hs]
  refine ⟨?_, ?_⟩
  · rw [repr_specPt, cx, cy, cz]
    unfold toBytesW
    apply leLimbsToNat_natToLeLimbs 4
    have h1 : (Cases.Zip2005.Fp.toAffine (Cases.Zip2005.Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).1
        (Cases.Zip2005.Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).2.1
        (Cases.Zip2005.Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).2.2).1 * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p < 2 ^ 255 :=
      lt_trans (Nat.mod_lt _ Cases.Zip2005.Fp.p_pos) p_lt_255
    have h2 := Nat.mod_lt ((Cases.Zip2005.Fp.toAffine (Cases.Zip2005.Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).1
        (Cases.Zip2005.Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).2.1
        (Cases.Zip2005.Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).2.2).2 * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p) (show 0 < 2 by decide)
    generalize (Cases.Zip2005.Fp.toAffine (Cases.Zip2005.Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).1
        (Cases.Zip2005.Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).2.1
        (Cases.Zip2005.Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).2.2).1 * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p = u at h1 ⊢
    generalize (Cases.Zip2005.Fp.toAffine (Cases.Zip2005.Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).1
        (Cases.Zip2005.Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).2.1
        (Cases.Zip2005.Fp.addJ (ptX A) (ptY A) (ptZ A) (ptX B) (ptY B) (ptZ B)).2.2).2 * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p % 2 = w at h2 ⊢
    simp only [Nat.reduceMul]
    omega
  · rw [specPt_eq _ (by rw [cz]; exact hok.1), cx, cy, cz]
    exact specT_valid hok


/-- **The randomized key is the spec's `SpendAuthSig.RandomizePublic`.** `ak`'s cells `a` a
well-formed point, `G` the decoded basepoint, `[α] G` as the run computed it (`mulFacts`), and
the instance `rk` (`u`, decoded from the bytes `b` with flag 1) whose bytes equal `to_bytes` of
`ak + [α] G`: then `rk = [α] 𝒢 + ak`. -/
theorem rk_spec (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 u0 u1 u2 u3 v0 v1 v2 v3 w0 w1 w2 w3 b0 b1 b2 b3 : Word) (k : List Word)
    (hA : JacW [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11])
    (hG : Cases.Zip2005.FromBytesPost 10167565023098292579#64 900452621665476876#64 4291112941855392863#64
      13210504334354273798#64 (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) 1#8)
    (hGz : leLimbsToNat [z0, z1, z2, z3] =
      if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Cases.Zip2005.Fp.R)
    (hm : mulFacts [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] k)
    (hR : Cases.Zip2005.FromBytesPost b0 b1 b2 b3 (leLimbsToNat [u0, u1, u2, u3]) (leLimbsToNat [v0, v1, v2, v3]) 1#8)
    (hRz : leLimbsToNat [w0, w1, w2, w3] =
      if leLimbsToNat [u0, u1, u2, u3] = 0 ∧ leLimbsToNat [v0, v1, v2, v3] = 0 then 0 else Cases.Zip2005.Fp.R)
    (heq : leLimbsToNat (toBytesW (rkJ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 (mulW [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] k))) = leLimbsToNat [b0, b1, b2, b3]) :
    specPt [u0, u1, u2, u3, v0, v1, v2, v3, w0, w1, w2, w3] = Zip2005.smul ((leLimbsToNat k * Cases.Zip2005.Fq.rInv % Cases.Zip2005.Fq.q : ℕ) : Fq) Zip2005.GOrchard +
      specPt [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] := by
  obtain ⟨hGpt, hGj⟩ := specPt_G _ _ _ _ _ _ _ _ _ _ _ _ hG hGz
  have hb : ptZ [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] ≠ 0 → Cases.Zip2005.SpecMul.ValidA (Cases.Zip2005.mulBase [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3]) := by
    intro hz0
    rcases hGj with h | h
    · exact absurd h hz0
    · exact validA_mulBase h.2
  have hGv : (specPt [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3]).Valid := by rw [hGpt]; exact Or.inl Zcash.Circuits.Action.orchardBases.spendAuthG.onCurve
  have hM := jacW_mulW _ _ hb hm
  have hMs := specPt_mulW _ _ hb hm hGv
  rw [hGpt] at hMs
  obtain ⟨hsum, hval⟩ := toBytes_addJ [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] (mulW [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] k) hA hM
  have e : rkJ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 (mulW [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] k) = Cases.Zip2005.Fp.addJ (ptX [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]) (ptY [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]) (ptZ [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11])
      (ptX (mulW [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] k)) (ptY (mulW [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] k)) (ptZ (mulW [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] k)) := rfl
  rw [e, hsum] at heq
  obtain ⟨-, hRv, hRr⟩ := fb_decode u0 u1 u2 u3 v0 v1 v2 v3 w0 w1 w2 w3 b0 b1 b2 b3 hR hRz
  have hAv : (specPt [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]).Valid := by
    rw [specPt_eq _ (ptZ_lt_of_jacW hA)]; exact specT_valid (jacOk_of_jacW hA)
  have hMv : (specPt (mulW [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] k)).Valid := by
    rw [specPt_eq _ (ptZ_lt_of_jacW hM)]; exact specT_valid (jacOk_of_jacW hM)
  rw [← hMs, Zcash.Circuits.Point.add_comm hMv hAv]
  exact reprPNat_inj hRv hval (hRr.trans heq.symm)

/-- Montgomery limbs of `a`, read back. -/
theorem fp_back (n : ℕ) (a : Fp) (h : n = a.val * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p) :
    ((n * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p : ℕ) : Fp) = a := by
  rw [h, Cases.Zip2005.Fp.mont_back, Nat.mod_eq_of_lt (show a.val < Cases.Zip2005.Fp.p from ZMod.val_lt a)]
  exact ZMod.natCast_zmod_val a

theorem fq_back (n : ℕ) (a : Fq) (h : n = a.val * Cases.Zip2005.Fq.R % Cases.Zip2005.Fq.q) :
    ((n * Cases.Zip2005.Fq.rInv % Cases.Zip2005.Fq.q : ℕ) : Fq) = a := by
  rw [h, Cases.Zip2005.Fq.mont_back, Nat.mod_eq_of_lt (show a.val < Cases.Zip2005.Fq.q from ZMod.val_lt a)]
  exact ZMod.natCast_zmod_val a

/-- `to_bytes` of cells is `repr_ℙ` of the spec point they denote. -/
theorem ptBytes_repr (M : List Word) : leLimbsToNat (ptBytesW M) = Zip2005.reprPNat (specPt M) := by
  rw [repr_specPt]
  unfold ptBytesW toBytesW
  apply leLimbsToNat_natToLeLimbs 4
  have h1 : (Cases.Zip2005.Fp.toAffine (ptX M) (ptY M) (ptZ M)).1 * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p < 2 ^ 255 :=
    lt_trans (Nat.mod_lt _ Cases.Zip2005.Fp.p_pos) p_lt_255
  have h2 := Nat.mod_lt ((Cases.Zip2005.Fp.toAffine (ptX M) (ptY M) (ptZ M)).2 * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p)
    (show 0 < 2 by decide)
  simp only
  generalize (Cases.Zip2005.Fp.toAffine (ptX M) (ptY M) (ptZ M)).1 * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p = u at h1 ⊢
  generalize (Cases.Zip2005.Fp.toAffine (ptX M) (ptY M) (ptZ M)).2 * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p % 2 = w at h2 ⊢
  simp only [Nat.reduceMul]
  omega

/-- **`ak` is `[±ask] 𝒢`.** The decoded spend-validating key (`x`.., from the bytes `b` with flag 1)
whose bytes are `to_bytes` of `[±ask] G` (`G` the decoded basepoint) is that point. -/
theorem ak_spec (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 b0 b1 b2 b3 : Word)
    (g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 neg s0 s1 s2 s3 : Word)
    (hfb : Cases.Zip2005.FromBytesPost b0 b1 b2 b3 (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) 1#8)
    (hz : leLimbsToNat [z0, z1, z2, z3] =
      if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Cases.Zip2005.Fp.R)
    (hG : Cases.Zip2005.FromBytesPost 10167565023098292579#64 900452621665476876#64 4291112941855392863#64
      13210504334354273798#64 (leLimbsToNat [g0, g1, g2, g3]) (leLimbsToNat [g4, g5, g6, g7]) 1#8)
    (hGz : leLimbsToNat [g8, g9, g10, g11] =
      if leLimbsToNat [g0, g1, g2, g3] = 0 ∧ leLimbsToNat [g4, g5, g6, g7] = 0 then 0 else Cases.Zip2005.Fp.R)
    (hm : mulFacts [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] (skW (askR neg s0 s1 s2 s3)))
    (hb : [b0, b1, b2, b3] = ptBytesW (mulW [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11]
      (skW (askR neg s0 s1 s2 s3)))) :
    specPt [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] =
      Zip2005.spendAuthDerivePublic
        (if neg = 0#64 then Zip2005.hAsk (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))
          else -Zip2005.hAsk (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))) := by
  obtain ⟨hGpt, hGj⟩ := specPt_G _ _ _ _ _ _ _ _ _ _ _ _ hG hGz
  have hbase : ptZ [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] ≠ 0 →
      Cases.Zip2005.SpecMul.ValidA (Cases.Zip2005.mulBase [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11]) := by
    intro hz0
    rcases hGj with h | h
    · exact absurd h hz0
    · exact validA_mulBase h.2
  have hGv : (specPt [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11]).Valid := by
    rw [hGpt]; exact Or.inl Zcash.Circuits.Action.orchardBases.spendAuthG.onCurve
  have hM := jacW_mulW _ _ hbase hm
  have hMv : (specPt (mulW [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] (skW (askR neg s0 s1 s2 s3)))).Valid := by
    rw [specPt_eq _ (ptZ_lt_of_jacW hM)]; exact specT_valid (jacOk_of_jacW hM)
  obtain ⟨-, hAv, hAr⟩ := fb_decode _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfb hz
  have hP := askPt neg s0 s1 s2 s3 _ hbase hm hGv
  rw [hGpt] at hP
  unfold Zip2005.spendAuthDerivePublic
  rw [← hP]
  apply reprPNat_inj hAv hMv
  rw [hAr, hb, ptBytes_repr]

/-- A point's 32 bytes with the sign bit clear are `I2LEOSP_256` of its `x`. -/
theorem bytes_of_msb (b0 b1 b2 b3 : Word) (P : Point Fp) (hb : b3.msb = false)
    (hr : Zip2005.reprPNat P = leLimbsToNat [b0, b1, b2, b3]) :
    Zip2005.Blake2b.stateBytes ([b0, b1, b2, b3].map BitVec.toNat) = Zip2005.i2leosp 256 P.x.val := by
  have hs := bytes_split b0 b1 b2 b3
  rw [hb] at hs
  have hlt : leLimbsToNat [b0, b1, b2, b3 &&& 0x7fffffffffffffff#64] < 2 ^ 255 := by
    simp only [Cases.Zip2005.Precompile.leLimbsToNat_cons, Cases.Zip2005.Precompile.leLimbsToNat_nil, BitVec.toNat_and]
    have := b0.isLt; have := b1.isLt; have := b2.isLt
    have : b3.toNat &&& (0x7fffffffffffffff#64).toNat < 2 ^ 63 := by
      apply Nat.lt_of_le_of_lt Nat.and_le_right; decide
    omega
  have hx : P.x.val < 2 ^ 255 := lt_trans (ZMod.val_lt P.x) p_lt_255
  have hy : Zip2005.ytilde P < 2 := Nat.mod_lt _ (by decide)
  unfold Zip2005.reprPNat at hr
  simp only [Bool.false_eq_true, if_false, Nat.zero_mul, Nat.add_zero] at hs
  have hval : leLimbsToNat [b0, b1, b2, b3] = P.x.val := by
    have h01 : Zip2005.ytilde P = 0 ∨ Zip2005.ytilde P = 1 := by omega
    generalize (2 : ℕ) ^ 255 = c at *
    rcases h01 with h | h <;> rw [h] at hr <;> omega
  rw [Cases.Zip2005.i2leosp256_limbs _ (lt_trans hx (by norm_num)), ← hval,
    show (4 : ℕ) = [b0, b1, b2, b3].length from rfl, natToLeLimbs_leLimbsToNat]

/-- **`rivk` is `rivk_ext` or the internal `rivk`.** The witness `rivk` (`k`) equal, word by word,
to `FullViewingKey::rivk(Internal)`'s output (`c`) or to `rivk_ext` (`e`) is, as a scalar, one of
the spec's two. -/
theorem rivk_spec (k0 k1 k2 k3 c0 c1 c2 c3 e0 e1 e2 e3 w0 w1 w2 w3 n0 n1 n2 n3 : Word)
    (rivkE : Fq) (akP : Point Fp) (nk : Fp)
    (he : leLimbsToNat [e0, e1, e2, e3] = rivkE.val * Cases.Zip2005.Fq.R % Cases.Zip2005.Fq.q)
    (hn : leLimbsToNat [n0, n1, n2, n3] = nk.val * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p)
    (hw : Zip2005.Blake2b.stateBytes ([w0, w1, w2, w3].map BitVec.toNat) = Zip2005.i2leosp 256 akP.x.val)
    (hc : [c0, c1, c2, c3] = natToLeLimbs 4 (rivkIntX w0 w1 w2 w3 n0 n1 n2 n3 e0 e1 e2 e3))
    (hrk : (k0 = c0 ∧ k1 = c1 ∧ k2 = c2 ∧ k3 = c3) ∨ (k0 = e0 ∧ k1 = e1 ∧ k2 = e2 ∧ k3 = e3)) :
    ((leLimbsToNat [k0, k1, k2, k3] * Cases.Zip2005.Fq.rInv % Cases.Zip2005.Fq.q : ℕ) : Fq) = rivkE ∨
      ((leLimbsToNat [k0, k1, k2, k3] * Cases.Zip2005.Fq.rInv % Cases.Zip2005.Fq.q : ℕ) : Fq) =
        Zip2005.hRivkInt (Zip2005.i2leosp 256 rivkE.val) (Zip2005.extractP akP) nk := by
  rcases hrk with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · right
    have hx := rivkIntX_correct w0 w1 w2 w3 n0 n1 n2 n3 e0 e1 e2 e3 rivkE akP.x nk he hn hw
    have hlt : rivkIntX w0 w1 w2 w3 n0 n1 n2 n3 e0 e1 e2 e3 < 2 ^ 256 :=
      hx ▸ lt_trans (Nat.mod_lt _ Cases.Zip2005.Fq.q_pos) (by decide +kernel)
    rw [hc, Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four hlt]
    exact fq_back _ _ hx
  · left
    exact fq_back _ _ he

theorem nip_one {fl : BitVec 8} {z0 z1 z2 z3 : Word} (h : nipFlag fl z0 z1 z2 z3 = 1#8) : fl = 1#8 := by
  unfold nipFlag at h
  split at h
  · rename_i hc; exact hc.1
  · exact absurd h (by decide)

/-- Segment C's predicate, read in the spec's vocabulary (`accC_spec` over `AcceptC`'s witnesses). -/
theorem accC_of (n f rb sd : List Word) (i0 i1 i2 i3 b0 b1 b2 b3 v : Word) (x : ℕ) (nkF : Fp)
    (hn : leLimbsToNat n = nkF.val * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p)
    (hxq : x < Cases.Zip2005.Fq.q) (hi : [i0, i1, i2, i3] = natToLeLimbs 4 (Cases.Zip2005.Fq.mul x Cases.Zip2005.Fq.R2))
    (h : AcceptC n f rb sd [i0, i1, i2, i3] [b0, b1, b2, b3] v) :
    ∃ gd : Point Fp, gd.Valid ∧ Zip2005.reprPNat gd = leLimbsToNat [b0, b1, b2, b3] ∧
    ∃ cm : Point Fp,
      Zip2005.noteCommit
        (Zip2005.hRcmOrchard (Zip2005.Blake2b.stateBytes ([sd[0]!, sd[1]!, sd[2]!, sd[3]!].map BitVec.toNat))
          gd (Zip2005.smul (x : Fq) gd) v.toNat ((leLimbsToNat rb : ℕ) : Fp)
          (Zip2005.hPsiOrchard (Zip2005.Blake2b.stateBytes ([sd[0]!, sd[1]!, sd[2]!, sd[3]!].map BitVec.toNat))
            ((leLimbsToNat rb : ℕ) : Fp)))
        gd (Zip2005.smul (x : Fq) gd) v.toNat ((leLimbsToNat rb : ℕ) : Fp)
        (Zip2005.hPsiOrchard (Zip2005.Blake2b.stateBytes ([sd[0]!, sd[1]!, sd[2]!, sd[3]!].map BitVec.toNat))
          ((leLimbsToNat rb : ℕ) : Fp)) = some cm ∧
      ((leLimbsToNat f : ℕ) : Fp) = Zip2005.deriveNullifier nkF ((leLimbsToNat rb : ℕ) : Fp)
        (Zip2005.hPsiOrchard (Zip2005.Blake2b.stateBytes ([sd[0]!, sd[1]!, sd[2]!, sd[3]!].map BitVec.toNat))
          ((leLimbsToNat rb : ℕ) : Fp)) cm := by
  obtain ⟨r0, r1, r2, r3, q0, q1, q2, q3, c0, c1, c2, c3, d0, d1, d2, d3, k0, k1, k2, k3,
    l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, m, y, hE, hR, hQ, hc, hm, hd, hk, hrcm,
    hrb, ⟨fl, hfb, hnip⟩, hz, hml⟩ := h
  have hfl := nip_one hnip
  subst hfl
  obtain ⟨hV, hrep, hrest⟩ := accC_spec n f rb sd i0 i1 i2 i3 v x nkF r0 r1 r2 r3 q0 q1 q2 q3
    c0 c1 c2 c3 d0 d1 d2 d3 k0 k1 k2 k3 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 m y b0 b1 b2 b3
    hn hxq hi hrb hfb hz hml hE hR hQ hc hm hd hk hrcm
  exact ⟨_, hV, hrep, hrest⟩

end

end Cases.Zip2005.Top
