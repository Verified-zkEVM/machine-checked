import Cases.Zip2005.Bridge.SpecTop
import Cases.Zip2005.Spec.Zip2005.Divergences
import Cases.Zip2005.Precompile

/-!
# The accepting path's checks as `Zip2005.GuestStatement`

`guest_of_a2c` assembles the `SpecTop` bridges over segment A2c's acceptance facts and `ak`'s
decode into every conjunct of `GuestChecks`. The instance enters through its two fields only (`rk`,
`nf`), which the segments before A2c and the input decoding supply.
-/

namespace Cases.Zip2005.Top

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.SpecMul Cases.Zip2005.Poseidon
open Zcash.Circuits (Fp Fq Point)

set_option autoImplicit false

theorem askW_bytes (neg s0 s1 s2 s3 : Word) (G : List Word) :
    ((askW neg s0 s1 s2 s3 G).drop 12).take 4 = ptBytesW (mulW G (skW (askR neg s0 s1 s2 s3))) := by
  have h12 := length_mulW G (skW (askR neg s0 s1 s2 s3))
  have h4 : (ptBytesW (mulW G (skW (askR neg s0 s1 s2 s3)))).length = 4 := by simp [ptBytesW, toBytesW]
  unfold askW
  rw [List.append_assoc, List.drop_left' h12, List.take_left' h4]

theorem modRP_cast (x : ℕ) (hx : x < Cases.Zip2005.Fp.p) :
    Zip2005.modRP ((x : ℕ) : Fp) = ((x : ℕ) : Fq) := by
  unfold Zip2005.modRP
  rw [ZMod.val_natCast, Fp.p_card, Nat.mod_eq_of_lt hx]

theorem negate_if (neg : Word) (a : Fq) :
    (if neg = 0#64 then a else -a) = (if (!(neg == 0#64)) = true then -a else a) := by
  by_cases h : neg = 0#64 <;> simp [h]


theorem four_eta (l : List Word) (h : l.length = 4) : l = [l[0]!, l[1]!, l[2]!, l[3]!] := by
  match l, h with
  | [a, b, c, d], _ => rfl

/-- **The `sk` arm's checks are `GuestStatement`'s.** Segment A2c's acceptance facts, with `ak`'s
bytes `w` decoding (flag 1) to the cells `a` and their sign bit clear, give every conjunct of
`GuestChecks` for the key `sk` the words `s` spell, `negate` the low bit `neg`, `ak^ℙ` the decoded
point, `rivk` the witness words `k`, `rseed` the seed words `d`, `ρ` the witness bytes `rb`, and
`g_d` the point the witness bytes `b` encode. The instance enters only through its two fields: an
instance whose `rk` is `RandomizePublic(α, ak^ℙ)` and whose `nf` is the nullifier words `f`. -/
theorem guest_of_a2c (s0 s1 s2 s3 neg : Word) (n f rb e : List Word) (d0 d1 d2 d3 w0 w1 w2 w3 k0 k1 k2 k3
    b0 b1 b2 b3 v : Word) (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Word) (x : ℕ)
    (hfa : Cases.Zip2005.FromBytesPost w0 w1 w2 w3 (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [a4, a5, a6, a7]) 1#8)
    (hza : leLimbsToNat [a8, a9, a10, a11] =
      if leLimbsToNat [a0, a1, a2, a3] = 0 ∧ leLimbsToNat [a4, a5, a6, a7] = 0 then 0 else Cases.Zip2005.Fp.R)
    (hx : (Cases.Zip2005.Fp.toAffine (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [a4, a5, a6, a7])
      (leLimbsToNat [a8, a9, a10, a11])).1 = x)
    (hmsb : w3.msb = false)
    (hA : AcceptA2c s0 s1 s2 s3 neg n f rb [d0, d1, d2, d3] [w0, w1, w2, w3] e [k0, k1, k2, k3]
      [BitVec.ofNat 64 (x >>> (64 * 0)), BitVec.ofNat 64 (x >>> (64 * 1)), BitVec.ofNat 64 (x >>> (64 * 2)),
        BitVec.ofNat 64 (x >>> (64 * 3))] [b0, b1, b2, b3] v) :
    ∃ gd : Point Fp, gd.Valid ∧ Zip2005.reprPNat gd = leLimbsToNat [b0, b1, b2, b3] ∧
      ∀ (pi : Zip2005.PrimaryInput) (α : Fq),
        pi.rk = Zip2005.spendAuthRandomizePublic α (specPt [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]) →
        pi.nf = ((leLimbsToNat f : ℕ) : Fp) →
        Zip2005.GuestStatement pi (!(neg == 0#64)) (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))
          α (specPt [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11])
          (Zip2005.hNk (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat)))
          (Zip2005.hRivkLegacy (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat)))
          ((leLimbsToNat [k0, k1, k2, k3] * Cases.Zip2005.Fq.rInv % Cases.Zip2005.Fq.q : ℕ) : Fq)
          (Zip2005.Blake2b.stateBytes ([d0, d1, d2, d3].map BitVec.toNat)) gd v.toNat
          ((leLimbsToNat rb : ℕ) : Fp) := by
  obtain ⟨hB, hn, he, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, ⟨hG, hGz, hm⟩, hw⟩ := hA
  have hnv : leLimbsToNat n =
      (Zip2005.hNk (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))).val * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p := by
    rw [hn]; exact nkW_val s0 s1 s2 s3
  obtain ⟨c0, c1, c2, c3, i0, i1, i2, i3, xi, hC, hxp, hxq, hi, hcommit, hne, hc, hrk⟩ :=
    accB_ivk _ _ _ _ _ _ _ _ _ _ hB
  obtain ⟨gd, hgv, hgr, cm, hnote, hnf⟩ :=
    accC_of n f rb [d0, d1, d2, d3] i0 i1 i2 i3 b0 b1 b2 b3 v xi _ hnv hxq hi hC
  have hak := ak_spec a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 w0 w1 w2 w3 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
    neg s0 s1 s2 s3 hfa hza hG hGz hm (by rw [hw, askW_bytes])
  obtain ⟨-, -, hAr⟩ := fb_decode _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfa hza
  have hbytes := bytes_of_msb w0 w1 w2 w3 _ hmsb hAr
  have hel : e = [e[0]!, e[1]!, e[2]!, e[3]!] := four_eta e (by rw [he, rivkW, Cases.Zip2005.length_natToLeLimbs])
  have hnl : n = [n[0]!, n[1]!, n[2]!, n[3]!] := four_eta n (by rw [hn, nkW, Cases.Zip2005.length_natToLeLimbs])
  have hev : leLimbsToNat [e[0]!, e[1]!, e[2]!, e[3]!] =
      (Zip2005.hRivkLegacy (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))).val *
        Cases.Zip2005.Fq.R % Cases.Zip2005.Fq.q := by
    rw [← hel, he]; exact rivkW_val s0 s1 s2 s3
  have hrivk := rivk_spec k0 k1 k2 k3 c0 c1 c2 c3 e[0]! e[1]! e[2]! e[3]! w0 w1 w2 w3 n[0]! n[1]! n[2]! n[3]! _ _ _
    hev (by rw [← hnl]; exact hnv) hbytes hc (by simpa using hrk)
  -- `ak`'s coordinate as `commit_ivk` reads it is `Extract_ℙ(ak^ℙ)`
  have hxlt : x < 2 ^ 256 := by
    rw [← hx]
    exact (Cases.Zip2005.toAffine_lt (by simpa using Cases.Zip2005.leLimbsToNat_lt [a0, a1, a2, a3]) (by simpa using Cases.Zip2005.leLimbsToNat_lt [a4, a5, a6, a7])).1
  have hakx : ((leLimbsToNat [BitVec.ofNat 64 (x >>> (64 * 0)), BitVec.ofNat 64 (x >>> (64 * 1)),
      BitVec.ofNat 64 (x >>> (64 * 2)), BitVec.ofNat 64 (x >>> (64 * 3))] * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p : ℕ) : Fp) =
      Zip2005.extractP (specPt [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11]) := by
    have hx4 : leLimbsToNat [BitVec.ofNat 64 (x >>> (64 * 0)), BitVec.ofNat 64 (x >>> (64 * 1)),
        BitVec.ofNat 64 (x >>> (64 * 2)), BitVec.ofNat 64 (x >>> (64 * 3))] = x :=
      Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four hxlt
    have ex : ptX [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] = leLimbsToNat [a0, a1, a2, a3] := rfl
    have ey : ptY [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] = leLimbsToNat [a4, a5, a6, a7] := rfl
    have ez : ptZ [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11] = leLimbsToNat [a8, a9, a10, a11] := rfl
    rw [hx4]
    unfold Zip2005.extractP specPt jacXY
    rw [ex, ey, ez, hx]
  rw [hakx, fp_back _ _ hnv] at hcommit
  refine ⟨gd, hgv, hgr, fun pi α hrkpi hnfpi => ⟨(xi : Fp), cm, ?_⟩⟩
  unfold Zip2005.GuestChecks Zip2005.BindKeysSkNegate
  rw [modRP_cast xi hxp, hnfpi]
  exact ⟨hrkpi, ⟨by rw [hak, negate_if], rfl, rfl⟩, hrivk, hcommit, hne, hnote, hnf⟩

/-- The instance nullifier's and `ρ`'s words are canonical on the accepting path: `Nullifier::from_bytes`
and `parse_rho` are `unwrap`ped. -/
theorem accA2c_canon {s0 s1 s2 s3 neg v : Word} {n f rb sd w e rk ak gb : List Word}
    (h : AcceptA2c s0 s1 s2 s3 neg n f rb sd w e rk ak gb v) :
    leLimbsToNat f < Cases.Zip2005.Fp.p ∧ leLimbsToNat rb < Cases.Zip2005.Fp.p := by
  obtain ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _, ⟨_, hf, _⟩, _, _, _, _, _, _, _, hrb, _⟩, _⟩, _⟩ := h
  exact ⟨hf, hrb⟩

end Cases.Zip2005.Top
