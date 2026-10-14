import Cases.Zip2005.Bridge.SpecGuest
import Cases.Zip2005.Precompile

/-!
# Segment A2's facts as `GuestStatement`, over the input words

`guest_of_a2` adds to `guest_of_a2c` what segment A2 learns before A2c: `ak`'s decoding by
`SpendValidatingKey::from_bytes`, the randomized key `ak + [α] G` and the instance `rk` it is
compared with, and the parses of `nk`, `rivk_ext` and `rivk`. The conclusion `GuestW` names only
the words A2 reads from the frame (the instance's `rk` and `nf`, the witness's bytes, `α` in
Montgomery form), so the segments before A2 can state it over the input.
-/

namespace Cases.Zip2005.Top

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.BridgeMul Cases.Zip2005.Poseidon
open Zcash.Circuits (Fp Fq Point)

set_option autoImplicit false

/-- **The guest's statement over the words segment A2 reads.** `kr`, `f`: the instance's `rk` and
`nf` bytes. `kb`, `nb`, `xb`, `ib`, `gb`, `rb`, `sd`: the witness's `ak`, `nk`, `rivk_ext`,
`rivk`, `g_d`, `ρ` and `rseed` bytes. `al`: `α` in Montgomery form. `s`: the key's bytes. `neg`:
`negate`'s low bit. `v`: the value. Each typed input decodes from its bytes, and the checks hold for
every instance with that `rk` and `nf`. -/
def GuestW (kr f kb nb xb ib gb rb sd al : List Word) (s0 s1 s2 s3 neg v : Word) : Prop :=
  ∃ (rkP akP : Point Fp) (nk : Fp) (rivkExt rivk : Fq) (gd : Point Fp) (ρ : Fp),
    rkP.Valid ∧ Zip2005.reprPNat rkP = leLimbsToNat kr ∧ leLimbsToNat f < Cases.Zip2005.Fp.p ∧
    akP.Valid ∧ Zip2005.reprPNat akP = leLimbsToNat kb ∧
    nk.val = leLimbsToNat nb ∧ rivkExt.val = leLimbsToNat xb ∧ rivk.val = leLimbsToNat ib ∧
    gd.Valid ∧ Zip2005.reprPNat gd = leLimbsToNat gb ∧ ρ.val = leLimbsToNat rb ∧
    ∀ pi : Zip2005.PrimaryInput, pi.rk = rkP → pi.nf = ((leLimbsToNat f : ℕ) : Fp) →
      Zip2005.GuestStatement pi (!(neg == 0#64)) (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))
        ((leLimbsToNat al * Cases.Zip2005.Fq.rInv % Cases.Zip2005.Fq.q : ℕ) : Fq) akP nk rivkExt rivk
        (Zip2005.Blake2b.stateBytes (sd.map BitVec.toNat)) gd v.toNat ρ

theorem fq_mul_R2 (a : ℕ) : Cases.Zip2005.Fq.mul a Cases.Zip2005.Fq.R2 = a * Cases.Zip2005.Fq.R % Cases.Zip2005.Fq.q := by
  have h1 : Cases.Zip2005.Fq.R2 * Cases.Zip2005.Fq.rInv % Cases.Zip2005.Fq.q = Cases.Zip2005.Fq.R % Cases.Zip2005.Fq.q := by decide +kernel
  unfold Cases.Zip2005.Fq.mul
  rw [Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, h1, ← Nat.mul_mod]

/-- Two Montgomery forms of canonical integers agree only if the integers do. -/
theorem fp_mont_inj {a b : ℕ} (ha : a < Cases.Zip2005.Fp.p) (hb : b < Cases.Zip2005.Fp.p)
    (h : a * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p = b * Cases.Zip2005.Fp.R % Cases.Zip2005.Fp.p) : a = b := by
  have := congrArg (fun n => n * Cases.Zip2005.Fp.rInv % Cases.Zip2005.Fp.p) h
  simp only [Cases.Zip2005.Fp.mont_back, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact this

theorem fq_mont_inj {a b : ℕ} (ha : a < Cases.Zip2005.Fq.q) (hb : b < Cases.Zip2005.Fq.q)
    (h : a * Cases.Zip2005.Fq.R % Cases.Zip2005.Fq.q = b * Cases.Zip2005.Fq.R % Cases.Zip2005.Fq.q) : a = b := by
  have := congrArg (fun n => n * Cases.Zip2005.Fq.rInv % Cases.Zip2005.Fq.q) h
  simp only [Cases.Zip2005.Fq.mont_back, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact this

theorem fq_natToLe_val (y : ℕ) (hy : y < Cases.Zip2005.Fq.q) : leLimbsToNat (natToLeLimbs 4 y) = y :=
  Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four (lt_trans hy (by decide +kernel))

/-- **Segment A2's accepting path is `GuestW`.** `c`: `ak`'s cells as `SpendValidatingKey::from_bytes`
decoded them from `kb`. `g`, `al`: the basepoint and `α` of the randomization `ak + [α] G`. `u`: the
instance `rk` decoded from `kr`, which the run compared with the randomized key's bytes (`hb4`). `a`, `x`: `ak` decoded
again, and its affine `x`, as segment A2r passes them to A2c. `n`, `e`, `k`: the parsed `nk`,
`rivk_ext` and `rivk`. -/
theorem guest_of_a2 (s0 s1 s2 s3 neg v : Word)
    (kr0 kr1 kr2 kr3 f0 f1 f2 f3 kb0 kb1 kb2 kb3 nb0 nb1 nb2 nb3 xb0 xb1 xb2 xb3 ib0 ib1 ib2 ib3
      gb0 gb1 gb2 gb3 rb0 rb1 rb2 rb3 d0 d1 d2 d3 al0 al1 al2 al3 : Word)
    (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 : Word)
    (u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 : Word)
    (n0 n1 n2 n3 e0 e1 e2 e3 k0 k1 k2 k3 : Word) (x : ℕ)
    (hsv : Cases.Zip2005.FromBytesPost kb0 kb1 kb2 kb3 (leLimbsToNat [c0, c1, c2, c3]) (leLimbsToNat [c4, c5, c6, c7]) 1#8)
    (hsvz : leLimbsToNat [c8, c9, c10, c11] =
      if leLimbsToNat [c0, c1, c2, c3] = 0 ∧ leLimbsToNat [c4, c5, c6, c7] = 0 then 0 else Cases.Zip2005.Fp.R)
    (hmsb : kb3.msb = false)
    (hG : Cases.Zip2005.FromBytesPost 10167565023098292579#64 900452621665476876#64 4291112941855392863#64
      13210504334354273798#64 (leLimbsToNat [g0, g1, g2, g3]) (leLimbsToNat [g4, g5, g6, g7]) 1#8)
    (hGz : leLimbsToNat [g8, g9, g10, g11] =
      if leLimbsToNat [g0, g1, g2, g3] = 0 ∧ leLimbsToNat [g4, g5, g6, g7] = 0 then 0 else Cases.Zip2005.Fp.R)
    (hm : mulFacts [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] [al0, al1, al2, al3])
    (hb4 : toBytesW (rkJ c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
        (mulW [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11] [al0, al1, al2, al3])) = [kr0, kr1, kr2, kr3])
    (hR : Cases.Zip2005.FromBytesPost kr0 kr1 kr2 kr3 (leLimbsToNat [u0, u1, u2, u3]) (leLimbsToNat [u4, u5, u6, u7]) 1#8)
    (hRz : leLimbsToNat [u8, u9, u10, u11] =
      if leLimbsToNat [u0, u1, u2, u3] = 0 ∧ leLimbsToNat [u4, u5, u6, u7] = 0 then 0 else Cases.Zip2005.Fp.R)
    (hfa : Cases.Zip2005.FromBytesPost kb0 kb1 kb2 kb3 (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [a4, a5, a6, a7]) 1#8)
    (hza : leLimbsToNat [a8, a9, a10, a11] =
      if leLimbsToNat [a0, a1, a2, a3] = 0 ∧ leLimbsToNat [a4, a5, a6, a7] = 0 then 0 else Cases.Zip2005.Fp.R)
    (hx : (Cases.Zip2005.Fp.toAffine (leLimbsToNat [a0, a1, a2, a3]) (leLimbsToNat [a4, a5, a6, a7])
      (leLimbsToNat [a8, a9, a10, a11])).1 = x)
    (hA : AcceptA2c s0 s1 s2 s3 neg [n0, n1, n2, n3] [f0, f1, f2, f3] [rb0, rb1, rb2, rb3] [d0, d1, d2, d3]
      [kb0, kb1, kb2, kb3] [e0, e1, e2, e3] [k0, k1, k2, k3]
      [BitVec.ofNat 64 (x >>> (64 * 0)), BitVec.ofNat 64 (x >>> (64 * 1)), BitVec.ofNat 64 (x >>> (64 * 2)),
        BitVec.ofNat 64 (x >>> (64 * 3))] [gb0, gb1, gb2, gb3] v)
    (hn : leLimbsToNat [n0, n1, n2, n3] = Cases.Zip2005.Fp.mul (leLimbsToNat [nb0, nb1, nb2, nb3]) Cases.Zip2005.Fp.R2)
    (hnb : leLimbsToNat [nb0, nb1, nb2, nb3] < Cases.Zip2005.Fp.p)
    (hxb : leLimbsToNat [xb0, xb1, xb2, xb3] < Cases.Zip2005.Fq.q)
    (he : [e0, e1, e2, e3] = natToLeLimbs 4 (Cases.Zip2005.Fq.mul (leLimbsToNat [xb0, xb1, xb2, xb3]) Cases.Zip2005.Fq.R2))
    (hib : leLimbsToNat [ib0, ib1, ib2, ib3] < Cases.Zip2005.Fq.q)
    (hk : [k0, k1, k2, k3] = natToLeLimbs 4 (Cases.Zip2005.Fq.mul (leLimbsToNat [ib0, ib1, ib2, ib3]) Cases.Zip2005.Fq.R2)) :
    GuestW [kr0, kr1, kr2, kr3] [f0, f1, f2, f3] [kb0, kb1, kb2, kb3] [nb0, nb1, nb2, nb3]
      [xb0, xb1, xb2, xb3] [ib0, ib1, ib2, ib3] [gb0, gb1, gb2, gb3] [rb0, rb1, rb2, rb3]
      [d0, d1, d2, d3] [al0, al1, al2, al3] s0 s1 s2 s3 neg v := by
  have ⟨hfc, hrb⟩ := accA2c_canon hA
  have hnW := hA.2.1
  have heW := hA.2.2.1
  obtain ⟨gd, hgv, hgr, hall⟩ := guest_of_a2c s0 s1 s2 s3 neg [n0, n1, n2, n3] [f0, f1, f2, f3]
    [rb0, rb1, rb2, rb3] [e0, e1, e2, e3] d0 d1 d2 d3 kb0 kb1 kb2 kb3 k0 k1 k2 k3 gb0 gb1 gb2 gb3 v
    a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 x hfa hza hx hmsb hA
  -- the two decodings of `kb` are one point
  obtain ⟨hJc, hcv, hcr⟩ := fb_decode _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hsv hsvz
  obtain ⟨-, hav, har⟩ := fb_decode _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hfa hza
  have hca := reprPNat_inj hcv hav (hcr.trans har.symm)
  -- the instance `rk` is `ak + [α] G`
  obtain ⟨-, huv, hur⟩ := fb_decode _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR hRz
  have hrk := rk_spec c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11
    u0 u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 kr0 kr1 kr2 kr3 [al0, al1, al2, al3] hJc hG hGz hm hR hRz
    (by rw [hb4])
  rw [hca] at hrk
  -- the parsed keys, read back
  have hnk : (Zip2005.hNk (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))).val =
      leLimbsToNat [nb0, nb1, nb2, nb3] := by
    have h1 := nkW_val s0 s1 s2 s3
    have hlt : (Zip2005.hNk (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))).val <
        Cases.Zip2005.Fp.p := ZMod.val_lt _
    rw [← hnW, hn, fp_mul_R2] at h1
    exact (fp_mont_inj hnb hlt h1).symm
  have hrx : (Zip2005.hRivkLegacy (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))).val =
      leLimbsToNat [xb0, xb1, xb2, xb3] := by
    have h1 := rivkW_val s0 s1 s2 s3
    have hlt : (Zip2005.hRivkLegacy (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))).val <
        Cases.Zip2005.Fq.q := ZMod.val_lt _
    rw [← heW, he, fq_natToLe_val _ (by rw [fq_mul_R2]; exact Nat.mod_lt _ Cases.Zip2005.Fq.q_pos), fq_mul_R2] at h1
    exact (fq_mont_inj hxb hlt h1).symm
  have hri : ((leLimbsToNat [k0, k1, k2, k3] * Cases.Zip2005.Fq.rInv % Cases.Zip2005.Fq.q : ℕ) : Fq).val =
      leLimbsToNat [ib0, ib1, ib2, ib3] := by
    rw [hk, fq_natToLe_val _ (by rw [fq_mul_R2]; exact Nat.mod_lt _ Cases.Zip2005.Fq.q_pos), fq_mul_R2,
      Cases.Zip2005.Fq.mont_back, Nat.mod_eq_of_lt hib, ZMod.val_natCast, Cases.Zip2005.Fq.q_card, Nat.mod_eq_of_lt hib]
  refine ⟨_, _, _, _, ((leLimbsToNat [k0, k1, k2, k3] * Cases.Zip2005.Fq.rInv % Cases.Zip2005.Fq.q : ℕ) : Fq), gd,
    ((leLimbsToNat [rb0, rb1, rb2, rb3] : ℕ) : Fp), huv, hur, hfc, hav, har, hnk, hrx, hri, hgv, hgr, ?_, ?_⟩
  · rw [ZMod.val_natCast, Fp.p_card, Nat.mod_eq_of_lt hrb]
  · intro pi hpi hnf
    exact hall pi _ (hpi.trans hrk) hnf

end Cases.Zip2005.Top
