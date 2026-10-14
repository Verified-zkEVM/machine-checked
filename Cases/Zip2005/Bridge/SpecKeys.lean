import Cases.Zip2005.Main.MainAccept
import Cases.Zip2005.Bridge.SpecNoteNf
import Cases.Zip2005.Precompile

/-!
# The spending key's derivations are the spec's

`nkW_val` (`H^nk`), `rivkW_val` (`H^rivk_legacy`), `askX_val` / `askR_val` (`H^ask`, negated
when `negate`'s bit is set: `neg_mont` is `Fq::neg`), and `askPt`: `derive_unchecked`'s point is
`[±ask] G` in the spec's group, for `sk` the 32 bytes of the key's words.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym Cases.Zip2005.B2b

set_option autoImplicit false

/-- `ToBase^Orchard(PRF^expand_sk([d]))` as the guest computes it, in Montgomery form. -/
theorem uniform_p (d s0 s1 s2 s3 : Word) :
    Fp.add
      (Fp.mul (leLimbsToNat [(prfExpandW d s0 s1 s2 s3)[0]!, (prfExpandW d s0 s1 s2 s3)[1]!,
        (prfExpandW d s0 s1 s2 s3)[2]!, (prfExpandW d s0 s1 s2 s3)[3]!]) Fp.R2)
      (Fp.mul (leLimbsToNat [(prfExpandW d s0 s1 s2 s3)[4]!, (prfExpandW d s0 s1 s2 s3)[5]!,
        (prfExpandW d s0 s1 s2 s3)[6]!, (prfExpandW d s0 s1 s2 s3)[7]!]) Fp.R3) =
    (Zip2005.toBaseOrchard (Zip2005.prfExpand (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))
      [UInt8.ofNat d.toNat])).val * Fp.R % Fp.p := by
  rw [Fp.from_uniform_eq, leLimbsToNat_halves (prfExpandW d s0 s1 s2 s3) (compress_length _ _ _ _ _ _), toBaseOrchard_val,
    Nat.mod_mul_mod, ← prfExpand33_eq, leos2ip_stateBytes]
  rfl

/-- `ToScalar^Orchard(PRF^expand_sk([d]))` as the guest computes it, in Montgomery form. -/
theorem uniform_q (d s0 s1 s2 s3 : Word) :
    Fq.add
      (Fq.mul (leLimbsToNat [(prfExpandW d s0 s1 s2 s3)[0]!, (prfExpandW d s0 s1 s2 s3)[1]!,
        (prfExpandW d s0 s1 s2 s3)[2]!, (prfExpandW d s0 s1 s2 s3)[3]!]) Fq.R2)
      (Fq.mul (leLimbsToNat [(prfExpandW d s0 s1 s2 s3)[4]!, (prfExpandW d s0 s1 s2 s3)[5]!,
        (prfExpandW d s0 s1 s2 s3)[6]!, (prfExpandW d s0 s1 s2 s3)[7]!]) Fq.R3) =
    (Zip2005.toScalarOrchard (Zip2005.prfExpand (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))
      [UInt8.ofNat d.toNat])).val * Fq.R % Fq.q := by
  rw [Fq.from_uniform_eq, leLimbsToNat_halves (prfExpandW d s0 s1 s2 s3) (compress_length _ _ _ _ _ _), toScalarOrchard_val,
    Nat.mod_mul_mod, ← prfExpand33_eq, leos2ip_stateBytes]
  rfl

theorem fqadd_lt (a b : ℕ) : Fq.add a b < 2 ^ 256 :=
  lt_trans (Nat.mod_lt _ Fq.q_pos) (by decide +kernel)

/-- `nk` from `sk` (`nkW`) is the Montgomery form of `H^nk(sk)`. -/
theorem nkW_val (s0 s1 s2 s3 : Word) :
    leLimbsToNat (nkW s0 s1 s2 s3) =
      (Zip2005.hNk (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))).val * Fp.R % Fp.p := by
  unfold nkW
  rw [Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four (lt_trans (Fp.add_lt _ _) Fp.p_lt), uniform_p]
  rfl

/-- `rivk` from `sk` (`rivkW`) is the Montgomery form of `H^rivk_legacy(sk)`. -/
theorem rivkW_val (s0 s1 s2 s3 : Word) :
    leLimbsToNat (rivkW s0 s1 s2 s3) =
      (Zip2005.hRivkLegacy (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))).val * Fq.R % Fq.q := by
  unfold rivkW
  rw [Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four (fqadd_lt _ _),
    uniform_q]
  rfl

/-- `ask` from `sk` (`askX`) is the Montgomery form of `H^ask(sk)`. -/
theorem askX_val (s0 s1 s2 s3 : Word) :
    askX s0 s1 s2 s3 =
      (Zip2005.hAsk (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))).val * Fq.R % Fq.q := by
  unfold askX
  rw [uniform_q]
  rfl

theorem castQ_mod (n : ℕ) : ((n % Fq.q : ℕ) : Zcash.Circuits.Fq) = (n : Zcash.Circuits.Fq) := by
  rw [← Fq.q_card, ZMod.natCast_mod]

theorem RrInv_q : ((Fq.R : ℕ) : Zcash.Circuits.Fq) * ((Fq.rInv : ℕ) : Zcash.Circuits.Fq) = 1 := by
  rw [← Nat.cast_mul, ← castQ_mod, show Fq.R * Fq.rInv % Fq.q = 1 by decide +kernel, Nat.cast_one]

/-- The negation `Fq::neg` computes (`0 - x` in Montgomery form) is the field negation. -/
theorem neg_mont (a : Zcash.Circuits.Fq) :
    Fq.sub 0 (a.val * Fq.R % Fq.q) * Fq.rInv % Fq.q = (-a).val := by
  have hlt : Fq.sub 0 (a.val * Fq.R % Fq.q) * Fq.rInv % Fq.q < Fq.q := Nat.mod_lt _ Fq.q_pos
  have hx : a.val * Fq.R % Fq.q ≤ Fq.q := le_of_lt (Nat.mod_lt _ Fq.q_pos)
  have key : ((Fq.sub 0 (a.val * Fq.R % Fq.q) * Fq.rInv % Fq.q : ℕ) : Zcash.Circuits.Fq) = -a := by
    rw [castQ_mod, Nat.cast_mul, Fq.sub, Nat.zero_add, castQ_mod, Nat.cast_sub hx, castQ_mod, Nat.cast_mul,
      ← Fq.q_card, ZMod.natCast_self, ZMod.natCast_zmod_val]
    linear_combination (-a) * RrInv_q
  have := congrArg ZMod.val key
  rwa [ZMod.val_cast_of_lt (show _ < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD by rw [← Fq.q_card]; exact hlt)]
    at this

/-- `ask`'s canonical limbs, negated when `neg ≠ 0`. -/
theorem askR_val (neg s0 s1 s2 s3 : Word) :
    leLimbsToNat (askR neg s0 s1 s2 s3) =
      (if neg = 0#64 then Zip2005.hAsk (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))
        else -Zip2005.hAsk (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))).val := by
  unfold askR askK
  rw [Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four (lt_trans (Nat.mod_lt _ Fq.q_pos) (by decide +kernel)),
    askX_val]
  split_ifs
  · rw [Fq.mont_back, Nat.mod_eq_of_lt (show _ < Fq.q by rw [← Fq.q_card]; exact ZMod.val_lt _)]
  · exact neg_mont _

/-- `derive_unchecked`'s point `[±ask] G` is the spec's scalar multiplication by `±H^ask(sk)`. -/
theorem askPt (neg s0 s1 s2 s3 : Word) (G : List Word) (hb : ptZ G ≠ 0 → Cases.Zip2005.SpecMul.ValidA (mulBase G))
    (hf : mulFacts G (skW (askR neg s0 s1 s2 s3))) (hP : (Cases.Zip2005.SpecMul.specPt G).Valid) :
    Cases.Zip2005.SpecMul.specPt (mulW G (skW (askR neg s0 s1 s2 s3))) =
      Zip2005.smul (if neg = 0#64 then Zip2005.hAsk (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat))
        else -Zip2005.hAsk (Zip2005.Blake2b.stateBytes ([s0, s1, s2, s3].map BitVec.toNat)))
        (Cases.Zip2005.SpecMul.specPt G) := by
  rw [Cases.Zip2005.SpecMul.specPt_mulW G _ hb hf hP]
  refine congrArg (fun a => Zip2005.smul a (Cases.Zip2005.SpecMul.specPt G)) ?_
  have hlt : leLimbsToNat (askR neg s0 s1 s2 s3) < Fq.q := by
    rw [askR_val, ← Fq.q_card]; exact ZMod.val_lt _
  unfold skW
  rw [Cases.Zip2005.Precompile.leLimbsToNat_natToLeLimbs_four (lt_trans (Fq.mul_lt _ _) (by decide +kernel)),
    Cases.Zip2005.Poseidon.Fq_mont_in_out _ hlt, askR_val, ZMod.natCast_zmod_val]

end Cases.Zip2005
