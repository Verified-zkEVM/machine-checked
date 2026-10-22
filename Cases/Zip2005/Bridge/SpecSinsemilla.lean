import Cases.Zip2005.Bridge.SinsemillaTable
import Cases.Zip2005.Precompile

/-!
# The guest's Sinsemilla chain is the spec's `hashToPoint`

`dec8` reads an eight-word affine point (canonical limbs) as a spec point. On points on the curve,
the guest's `incomplete_add` (`sinAdd`) is the spec's `⸭` (`sinAdd_spec`), one chunk step is the
spec's `step` (`sinStep_spec`), and the chunk fold from a domain point is `hashToPoint`
(`sinFold_hash`) for a table matching the generators, which `sTable` does (`sEntry_ok`, from
`Proof/Spec/SinsemillaTable.lean`).
-/

namespace Cases.Zip2005.SpecMul

open RiscvZkvm.Rv64 Cases.Zip2005.Precompile.Pallas MachineChecked.RiscV.Wire CompElliptic.CurveForms
open Zcash.Circuits (Fp Fq Point)

/-- The spec point an eight-word affine point (canonical limbs) denotes. -/
def dec8 (w : List Word) : Point Fp := ⟨((xOf w : ℕ) : Fp), ((yOf w : ℕ) : Fp)⟩

/-- An eight-word affine point on the curve, reduced. -/
def AffOk (w : List Word) : Prop :=
  w.length = 8 ∧ Accel.ptValid Sp1.pallasP 4 w = true ∧ OnCurve (xOf w) (yOf w)

theorem dec8_onCurve {w : List Word} (h : AffOk w) : (dec8 w).OnCurve := by
  rw [Point.onCurve_iff]; exact (onCurve_iff_sw _ _).mp h.2.2

theorem grp_dec8 (w : List Word) : grp (dec8 w) = (pointOf (xOf w) (yOf w) : G) :=
  (pointOf_eq_grp _ _).symm

theorem grp_add {P Q : Point Fp} (hP : P.Valid) (hQ : Q.Valid) : grp (P + Q) = grp P + grp Q :=
  ShortWeierstrass.toPt_add five_ne_zero ((Point.valid_iff P).mp hP) ((Point.valid_iff Q).mp hQ)

theorem natCast_inj_lt {a b : ℕ} (ha : a < Sp1.pallasP) (hb : b < Sp1.pallasP)
    (h : (a : Fp) = (b : Fp)) : a = b := by
  have ha' : a < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := ha
  have hb' : b < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := hb
  rw [← ZMod.val_cast_of_lt ha', ← ZMod.val_cast_of_lt hb', h]

/-- `sinAdd` (the guest's `incomplete_add`) is the spec's `⸭` on points on the curve. -/
theorem sinAdd_spec {a b : List Word} (ha : AffOk a) (hb : AffOk b) :
    (sinAdd a b).map dec8 = Point.incompleteAdd (dec8 a) (dec8 b) ∧
      ∀ c, sinAdd a b = some c → AffOk c := by
  have hpa := dec8_onCurve ha
  have hpb := dec8_onCurve hb
  unfold sinAdd Point.incompleteAdd
  have hxa := (ptValid_iff a).mp ha.2.1
  have hxb := (ptValid_iff b).mp hb.2.1
  by_cases hx : a.take 4 = b.take 4
  · rw [if_pos hx, if_pos (Or.inr (Or.inr (by simp only [dec8, xOf, hx])))]
    exact ⟨rfl, fun c h => by cases h⟩
  have hxne : xOf a ≠ xOf b := fun h => hx (limbs_eq_of_val (by simp [ha.1, hb.1]) h)
  have hxne' : (dec8 a).x ≠ (dec8 b).x := fun h => hxne (natCast_inj_lt hxa.1 hxb.1 h)
  rw [if_neg hx, if_neg (by
    rintro (h | h | h)
    · exact Point.ne_zero_of_onCurve hpa h
    · exact Point.ne_zero_of_onCurve hpb h
    · exact hxne' h)]
  obtain ⟨hl, hv, hc, hpt⟩ := curveAddL_spec a b ha.2.1 hb.2.1 hxne ha.2.2 hb.2.2
  refine ⟨?_, fun c h => by cases h; exact ⟨hl, hv, hc⟩⟩
  simp only [Option.map_some]
  congr 1
  apply grp_inj (Or.inl (dec8_onCurve ⟨hl, hv, hc⟩)) (Point.valid_add (Or.inl hpa) (Or.inl hpb))
  rw [grp_add (Or.inl hpa) (Or.inl hpb), grp_dec8, grp_dec8, grp_dec8]
  exact hpt

/-- One chunk: the guest's `(acc ⸭ S[m]) ⸭ acc` is the spec's `step`. -/
theorem sinStep_spec (T : List Word) (S : ℕ → Point Fp) (m : ℕ)
    (hT : AffOk (sEntryW T m) ∧ dec8 (sEntryW T m) = S m)
    (acc : Option (List Word)) (hacc : ∀ L, acc = some L → AffOk L) :
    (sinStep T acc m).map dec8 = (acc.map dec8).bind (Zcash.Circuits.Specs.Sinsemilla.step S m) ∧
      ∀ L, sinStep T acc m = some L → AffOk L := by
  cases acc with
  | none => exact ⟨rfl, fun L h => by cases h⟩
  | some a =>
    have ha := hacc a rfl
    obtain ⟨h1, h1ok⟩ := sinAdd_spec ha hT.1
    simp only [sinStep, Option.bind_some, Option.map_some, Zcash.Circuits.Specs.Sinsemilla.step,
      Point.doubleAndAdd]
    rw [← hT.2]
    cases ht : sinAdd a (sEntryW T m) with
    | none =>
      rw [ht, Option.map_none] at h1
      rw [← h1]
      exact ⟨rfl, fun L h => by cases h⟩
    | some t =>
      rw [ht, Option.map_some] at h1
      rw [← h1]
      have htok := h1ok t ht
      obtain ⟨h2, h2ok⟩ := sinAdd_spec htok ha
      exact ⟨by simpa using h2, fun L h => h2ok L (by simpa using h)⟩

/-- **The chunk fold is `hashToPoint`**, for a table whose entries (at the chunks used) are on the
curve and denote the spec's generators. -/
theorem sinFold_spec (T : List Word) (S : ℕ → Point Fp) :
    ∀ (ms : List ℕ), (∀ m ∈ ms, AffOk (sEntryW T m) ∧ dec8 (sEntryW T m) = S m) →
    ∀ (acc : Option (List Word)), (∀ L, acc = some L → AffOk L) →
      (sinFold T acc ms).map dec8 =
        ms.foldl (fun acc m => acc.bind (Zcash.Circuits.Specs.Sinsemilla.step S m)) (acc.map dec8) ∧
      ∀ L, sinFold T acc ms = some L → AffOk L
  | [], _, acc, hacc => ⟨rfl, hacc⟩
  | m :: ms, hT, acc, hacc => by
    obtain ⟨s1, s2⟩ := sinStep_spec T S m (hT m (List.mem_cons_self ..)) acc hacc
    have ih := sinFold_spec T S ms (fun m' hm => hT m' (List.mem_cons_of_mem _ hm)) _ s2
    simp only [sinFold, List.foldl_cons] at ih ⊢
    rw [← s1]
    exact ih

/-- `hashToPoint` from an eight-word domain point. -/
theorem sinFold_hash (T : List Word) (S : ℕ → Point Fp) (ms : List ℕ)
    (hT : ∀ m ∈ ms, AffOk (sEntryW T m) ∧ dec8 (sEntryW T m) = S m) (q : List Word) (hq : AffOk q) :
    (sinFold T (some q) ms).map dec8 = Zcash.Circuits.Specs.Sinsemilla.hashToPoint S (dec8 q) ms :=
  (sinFold_spec T S ms hT (some q) (fun L h => by cases h; exact hq)).1

/-- Entry `m < 1024` of the guest's table: on the curve, and the spec's generator `S m`. -/
theorem sEntry_ok (m : ℕ) (hm : m < 1024) :
    AffOk (sEntryW sTable m) ∧
      dec8 (sEntryW sTable m) = Zcash.Circuits.Specs.Sinsemilla.orchardGenerators.S m := by
  obtain ⟨hl, hx, hy⟩ := encode_decode
    (a := Accel.leLimbsToNat [sTable[8 * m]!, sTable[8 * m + 1]!, sTable[8 * m + 2]!, sTable[8 * m + 3]!] *
      Fp.rInv % Fp.p)
    (b := Accel.leLimbsToNat [sTable[8 * m + 4]!, sTable[8 * m + 5]!, sTable[8 * m + 6]!,
      sTable[8 * m + 7]!] * Fp.rInv % Fp.p)
    (Nat.mod_lt _ Fp.p_pos) (Nat.mod_lt _ Fp.p_pos)
  have hdec : dec8 (sEntryW sTable m) = Zcash.Circuits.Specs.Sinsemilla.orchardGenerators.S m := by
    rw [← sTable_gen m hm]
    unfold dec8 sEntryW tabPt
    rw [hx, hy]
  refine ⟨⟨hl, ?_, ?_⟩, hdec⟩
  · rw [ptValid_iff]; unfold sEntryW; rw [hx, hy]
    exact ⟨Nat.mod_lt _ Fp.p_pos, Nat.mod_lt _ Fp.p_pos⟩
  · have hon := Zcash.Circuits.Specs.Sinsemilla.orchardGenerators.S_onCurve
      (k := m) (by norm_num [Zcash.Circuits.Specs.K]; omega)
    rw [← hdec, Point.onCurve_iff] at hon
    exact (onCurve_iff_sw _ _).mpr hon

end Cases.Zip2005.SpecMul
