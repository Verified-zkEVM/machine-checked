/-
  Cases.Zip2005.Limbs

  Little-endian limb lists as numbers: `leLimbsToNat` and `natToLeLimbs`, the
  two directions the accelerators are stated in.
-/

import RiscvZkvm.Rv64.ZiskAccel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel

theorem natToLeLimbs_succ (n x : Nat) :
    natToLeLimbs (n + 1) x = BitVec.ofNat 64 x :: natToLeLimbs n (x >>> 64) := by
  unfold natToLeLimbs
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Function.comp_def, List.cons.injEq, List.map_inj_left]
  refine ⟨by simp, fun i _ => ?_⟩
  rw [show 64 * (i + 1) = 64 + 64 * i by ring, Nat.shiftRight_add]

@[simp] theorem leLimbsToNat_cons (w : Word) (ws : List Word) :
    leLimbsToNat (w :: ws) = leLimbsToNat ws * 2 ^ 64 + w.toNat := rfl

@[simp] theorem leLimbsToNat_nil : leLimbsToNat [] = 0 := rfl

theorem leLimbsToNat_natToLeLimbs (n x : Nat) (h : x < 2 ^ (64 * n)) :
    leLimbsToNat (natToLeLimbs n x) = x := by
  induction n generalizing x with
  | zero => simp at h; subst h; rfl
  | succ n ih =>
    rw [natToLeLimbs_succ, leLimbsToNat_cons, ih]
    · rw [BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      omega
    · rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add]
      rw [show 64 * n + 64 = 64 * (n + 1) by ring]; exact h

theorem leLimbsToNat_lt (ws : List Word) : leLimbsToNat ws < 2 ^ (64 * ws.length) := by
  induction ws with
  | nil => simp
  | cons w ws ih =>
    rw [leLimbsToNat_cons, List.length_cons, show 64 * (ws.length + 1) = 64 * ws.length + 64 by ring,
      Nat.pow_add]
    have := w.isLt
    have : (leLimbsToNat ws + 1) * 2 ^ 64 ≤ 2 ^ (64 * ws.length) * 2 ^ 64 :=
      Nat.mul_le_mul_right _ ih
    nlinarith

@[simp] theorem length_natToLeLimbs (n x : Nat) : (natToLeLimbs n x).length = n := by
  simp [natToLeLimbs]

theorem natToLeLimbs_leLimbsToNat (ws : List Word) :
    natToLeLimbs ws.length (leLimbsToNat ws) = ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.length_cons, natToLeLimbs_succ, leLimbsToNat_cons, Nat.shiftRight_eq_div_pow]
    have hw := w.isLt
    have e : (leLimbsToNat ws * 2 ^ 64 + w.toNat) / 2 ^ 64 = leLimbsToNat ws := by omega
    rw [e, ih]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    omega

/-! ## Montgomery reduction -/

/-- Montgomery reduction's contract: `2^256·T = X + M·m` with `X, M < 2^256`
    gives `T ≤ m`, and the conditionally subtracted `T` is `X·R⁻¹ mod m`. -/
theorem redc_eq {m rInv X M T r : Nat} (hm : 0 < m) (hr : rInv * 2 ^ 256 % m = 1)
    (hT : 2 ^ 256 * T = X + M * m) (hX : X < 2 ^ 256) (hM : M < 2 ^ 256) (h1 : T < m → r = T) (h2 : m ≤ T → r + m = T) : r = X * rInv % m := by
  have hTp : T ≤ m := by
    by_contra h
    have : 2 ^ 256 * (m + 1) ≤ 2 ^ 256 * T := Nat.mul_le_mul_left _ (by omega)
    have : M * m ≤ 2 ^ 256 * m := Nat.mul_le_mul_right _ hM.le
    omega
  have hrT : r < m ∧ r % m = T % m := by
    by_cases h : T < m
    · rw [h1 h]; exact ⟨h, rfl⟩
    · have e := h2 (by omega)
      have : r = 0 := by omega
      subst this
      have : T = m := by omega
      subst this
      exact ⟨hm, by simp⟩
  have hx : X * rInv % m = T % m := by
    calc X * rInv % m = (X * rInv + M * rInv * m) % m := (Nat.add_mul_mod_self_right _ _ _).symm
      _ = (2 ^ 256 * T * rInv) % m := by rw [hT]; ring_nf
      _ = T * (rInv * 2 ^ 256 % m) % m := by rw [Nat.mul_mod_mod]; ring_nf
      _ = T % m := by rw [hr, Nat.mul_one]
  rw [hx, ← hrT.2, Nat.mod_eq_of_lt hrT.1]

/-- `redc_eq` for a double-width input (a full product `X < 2^256·m`): then
    `T < 2m`, which is all the conditional subtraction needs. -/
theorem redc_eq_wide {m rInv X M T r : Nat} (hm : 0 < m) (hr : rInv * 2 ^ 256 % m = 1)
    (hT : 2 ^ 256 * T = X + M * m) (hX : X < 2 ^ 256 * m) (hM : M < 2 ^ 256)
    (h1 : T < m → r = T) (h2 : m ≤ T → r + m = T) : r = X * rInv % m := by
  have hT2 : T < 2 * m := by
    by_contra h
    have : 2 ^ 256 * (2 * m) ≤ 2 ^ 256 * T := Nat.mul_le_mul_left _ (by omega)
    have : M * m < 2 ^ 256 * m := Nat.mul_lt_mul_of_pos_right hM hm
    omega
  have hrT : r < m ∧ r % m = T % m := by
    by_cases h : T < m
    · rw [h1 h]; exact ⟨h, rfl⟩
    · have e := h2 (by omega)
      refine ⟨by omega, ?_⟩
      rw [← e, Nat.add_mod_right]
  have hx : X * rInv % m = T % m := by
    calc X * rInv % m = (X * rInv + M * rInv * m) % m := (Nat.add_mul_mod_self_right _ _ _).symm
      _ = (2 ^ 256 * T * rInv) % m := by rw [hT]; ring_nf
      _ = T * (rInv * 2 ^ 256 % m) % m := by rw [Nat.mul_mod_mod]; ring_nf
      _ = T % m := by rw [hr, Nat.mul_one]
  rw [hx, ← hrT.2, Nat.mod_eq_of_lt hrT.1]

theorem list4_eta {l : List Word} (h : l.length = 4) : [l[0]!, l[1]!, l[2]!, l[3]!] = l := by
  match l, h with | [_, _, _, _], _ => rfl

theorem list9_eta {l : List Word} (h : l.length = 9) :
    [l[0]!, l[1]!, l[2]!, l[3]!, l[4]!, l[5]!, l[6]!, l[7]!, l[8]!] = l := by
  match l, h with | [_, _, _, _, _, _, _, _, _], _ => rfl

theorem list12_eta {l : List Word} (h : l.length = 12) :
    [l[0]!, l[1]!, l[2]!, l[3]!, l[4]!, l[5]!, l[6]!, l[7]!, l[8]!, l[9]!, l[10]!, l[11]!] = l := by
  match l, h with | [_, _, _, _, _, _, _, _, _, _, _, _], _ => rfl

end Cases.Zip2005
