/-
  MachineChecked.ARM.Lift.Sound.Bitfield

  The lift of AArch64 against arm64-semantics: the bit fields (`ubfm`, `sbfm`, `bfm`), which
  are the shifts by a constant, the extensions, and the extractions and insertions of a field.

  The machine's `evalBitfield` computes with masks made from natural numbers; the lift shifts.
  Each of the six lemmas (three operations at two widths) names the immediates as bitvectors
  and leaves an equation of bitvectors, with shifts by variable amounts, to `bv_decide`.

  ## Main results

  * `ubfm64`, `sbfm64`, `bfm64`, `ubfm32`, `sbfm32`, `bfm32`: the value of a field
  * `bitfield_sound`: the instruction
  * `extr_sound`: `extr`, the extraction from a pair of registers
-/

import MachineChecked.ARM.Lift.Sound.Basic

namespace MachineChecked.ARM.Lift

open Lprog Lprog.ARM Lprog.Build
open Arm64 (Instr RegWidth MemWidth)

variable {regs : Reg → BitVec 64} {m : Arm64.Memory} {s : Arm64.State}

/-- A mask of the low bits, by a shift. -/
theorem mask_eq (k : BitVec 64) (hk : k.toNat ≤ 64) :
    BitVec.ofNat 64 (2 ^ k.toNat - 1) = (1#64 <<< k) - 1#64 := by
  apply BitVec.eq_of_toNat_eq
  rcases Nat.lt_or_eq_of_le hk with h | h
  · have : 2 ^ k.toNat < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) h
    have h1 : 0 < 2 ^ k.toNat := Nat.two_pow_pos _
    simp [BitVec.toNat_sub, Nat.shiftLeft_eq, Nat.mod_eq_of_lt this]
    omega
  · simp [h]

theorem mask_eq' (k : BitVec 64) (hk : k.toNat ≤ 64) :
    BitVec.ofNat 64 (1 <<< k.toNat - 1) = (1#64 <<< k) - 1#64 := by
  rw [← mask_eq k hk, Nat.shiftLeft_eq, Nat.one_mul]

@[simp] theorem eval_ones (n : Nat) : (ones n : E).eval regs = BitVec.ofNat 64 (2 ^ n - 1) := rfl

theorem bfop_beq : ∀ a b : Arm64.BitfieldOp, (a == b) = decide (a = b) := by
  intro a b; cases a <;> cases b <;> rfl

/-- The 64-bit bit fields, unsigned. -/
theorem ubfm64 (x d : BitVec 64) {immr imms : Nat} (hr : immr < 64) (hi : imms < 64) :
    (let p : Nat × Nat × Nat :=
        if imms ≥ immr then (imms - immr + 1, immr, 0) else (imms + 1, 0, 64 - immr);
      ((x >>> (p.2.1 % 2 ^ 64)) &&& BitVec.ofNat 64 (2 ^ p.1 - 1)) <<< (p.2.2 % 2 ^ 64)) =
      Arm64.evalBitfield .W64 .UBFM d x immr imms := by
  obtain ⟨r, rfl, hr'⟩ : ∃ r : BitVec 64, immr = r.toNat ∧ r < 64#64 :=
    ⟨BitVec.ofNat 64 immr, by simp; omega, by rw [BitVec.lt_def]; simp; omega⟩
  obtain ⟨i, rfl, hi'⟩ : ∃ i : BitVec 64, imms = i.toNat ∧ i < 64#64 :=
    ⟨BitVec.ofNat 64 imms, by simp; omega, by rw [BitVec.lt_def]; simp; omega⟩
  simp only [Arm64.evalBitfield, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hi, bfop_beq]
  by_cases hge : i.toNat ≥ r.toNat
  · by_cases h63 : i.toNat = 63
    · obtain ⟨L, hL, eL⟩ : ∃ L : BitVec 64, L = i - r + 1#64 ∧ i.toNat - r.toNat + 1 = L.toNat :=
        ⟨_, rfl, by bv_omega⟩
      have hi63 : i = 63#64 := by bv_omega
      simp only [hge, ite_true, eL, mask_eq L (by omega), Nat.mod_eq_of_lt r.isLt]
      simp [h63]
      bv_decide
    · have hgt : ¬ r.toNat > i.toNat := by omega
      simp [hge, h63, hgt, Nat.mod_eq_of_lt r.isLt, Nat.shiftLeft_eq]
  · have h63 : ¬ i.toNat = 63 := by omega
    have hgt : r.toNat > i.toNat := by omega
    have e64 : (64 - r.toNat) % 18446744073709551616 = 64 - r.toNat := Nat.mod_eq_of_lt (by omega)
    by_cases h1 : i.toNat + 1 = r.toNat
    · obtain ⟨P, hP, eP⟩ : ∃ P : BitVec 64, P = 64#64 - r ∧ 64 - r.toNat = P.toNat :=
        ⟨_, rfl, by bv_omega⟩
      have hr64 : ¬ r.toNat = 64 := by omega
      simp only [hge, ite_false, h1, mask_eq r (by omega), eP]
      simp [hgt, hr64, Nat.mod_eq_of_lt P.isLt]
      bv_decide
    · simp [hge, h63, h1, Nat.shiftLeft_eq, e64]

/-- The 64-bit bit fields, inserted. -/
theorem bfm64 (x d : BitVec 64) {immr imms : Nat} (hr : immr < 64) (hi : imms < 64) :
    (let p : Nat × Nat × Nat :=
        if imms ≥ immr then (imms - immr + 1, immr, 0) else (imms + 1, 0, 64 - immr);
      (d &&& ~~~(BitVec.ofNat 64 (2 ^ p.1 - 1) <<< (p.2.2 % 2 ^ 64))) |||
        ((x >>> (p.2.1 % 2 ^ 64)) &&& BitVec.ofNat 64 (2 ^ p.1 - 1)) <<< (p.2.2 % 2 ^ 64)) =
      Arm64.evalBitfield .W64 .BFM d x immr imms := by
  have e64 : (64 - immr) % 18446744073709551616 = 64 - immr := Nat.mod_eq_of_lt (by omega)
  have er : immr % 18446744073709551616 = immr := Nat.mod_eq_of_lt (by omega)
  simp only [Arm64.evalBitfield, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hi, bfop_beq]
  by_cases hge : imms ≥ immr <;> simp [hge, Nat.shiftLeft_eq, e64, er]

/-- The 64-bit bit fields, signed. -/
theorem sbfm64 (x d : BitVec 64) {immr imms : Nat} (hr : immr < 64) (hi : imms < 64) :
    (let p : Nat × Nat × Nat :=
        if imms ≥ immr then (imms - immr + 1, immr, 0) else (imms + 1, 0, 64 - immr);
      (((x >>> (p.2.1 % 2 ^ 64)) <<< ((64 - p.1) % 2 ^ 64)).sshiftRight ((64 - p.1) % 2 ^ 64))
        <<< (p.2.2 % 2 ^ 64)) =
      Arm64.evalBitfield .W64 .SBFM d x immr imms := by
  obtain ⟨r, rfl, hr'⟩ : ∃ r : BitVec 64, immr = r.toNat ∧ r < 64#64 :=
    ⟨BitVec.ofNat 64 immr, by simp; omega, by rw [BitVec.lt_def]; simp; omega⟩
  obtain ⟨i, rfl, hi'⟩ : ∃ i : BitVec 64, imms = i.toNat ∧ i < 64#64 :=
    ⟨BitVec.ofNat 64 imms, by simp; omega, by rw [BitVec.lt_def]; simp; omega⟩
  simp only [Arm64.evalBitfield, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hi, bfop_beq]
  have hb : x.getLsbD i.toNat = (x >>> i).getLsbD 0 := by simp
  by_cases hge : i.toNat ≥ r.toNat
  · obtain ⟨L, hL, eL⟩ : ∃ L : BitVec 64, L = i - r + 1#64 ∧ i.toNat - r.toNat + 1 = L.toNat :=
      ⟨_, rfl, by bv_omega⟩
    obtain ⟨K, hK, eK⟩ : ∃ K : BitVec 64, K = 64#64 - L ∧ 64 - L.toNat = K.toNat :=
      ⟨_, rfl, by bv_omega⟩
    by_cases h63 : i.toNat = 63
    · have hi63 : i = 63#64 := by bv_omega
      simp only [hge, ite_true, eL, eK, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt K.isLt]
      simp [h63]
      bv_decide
    · simp only [hge, ite_true, eL, eK, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt K.isLt]
      have hge' : r ≤ i := by bv_omega
      simp [h63]
      rw [mask_eq' L (by omega), hb]
      bv_decide
  · have h63 : ¬ i.toNat = 63 := by omega
    obtain ⟨L, hL, eL⟩ : ∃ L : BitVec 64, L = i + 1#64 ∧ i.toNat + 1 = L.toNat :=
      ⟨_, rfl, by bv_omega⟩
    obtain ⟨K, hK, eK⟩ : ∃ K : BitVec 64, K = 64#64 - L ∧ 64 - L.toNat = K.toNat :=
      ⟨_, rfl, by bv_omega⟩
    obtain ⟨P, hP, eP⟩ : ∃ P : BitVec 64, P = 64#64 - r ∧ 64 - r.toNat = P.toNat :=
      ⟨_, rfl, by bv_omega⟩
    obtain ⟨Q, hQ, eQ⟩ : ∃ Q : BitVec 64, Q = P + L ∧ P.toNat + L.toNat = Q.toNat :=
      ⟨_, rfl, by bv_omega⟩
    have hlt' : i < r := by bv_omega
    have hL64 : ¬ L.toNat = 64 := by omega
    simp only [hge, ite_false, eL, eK, eP, eQ, Nat.mod_eq_of_lt P.isLt, Nat.mod_eq_of_lt K.isLt]
    by_cases hq : 64 ≤ Q.toNat
    · have hq' : 64#64 ≤ Q := by bv_omega
      simp [hL64, hq]
      rw [mask_eq' L (by omega)]
      bv_decide
    · have hq' : Q < 64#64 := by bv_omega
      simp [hL64, hq]
      rw [mask_eq' L (by omega), mask_eq' Q (by omega), hb]
      bv_decide

theorem shl1 (n : Nat) : Nat.shiftLeft 1 n = 2 ^ n := by
  show 1 <<< n = 2 ^ n
  rw [Nat.shiftLeft_eq, Nat.one_mul]

/-- The 32-bit bit fields, unsigned. -/
theorem ubfm32 (x d : BitVec 64) (hx : x = (x.setWidth 32).setWidth 64) {immr imms : Nat}
    (hr : immr < 32) (hi : imms < 32) :
    (let p : Nat × Nat × Nat :=
        if imms ≥ immr then (imms - immr + 1, immr, 0) else (imms + 1, 0, 32 - immr);
      ((x >>> (p.2.1 % 2 ^ 64)) &&& BitVec.ofNat 64 (2 ^ p.1 - 1)) <<< (p.2.2 % 2 ^ 64)) =
      ((Arm64.evalBitfield .W32 .UBFM d x immr imms).truncate 32).zeroExtend 64 := by
  obtain ⟨r, rfl, hr'⟩ : ∃ r : BitVec 64, immr = r.toNat ∧ r < 32#64 :=
    ⟨BitVec.ofNat 64 immr, by simp; omega, by rw [BitVec.lt_def]; simp; omega⟩
  obtain ⟨i, rfl, hi'⟩ : ∃ i : BitVec 64, imms = i.toNat ∧ i < 32#64 :=
    ⟨BitVec.ofNat 64 imms, by simp; omega, by rw [BitVec.lt_def]; simp; omega⟩
  simp only [Arm64.evalBitfield, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hi, bfop_beq, shl1]
  by_cases hge : i.toNat ≥ r.toNat
  · obtain ⟨L, hL, eL⟩ : ∃ L : BitVec 64, L = i - r + 1#64 ∧ i.toNat - r.toNat + 1 = L.toNat :=
      ⟨_, rfl, by bv_omega⟩
    have hge' : r ≤ i := by bv_omega
    have hgt : ¬ r.toNat > i.toNat := by omega
    have hM := mask_eq L (by omega)
    simp only [hge, ite_true, eL, Nat.mod_eq_of_lt r.isLt]
    generalize BitVec.ofNat 64 (2 ^ L.toNat - 1) = M at hM ⊢
    by_cases h31 : i.toNat = 31
    · have hi31 : i = 31#64 := by bv_omega
      simp [h31]
      bv_decide
    · have hi31 : i ≠ 31#64 := by bv_omega
      simp [h31, hgt]
      bv_decide
  · have h31 : ¬ i.toNat = 31 := by omega
    have hgt : r.toNat > i.toNat := by omega
    have hlt' : i < r := by bv_omega
    obtain ⟨L, hL, eL⟩ : ∃ L : BitVec 64, L = i + 1#64 ∧ i.toNat + 1 = L.toNat :=
      ⟨_, rfl, by bv_omega⟩
    obtain ⟨P, hP, eP⟩ : ∃ P : BitVec 64, P = 32#64 - r ∧ 32 - r.toNat = P.toNat :=
      ⟨_, rfl, by bv_omega⟩
    have hL32 : ¬ L.toNat = 32 := by omega
    have hM := mask_eq L (by omega)
    simp only [hge, ite_false, eL, eP, Nat.mod_eq_of_lt P.isLt]
    generalize BitVec.ofNat 64 (2 ^ L.toNat - 1) = M at hM ⊢
    by_cases h1 : L.toNat = r.toNat
    · have h1' : L = r := by bv_omega
      have hr32 : ¬ r.toNat = 32 := by omega
      simp [hr32, hgt, h1]
      bv_decide
    · have h1' : L ≠ r := by bv_omega
      simp [hL32, hgt, h1]
      bv_decide

/-- The 32-bit bit fields, inserted. -/
theorem bfm32 (x d : BitVec 64) (hx : x = (x.setWidth 32).setWidth 64)
    (hd : d = (d.setWidth 32).setWidth 64) {immr imms : Nat} (hr : immr < 32) (hi : imms < 32) :
    (let p : Nat × Nat × Nat :=
        if imms ≥ immr then (imms - immr + 1, immr, 0) else (imms + 1, 0, 32 - immr);
      (d &&& ((~~~(BitVec.ofNat 64 (2 ^ p.1 - 1) <<< (p.2.2 % 2 ^ 64))).setWidth 32).setWidth 64)
        ||| ((x >>> (p.2.1 % 2 ^ 64)) &&& BitVec.ofNat 64 (2 ^ p.1 - 1)) <<< (p.2.2 % 2 ^ 64)) =
      ((Arm64.evalBitfield .W32 .BFM d x immr imms).truncate 32).zeroExtend 64 := by
  obtain ⟨r, rfl, hr'⟩ : ∃ r : BitVec 64, immr = r.toNat ∧ r < 32#64 :=
    ⟨BitVec.ofNat 64 immr, by simp; omega, by rw [BitVec.lt_def]; simp; omega⟩
  obtain ⟨i, rfl, hi'⟩ : ∃ i : BitVec 64, imms = i.toNat ∧ i < 32#64 :=
    ⟨BitVec.ofNat 64 imms, by simp; omega, by rw [BitVec.lt_def]; simp; omega⟩
  simp only [Arm64.evalBitfield, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hi, bfop_beq, shl1]
  by_cases hge : i.toNat ≥ r.toNat
  · obtain ⟨L, hL, eL⟩ : ∃ L : BitVec 64, L = i - r + 1#64 ∧ i.toNat - r.toNat + 1 = L.toNat :=
      ⟨_, rfl, by bv_omega⟩
    have hge' : r ≤ i := by bv_omega
    have hM := mask_eq L (by omega)
    simp only [hge, ite_true, eL, Nat.mod_eq_of_lt r.isLt]
    generalize BitVec.ofNat 64 (2 ^ L.toNat - 1) = M at hM ⊢
    simp
    bv_decide
  · have hlt' : i < r := by bv_omega
    obtain ⟨L, hL, eL⟩ : ∃ L : BitVec 64, L = i + 1#64 ∧ i.toNat + 1 = L.toNat :=
      ⟨_, rfl, by bv_omega⟩
    obtain ⟨P, hP, eP⟩ : ∃ P : BitVec 64, P = 32#64 - r ∧ 32 - r.toNat = P.toNat :=
      ⟨_, rfl, by bv_omega⟩
    have hM := mask_eq L (by omega)
    simp only [hge, ite_false, eL, eP, Nat.mod_eq_of_lt P.isLt]
    generalize BitVec.ofNat 64 (2 ^ L.toNat - 1) = M at hM ⊢
    simp
    bv_decide

/-- The 32-bit bit fields, signed. -/
theorem sbfm32 (x d : BitVec 64) (hx : x = (x.setWidth 32).setWidth 64) {immr imms : Nat}
    (hr : immr < 32) (hi : imms < 32) :
    (let p : Nat × Nat × Nat :=
        if imms ≥ immr then (imms - immr + 1, immr, 0) else (imms + 1, 0, 32 - immr);
      (((((x >>> (p.2.1 % 2 ^ 64)) <<< ((64 - p.1) % 2 ^ 64)).sshiftRight ((64 - p.1) % 2 ^ 64))
        <<< (p.2.2 % 2 ^ 64)).setWidth 32).setWidth 64) =
      ((Arm64.evalBitfield .W32 .SBFM d x immr imms).truncate 32).zeroExtend 64 := by
  obtain ⟨r, rfl, hr'⟩ : ∃ r : BitVec 64, immr = r.toNat ∧ r < 32#64 :=
    ⟨BitVec.ofNat 64 immr, by simp; omega, by rw [BitVec.lt_def]; simp; omega⟩
  obtain ⟨i, rfl, hi'⟩ : ∃ i : BitVec 64, imms = i.toNat ∧ i < 32#64 :=
    ⟨BitVec.ofNat 64 imms, by simp; omega, by rw [BitVec.lt_def]; simp; omega⟩
  simp only [Arm64.evalBitfield, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hi, bfop_beq, shl1]
  have hi64 : i.toNat < 64 := by omega
  have hb : x[i.toNat] = (x >>> i).getLsbD 0 := by
    simp [← BitVec.getLsbD_eq_getElem]
  by_cases hge : i.toNat ≥ r.toNat
  · obtain ⟨L, hL, eL⟩ : ∃ L : BitVec 64, L = i - r + 1#64 ∧ i.toNat - r.toNat + 1 = L.toNat :=
      ⟨_, rfl, by bv_omega⟩
    obtain ⟨K, hK, eK⟩ : ∃ K : BitVec 64, K = 64#64 - L ∧ 64 - L.toNat = K.toNat :=
      ⟨_, rfl, by bv_omega⟩
    have hge' : r ≤ i := by bv_omega
    have hM := mask_eq L (by omega)
    simp only [hge, ite_true, eL, eK, Nat.mod_eq_of_lt r.isLt, Nat.mod_eq_of_lt K.isLt]
    generalize BitVec.ofNat 64 (2 ^ L.toNat - 1) = M at hM ⊢
    by_cases h31 : i.toNat = 31
    · have hi31 : i = 31#64 := by bv_omega
      simp [h31]
      bv_decide
    · have hi31 : i ≠ 31#64 := by bv_omega
      simp [h31, hi, hi64]
      rw [hb]
      bv_decide
  · have h31 : ¬ i.toNat = 31 := by omega
    have hlt' : i < r := by bv_omega
    obtain ⟨L, hL, eL⟩ : ∃ L : BitVec 64, L = i + 1#64 ∧ i.toNat + 1 = L.toNat :=
      ⟨_, rfl, by bv_omega⟩
    obtain ⟨K, hK, eK⟩ : ∃ K : BitVec 64, K = 64#64 - L ∧ 64 - L.toNat = K.toNat :=
      ⟨_, rfl, by bv_omega⟩
    obtain ⟨P, hP, eP⟩ : ∃ P : BitVec 64, P = 32#64 - r ∧ 32 - r.toNat = P.toNat :=
      ⟨_, rfl, by bv_omega⟩
    obtain ⟨Q, hQ, eQ⟩ : ∃ Q : BitVec 64, Q = P + L ∧ P.toNat + L.toNat = Q.toNat :=
      ⟨_, rfl, by bv_omega⟩
    have hL32 : ¬ L.toNat = 32 := by omega
    have hq : ¬ 64 ≤ Q.toNat := by omega
    have hM := mask_eq L (by omega)
    have hN := mask_eq Q (by omega)
    simp only [hge, ite_false, eL, eK, eP, eQ, Nat.mod_eq_of_lt P.isLt, Nat.mod_eq_of_lt K.isLt]
    generalize BitVec.ofNat 64 (2 ^ L.toNat - 1) = M at hM ⊢
    generalize BitVec.ofNat 64 (2 ^ Q.toNat - 1) = N at hN ⊢
    simp [hL32, hq, hi, hi64]
    rw [hb]
    bv_decide

/-- **`ubfm`, `sbfm`, `bfm`**: the immediates are below the width. -/
theorem bitfield_sound (h : Agree regs m s) (pc : BitVec 64) (w : RegWidth)
    (op : Arm64.BitfieldOp) {dst rn : Arm64.Reg} (hd : Wf dst) (hn : Wf rn) {immr imms : Nat}
    (hr : immr < w.bits) (hi : imms < w.bits) {os : List O}
    (ho : ops pc (.bitfield w op dst rn immr imms) = some os) :
    ∃ r', run os regs m = some (r', m) ∧
      Agree r' m (Arm64.execBitfield w op dst rn immr imms s) := by
  simp only [ops] at ho
  cases ho
  refine result_sound h hd w ?_
  have ex := rdw_eval h w hn
  have ed := rdw_eval h w hd
  have wx := rdw_width (regs := regs) w rn
  have wd := rdw_width (regs := regs) w dst
  rw [ex] at wx; rw [ed] at wd
  cases w <;> cases op <;>
    simp only [eval_shl, eval_band, eval_lshr, eval_ones, eval_trunc, eval_ashr, eval_bor,
      eval_bnot, ex, ed, RegWidth.bits, ↓reduceIte, reduceCtorEq]
  · exact sbfm32 _ _ (wx rfl) hr hi
  · exact bfm32 _ _ (wx rfl) (wd rfl) hr hi
  · exact ubfm32 _ _ (wx rfl) hr hi
  · exact sbfm64 _ _ hr hi
  · exact bfm64 _ _ hr hi
  · exact ubfm64 _ _ hr hi

/-- **`extr`**, which is also the rotation by a constant: the shift is below the width. -/
theorem extr_sound (h : Agree regs m s) (w : RegWidth) {dst rn rm : Arm64.Reg} (hd : Wf dst)
    (hn : Wf rn) (hm : Wf rm) {lsb : Nat} (hl : lsb < w.bits) :
    ∃ r', run (wr dst (if lsb = 0 then rdw w rm
        else trunc w (bor (lshr (rdw w rm) lsb) (shl (rdw w rn) (w.bits - lsb))))) regs m =
        some (r', m) ∧
      Agree r' m (s.writeReg w dst (match w with
        | .W32 => (((s.readReg32 rn ++ s.readReg32 rm : BitVec 64) >>> (lsb % 32)).truncate
            32).zeroExtend 64
        | .W64 => ((s.readReg64 rn ++ s.readReg64 rm : BitVec 128) >>> (lsb % 64)).truncate
            64)).advancePC := by
  refine result_sound h hd w ?_
  have en := rdw_eval h w hn
  have em := rdw_eval h w hm
  obtain ⟨k, rfl, hk⟩ : ∃ k : BitVec 64, lsb = k.toNat ∧ k.toNat < w.bits := by
    refine ⟨BitVec.ofNat 64 lsb, ?_, ?_⟩ <;> cases w <;> simp [RegWidth.bits] at hl ⊢ <;> omega
  by_cases h0 : k.toNat = 0
  · have hk0 : k = 0#64 := by bv_omega
    subst hk0
    cases w <;> simp [em, Arm64.State.readReg, Arm64.State.readReg32] <;> bv_decide
  · cases w
    · simp only [RegWidth.bits] at hk
      obtain ⟨j, hj, ej⟩ : ∃ j : BitVec 64, j = 32#64 - k ∧ 32 - k.toNat = j.toNat :=
        ⟨_, rfl, by bv_omega⟩
      have hk' : k < 32#64 := by bv_omega
      have hk0 : k ≠ 0#64 := by bv_omega
      simp [h0, en, em, Arm64.State.readReg, Arm64.State.readReg32, RegWidth.bits, ej,
        Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt j.isLt]
      bv_decide
    · simp only [RegWidth.bits] at hk
      obtain ⟨j, hj, ej⟩ : ∃ j : BitVec 64, j = 64#64 - k ∧ 64 - k.toNat = j.toNat :=
        ⟨_, rfl, by bv_omega⟩
      have hk' : k < 64#64 := by bv_omega
      have hk0 : k ≠ 0#64 := by bv_omega
      simp [h0, en, em, Arm64.State.readReg, RegWidth.bits, ej,
        Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt j.isLt]
      bv_decide

end MachineChecked.ARM.Lift
