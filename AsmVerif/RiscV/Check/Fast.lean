/-
  AsmVerif.RiscV.Check.Fast

  The one-pass check implies the indexed one.
-/

import AsmVerif.RiscV.Check.Domain
import AsmVerif.RiscV.Frame.Sound

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame

theorem AState.le_refl (A : AState) : A.le A = true := by
  simp [AState.le, AVal.le, List.all_eq_true]

theorem edgeOkAt_imp {anno : Array (Option AState)} {i : Nat} {e : Edge}
    (h : edgeOkAt anno i (anno.toList[i + 1]?) e = true) : edgeOk anno e = true := by
  cases e with
  | goto j B =>
    simp only [edgeOkAt] at h
    split at h
    · rename_i hj; subst hj
      simp only [edgeOk, Fn.annoAt_eq]
      cases hx : anno.toList[i + 1]? with
      | none => rw [hx] at h; cases h
      | some x =>
        rw [hx] at h
        cases x with
        | none => cases h
        | some C =>
          simp only [Bool.or_eq_true, beq_iff_eq] at h
          rcases h with rfl | h
          · exact AState.le_refl _
          · exact h
    · exact h
  | ret B => exact h

theorem Ctx.walk_sound {c : Ctx} {anno : Array (Option AState)}
    (hsize : anno.size = c.f.prog.length) :
    ∀ (ps : List (Option Instr)) (as : List (Option AState)) (i : Nat),
      c.walk anno i ps as = true → ps = c.f.prog.drop i → as = anno.toList.drop i →
      ∀ k, i ≤ k → k < c.f.prog.length → c.instrOk anno k = true
  | [], _, i, _, hps, _, k, hik, hk => by
    have : c.f.prog.length ≤ i := by simpa using hps.symm
    omega
  | _ :: _, [], i, _, hps, has, k, hik, hk => by
    have h1 : anno.toList.length ≤ i := by simpa using has.symm
    have h2 : i < c.f.prog.length := by
      have := congrArg List.length hps; simp at this; omega
    simp at h1; omega
  | oi :: ps, a :: as, i, hw, hps, has, k, hik, hk => by
    simp only [Ctx.walk, Bool.and_eq_true] at hw
    have hpi : c.f.prog[i]? = some oi := by
      have := congrArg (·[0]?) hps; simpa using this.symm
    have hai : anno.toList[i]? = some a := by
      have := congrArg (·[0]?) has; simpa using this.symm
    have hps' : ps = c.f.prog.drop (i + 1) := by
      have := congrArg List.tail hps; simpa [List.tail_drop] using this
    have has' : as = anno.toList.drop (i + 1) := by
      have := congrArg List.tail has; simpa [List.tail_drop] using this
    rcases Nat.eq_or_lt_of_le hik with rfl | hlt
    · unfold Ctx.instrOk
      rw [Fn.annoAt_eq, hai]
      have hnext : as.head? = anno.toList[i + 1]? := by
        rw [has']; simp
      cases a with
      | none => rfl
      | some A =>
        have hw1 := hw.1
        simp only [Option.join] at hw1 ⊢
        simp only [Ctx.step, hpi]
        cases hst : c.stepAt (c.f.pcOf i) oi A with
        | none => rw [hst] at hw1; cases hw1
        | some es =>
          rw [hst] at hw1
          simp only [List.all_eq_true] at hw1
          simp only [Option.bind_some, id_eq, hst, List.all_eq_true]
          intro e he
          have := hw1 e he
          rw [hnext] at this
          exact edgeOkAt_imp this
    · exact Ctx.walk_sound hsize ps as (i + 1) hw.2 hps' has' k hlt hk

/-- **The one-pass check suffices.** -/
theorem Ctx.validFast_sound {c : Ctx} {anno : Array (Option AState)}
    (h : c.validFast anno = true) : c.valid anno = true := by
  simp only [Ctx.validFast, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hb, h0⟩, hsize⟩, hw⟩ := h
  simp only [Ctx.valid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  exact ⟨⟨hb, h0⟩, fun k hk => Ctx.walk_sound hsize _ _ 0 hw (by simp) (by simp) k (Nat.zero_le _) hk⟩

end AsmVerif.RiscV.Check
