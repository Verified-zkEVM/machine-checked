/-
  MachineChecked.RiscV.Check.Fast

  The one-pass check implies the indexed one.
-/

import MachineChecked.RiscV.Check.Domain
import MachineChecked.RiscV.Frame.Sound

namespace MachineChecked.RiscV.Check

open RiscvZkvm.Rv64 MachineChecked.RiscV.Frame

theorem Ctx.edgeOkAt_imp {c : Ctx} {anno : Array (List AState)} {i : Nat} {e : Edge}
    (h : c.edgeOkAt anno i ((anno.toList[i + 1]?).getD []) e = true) :
    c.edgeOk anno e = true := by
  cases e with
  | goto j B =>
    simp only [Ctx.edgeOkAt] at h
    split at h
    · rename_i hj; subst hj
      simp only [Ctx.edgeOk, annoAt, Array.getElem?_toList] at h ⊢
      exact h
    · exact h
  | ret B => exact h

theorem Ctx.walk_sound {c : Ctx} {anno : Array (List AState)}
    (hsize : anno.size = c.f.prog.length) :
    ∀ (ps : List (Option Instr)) (as : List (List AState)) (i : Nat),
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
    have hai : anno[i]? = some a := by
      have := congrArg (·[0]?) has; simpa using this.symm
    have hps' : ps = c.f.prog.drop (i + 1) := by
      have := congrArg List.tail hps; simpa [List.tail_drop] using this
    have has' : as = anno.toList.drop (i + 1) := by
      have := congrArg List.tail has; simpa [List.tail_drop] using this
    rcases Nat.eq_or_lt_of_le hik with rfl | hlt
    · unfold Ctx.instrOk
      rw [annoAt, hai, Option.getD_some]
      have hnext : as.head?.getD [] = (anno.toList[i + 1]?).getD [] := by
        rw [has']; simp
      have hw1 := hw.1
      simp only [List.all_eq_true] at hw1 ⊢
      intro A hA
      have hwA := hw1 A hA
      simp only [Ctx.step, hpi]
      cases hst : c.stepAt (c.f.pcOf i) oi A with
      | none => rw [hst] at hwA; cases hwA
      | some es =>
        rw [hst] at hwA
        simp only [List.all_eq_true] at hwA ⊢
        intro e he
        have := hwA e he
        rw [hnext] at this
        exact Ctx.edgeOkAt_imp this
    · exact Ctx.walk_sound hsize ps as (i + 1) hw.2 hps' has' k hlt hk

/-- **The one-pass check suffices.** -/
theorem Ctx.validFast_sound {c : Ctx} {anno : Array (List AState)}
    (h : c.validFast anno = true) : c.valid anno = true := by
  simp only [Ctx.validFast, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hptr, hsf⟩, hb⟩, h0⟩, hsize⟩, hw⟩ := h
  have hall : (List.range c.f.prog.length).all (c.instrOk anno) = true := by
    simp only [List.all_eq_true, List.mem_range]
    exact fun k hk => Ctx.walk_sound hsize _ _ 0 hw (by simp) (by simp) k (Nat.zero_le _) hk
  simp only [Ctx.valid, Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨⟨⟨hptr, hsf⟩, hb⟩, h0⟩, hall⟩

end MachineChecked.RiscV.Check
