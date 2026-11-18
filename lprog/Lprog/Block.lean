/-
  Lprog.Block

  Straight-line code in one step, for any instruction set: a piece of a body that is only
  operations and labels does what its operations do in order (`Isa.runStraight`), and
  `SafeN.block` steps over it at once. A proof then pays one rule for a block, not one for
  each instruction, and the state after it is one term to normalise.

  The budget of `Isa.SafeN` does not change across an instruction that has one result, so a
  block needs no account of its length.

  ## Main definitions

  * `Isa.runStraight`

  ## Main results

  * `SafeN.block`
-/

import Lprog.Sem

namespace Lprog

namespace Isa

variable (I : Isa)

/-- **Run a straight-line piece of code**: its operations in order, skipping labels. `none` if
    an operation faults, or if the piece has an instruction other than an operation or a
    label. -/
def runStraight : Lcmd I.Op I.Reg → (I.Reg → BitVec 64) → I.M → Option ((I.Reg → BitVec 64) × I.M)
  | [], r, m => some (r, m)
  | .Llabel _ _ :: is, r, m => runStraight is r m
  | .Lopn op :: is, r, m => match I.opn op r m with
    | some (r', m') => runStraight is r' m'
    | none => none
  | _ :: _, _, _ => none

@[simp] theorem runStraight_nil (r : I.Reg → BitVec 64) (m : I.M) : I.runStraight [] r m = some (r, m) := rfl

@[simp] theorem runStraight_label {kd : LabelKind} {l : LLabel} (is : Lcmd I.Op I.Reg)
    (r : I.Reg → BitVec 64) (m : I.M) : I.runStraight (.Llabel kd l :: is) r m = I.runStraight is r m := rfl

theorem runStraight_opn {op : I.Op} (is : Lcmd I.Op I.Reg) {r r' : I.Reg → BitVec 64} {m m' : I.M}
    (h : I.opn op r m = some (r', m')) : I.runStraight (.Lopn op :: is) r m = I.runStraight is r' m' := by
  simp [runStraight, h]

end Isa

namespace SafeN

variable {I : Isa} {p : Lprog I.Op I.Reg} {E : Type} {c : Context I E} {G : State I → Prop} {n : Nat}
  {Q : State I → Prop} {rest : List Frame} {fd : Lfundef I.Op I.Reg} {fn : Nat} {rv top : BitVec 64}

/-- The instruction at the start of a piece of a body, and the rest of the piece. -/
theorem piece_cons {body is : Lcmd I.Op I.Reg} {i : LinstrR I.Op I.Reg} {pc : Nat}
    (h : (body.drop pc).take (is.length + 1) = i :: is) :
    body[pc]? = some i ∧ (body.drop (pc + 1)).take is.length = is := by
  have e1 : body[pc]? = (body.drop pc).head? := by simp [List.head?_drop]
  have e2 : body.drop (pc + 1) = (body.drop pc).tail := by simp [List.tail_drop]
  rw [e1, e2]
  cases hl : body.drop pc with
  | nil => simp [hl] at h
  | cons x xs =>
    simp only [hl, List.take_succ_cons, List.cons.injEq] at h
    obtain ⟨rfl, h2⟩ := h
    exact ⟨rfl, h2⟩

/-- **A straight-line block in one step.** If the body of the function at `fn` holds the
    piece `is` from `pc`, and running it from `regs` and `m` gives `r'` and `m'`, then safety
    after the piece gives safety at its start. -/
theorem block (hf : p[fn]? = some fd) :
    ∀ (is : Lcmd I.Op I.Reg) (pc : Nat) (regs : I.Reg → BitVec 64) (m : I.M)
      {r' : I.Reg → BitVec 64} {m' : I.M},
      (fd.body.drop pc).take is.length = is → I.runStraight is regs m = some (r', m') →
      I.SafeN p c G n Q ⟨⟨fn, pc + is.length, rv, top⟩ :: rest, r', m'⟩ →
      I.SafeN p c G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩
  | [], pc, regs, m, _, _, _, hr, h => by
    simp only [Isa.runStraight, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    simpa using h
  | i :: is, pc, regs, m, r', m', hb, hr, h => by
    obtain ⟨hi, hb'⟩ := piece_cons hb
    have h' : I.SafeN p c G n Q ⟨⟨fn, (pc + 1) + is.length, rv, top⟩ :: rest, r', m'⟩ := by
      simpa [Nat.add_assoc, Nat.add_comm 1] using h
    cases i with
    | Llabel kd l =>
      exact label hf hi (block hf is (pc + 1) regs m hb' (by simpa using hr) h')
    | Lopn op =>
      cases ho : I.opn op regs m with
      | none => simp [Isa.runStraight, ho] at hr
      | some rm =>
        obtain ⟨r1, m1⟩ := rm
        rw [Isa.runStraight_opn _ _ ho] at hr
        exact opn hf hi ho (block hf is (pc + 1) r1 m1 hb' hr h')
    | _ => simp [Isa.runStraight] at hr

end SafeN

end Lprog
