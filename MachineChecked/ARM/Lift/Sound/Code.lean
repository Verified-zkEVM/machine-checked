/-
  MachineChecked.ARM.Lift.Sound.Code

  The lift of AArch64 against arm64-semantics: the code stays where it is. A store of the
  lift writes only bytes that may be written, which are never executable, so what the machine
  fetches does not change as the operations of an instruction run.

  ## Main definitions

  * `Keeps`

  ## Main results

  * `keeps_writeSized`: a permitted store keeps the executable bytes
  * `run_keeps`: so do the operations of an instruction
  * `fetchMem_keeps`: and then the machine fetches the same instruction
  * `run_sp`: operations that do not write the stack pointer leave it
-/

import MachineChecked.ARM.Lift.Sound.Memory

namespace MachineChecked.ARM.Lift

open Lprog Lprog.ARM Lprog.Build
open Arm64 (Instr RegWidth MemWidth AddrMode)

/-- **A memory keeps another's executable bytes**, and every permission. -/
def Keeps (m m' : Arm64.Memory) : Prop :=
  (∀ b, (m.perm b).x = true → m'.read8 b = m.read8 b) ∧ ∀ b, m'.perm b = m.perm b

theorem Keeps.rfl {m : Arm64.Memory} : Keeps m m := ⟨fun _ _ => _root_.rfl, fun _ => _root_.rfl⟩

theorem Keeps.trans {m m' m'' : Arm64.Memory} (h : Keeps m m') (h' : Keeps m' m'') :
    Keeps m m'' :=
  ⟨fun b hb => (h'.1 b (by rw [h.2 b]; exact hb)).trans (h.1 b hb),
    fun b => (h'.2 b).trans (h.2 b)⟩

theorem read8_write8 (m : Arm64.Memory) (c : BitVec 64) (v : BitVec 8) (b : BitVec 64) :
    (m.write8 c v).read8 b = if b = c then v else m.read8 b := by
  simp only [Arm64.Memory.read8, Arm64.Memory.write8]
  by_cases h : b = c <;> simp [h]

/-- A write of a byte that is not executable. -/
theorem keeps_write8 (m : Arm64.Memory) {c : BitVec 64} (hc : (m.perm c).x = false)
    (v : BitVec 8) : Keeps m (m.write8 c v) := by
  refine ⟨fun b hb => ?_, perm_write8 m c v⟩
  have hne : b ≠ c := by
    rintro rfl
    rw [hc] at hb
    cases hb
  simp [read8_write8, hne]

/-- Every byte of a range that satisfies a test of its permission does. -/
theorem allPerm_at {m : Arm64.Memory} {p : Option Arm64.Perm → Bool} {a : BitVec 64} {n : Nat}
    (h : m.allPerm p a n = true) (j : Nat) (hj : j < n) :
    p (m.perm (a + BitVec.ofNat 64 j)) = true := by
  induction n generalizing a j with
  | zero => omega
  | succ n ih =>
    simp only [Arm64.Memory.allPerm, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have := ih h.2 j (by omega)
      rw [BitVec.add_assoc] at this
      rw [show BitVec.ofNat 64 (j + 1) = 1#64 + BitVec.ofNat 64 j by
        rw [Nat.add_comm, BitVec.ofNat_add]]
      exact this

/-- A byte that may be written is not executable. -/
theorem not_x_of_canWrite {m : Arm64.Memory} {a : BitVec 64} {n : Nat}
    (h : m.canWrite a n = true) (j : Nat) (hj : j < n) :
    (m.perm (a + BitVec.ofNat 64 j)).x = false := by
  have := allPerm_at h j hj
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  exact this.2

/-- **A permitted store keeps the executable bytes.** -/
theorem keeps_writeSized (m : Arm64.Memory) (sz : MemWidth) {a : BitVec 64}
    (h : m.canWrite a sz.bytes = true) (v : BitVec 64) : Keeps m (m.writeSized sz a v) := by
  have hx := not_x_of_canWrite h
  -- a byte written keeps, in a memory with the permissions of `m`
  have step : ∀ (m1 : Arm64.Memory), Keeps m m1 → ∀ (j : Nat), j < sz.bytes → ∀ b : BitVec 8,
      Keeps m (m1.write8 (a + BitVec.ofNat 64 j) b) := fun m1 h1 j hj b =>
    h1.trans (keeps_write8 m1 (by rw [h1.2]; exact hx j hj) b)
  cases sz
  · simpa [Arm64.Memory.writeSized] using step m .rfl 0 (by decide) _
  · exact step _ (step m .rfl 0 (by decide) _) 1 (by decide) _
  · exact step _ (step _ (step _ (step m .rfl 0 (by decide) _) 1 (by decide) _) 2 (by decide) _)
      3 (by decide) _
  · exact step _ (step _ (step _ (step _ (step _ (step _ (step _ (step m .rfl 0 (by decide) _)
      1 (by decide) _) 2 (by decide) _) 3 (by decide) _) 4 (by decide) _) 5 (by decide) _)
      6 (by decide) _) 7 (by decide) _

/-- **The operations of an instruction keep the executable bytes.** -/
theorem run_keeps {os : List O} {regs r' : Reg → BitVec 64} {m m' : Arm64.Memory}
    (h : run os regs m = some (r', m')) : Keeps m m' := by
  induction os generalizing regs m with
  | nil => cases h; exact .rfl
  | cons o os ih =>
    rw [run_cons] at h
    cases he : o.eval armMem regs m with
    | none => rw [he] at h; cases h
    | some rm =>
      obtain ⟨r1, m1⟩ := rm
      rw [he] at h
      refine Keeps.trans ?_ (ih h)
      cases o with
      | set d e => cases he; exact .rfl
      | skip => cases he; exact .rfl
      | trap => cases he
      | load d w sg a =>
        by_cases hc : m.canRead (a.eval regs) w.bytes = true
        · simp only [Op.eval, armMem, hc, ↓reduceIte, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at he
          rw [← he.2]; exact .rfl
        · simp [Op.eval, armMem, hc] at he
      | store w a e =>
        by_cases hc : m.canWrite (a.eval regs) w.bytes = true
        · simp only [Op.eval, armMem, hc, ↓reduceIte, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at he
          rw [← he.2]
          exact keeps_writeSized m (memWidth w) (by cases w <;> exact hc) _
        · simp [Op.eval, armMem, hc] at he

/-- **The machine fetches the same instruction** from a memory that keeps the executable
    bytes. -/
theorem fetchMem_keeps {prog : Arm64.Program} {m m' : Arm64.Memory} (h : Keeps m m')
    {pc : BitVec 64} {i : Instr} (hf : prog.fetchMem m pc = some i) :
    prog.fetchMem m' pc = some i := by
  unfold Arm64.Program.fetchMem at hf ⊢
  split at hf
  · cases hf
  · next he =>
    split at hf
    · cases hf
    · next hal =>
      split at hf
      · cases hf
      · next hx =>
        have hx' : m.canExec pc 4 = true := by simpa using hx
        have hb := allPerm_at hx'
        have hexec : m'.canExec pc 4 = m.canExec pc 4 := allPerm_congr h.2 _ _ _
        have hr : m'.read32 pc = m.read32 pc := by
          simp only [Arm64.Memory.read32]
          rw [h.1 _ (hb 0 (by decide)), h.1 _ (hb 1 (by decide)), h.1 _ (hb 2 (by decide)),
            h.1 _ (hb 3 (by decide))]
        simp [he, hal, hexec, hx', hr, hf]

/-- **Operations that do not write the stack pointer leave it.** -/
theorem run_sp {os : List O} {regs r' : Reg → BitVec 64} {m m' : Arm64.Memory}
    (h : run os regs m = some (r', m')) (hw : os.any writesSp = false) : r' .sp = regs .sp := by
  induction os generalizing regs m with
  | nil => cases h; rfl
  | cons o os ih =>
    rw [run_cons] at h
    simp only [List.any_cons, Bool.or_eq_false_iff] at hw
    cases he : o.eval armMem regs m with
    | none => rw [he] at h; cases h
    | some rm =>
      obtain ⟨r1, m1⟩ := rm
      rw [he] at h
      rw [ih h hw.2]
      cases o with
      | set d e =>
        cases he
        have : Reg.sp ≠ d := by rintro rfl; simp [writesSp] at hw
        simp [updReg, this]
      | skip => cases he; rfl
      | trap => cases he
      | load d w sg a =>
        have hd : Reg.sp ≠ d := by rintro rfl; simp [writesSp] at hw
        by_cases hc : m.canRead (a.eval regs) w.bytes = true
        · simp only [Op.eval, armMem, hc, ↓reduceIte, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at he
          rw [← he.1]; simp [updReg, hd]
        · simp [Op.eval, armMem, hc] at he
      | store w a e =>
        by_cases hc : m.canWrite (a.eval regs) w.bytes = true
        · simp only [Op.eval, armMem, hc, ↓reduceIte, Option.map_some, Option.some.injEq,
            Prod.mk.injEq] at he
          rw [← he.1]
        · simp [Op.eval, armMem, hc] at he

end MachineChecked.ARM.Lift
