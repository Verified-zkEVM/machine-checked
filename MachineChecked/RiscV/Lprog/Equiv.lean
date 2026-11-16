/-
  MachineChecked.RiscV.Lprog.Equiv

  The lifted program is equivalent to the machine.

  The machine under SP1 is a system that makes no events and stops, accepting, at `exit`,
  where the outermost function returns (`msys`). A machine state and the Lprog state of the
  lifted program that stands for it (`Sim`) show an observer the same (`Ascent.Equivalent`):

  * the machine refines the lifted program, where `wrong` at Lprog is undefined behaviour:
    everything the machine does, the lifted program does, unless it can go `wrong`;
  * a lifted program that never goes `wrong` refines the machine.

  The first is the simulation of `Transfer.lean`. The second runs it backwards: an
  instruction other than an external call has one result, so the step the simulation gives
  is the step the program took; and SP1's `ecall` gives agreeing results from agreeing
  states (`sp1Ecall_agree`).

  `exit` must lie outside the code (`ExitOut`), or the machine would stop where the lifted
  program runs on.

  ## Main definitions

  * `msys`, `ExitOut`, `NoWrong`

  ## Main results

  * `refines_lift`: the machine refines the lifted program
  * `lift_refines`: a lifted program that never goes `wrong` refines the machine
  * `equivalent_lift`, `equivalent_of_entry`: they are equivalent
-/

import MachineChecked.RiscV.Lprog.Transfer
import MachineChecked.RiscV.Lprog.Ecall

namespace MachineChecked.RiscV.Lprog

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.Lprog
open MachineChecked.Ascent (Outcome Steps Behaves GoesWrong Refines Equivalent)

/-! ## The machine as a system -/

/-- The machine under SP1 as a system: it makes no events, and stops, accepting, where a
    return to `exit` lands. -/
def msys (exit : Word) : Ascent.System MachineState Unit :=
  (⟨Ascent.silent (Ascent.detStep stepSp1), Accepted⟩ : Ascent.System MachineState Unit).stopAt
    fun t => t.pc = exit &&& ~~~1#64

theorem msys_step_ok {exit : Word} {t t' : MachineState} {es : List Unit} :
    (msys exit).step t (.ok (t', es)) ↔
      t.pc ≠ exit &&& ~~~1#64 ∧ es = [] ∧ stepSp1 t = some t' := by
  cases h : stepSp1 t <;>
    simp [msys, Ascent.System.stopAt, Ascent.silent, Ascent.detStep, h, eq_comm]

theorem msys_step_trap {exit : Word} {t : MachineState} :
    (msys exit).step t .trap ↔ t.pc ≠ exit &&& ~~~1#64 ∧ stepSp1 t = none := by
  cases h : stepSp1 t <;> simp [msys, Ascent.System.stopAt, Ascent.silent, Ascent.detStep, h]

theorem msys_not_wrong {exit : Word} {t : MachineState} : ¬ (msys exit).step t .wrong := by
  cases h : stepSp1 t <;> simp [msys, Ascent.System.stopAt, Ascent.silent, Ascent.detStep, h]

/-- `exit` is no address of the code: the machine does not stop inside a function. -/
def ExitOut (fs : List Fn) (exit : Word) : Prop :=
  ∀ f ∈ fs, ∀ k ≤ f.prog.length, f.base + BitVec.ofNat 64 (4 * k) ≠ exit &&& ~~~1#64

variable {fs : List Fn} {exit : Word} {s : State rvIsa} {t : MachineState}

theorem Sim.pc_ne (hs : Sim fs exit s t) (hex : ExitOut fs exit) : t.pc ≠ exit &&& ~~~1#64 := by
  obtain ⟨stack, regs, m⟩ := s
  cases stack with
  | nil => exact absurd rfl hs.ne
  | cons fr rest =>
    obtain ⟨⟨f, hf, hle, htpc⟩, -⟩ := hs.chain
    rw [htpc]
    exact hex f (List.mem_of_getElem? hf) _ (by omega)

/-! ## The machine refines the lifted program -/

/-- **The machine refines the lifted program**, from a machine state and the Lprog state that
    stands for it, or a returned one with the machine at `exit`. -/
theorem refines_lift (hok : ProgOk fs) (hex : ExitOut fs exit)
    (h : Sim fs exit s t ∨ Ret exit s t) : Refines (msys exit) t (lsys fs) s := by
  refine Refines.of_sim (fun t s => Sim fs exit s t ∨ Ret exit s t) ?_ ?_ ?_ ?_ h
  · rintro t s (hs | hr) ha
    · rcases ha with ha | ha
      · rcases back_step hok hs with hw | ⟨-, h2, -⟩
        · exact .inl hw
        · obtain ⟨s', hs', -, hacc⟩ := h2 ha
          exact .inr ⟨s', hs', hacc⟩
      · exact absurd ha (hs.pc_ne hex)
    · exact .inr ⟨s, .refl _, .inl hr.1⟩
  · rintro t s t' es (hs | hr) hst
    · obtain ⟨-, rfl, hst'⟩ := msys_step_ok.1 hst
      rcases back_step hok hs with hw | ⟨h1, -, -⟩
      · exact .inl hw
      · obtain ⟨s', hs', hrel⟩ := h1 t' hst'
        exact .inr ⟨s', hs', hrel⟩
    · exact absurd hr.2.2 (msys_step_ok.1 hst).1
  · rintro t s (hs | hr) hna htr
    · obtain ⟨-, hn⟩ := msys_step_trap.1 htr
      rcases back_step hok hs with hw | ⟨-, -, h3⟩
      · exact .inl hw
      · exact .inr (h3 hn fun ha => hna (.inl ha))
    · exact absurd hr.2.2 (msys_step_trap.1 htr).1
  · exact fun _ _ _ hw => (msys_not_wrong hw).elim

/-! ## The lifted program refines the machine -/

/-- The Lprog state never goes `wrong`. -/
def NoWrong (fs : List Fn) (s : State rvIsa) : Prop := ∀ tr, ¬ Behaves (lsys fs) s tr .wrong

theorem NoWrong.step {s' : State rvIsa} {es : List Unit} (h : NoWrong fs s)
    (hs : (lsys fs).step s (.ok (s', es))) : NoWrong fs s' :=
  fun tr hb => h (es ++ tr) (.step hs hb)

theorem NoWrong.not_wrong (h : NoWrong fs s) : ¬ (lsys fs).step s .wrong :=
  fun hw => h [] (.wrong hw)

theorem AllSafe.noWrong {Q : State rvIsa → Prop} (h : AllSafe fs Q s) : NoWrong fs s :=
  fun tr hb => h.not_goesWrong ⟨tr, List.prefix_refl _, hb⟩

section Forward

variable {fr : Frame} {rest : List Frame} {regs : Reg → BitVec 64} {m : MachineState} {f : Fn}
  {k : Nat}

/-- **One instruction, forwards.** At an instruction that does not go `wrong`: a step of the
    lifted program is a step of the machine, to states that stand for each other; an accepting
    state is an accepting machine; a trap is a machine stuck and not accepting. -/
theorem At.fwd (hok : ProgOk fs) (h : At fs exit fr rest regs m t f k)
    (hnw : ¬ (lsys fs).step ⟨fr :: rest, regs, m⟩ .wrong) :
    (∀ s' es, (lsys fs).step ⟨fr :: rest, regs, m⟩ (.ok (s', es)) →
        es = [] ∧ ∃ t', stepSp1 t = some t' ∧ (Sim fs exit s' t' ∨ Ret exit s' t')) ∧
      ((lsys fs).accept ⟨fr :: rest, regs, m⟩ → Accepted t) ∧
      (¬ (lsys fs).accept ⟨fr :: rest, regs, m⟩ → (lsys fs).step ⟨fr :: rest, regs, m⟩ .trap →
        stepSp1 t = none ∧ ¬ Accepted t) := by
  have hfetch := h.fetch
  have hstep := h.step_iff
  have hbody := h.body.2
  have hf := getElem?_liftProg h.hf
  have hag := h.sim.agree
  obtain ⟨hnext, hacc⟩ := back_instr hok hnw h
  generalize hL : liftI fs f.prog.length k (f.base + BitVec.ofNat 64 (4 * k)) (f.prog[k]'h.hk) = L
    at hstep hbody
  by_cases hext : ∃ n, L = .Lext n
  · obtain ⟨n, rfl⟩ := hext
    rw [liftI_eq_ext hL] at hfetch
    refine ⟨fun s' es hs => ?_, ?_, fun hna htr => ?_⟩
    · obtain ⟨hstack, u, hu, huf, hm⟩ := (hstep _).1 hs
      obtain ⟨stack, r', m'⟩ := s'
      cases hw : sp1Ecall u with
      | none => simp [hw] at hm
      | some w =>
        simp only [hw, Outcome.ok.injEq, Prod.mk.injEq] at hm
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hm
        obtain ⟨t', ht', hwt⟩ := (sp1Ecall_agree (hu.symm.trans hag) huf hfetch).2 _ hw
        have hst : stepSp1 t = some t' := by rw [stepSp1_ecall hfetch]; exact ht'
        cases hstack
        exact ⟨rfl, t', hst, .inl (h.next ((agree_ofParts_regsOf _).trans hwt) (code_stepSp1 hst)
          (pc_sp1Ecall hfetch ht'))⟩
    · rintro (hnil | ⟨-, -, h5, h10⟩)
      · cases hnil
      · exact ⟨hfetch, by rw [← hag.regs]; exact h5, by rw [← hag.regs]; exact h10⟩
    · obtain ⟨u, hu, huf, hm⟩ := (hstep _).1 htr
      cases hw : sp1Ecall u with
      | some w => simp [hw] at hm
      | none =>
        refine ⟨by rw [stepSp1_ecall hfetch]; exact (sp1Ecall_agree (hu.symm.trans hag) huf hfetch).1 hw,
          fun ha => hna (hacc ha)⟩
  · have hext : ∀ n, L ≠ .Lext n := fun n h => hext ⟨n, h⟩
    have hdet : ∀ {o₁ o₂}, (lsys fs).step ⟨fr :: rest, regs, m⟩ o₁ →
        (lsys fs).step ⟨fr :: rest, regs, m⟩ o₂ → o₁ = o₂ := fun h₁ h₂ =>
      MachineChecked.Lprog.SafeN.stepI_det hext ((hstep _).1 h₁) ((hstep _).1 h₂)
    have hna : ¬ (lsys fs).accept ⟨fr :: rest, regs, m⟩ :=
      MachineChecked.Lprog.SafeN.not_accept hf hbody hext
    have hstuck : stepSp1 t = none → ¬ (lsys fs).accept ⟨fr :: rest, regs, m⟩ ∧
        (lsys fs).step ⟨fr :: rest, regs, m⟩ .trap := fun hn =>
      (trap_instr h hn fun ha => hna (hacc ha)).resolve_left hnw
    refine ⟨fun s' es hs => ?_, fun ha => absurd ha hna, fun _ htr => ?_⟩
    · cases hst : stepSp1 t with
      | none => cases hdet hs (hstuck hst).2
      | some t' =>
        obtain ⟨s'', hrel, hs''⟩ := hnext t' hst
        cases hdet hs hs''
        exact ⟨rfl, t', rfl, hrel⟩
    · cases hst : stepSp1 t with
      | none => exact ⟨rfl, fun ha => hna (hacc ha)⟩
      | some t' =>
        obtain ⟨s'', -, hs''⟩ := hnext t' hst
        cases hdet htr hs''

end Forward

/-- **A lifted program that never goes `wrong` refines the machine**, from an Lprog state and
    the machine state it stands for, or a returned one with the machine at `exit`. -/
theorem lift_refines (hok : ProgOk fs) (hex : ExitOut fs exit)
    (h : Sim fs exit s t ∨ Ret exit s t) (hnw : NoWrong fs s) :
    Refines (lsys fs) s (msys exit) t := by
  refine Refines.of_sim
    (fun s t => (Sim fs exit s t ∨ Ret exit s t) ∧ NoWrong fs s) ?_ ?_ ?_ ?_ ⟨h, hnw⟩
  · rintro ⟨stack, regs, m⟩ t ⟨hs | hr, hnw⟩ ha
    · cases stack with
      | nil => exact absurd rfl hs.ne
      | cons fr rest =>
        rcases hs.split with ⟨f, k, hAt⟩ | ⟨f, k, -, hna, -⟩ | hw
        · exact .inr ⟨t, .refl _, .inl ((hAt.fwd hok hnw.not_wrong).2.1 ha)⟩
        · exact absurd ha hna
        · exact absurd hw hnw.not_wrong
    · exact .inr ⟨t, .refl _, .inr hr.2.2⟩
  · rintro ⟨stack, regs, m⟩ t s' es ⟨hs | hr, hnw⟩ hst
    · cases stack with
      | nil => exact absurd rfl hs.ne
      | cons fr rest =>
        rcases hs.split with ⟨f, k, hAt⟩ | ⟨f, k, hAt, -, hlab⟩ | hw
        · obtain ⟨rfl, t', ht', hrel⟩ := (hAt.fwd hok hnw.not_wrong).1 s' es hst
          exact .inr ⟨t', .one (msys_step_ok.2 ⟨hs.pc_ne hex, rfl, ht'⟩), hrel, hnw.step hst⟩
        · have hnw' := hnw.step hst
          cases (hlab _).1 hst
          exact .inr ⟨t, .refl _, .inl hAt.sim, hnw'⟩
        · exact absurd hw hnw.not_wrong
    · obtain ⟨rfl, -⟩ := hr
      exact hst.elim
  · rintro ⟨stack, regs, m⟩ t ⟨hs | hr, hnw⟩ hna htr
    · cases stack with
      | nil => exact absurd rfl hs.ne
      | cons fr rest =>
        rcases hs.split with ⟨f, k, hAt⟩ | ⟨f, k, -, -, hlab⟩ | hw
        · obtain ⟨hn, hnacc⟩ := (hAt.fwd hok hnw.not_wrong).2.2 hna htr
          have hpc := hs.pc_ne hex
          exact .inr ⟨t, .refl _, fun ha => ha.elim hnacc hpc, msys_step_trap.2 ⟨hpc, hn⟩⟩
        · cases (hlab _).1 htr
        · exact absurd hw hnw.not_wrong
    · obtain ⟨rfl, -⟩ := hr
      exact htr.elim
  · exact fun _ _ h hw => (h.2.not_wrong hw).elim

/-! ## Equivalence -/

/-- **The lifted program is equivalent to the machine**, where it never goes `wrong`. -/
theorem equivalent_lift (hok : ProgOk fs) (hex : ExitOut fs exit)
    (h : Sim fs exit s t ∨ Ret exit s t) (hnw : NoWrong fs s) :
    Equivalent (msys exit) t (lsys fs) s :=
  ⟨refines_lift hok hex h, lift_refines hok hex h hnw⟩

/-- **Equivalence from a function's entry.** A machine at the entry of function `g` of a lifted
    program it holds, run until `g` returns, is equivalent to the call `⟨g, 0, ra, sp⟩` at
    Lprog, where that never goes `wrong`. -/
theorem equivalent_of_entry (hok : ProgOk fs) {g : Nat} {fn : Fn} (hg : fs[g]? = some fn)
    (hpc : t.pc = fn.base) (hcode : ∀ f ∈ fs, CodeAt f.base (f.prog.map some) t)
    (hex : ExitOut fs (t.getReg .x1))
    (hnw : NoWrong fs ⟨[⟨g, 0, t.getReg .x1, t.getReg .x2⟩], regsOf t, t⟩) :
    Equivalent (msys (t.getReg .x1)) t (lsys fs)
      ⟨[⟨g, 0, t.getReg .x1, t.getReg .x2⟩], regsOf t, t⟩ :=
  equivalent_lift hok hex
    (.inl ⟨agree_ofParts_regsOf t, hcode, ⟨⟨fn, hg, Nat.zero_le _, by simp [hpc]⟩, nofun, rfl⟩,
      by simp⟩) hnw

end MachineChecked.RiscV.Lprog
