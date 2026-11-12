/-
  MachineChecked.RiscV.Lprog.Rules

  Running a lifted RISC-V program at Lprog: one rule per lifted instruction, in continuation
  form.

  Each rule takes a machine state `u` the Lprog state stands for (`Agree (ofParts regs m) u`),
  so that what an instruction reads is stated on `u` with riscv-zkvm's own functions, and
  continues from every Lprog state that stands for the machine state after it. The generic
  rules (`Lprog.SafeN.label`, `goto`, `ret`, …) apply as they are; these add the RISC-V
  reading: an operation through `opOf_spec`, a branch through `cmpEval`, a call or tail call
  to the function at the address a register holds, and SP1's system calls.

  ## Main results

  * `lsafe_opn`, `lsafe_auipc`, `lsafe_cond`, `lsafe_ret`
  * `lsafe_call`, `lsafe_tail`: indirect calls and tail calls
  * `lsafe_write`: SP1's `WRITE` to a descriptor other than 13
-/

import MachineChecked.RiscV.Lprog.Transfer

namespace MachineChecked.RiscV.Lprog

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.Lprog
open MachineChecked.Ascent (Outcome)

section Rules

variable {fs : List Fn} {G : State rvIsa → Prop} {n : Nat} {Q : State rvIsa → Prop}
  {fn pc : Nat} {rv top : Word} {rest : List Frame} {regs : Reg → BitVec 64} {m u : MachineState}
  {fd : Lfundef (Op Reg) Reg}

theorem regs_of_agree (hag : Agree (ofParts regs m) u) {r : Reg} (hr : r ≠ .x0) : regs r = u.getReg r := by
  rw [← hag.regs r, getReg_ofParts, if_neg hr]

/-- An operation (pure, or a load or store) the memory check admits. -/
theorem lsafe_opn (hf : (liftProg fs)[fn]? = some fd) (hag : Agree (ofParts regs m) u) {i : Instr}
    (hb : fd.body[pc]? = some (.Lopn (opOf i))) (hop : opnOk i = true) (hok : memOkSp1 u i = true)
    (h : ∀ r' m', Agree (ofParts r' m') (execInstrBr u i) →
      LSafeN fs G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    LSafeN fs G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  have hspec := opOf_spec hop regs m
  cases he : (opOf i).eval rvMem regs m with
  | none =>
    simp only [he] at hspec
    rw [hag.memOkSp1 i, hok] at hspec
    cases hspec
  | some rm =>
    obtain ⟨r', m'⟩ := rm
    simp only [he] at hspec
    exact SafeN.opn hf hb he (h _ _ (hspec.2.trans (hag.execInstrBr hop)))

/-- `auipc`, lifted to the constant it computes: the register is set to it. -/
theorem lsafe_auipc (hf : (liftProg fs)[fn]? = some fd) (hag : Agree (ofParts regs m) u)
    {rd : Reg} {v : Word} (hb : fd.body[pc]? = some (.Lopn (.set rd (.imm v))))
    (h : ∀ r' m', Agree (ofParts r' m') (u.setReg rd v) →
      LSafeN fs G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    LSafeN fs G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  SafeN.opn (r' := updReg regs rd v) (m' := m) hf hb (by simp [Op.eval, Expr.eval])
    (h _ _ ((agree_set' hag rd u.pc rfl).trans (agree_setPC _ _).symm))

/-- A conditional branch on a comparison of two registers. -/
theorem lsafe_cond (hf : (liftProg fs)[fn]? = some fd) (hag : Agree (ofParts regs m) u)
    {op : String} {a b : Reg} {l : LLabel} (hb : fd.body[pc]? = some (.Lcond (.cmp op (opnd a) (opnd b)) l))
    {c : Bool} (hc : cmpEval op (u.getReg a) (u.getReg b) = some c) {j : Nat} (hl : labelIdx fd.body l = some j)
    (ht : c = true → LSafeN fs G n Q ⟨⟨fn, j, rv, top⟩ :: rest, regs, m⟩)
    (hn : c = false → LSafeN fs G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, regs, m⟩) :
    LSafeN fs G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  SafeN.cond hf hb (by simp [condEval, opnd_val_of_agree hag, hc]) hl ht hn

/-- `ret`: the link register holds the return value and the stack pointer is back. -/
theorem lsafe_ret (hf : (liftProg fs)[fn]? = some fd) (hag : Agree (ofParts regs m) u)
    (hb : fd.body[pc]? = some .Lret) (hra : u.getReg .x1 = rv) (hsp : u.getReg .x2 = top)
    (h : LSafeN fs G n Q ⟨rest, regs, m⟩) : LSafeN fs G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ :=
  SafeN.ret hf hb (by rw [← hra]; exact regs_of_agree hag (by decide))
    (by rw [← hsp]; exact regs_of_agree hag (by decide)) h

/-- An indirect tail call: to the function at the address `jalr` computes, with the stack
    pointer back. -/
theorem lsafe_tail (hf : (liftProg fs)[fn]? = some fd) (hag : Agree (ofParts regs m) u)
    {rs : Reg} {off : BitVec 12}
    (hb : fd.body[pc]? = some (.Ltail (.indirect (jalrTgt rs off) (List.range fs.length))))
    (hsp : u.getReg .x2 = top) {g : Nat} {tf : Fn} (hg : fs[g]? = some tf)
    (haddr : tf.base = (u.getReg rs + signExtend12 off) &&& ~~~1#64)
    (h : ∀ g' fn', fs[g']? = some fn' → fn'.base = tf.base →
      LSafeN fs G n Q ⟨⟨g', 0, rv, top⟩ :: rest, regs, m⟩) :
    LSafeN fs G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  obtain ⟨g', hc⟩ := callee_indirect_of hg (haddr.trans (jalrTgt_eval hag rs off).symm)
  obtain ⟨fn', hfn', hbase⟩ := callee_indirect hc
  exact SafeN.tail hf hb (by rw [← hsp]; exact regs_of_agree hag (by decide)) hc
    (h g' fn' hfn' (hbase.trans ((jalrTgt_eval hag rs off).trans haddr.symm)))

/-- An indirect call: to the function at the address `jalr` computes, with the return value
    `ret` in `ra`. -/
theorem lsafe_call (hf : (liftProg fs)[fn]? = some fd) (hag : Agree (ofParts regs m) u)
    {ret : Word} {rs : Reg} {off : BitVec 12}
    (hb : fd.body[pc]? = some (.Lcall ret (.indirect (jalrTgt rs off) (List.range fs.length))))
    {g : Nat} {tf : Fn} (hg : fs[g]? = some tf)
    (haddr : tf.base = (u.getReg rs + signExtend12 off) &&& ~~~1#64)
    (h : ∀ g' fn', fs[g']? = some fn' → fn'.base = tf.base → ∀ r' m',
      Agree (ofParts r' m') ((u.setReg .x1 ret).setPC tf.base) →
      LSafeN fs G n Q ⟨⟨g', 0, ret, u.getReg .x2⟩ :: ⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    LSafeN fs G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  obtain ⟨g', hc⟩ := callee_indirect_of hg (haddr.trans (jalrTgt_eval hag rs off).symm)
  obtain ⟨fn', hfn', hbase⟩ := callee_indirect hc
  refine SafeN.call hf hb hc ?_
  have := h g' fn' hfn' (hbase.trans ((jalrTgt_eval hag rs off).trans haddr.symm)) _ _
    (agree_set' hag .x1 _ rfl)
  rwa [show (rvIsa.sp : Reg) = .x2 from rfl, regs_of_agree hag (by decide)]

/-- SP1's `WRITE` to a descriptor other than 13: the pc advances, nothing else changes. -/
theorem lsafe_write (hf : (liftProg fs)[fn]? = some fd) (hag : Agree (ofParts regs m) u)
    (hb : fd.body[pc]? = some .Lext) (ht0 : u.getReg .x5 = 2#64) (hfd : u.getReg .x10 ≠ 13#64)
    (h : ∀ r' m', Agree (ofParts r' m') u → LSafeN fs G n Q ⟨⟨fn, pc + 1, rv, top⟩ :: rest, r', m'⟩) :
    LSafeN fs G n Q ⟨⟨fn, pc, rv, top⟩ :: rest, regs, m⟩ := by
  refine SafeN.ext hf hb
    (fun ha => absurd (ha.1.symm.trans ((hag.regs .x5).trans ht0)) (by decide : (0#64 : Word) ≠ 2#64))
    sp1Ctx_ext_ne_wrong fun r' m' he => ?_
  obtain ⟨w, hagw, hcw, hw⟩ := he
  have h5 : w.getReg .x5 = 2#64 := (hagw.regs .x5).symm.trans ((hag.regs .x5).trans ht0)
  have h10 : w.getReg .x10 ≠ 13#64 := fun e => hfd ((hag.regs .x10).symm.trans ((hagw.regs .x10).trans e))
  have hstep : sp1Ecall w = some (w.setPC (w.pc + 4)) := by
    have hacc : Sp1.isAccelId 2#64 = false := by decide
    simp only [sp1Ecall, h5, hacc, Bool.false_eq_true, if_false]
    simp only [show (2#64 : Word) ≠ Sp1.HINT_LEN by decide, show (2#64 : Word) ≠ Sp1.HINT_READ by decide,
      show (2#64 : Word) ≠ Sp1.COMMIT by decide, show (2#64 : Word) ≠ Sp1.COMMIT_DEFERRED_PROOFS by decide,
      if_false, show Sp1.isHostId 2#64 = true by decide, if_true]
    unfold step
    rw [hcw]
    simp [h5, h10]
  rw [hstep] at hw
  simp only [Outcome.ok.injEq, Prod.mk.injEq] at hw
  obtain ⟨rfl, rfl⟩ := hw
  exact h _ _ ((agree_ofParts_regsOf _).trans ((agree_setPC w _).symm.trans (hagw.symm.trans hag)))

end Rules

end MachineChecked.RiscV.Lprog
