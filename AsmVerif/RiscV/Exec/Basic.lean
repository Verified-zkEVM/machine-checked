/-
  AsmVerif.RiscV.Exec.Basic

  Hand proofs of interfaces: what the checker cannot derive (loops over memory, the
  allocator, the panic runtime) is proved here, against the same `Iface.HoldsN`, so it
  enters the same table and composes with the checker's results by `table_sound`.

  ## Cut points

  A proof gives an invariant `Inv s0 s` relating the activation's entry state `s0` to a
  state `s` at one of its cut points (the entry, loop heads), and shows: from a cut state,
  with budget `k`, the run is safe, *assuming* every cut state is safe for every smaller
  budget. Reaching the next cut point therefore has to take at least one step
  (`SafeN.step`); steps before that are free (`SafeN.of_step`). A callee's interface is used
  at the budget left after its call instruction, which is smaller.

  ## Steps

  `safe_step` executes one instruction other than `ecall`/`ebreak`: if SP1's memory check
  fails the step traps, which is safe; otherwise the run continues from `execInstrBr`. The
  continuation receives the memory check, which carries alignment and the SP1 address
  bound.
-/

import AsmVerif.RiscV.Check.Sound

namespace AsmVerif.RiscV.Exec

open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame AsmVerif.RiscV.Check

/-! ## The cut-point principle -/

/-- An interface holds at budget `n` if an invariant holds at the entry and every cut
    state is safe given that every cut state is safe for smaller budgets. -/
theorem holdsN_of_inv {env : Env} {C : Word → Option Instr} {σ : Iface} {n : Nat}
    (Inv : MachineState → MachineState → Prop)
    (hentry : ∀ s0, s0.pc = σ.entry → Pre env C σ s0 → Inv s0 s0)
    (hstep : ∀ s0 (P : Prop) k, s0.pc = σ.entry → Pre env C σ s0 → k ≤ n →
      (∀ t, Post σ s0 t → SafeN k P t) →
      (∀ m < k, ∀ t, Inv s0 t → SafeN m P t) →
      ∀ s, Inv s0 s → SafeN k P s) :
    σ.HoldsN env C n := by
  intro P s0 hpc hpre hk
  have key : ∀ k, k ≤ n → ∀ s, Inv s0 s → SafeN k P s := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hkn s hs
      exact hstep s0 P k hpc hpre hkn (fun t ht => SafeN.mono hkn (hk t ht))
        (fun m hm t ht => ih m hm (by omega) t ht) s hs
  exact key n (Nat.le_refl n) s0 (hentry s0 hpc hpre)

/-! ## One step -/

/-- `stepSp1` on an instruction other than `ecall`, `ebreak` and `csrs`: the memory check,
    then `execInstrBr`. -/
theorem stepSp1_eq {s : MachineState} {i : Instr} (hf : s.code s.pc = some i)
    (he : i ≠ .ECALL) (hb : i ≠ .EBREAK) (hc : ∀ c r, i ≠ .CSRS c r) :
    stepSp1 s = if memOkSp1 s i then some (execInstrBr s i) else none := by
  unfold stepSp1
  rw [hf]
  cases i <;> simp_all [Instr.isMemAccess, memOkSp1, memAccess]

/-- Execute one instruction, spending no budget. -/
theorem safe_step {k : Nat} {P : Prop} {s : MachineState} {i : Instr}
    (hf : s.code s.pc = some i) (he : i ≠ .ECALL) (hb : i ≠ .EBREAK)
    (hc : ∀ c r, i ≠ .CSRS c r)
    (h : memOkSp1 s i = true → SafeN k P (execInstrBr s i)) : SafeN k P s := by
  have hs := stepSp1_eq hf he hb hc
  by_cases hm : memOkSp1 s i = true
  · rw [if_pos hm] at hs
    exact SafeN.of_step (not_accepted_of_code hf he) hs (h hm)
  · rw [if_neg hm] at hs
    exact SafeN.stuck hs (fun ha => absurd ha (not_accepted_of_code hf he))

/-- Execute one instruction, spending one unit of budget. -/
theorem safe_step1 {k : Nat} {P : Prop} {s : MachineState} {i : Instr}
    (hf : s.code s.pc = some i) (he : i ≠ .ECALL) (hb : i ≠ .EBREAK)
    (hc : ∀ c r, i ≠ .CSRS c r)
    (h : memOkSp1 s i = true → SafeN k P (execInstrBr s i)) : SafeN (k + 1) P s := by
  have hs := stepSp1_eq hf he hb hc
  by_cases hm : memOkSp1 s i = true
  · rw [if_pos hm] at hs
    exact SafeN.step (not_accepted_of_code hf he) hs (h hm)
  · rw [if_neg hm] at hs
    exact SafeN.stuck hs (fun ha => absurd ha (not_accepted_of_code hf he))

/-- What SP1's memory check gives an access of `w` bytes at `a`: the address is below
    SP1's memory bound, and naturally aligned. -/
theorem memOk_addr {s : MachineState} {i : Instr} {a : Word} {w : Nat} {st : Bool}
    (hacc : memAccess s i = some (a, w, st)) (h : memOkSp1 s i = true) :
    a.toNat < SP1_MAX_MEMORY ∧ alignedFor w a = true := by
  simp only [memOkSp1, hacc, Bool.and_eq_true, isValidMemAddrSp1, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

/-! ## Reading a state after a step -/

@[simp] theorem pc_setPC (s : MachineState) (v : Word) : (s.setPC v).pc = v := rfl

theorem setPC_self {s : MachineState} {p : Word} (h : s.pc = p) : s.setPC p = s := by
  subst h; rfl

@[simp] theorem getReg_x0 (s : MachineState) : s.getReg .x0 = 0 := rfl

theorem getReg_setReg (s : MachineState) (r r' : Reg) (v : Word) :
    (s.setReg r v).getReg r' = if r' = r ∧ r ≠ .x0 then v else s.getReg r' := by
  cases r <;> cases r' <;> rfl

@[simp] theorem getReg_setByte (s : MachineState) (a : Word) (b : BitVec 8) (r : Reg) :
    (s.setByte a b).getReg r = s.getReg r := by
  cases r <;> rfl

/-! ## Fetching from the function's code -/

theorem fetch {f : Fn} {C : Word → Option Instr} (hC : CodeAt f C) {x : MachineState}
    (hcode : x.code = C) {j : Nat} {i : Instr} (hpc : x.pc = f.pcOf j)
    (hj : f.prog[j]? = some (some i)) : x.code x.pc = some i := by
  rw [hcode, hpc]; exact hC.1 j _ hj

/-- `fetch` at a literal program counter: the index is computed. -/
theorem fetchLit {f : Fn} {C : Word → Option Instr} (hC : CodeAt f C) {x : MachineState}
    (hcode : x.code = C) {p : Word} (hpc : x.pc = p) {i : Instr}
    (hj : f.prog[(p - f.base).toNat / 4]? = some (some i))
    (hp : f.pcOf ((p - f.base).toNat / 4) = p) : x.code x.pc = some i :=
  fetch hC hcode (hpc.trans hp.symm) hj

/-- `fetch` with the index computed from the state's own program counter. -/
theorem fetchPC {f : Fn} {C : Word → Option Instr} (hC : CodeAt f C) {x : MachineState}
    (hcode : x.code = C) {i : Instr}
    (hj : f.prog[(x.pc - f.base).toNat / 4]? = some (some i))
    (hp : f.pcOf ((x.pc - f.base).toNat / 4) = x.pc) : x.code x.pc = some i :=
  fetch hC hcode hp.symm hj

/-! ## The frame part of an invariant

What every state of an activation keeps, whatever its function computes: the code, `ra`,
the callee-saved registers, and memory outside what the interface lets it write. At a
`ret` it is the postcondition. -/

structure Frame (σ : Iface) (C : Word → Option Instr) (s0 s : MachineState) : Prop where
  code0 : s0.code = C
  code : s.code = C
  ra : s.getReg .x1 = s0.getReg .x1
  saved : ∀ r ∈ savedRegs, s.getReg r = s0.getReg r
  mem : ∀ a, Aligned a → ¬ Written σ (regsOf s0) a → s.getMem a = s0.getMem a

namespace Frame

variable {σ : Iface} {C : Word → Option Instr} {s0 s : MachineState}

theorem entry (h : s0.code = C) : Frame σ C s0 s0 := ⟨h, h, rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem setPC (h : Frame σ C s0 s) (v : Word) : Frame σ C s0 (s.setPC v) :=
  ⟨h.code0, h.code, h.ra, h.saved, h.mem⟩

theorem setReg (h : Frame σ C s0 s) {r : Reg} (hr : r ≠ .x1) (hs : r ∉ savedRegs) (v : Word) :
    Frame σ C s0 (s.setReg r v) := by
  refine ⟨h.code0, by rw [MachineState.code_setReg]; exact h.code, ?_, fun r' hr' => ?_, fun a ha hw => ?_⟩
  · rw [MachineState.getReg_setReg_ne _ _ _ _ hr]; exact h.ra
  · have : r' ≠ r := fun e => hs (e ▸ hr')
    rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm this)]; exact h.saved r' hr'
  · cases r <;> first | exact h.mem a ha hw | (simp only [MachineState.setReg]; exact h.mem a ha hw)

theorem setMem (h : Frame σ C s0 s) {k : Word} (hk : Aligned k → Written σ (regsOf s0) k)
    (v : Word) : Frame σ C s0 (s.setMem k v) := by
  refine ⟨h.code0, by rw [MachineState.code_setMem]; exact h.code, by rw [getReg_setMem]; exact h.ra,
    fun r hr => by rw [getReg_setMem]; exact h.saved r hr, fun a ha hw => ?_⟩
  rw [getMem_setMem, if_neg (by intro e; subst e; exact hw (hk ha))]
  exact h.mem a ha hw

theorem setByte (h : Frame σ C s0 s) {a : Word}
    (hk : Aligned (alignToDword a) → Written σ (regsOf s0) (alignToDword a)) (b : BitVec 8) :
    Frame σ C s0 (s.setByte a b) :=
  h.setMem hk _

end Frame

/-- A `ret` from a state that keeps the frame: the postcondition, so the continuation
    applies. -/
theorem safe_ret {σ : Iface} {C : Word → Option Instr} {s0 s : MachineState}
    {k : Nat} {P : Prop} (hσ : σ.returns = true) (h : Frame σ C s0 s)
    (hf : s.code s.pc = some (.JALR .x0 .x1 0)) (hk : ∀ t, Post σ s0 t → SafeN k P t) :
    SafeN k P s := by
  refine safe_step (k := k) (P := P) hf (by decide) (by decide) (by intro c r h; cases h) ?_
  intro _
  apply hk (execInstrBr s (.JALR .x0 .x1 0))
  refine ⟨hσ, ?_, fun r hr => h.saved r hr, h.mem, by simp [execInstrBr, MachineState.setPC, h.code, h.code0]⟩
  · have h0 : signExtend12 0#12 = 0 := by decide
    simp [execInstrBr, MachineState.setPC, h.ra, MachineState.setReg, h0]

end AsmVerif.RiscV.Exec
