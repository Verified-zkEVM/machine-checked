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

/-- A return that writes no owned static: the postcondition without the module invariant,
    which follows (`Post.of_ret`). What a leaf function's proof establishes. -/
def Ret (σ : Iface) (s t : MachineState) : Prop :=
  σ.returns = true ∧ t.pc = s.getReg .x1 &&& ~~~1#64 ∧
  (∀ r ∈ savedRegs, t.getReg r = s.getReg r) ∧
  (∀ a, Aligned a → ¬ Written σ (regsOf s) a → t.getMem a = s.getMem a) ∧
  t.code = s.code

/-- A function that writes no owned key keeps the module invariant; one that writes no
    writer's key keeps every writer. -/
theorem Post.of_ret {env : Env} {σ : Iface} {s t : MachineState}
    (hown : ∀ a, Aligned a → env.InOwn a → ¬ Written σ (regsOf s) a)
    (hinv : env.Inv s.getMem ∧ StrsPre env σ (regsOf s) s.getMem) (h : Ret σ s t) :
    Post env σ s t :=
  ⟨h.1, h.2.1, h.2.2.1, fun a ha hnw _ _ => h.2.2.2.1 a ha hnw, h.2.2.2.2,
    Env.Inv_congr (fun a ha ho => h.2.2.2.1 a ha (hown a ha ho)) hinv.1,
    fun e he => Model.Keeps.of_congr (hinv.2.1 e he).1 fun a hh =>
      h.2.2.2.1 a (Model.hit_aligned hh) ((hinv.2.1 e he).2.1 a hh).1,
    fun _ _ hw hh => Model.Keeps.of_congr hw fun a ha =>
      h.2.2.2.1 a (Model.hit_aligned ha) (hh a ha).1⟩

/-- An interface with an empty window writes no owned key: its footprint avoids them. -/
theorem Pre.own_not_written {env : Env} {C : Word → Option Instr} {σ : Iface}
    {s : MachineState} (h0 : σ.depth = 0) (hpre : Pre env C σ s) :
    ∀ a, Aligned a → env.InOwn a → ¬ Written σ (regsOf s) a := by
  rintro a ha ho (hw | ⟨it, hit, hh⟩)
  · rw [h0] at hw; simp [InWin, Hits] at hw
  · exact (hpre.2.2.2.2.2.1 it hit a ha hh).2.2 ho

/-- An interface holds at budget `n` if an invariant holds at the entry and every cut
    state is safe given that every cut state is safe for smaller budgets. The function
    writes no owned key (`hown`), so its returns keep the module invariant. -/
theorem holdsN_of_inv {env : Env} {C : Word → Option Instr} {σ : Iface} {n : Nat}
    (Inv : MachineState → MachineState → Prop)
    (hown : ∀ s0, Pre env C σ s0 → ∀ a, Aligned a → env.InOwn a → ¬ Written σ (regsOf s0) a)
    (hentry : ∀ s0, s0.pc = σ.entry → Pre env C σ s0 → Inv s0 s0)
    (hstep : ∀ (G : MachineState → Prop) s0 (P : Prop) k, s0.pc = σ.entry → Pre env C σ s0 →
      k ≤ n →
      (∀ t, Ret σ s0 t → SafeN G k P t) →
      (∀ m < k, ∀ t, Inv s0 t → SafeN G m P t) →
      ∀ s, Inv s0 s → SafeN G k P s) :
    σ.HoldsN env C n := by
  intro G _ P s0 hpc hpre hk
  have key : ∀ k, k ≤ n → ∀ s, Inv s0 s → SafeN G k P s := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hkn s hs
      exact hstep G s0 P k hpc hpre hkn
        (fun t ht => SafeN.mono hkn (hk t (Post.of_ret (hown s0 hpre) hpre.2.2.2.2.2.2.2.2.2 ht)))
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
theorem safe_step {G : MachineState → Prop} {k : Nat} {P : Prop} {s : MachineState} {i : Instr}
    (hf : s.code s.pc = some i) (he : i ≠ .ECALL) (hb : i ≠ .EBREAK)
    (hc : ∀ c r, i ≠ .CSRS c r)
    (h : memOkSp1 s i = true → SafeN G k P (execInstrBr s i)) : SafeN G k P s := by
  have hs := stepSp1_eq hf he hb hc
  by_cases hm : memOkSp1 s i = true
  · rw [if_pos hm] at hs
    exact SafeN.of_step (not_accepted_of_code hf he) hs (h hm)
  · rw [if_neg hm] at hs
    exact SafeN.stuck hs (fun ha => absurd ha (not_accepted_of_code hf he))

/-- Execute one instruction, spending one unit of budget. -/
theorem safe_step1 {G : MachineState → Prop} {k : Nat} {P : Prop} {s : MachineState} {i : Instr}
    (hf : s.code s.pc = some i) (he : i ≠ .ECALL) (hb : i ≠ .EBREAK)
    (hc : ∀ c r, i ≠ .CSRS c r)
    (h : memOkSp1 s i = true → SafeN G k P (execInstrBr s i)) : SafeN G (k + 1) P s := by
  have hs := stepSp1_eq hf he hb hc
  by_cases hm : memOkSp1 s i = true
  · rw [if_pos hm] at hs
    exact SafeN.step (not_accepted_of_code hf he) hs (h hm)
  · rw [if_neg hm] at hs
    exact SafeN.stuck hs (fun ha => absurd ha (not_accepted_of_code hf he))

/-- A load whose value does not matter: the destination register takes an arbitrary value.
    Keeping it abstract keeps the state small. -/
theorem safe_load {G : MachineState → Prop} {k : Nat} {P : Prop} {s : MachineState} {i : Instr}
    (hf : s.code s.pc = some i) {rd rs : Reg} {off : BitVec 12} {isD : Bool}
    (hl : loadOf i = some (rd, rs, off, isD))
    (h : ∀ v, SafeN G k P ((s.setReg rd v).setPC (s.pc + 4))) : SafeN G k P s := by
  have hne : i ≠ .ECALL ∧ i ≠ .EBREAK ∧ ∀ c r, i ≠ .CSRS c r := by
    cases i <;> simp [loadOf] at hl <;> exact ⟨Instr.noConfusion, Instr.noConfusion, fun _ _ h => Instr.noConfusion h⟩
  refine safe_step hf hne.1 hne.2.1 hne.2.2 fun _ => ?_
  obtain ⟨w, hw, _⟩ := loadOf_shape (s := s) hl
  rw [hw]; exact h w

theorem safe_load1 {G : MachineState → Prop} {k : Nat} {P : Prop} {s : MachineState} {i : Instr}
    (hf : s.code s.pc = some i) {rd rs : Reg} {off : BitVec 12} {isD : Bool}
    (hl : loadOf i = some (rd, rs, off, isD))
    (h : ∀ v, SafeN G k P ((s.setReg rd v).setPC (s.pc + 4))) : SafeN G (k + 1) P s := by
  have hne : i ≠ .ECALL ∧ i ≠ .EBREAK ∧ ∀ c r, i ≠ .CSRS c r := by
    cases i <;> simp [loadOf] at hl <;> exact ⟨Instr.noConfusion, Instr.noConfusion, fun _ _ h => Instr.noConfusion h⟩
  refine safe_step1 hf hne.1 hne.2.1 hne.2.2 fun _ => ?_
  obtain ⟨w, hw, _⟩ := loadOf_shape (s := s) hl
  rw [hw]; exact h w

/-- What SP1's memory check gives an access of `w` bytes at `a`: the address is below
    SP1's memory bound, and naturally aligned. -/
theorem memOk_addr {s : MachineState} {i : Instr} {a : Word} {w : Nat} {st : Bool}
    (hacc : memAccess s i = some (a, w, st)) (h : memOkSp1 s i = true) :
    a.toNat < SP1_MAX_MEMORY ∧ alignedFor w a = true := by
  simp only [memOkSp1, hacc, Bool.and_eq_true, isValidMemAddrSp1, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2⟩

/-! ## Reading a state after a step -/

@[simp] theorem pc_setPC (s : MachineState) (v : Word) : (s.setPC v).pc = v := rfl

/-! State normal form: one `setPC` outermost, register writes collapsed.

These are proved by `cases s` rather than `rfl` on purpose: `simp` applies a `rfl` lemma as a
definitional change, and the kernel then re-checks it by unfolding the whole state term, which
on a long straight-line run recurses too deep. -/

theorem setPC_setPC (s : MachineState) (a b : Word) : (s.setPC a).setPC b = s.setPC b := by
  cases s; rfl

theorem setReg_setPC (s : MachineState) (a : Word) (r : Reg) (v : Word) :
    (s.setPC a).setReg r v = (s.setReg r v).setPC a := by
  cases r <;> rfl

theorem setMem_setPC (s : MachineState) (a x v : Word) :
    (s.setPC a).setMem x v = (s.setMem x v).setPC a := by
  cases s; rfl

theorem setByte_setPC (s : MachineState) (a x : Word) (b : BitVec 8) :
    (s.setPC a).setByte x b = (s.setByte x b).setPC a := by
  cases s; rfl

theorem setHalfword_setPC (s : MachineState) (a x : Word) (b : BitVec 16) :
    (s.setPC a).setHalfword x b = (s.setHalfword x b).setPC a := by
  cases s; rfl

theorem setWord32_setPC (s : MachineState) (a x : Word) (b : BitVec 32) :
    (s.setPC a).setWord32 x b = (s.setWord32 x b).setPC a := by
  cases s; rfl

theorem setReg_setReg_same (s : MachineState) (r : Reg) (a b : Word) :
    (s.setReg r a).setReg r b = s.setReg r b := by
  cases r <;> simp only [MachineState.setReg] <;> congr 1 <;> funext r' <;> split <;> rfl

theorem setPC_self {s : MachineState} {p : Word} (h : s.pc = p) : s.setPC p = s := by
  subst h; rfl

@[simp] theorem getReg_x0 (s : MachineState) : s.getReg .x0 = 0 := rfl

theorem getReg_setReg (s : MachineState) (r r' : Reg) (v : Word) :
    (s.setReg r v).getReg r' = if r' = r ∧ r ≠ .x0 then v else s.getReg r' := by
  cases r <;> cases r' <;> rfl

@[simp] theorem getReg_setByte (s : MachineState) (a : Word) (b : BitVec 8) (r : Reg) :
    (s.setByte a b).getReg r = s.getReg r := by
  cases r <;> rfl

@[simp] theorem getReg_setWord32 (s : MachineState) (a : Word) (b : BitVec 32) (r : Reg) :
    (s.setWord32 a b).getReg r = s.getReg r := by
  cases r <;> rfl

@[simp] theorem getReg_setHalfword (s : MachineState) (a : Word) (b : BitVec 16) (r : Reg) :
    (s.setHalfword a b).getReg r = s.getReg r := by
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

theorem setWord32 (h : Frame σ C s0 s) {a : Word}
    (hk : Aligned (alignToDword a) → Written σ (regsOf s0) (alignToDword a)) (b : BitVec 32) :
    Frame σ C s0 (s.setWord32 a b) :=
  h.setMem hk _

theorem setHalfword (h : Frame σ C s0 s) {a : Word}
    (hk : Aligned (alignToDword a) → Written σ (regsOf s0) (alignToDword a)) (b : BitVec 16) :
    Frame σ C s0 (s.setHalfword a b) :=
  h.setMem hk _

end Frame

/-- A `ret` from a state that keeps the frame: the postcondition, so the continuation
    applies. -/
theorem safe_ret {σ : Iface} {C : Word → Option Instr} {s0 s : MachineState}
    {G : MachineState → Prop} {k : Nat} {P : Prop} (hσ : σ.returns = true) (h : Frame σ C s0 s)
    (hf : s.code s.pc = some (.JALR .x0 .x1 0)) (hk : ∀ t, Ret σ s0 t → SafeN G k P t) :
    SafeN G k P s := by
  refine safe_step (k := k) (P := P) hf (by decide) (by decide) (by intro c r h; cases h) ?_
  intro _
  apply hk (execInstrBr s (.JALR .x0 .x1 0))
  refine ⟨hσ, ?_, fun r hr => h.saved r hr, h.mem, by simp [execInstrBr, MachineState.setPC, h.code, h.code0]⟩
  · have h0 : signExtend12 0#12 = 0 := by decide
    simp [execInstrBr, MachineState.setPC, h.ra, MachineState.setReg, h0]

/-! ## System calls -/

/-- An `ecall` that is not a halt, with what its successor keeps: safe if every such
    successor is. -/
theorem safe_ecall {G : MachineState → Prop} {k : Nat} {P : Prop} {x : MachineState}
    {kept : Bool} {rs : List (Word × Nat)} (h5 : x.getReg .x5 ≠ 0)
    (hnext : ∀ y, stepSp1 x = some y → SysNext x y kept rs)
    (h : ∀ y, SysNext x y kept rs → SafeN G k P y) : SafeN G k P x := by
  cases hs : stepSp1 x with
  | none => exact SafeN.stuck hs (fun ha => absurd ha.2.1 h5)
  | some y => exact SafeN.of_step (fun ha => h5 ha.2.1) hs (h y (hnext y hs))

/-- A halt with a nonzero exit code does not accept: the run ends there, safely. -/
theorem safe_halt {G : MachineState → Prop} {k : Nat} {P : Prop} {x : MachineState}
    (hf : x.code x.pc = some .ECALL) (h5 : x.getReg .x5 = 0) (h10 : x.getReg .x10 ≠ 0) :
    SafeN G k P x :=
  SafeN.stuck (stepSp1_halt hf h5) (fun ha => absurd ha.2.2 h10)

end AsmVerif.RiscV.Exec
