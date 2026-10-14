/-
  AsmVerif.RiscV.Sym.Core

  The facts about the trusted stepper everything else rests on.

  * `run k s`: `k` steps of `stepSp1`, the SP1 backend of `riscv-zkvm`'s RV64IM model
    (`stepNOn .sp1`), with its composition lemmas.
  * The code facts the specifications take: `CodeAt base prog s` (the decoded
    instructions of one function are loaded at `base`, as `gen-image` emits them in a
    case's `Image` modules) and `CodeWithin lo hi s` (the code map is confined to the
    `.text` window, which `memOkSp1` needs to admit a store). `stepSp1` never changes
    the code map (`code_stepSp1`), so both are preserved by every run.
  * One step equation per instruction shape (`stepSp1_plain`, `stepSp1_mem`, the
    syscalls), which the executor (`AsmVerif.RiscV.Sym.Sym`) rewrites with.
  * `Accepted s`: the observation. An accepting state is at an `ECALL` with `t0 = 0`
    (`HALT`) and `a0 = 0` (exit code 0), and it is stuck (`stepSp1_of_accepted`).

  `stepSp1` is a function, so runs are deterministic: a state the run passes through
  is on every longer run from the same start (`run_prefix`). The judgement the proofs
  are written in is `AsmVerif.RiscV.Sym.Safe`.
-/

import RiscvZkvm.Rv64
import RiscvZkvm.Rv64.StepOn
import RiscvZkvm.Interpreter
import AsmVerif.RiscV.Accept

namespace AsmVerif.RiscV.Sym

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter

/-! ## The run -/

/-- `k` steps of the SP1 backend. This is the model's own iteration; it is
    given a short name so statements stay readable. -/
abbrev run (k : Nat) (s : MachineState) : Option MachineState := stepNOn .sp1 k s

@[simp] theorem run_zero (s : MachineState) : run 0 s = some s := rfl

theorem run_succ (k : Nat) (s : MachineState) :
    run (k + 1) s = (stepSp1 s).bind (run k) := rfl

theorem run_succ_of_step {k : Nat} {s s₁ : MachineState} (h : stepSp1 s = some s₁) :
    run (k + 1) s = run k s₁ := by
  rw [run_succ, h]; rfl

theorem run_add (m n : Nat) (s : MachineState) :
    run (m + n) s = (run m s).bind (run n) := by
  induction m generalizing s with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, run_succ, run_succ]
    cases stepSp1 s with
    | none => rfl
    | some s₁ => simpa using ih s₁

/-- Composition: a run of `m` steps to `s₁` followed by `n` steps to `s₂`. -/
theorem run_trans {m n : Nat} {s s₁ s₂ : MachineState}
    (h₁ : run m s = some s₁) (h₂ : run n s₁ = some s₂) : run (m + n) s = some s₂ := by
  rw [run_add, h₁]; exact h₂

/-- Determinism, in the form soundness needs: a longer run passes through the
    state a shorter one reaches. -/
theorem run_prefix {m n : Nat} {s s₁ s₂ : MachineState} (hmn : m ≤ n)
    (h₁ : run m s = some s₁) (h₂ : run n s = some s₂) : run (n - m) s₁ = some s₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [run_add, h₁] at h₂
  simpa using h₂

/-- A stuck run stays stuck. -/
theorem run_none_of_le {m n : Nat} {s : MachineState} (hmn : m ≤ n)
    (h : run m s = none) : run n s = none := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [run_add, h]; rfl

/-! ## The code hypothesis -/

/-- The loaded code map agrees with `prog` -- a list of decoded words, `none`
    marking a hole (an encoding `decode` does not model, so the loader inserted
    nothing) -- at every index. Stated over `Option Instr` rather than `Instr`
    so that a function containing an `unimp` can be named. -/
def CodeAt (base : Word) (prog : List (Option Instr)) (s : MachineState) : Prop :=
  ∀ i : Nat, i < prog.length → s.code (base + BitVec.ofNat 64 (4 * i)) = prog[i]!

/-- The code map is confined to `[lo, hi)`. This is SP1's store invariant: with
    it, a store whose target is outside the window is known to hit no code. -/
def CodeWithin (lo hi : Nat) (s : MachineState) : Prop :=
  ∀ a : Word, s.code a ≠ none → lo ≤ a.toNat ∧ a.toNat < hi

theorem codeAt_of_code_eq {base : Word} {prog : List (Option Instr)} {s s' : MachineState}
    (hc : s'.code = s.code) (h : CodeAt base prog s) : CodeAt base prog s' := by
  intro i hi; rw [hc]; exact h i hi

theorem codeWithin_of_code_eq {lo hi : Nat} {s s' : MachineState}
    (hc : s'.code = s.code) (h : CodeWithin lo hi s) : CodeWithin lo hi s' := by
  intro a ha; rw [hc] at ha; exact h a ha

/-- `HINT_READ` never rewrites code: it writes `mem` and drops the consumed
    prefix of `privateInput`, and `code` is a separate field. -/
theorem code_hintRead {s s' : MachineState} (h : hintRead s = some s') :
    s'.code = s.code := by
  -- `simp only` rather than `unfold`, because `hintRead`'s body binds its
  -- intermediate states with `have`, which `split` cannot see through.
  simp only [hintRead] at h
  split at h
  · simp at h                             -- stream exhausted
  · split at h
    · simp at h                           -- `a0` misaligned
    · split at h
      · simp at h                         -- write window out of range or on code
      · split at h
        · simp at h                       -- `a1` disagrees with the length
        · split at h
          · simp at h                     -- payload short
          · simp only [Option.some.injEq] at h; subst h; simp

/-- `stepSp1` never rewrites code. Every arm either traps, or ends in one of
    `execInstrBr` / `execSp1Accel` / `setReg` / `setMem` / `setPC` /
    `writeBytesAsWords` / a `privateInput` field update / `sp1Commit` (each has an
    `@[simp]` code-preservation lemma upstream or leaves the field untouched), or
    delegates to `step`, which has `code_step`.

    The splits are written out rather than driven by `repeat' split`: the SP1
    dispatch chain is six deep, and a greedy `repeat'` walks on past it into
    `execSp1Accel`'s own `match`. -/
theorem code_stepSp1 {s s' : MachineState} (h : stepSp1 s = some s') :
    s'.code = s.code := by
  unfold stepSp1 at h
  split at h
  · simp at h                             -- nothing fetched
  · simp at h                             -- `.CSRS`: traps under SP1
  · -- `.ECALL`: the SP1 syscall dispatch
    simp only [sp1Ecall] at h
    split at h
    · -- an accelerator id
      split at h
      · simp only [Option.some.injEq] at h; subst h; simp
      · simp at h                         -- bad operands, or a side condition
    · split at h
      · -- HINT_LEN
        simp only [Option.some.injEq] at h; subst h; simp [hintLen]
      · split at h
        · exact code_hintRead h           -- HINT_READ
        · split at h
          · -- COMMIT
            simp only [Option.some.injEq] at h; subst h; simp [MachineState.sp1Commit]
          · split at h
            · -- COMMIT_DEFERRED_PROOFS: an explicit no-op
              simp only [Option.some.injEq] at h; subst h; simp
            · split at h
              · exact code_step h         -- the enumerated host syscalls
              · simp at h                 -- unmodelled id: traps
  · simp at h                             -- `.EBREAK`
  · -- the backend-independent catch-all, gated on the SP1 memory profile
    split at h
    · split at h
      · simp only [Option.some.injEq] at h; subst h; simp
      · simp at h                         -- outside SP1's addressable space
    · simp only [Option.some.injEq] at h; subst h; simp

theorem code_run {k : Nat} {s s' : MachineState} (h : run k s = some s') : s'.code = s.code := by
  induction k generalizing s with
  | zero => simp at h; subst h; rfl
  | succ k ih =>
    rw [run_succ] at h
    cases hs : stepSp1 s with
    | none => rw [hs] at h; exact absurd h (by simp)
    | some s₁ =>
      rw [hs] at h
      exact (ih (by simpa using h)).trans (code_stepSp1 hs)

theorem codeAt_run {base : Word} {prog : List (Option Instr)} {k : Nat} {s s' : MachineState}
    (h : run k s = some s') (hc : CodeAt base prog s) : CodeAt base prog s' :=
  codeAt_of_code_eq (code_run h) hc

theorem codeWithin_run {lo hi : Nat} {k : Nat} {s s' : MachineState}
    (h : run k s = some s') (hc : CodeWithin lo hi s) : CodeWithin lo hi s' :=
  codeWithin_of_code_eq (code_run h) hc

/-- The fetch fact a block lemma reads off its code hypothesis: the instruction
    at index `i` of `prog`, when the pc is `base + 4 i`. -/
theorem fetch_of_codeAt {base : Word} {prog : List (Option Instr)} {s : MachineState}
    (hc : CodeAt base prog s) (i : Nat) (hi : i < prog.length) {ins : Instr}
    (hprog : prog[i]! = some ins) (hpc : s.pc = base + BitVec.ofNat 64 (4 * i)) :
    s.code s.pc = some ins := by
  rw [hpc, hc i hi, hprog]

/-! ## Step equations

One per instruction class, each turning a fetch fact (and, for memory, the
`memOkSp1` side condition) into `stepSp1 s = some (execInstrBr s i)`. The block
tactic applies these and then unfolds `execInstrBr`. -/

/-- A non-memory, non-system instruction steps to `execInstrBr`. -/
theorem stepSp1_plain {s : MachineState} {i : Instr}
    (hfetch : s.code s.pc = some i)
    (hmem : i.isMemAccess = false) (hecall : i ≠ .ECALL) (hbreak : i ≠ .EBREAK) :
    stepSp1 s = some (execInstrBr s i) := by
  rw [stepSp1_eq_step_of_fetch hfetch hmem hecall hbreak]
  exact step_non_ecall_non_mem hfetch hecall hbreak hmem

/-- `.CSRS`, the other backend's accelerator call; `stepSp1` traps on it. -/
def isCSRS : Instr → Bool
  | .CSRS _ _ => true
  | _ => false

/-- A memory instruction whose access is permitted steps to `execInstrBr`. -/
theorem stepSp1_mem {s : MachineState} {i : Instr}
    (hfetch : s.code s.pc = some i) (hmem : i.isMemAccess = true)
    (hcsrs : isCSRS i = false) (hok : memOkSp1 s i = true) :
    stepSp1 s = some (execInstrBr s i) := by
  unfold stepSp1; rw [hfetch]
  cases i <;> simp_all [Instr.isMemAccess, isCSRS]

/-- A memory instruction whose access is refused traps. -/
theorem stepSp1_mem_trap {s : MachineState} {i : Instr}
    (hfetch : s.code s.pc = some i) (hmem : i.isMemAccess = true)
    (hcsrs : isCSRS i = false) (hok : memOkSp1 s i = false) :
    stepSp1 s = none := by
  unfold stepSp1; rw [hfetch]
  cases i <;> simp_all [Instr.isMemAccess, isCSRS]

/-- No code at the pc: the machine is stuck. -/
theorem stepSp1_none {s : MachineState} (h : s.code s.pc = none) : stepSp1 s = none := by
  unfold stepSp1; rw [h]

theorem stepSp1_ebreak {s : MachineState} (h : s.code s.pc = some .EBREAK) : stepSp1 s = none := by
  unfold stepSp1; rw [h]

/-- The `HALT` syscall: `t0 = 0` at an `ECALL` stops the machine. -/
theorem stepSp1_halt {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = 0) : stepSp1 s = none := by
  have hhost : Sp1.isHostId (s.getReg .x5) = true := by rw [ht0]; decide
  rw [stepSp1_ecall_host hfetch hhost]
  exact step_ecall_halt hfetch ht0

/-- `COMMIT` (`0x10`): the digest word is recorded and the pc advances. -/
theorem stepSp1_commit {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.COMMIT) :
    stepSp1 s = some ((s.sp1Commit).setPC (s.pc + 4)) := by
  unfold stepSp1 sp1Ecall; rw [hfetch, ht0]
  simp [Sp1.isAccelId, Sp1.COMMIT, Sp1.HINT_LEN, Sp1.HINT_READ, Sp1.KECCAK_PERMUTE, Sp1.SECP256K1_ADD, Sp1.SECP256K1_DOUBLE, Sp1.BN254_ADD, Sp1.BN254_DOUBLE, Sp1.BLS12381_ADD, Sp1.BLS12381_DOUBLE, Sp1.BLS12381_FP2_ADD, Sp1.BLS12381_FP2_SUB, Sp1.BLS12381_FP2_MUL, Sp1.BN254_FP2_ADD, Sp1.BN254_FP2_SUB, Sp1.BN254_FP2_MUL, Sp1.UINT256_MUL, Sp1.PALLAS_ADD, Sp1.PALLAS_DOUBLE]

/-- `COMMIT_DEFERRED_PROOFS` (`0x1a`): a no-op that advances the pc. -/
theorem stepSp1_commit_deferred {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.COMMIT_DEFERRED_PROOFS) :
    stepSp1 s = some (s.setPC (s.pc + 4)) := by
  unfold stepSp1 sp1Ecall; rw [hfetch, ht0]
  simp [Sp1.isAccelId, Sp1.COMMIT, Sp1.COMMIT_DEFERRED_PROOFS, Sp1.HINT_LEN, Sp1.HINT_READ,
    Sp1.KECCAK_PERMUTE, Sp1.SECP256K1_ADD, Sp1.SECP256K1_DOUBLE, Sp1.BN254_ADD, Sp1.BN254_DOUBLE, Sp1.BLS12381_ADD, Sp1.BLS12381_DOUBLE, Sp1.BLS12381_FP2_ADD, Sp1.BLS12381_FP2_SUB, Sp1.BLS12381_FP2_MUL, Sp1.BN254_FP2_ADD, Sp1.BN254_FP2_SUB, Sp1.BN254_FP2_MUL, Sp1.UINT256_MUL, Sp1.PALLAS_ADD, Sp1.PALLAS_DOUBLE]

/-- `HINT_LEN` (`0xf0`). -/
theorem stepSp1_hintLen {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.HINT_LEN) : stepSp1 s = some (hintLen s) := by
  unfold stepSp1 sp1Ecall; rw [hfetch, ht0]
  simp [Sp1.isAccelId, Sp1.HINT_LEN, Sp1.KECCAK_PERMUTE, Sp1.SECP256K1_ADD, Sp1.SECP256K1_DOUBLE, Sp1.BN254_ADD, Sp1.BN254_DOUBLE, Sp1.BLS12381_ADD, Sp1.BLS12381_DOUBLE, Sp1.BLS12381_FP2_ADD, Sp1.BLS12381_FP2_SUB, Sp1.BLS12381_FP2_MUL, Sp1.BN254_FP2_ADD, Sp1.BN254_FP2_SUB, Sp1.BN254_FP2_MUL, Sp1.UINT256_MUL, Sp1.PALLAS_ADD, Sp1.PALLAS_DOUBLE]

/-- `HINT_READ` (`0xf1`). -/
theorem stepSp1_hintRead {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.HINT_READ) : stepSp1 s = hintRead s := by
  unfold stepSp1 sp1Ecall; rw [hfetch, ht0]
  simp [Sp1.isAccelId, Sp1.HINT_LEN, Sp1.HINT_READ, Sp1.KECCAK_PERMUTE, Sp1.SECP256K1_ADD, Sp1.SECP256K1_DOUBLE, Sp1.BN254_ADD, Sp1.BN254_DOUBLE, Sp1.BLS12381_ADD, Sp1.BLS12381_DOUBLE, Sp1.BLS12381_FP2_ADD, Sp1.BLS12381_FP2_SUB, Sp1.BLS12381_FP2_MUL, Sp1.BN254_FP2_ADD, Sp1.BN254_FP2_SUB, Sp1.BN254_FP2_MUL, Sp1.UINT256_MUL, Sp1.PALLAS_ADD, Sp1.PALLAS_DOUBLE]

/-- An accelerator syscall with valid operands. -/
theorem stepSp1_accel' {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (hid : Sp1.isAccelId (s.getReg .x5) = true)
    (hvalid : s.sp1AccelValid (s.getReg .x5) = true) :
    stepSp1 s = some ((s.execSp1Accel (s.getReg .x5)).setPC (s.pc + 4)) :=
  stepSp1_accel hfetch hid hvalid

/-! ## Accepting -/

-- The accept observation (`AsmVerif.RiscV.Accepted`): the machine is at the `HALT`
-- syscall with exit code `0`.
export AsmVerif.RiscV (Accepted)

/-- Reaching a state the machine cannot step from is final: nothing after it
    is `Accepted` (or anything else). -/
theorem run_of_stuck {s s' : MachineState} {k : Nat} (hstuck : stepSp1 s = none)
    (h : run k s = some s') : k = 0 ∧ s' = s := by
  cases k with
  | zero => simp at h; exact ⟨rfl, h.symm⟩
  | succ k => rw [run_succ, hstuck] at h; exact absurd h (by simp)

/-- An accepting state is itself stuck (`HALT` stops the machine). -/
theorem stepSp1_of_accepted {s : MachineState} (h : Accepted s) : stepSp1 s = none :=
  stepSp1_halt h.1 h.2.1

/-- **The soundness transfer.** If the run from `s₀` reaches `s₁` and from
    `s₁` never accepts, then the run from `s₀` never accepts *after* `s₁`; and
    if the states strictly before `s₁` are also not accepting, the run from
    `s₀` never accepts at all. Stated in the form `main`'s proof uses: a
    forward execution to a state, then a verdict about the remainder. -/
theorem not_accepted_of_run {s₀ s₁ : MachineState} {m : Nat} (h : run m s₀ = some s₁)
    (hbefore : ∀ k s', k < m → run k s₀ = some s' → ¬ Accepted s')
    (hafter : ∀ k s', run k s₁ = some s' → ¬ Accepted s') :
    ∀ k s', run k s₀ = some s' → ¬ Accepted s' := by
  intro k s' hk
  by_cases hkm : k < m
  · exact hbefore k s' hkm hk
  · have := run_prefix (Nat.le_of_not_lt hkm) h hk
    exact hafter _ _ this

/-- A state before an accepting halt on a run that is still going cannot be
    accepting: acceptance is stuck. -/
theorem not_accepted_of_run_succ {s s' : MachineState} {k : Nat}
    (h : run (k + 1) s = some s') : ¬ Accepted s := by
  intro ha
  rw [run_succ, stepSp1_of_accepted ha] at h
  exact absurd h (by simp)

/-- Along a run that continues for at least `m` steps, no intermediate state
    is accepting -- so `hbefore` in `not_accepted_of_run` is automatic. -/
theorem not_accepted_before {s₀ s₁ : MachineState} {m : Nat} (h : run m s₀ = some s₁) :
    ∀ k s', k < m → run k s₀ = some s' → ¬ Accepted s' := by
  intro k s' hkm hk
  have hrest := run_prefix (Nat.le_of_lt hkm) hk h
  obtain ⟨d, hd⟩ : ∃ d, m - k = d + 1 := ⟨m - k - 1, by omega⟩
  rw [hd] at hrest
  exact not_accepted_of_run_succ hrest

/-- The forward-execution form of soundness: if the run from `s₀` reaches `s₁`
    then any accepting state the run from `s₀` reaches is one the run from
    `s₁` reaches. -/
theorem accepted_of_run {s₀ s₁ : MachineState} {m : Nat} (h : run m s₀ = some s₁)
    {k : Nat} {s' : MachineState} (hk : run k s₀ = some s') (ha : Accepted s') :
    ∃ j, run j s₁ = some s' := by
  by_cases hkm : k < m
  · exact absurd ha (not_accepted_before h k s' hkm hk)
  · exact ⟨k - m, run_prefix (Nat.le_of_not_lt hkm) h hk⟩

end AsmVerif.RiscV.Sym
