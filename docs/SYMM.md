# SYMM: the symbolic executor on Lean's `SymM`

Plan for moving `sym_exec` (`AsmVerif/RiscV/Sym/`) and the proof patterns around it onto
`Lean.Meta.Sym`, the symbolic-computation layer shipped with our toolchain (v4.33.0). Status:
investigation only (2026-10-14). Nothing here is implemented.

## 1. What the build time actually is

Two modules were profiled with `-Dprofiler=true` and the executor's own trace
(`trace.AsmVerif.sym.time`). Both runs shared the machine with a full build, so absolute
times are inflated; the proportions are what matter.

| Module | Total | `sym_exec` | Executor steps | The rest |
|---|---|---|---|---|
| `Witness/OptionBytes32R0` | 84 s | 15 s (448 steps) | 11.6 s | 62 s: five byte-reconstruction lemmas (`subst …; apply word_ext; interval_cases k <;> simp only [byte_simp]`) |
| `Curve/ToAffine` | 363 s | 14 s (356 steps) | 14.1 s | 330 s: five `generalize … at *` after the run |

In both, the per-step cost of the executor is small: 25 to 40 ms per instruction, with the
local context growing to about 250 hypotheses. The dominant cost is ordinary `MetaM` tactics
run *after* the executor, over a context full of large machine-state terms:

- `generalize e = x at *` abstracts `e` in every hypothesis. Each `s_k` state term is a long
  chain of `setReg`/`setMem`/`setPC`, and `kabstract` walks it as a tree, not as the DAG it
  is. 34 proof files use `generalize`.
- The byte-reconstruction lemmas `subst` a chain of byte definitions into one term, split into
  64 cases, and run `simp` on each case, re-traversing the same unshared term each time. 21
  files use this pattern, 46 times, and `WitnessMidCells_*` does it 174 times per file.

The slowest modules of the last full build fall into three families:

1. **Executor-dominated**: `ParseMerklePath`, `SinsemillaCommitIvk`, `ArrayBytes32Ok`,
   `ToAffine`, `CommitIvk`. As `ToAffine` shows, "executor-dominated" can still mean the
   post-run tactics dominate.
2. **Byte reconstruction**: `WitnessMidCells_*`, `OptionBytes32R0`, `Array32R*`.
3. **Kernel-checked certificates**: `Contract/V_780361e0`, `V_78029d94`. These are the frame
   checker's reflective proofs, checked by kernel evaluation. Sym does not touch them;
   section 6 covers them separately.

## 2. What `Lean.Meta.Sym` provides

Source: `~/.elan/toolchains/leanprover--lean4---v4.33.0/src/lean/Lean/Meta/Sym*`. The new
`mvcgen` driver (`Lean/Elab/Tactic/Do/Internal/VCGen/`) is built on it and is the reference
client.

- **`SymM`**: goals are metavariables, but local contexts only grow; there is no `revert` or
  `clear`. A context is identified by its largest free variable, so checking a metavariable
  assignment is one hash lookup (`maxFVar`) instead of a traversal of both contexts.
- **Maximal sharing** (`AlphaShareCommon`, `AlphaShareBuilder`): terms are hash-consed, and
  `ReplaceS`, `InstantiateS`, `AbstractS` and `InstantiateMVarsS` traverse the DAG, not the
  tree. `abstractFVars` skips subterms whose largest free variable is below the ones being
  abstracted.
- **Structural matching and defeq**: reducible definitions are unfolded up front, proofs and
  instances are skipped during matching, and types are indexed. Matching is syntactic and has
  predictable cost.
- **`BackwardRule`** (`Sym/Apply`): a theorem with a precomputed `Pattern` and result
  positions, applied without `isDefEq`'s general machinery. Rules are cached under `repeat`.
- **`Sym.simp` / `Sym.dsimp`**: a structural simplifier over shared terms, with named
  *variants* (`register_sym_simp`: `pre`/`post` simproc chains), ground evaluation of literals
  (`EvalGround`), congruence information per function (`CongrInfo`) and a discharger.
- **`Sym.intro`**: intro without the general `MetaM` bookkeeping.
- **`GrindM` carried across goals**: hypotheses are *internalized* into grind's E-graph and
  arithmetic solvers once, and later goals reuse that state.
- **The `sym =>` tactic block**: interactive access to all of this (`intro`, `apply`, `simp
  variant`, `dsimp`, `internalize`, `finish`).

The output is an ordinary proof term, checked by the kernel. Sym adds no axioms and changes
no trust.

## 3. Where Sym fits

| Cost | Today | With Sym |
|---|---|---|
| `generalize … at *` over state terms | `kabstract` over each hypothesis, tree traversal | Not needed, see Phase 1; where an abstraction remains, `AbstractS` over shared terms |
| Byte reconstruction | `subst`, 64 cases, `simp` per case on unshared terms | One `Sym.simp` variant (`byte_simp` as `post` rules, `extractByte`/`replaceByte` as simprocs) over a shared term; or a decision lemma (Phase 2) |
| Executor step | `mkAppM` of a step lemma, `simpWith` per value, `isDefEq`, `introNP` | `BackwardRule` per instruction shape, `Sym.simp` variant for values, `Sym.intro` |
| Side conditions (address arithmetic, disjointness) | `omega` re-run on a filtered context per query (`omegaWith`: clear, simp, omega) | Hypotheses internalized once into grind's linear arithmetic; each query reuses that state |
| Context hygiene | `tryClearMany` per step; dead states stay in context otherwise | No clearing; context growth is O(1) per declaration, and nothing re-walks old hypotheses |
| Kernel checking of certificates | Reflection, kernel evaluation | Unaffected |

So Sym addresses the executor's internals and, more importantly, gives sharing-aware
primitives for the post-run work that dominates today. The biggest single win in the
measurements, however, comes from not running whole-context tactics at all after a run.

## 4. Plan

Every phase keeps the theorem statements unchanged, so each is a drop-in replacement
that a benchmark run can validate.

### Phase 0: a benchmark harness

- Pick a fixed benchmark set: `OptionBytes32R0`, `ToAffine`, `ParseMerklePath`,
  `WitnessMidCells_NN`, `SinsemillaCommitIvk`, `Runtime/MemcpySpec`, one main segment, and
  `Contract/V_780361e0`.
- Script it: profile each module alone (`lake env lean -Dprofiler=true`), and extract total,
  `sym_exec`, per-step and post-run time. Record a baseline in this file.
- Exit criterion: reproducible numbers on an idle machine.

### Phase 1: post-run context discipline (no Sym yet)

The measured 330 s and 62 s come from tactics that walk the whole context. Fix the shape of
the problem first; it is cheap and makes later phases measurable.

1. `sym_close` (and a new `sym_finish`) leaves a goal over the *values* the continuation
   needs, not the intermediate states. Every `s_k` and its facts are cleared once the run
   ends, or never introduced as hypotheses; the executor already tracks values as atoms with
   `_def` equations.
2. Replace `generalize e = x at *` in the 34 files with `generalize` at the goal (or at the
   named hypotheses that mention `e`). With item 1, `at *` has little left to walk.
3. Re-measure.

Exit criterion: `ToAffine` post-run time down from 330 s to seconds.

First experiment (2026-10-14, scratch copy, machine under load): narrowing the five
`generalize … at *` in `ToAffine` to `at hinvlt ⊢` cut its CPU time from 359 s to 128 s. The
remaining `generalize` time is spent on the goal itself, which is a large unshared term
after `sym_close`, so item 1 alone does not finish the job: the goal must be stated over
named values too (or abstracted with `AbstractS` over shared terms, Phase 3). Wall-clock
times from that run are unreliable (load average up to 27).

### Phase 2: byte reconstruction

Two candidates, measured against each other on `WitnessMidCells_NN`:

- **A decision lemma.** A word assembled from bytes is equal to a word read from a list
  iff a byte-wise equation over `Fin 8` holds, decided once per shape. `bv_decide` is allowed
  by our policies and fits fixed-width byte equations well; its axiom is already accepted.
- **`Sym.simp` with a `byte_simp` variant.** `extractByte`/`replaceByte`/`word8` as `post`
  rules and simprocs, run once over the shared reconstructed term instead of 64 times.

Either replaces the `subst …; apply word_ext; interval_cases k <;> simp` blocks (46 uses).
The executor's `asmverif.sym.foldBytes` byte folding should emit the same normal form, so
that most reconstructions disappear at the source.

Exit criterion: `WitnessMidCells_NN` well under a minute.

### Phase 3: the executor core on `SymM`

Port `AsmVerif/RiscV/Sym/Tactic.lean` (4.2k lines) piece by piece, keeping the `MetaM` path
until each piece matches it.

1. **Entry and goal.** `sym_exec` enters `SymM` (as `mvcgen` does) and preprocesses the goal
   into a `Grind.Goal`. Its state (`St`) holds shared terms.
2. **Steps as backward rules.** One `BackwardRule` per instruction shape: `SafeN.step_gen`
   instantiated with the step equation of `stepSp1_plain`, `stepSp1_mem`, the syscalls and
   the branches. Built once per run and cached.
3. **Values.** The register and memory rewrites (`simpWith` with `normLemmas`, `regRules`,
   `layoutRules`) become one `Sym.simp` variant with `BitVec` ground evaluation (`EvalGround`)
   and our simprocs for `Region`/`Unchanged` lookups.
4. **Intro.** `advance`'s `introNP` becomes `Sym.intro`. The per-step `tryClearMany` goes:
   `SymM` contexts only grow, and the operations no longer walk them.
5. **Specifications at call sites.** `applySpec` becomes a `BackwardRule` per specification.
   Its `isDefEq` conclusion check is the expensive general one today; structural matching
   fits, because specifications are stated over the same normal form.
6. **Fetch.** `prog_packed` and `getElem!_decodeWords_unpack` stay. The `decide` and `rfl`
   proofs of literal facts become ground evaluation where `EvalGround` covers them.

Exit criterion: the benchmark set's `sym_exec` time down by a measured factor, with identical
theorem statements.

### Phase 4: arithmetic side conditions through grind

`proveByOmega` and `omegaWith` re-run `omega` per query on a filtered context, with
heuristics for which facts to keep (clusters, disjointness splits, `mod 2^64` atoms). In
`SymM`, the facts the executor adds (`hdj*`, `hokm*`, `_def` equations, branch facts) are
internalized into grind's linear-arithmetic solver as they are created, and each query asks
that persistent state. `omega` stays as a fallback. Two points to check:

- Our side conditions mix `BitVec.toNat` with `% 2^64`. Grind's handling of these must
  match what `omega`'s preprocessing gives today.
- Disjointness facts are disjunctions. Internalizing them all may cost what the cluster
  filter avoids today; measure before choosing.

### Phase 5: remove the `MetaM` path

Once every benchmark module is at least as fast and the whole tree builds, delete the old
path and update `docs/PLAN.md`.

## 5. Constraints and risks

- **Sym is new.** It is marked `module`/`public section` and is clearly still evolving
  (`Grind` interactive mode, simp variants). A toolchain bump may change its API. Pin
  experiments to v4.33 and keep the port incremental.
- **Structural defeq.** Our code relies in places on `whnfD` and `decide` to unfold
  definitions such as the `Layout` projections, `run`, and `Ro.layout`. Sym unfolds only
  reducible definitions, eagerly. Each such definition must be reducible, given a rewrite
  rule, or evaluated by a simproc.
- **No `clear`.** The current executor clears dead facts to keep `omega`'s input small; in
  `SymM` that pressure moves to whatever consumes the context. The design of Phase 4 must
  not hand the whole context to a solver.
- **Proof terms.** Sharing in the elaborator does not bound the kernel's work. Kernel type
  checking is 5 s in both profiled modules and should be tracked through every phase.
- **Policy.** Nothing in this plan needs `native_decide`, new axioms or changes to
  riscv-zkvm. `bv_decide` (Phase 2) adds its usual axiom, which the policies allow.

## 6. Out of Sym's scope: the certificate checks

`Contract/V_*` modules check the frame checker's certificates by kernel evaluation (19
minutes for `V_780361e0` under contention; 141 s alone for `compress256`). Levers there are
on the checker's side: sharding a function's certificate by basic block, smaller
annotations, and fewer redundant facts per edge. They are tracked in `docs/PLAN.md`, not
here.

## 7. Open questions

- Does `Sym.simp` handle our `BitVec` workload (`BitVec.ofNat`, `toNat`, `+`/`-` modulo
  `2^64`, `extractByte`) with simprocs alone, or does it need `BitVec` support from grind?
- Can the `sym =>` interactive block serve for the hand-written parts of proofs (Phases 1
  and 2) before the executor itself moves?
- How much of `mvcgen`'s VCGen driver (`RuleCache`, `SpecDB`, `FrameProc`) can serve as a
  template for the executor's specification table and frame handling?
