# PLAN

The goal is to take care of the ELF in general. A guest's program logic should only have to
state and prove what its own functions compute. Everything else is a theorem here: the
loaded image, the calling convention, memory footprints, the stack, statics, indirect
control flow, syscalls and the SP1 runtime (entry, allocator, libc routines, panics).

zip-2005 is the worked example. Its program logic, `main` and the crypto, is phase F and out of
scope for now. The bar is zip-2005-asm's lesson: no hypothesis that the real run does not
satisfy, and no contract quantified over states the run never reaches.

## Architecture

**Judgement.** `SafeN n P s`: every accepting state reached from `s` in fewer than `n` steps
satisfies `P`. `Safe P s := ∀ n, SafeN n P s`. A function specification is in continuation
form, *step-indexed*:

    ∀ P n s, s.pc = entry → pre s → (∀ t, post s t → SafeN n P t) → SafeN n P s

The same budget `n` appears on both sides. This is what lets a caller's proof use a callee's
specification inside an induction on the budget. That covers loops, recursion, and a
function that calls back into its caller. Executor proofs carry `n` through unchanged, since a
step preserves `SafeN n`.

**Structural specification** of a function. It is derived by the frame checker, or proved
by hand where the checker cannot:
- `pre`: the code is the image's; `D ≤ sp ≤ STACK_TOP`, where `D` is the function's
  worst-case stack use, callees included; and the premises `reqs` over the entry registers.
- `post`: `t.pc = ra & ~1`; `sp`, `gp`, `tp` and `s0`–`s11` hold their entry values; and
  memory outside the footprint `W(entry)` is unchanged. `W` is the frame window
  `[sp - D, sp)` plus regions given by entry registers (`a0 + k`, length a constant or an
  entry register) and constant addresses.
- A function that cannot return has `post = False`. Calls to it are how "noreturn" stops
  being an assumption.
- No internal accepting halt. A halt's exit code must be provably nonzero (a `req` if it
  comes from an argument).

**Contract table.** A map from entry address to specification. Each entry is derived by
the checker or proved with the executor. The checker proves a function's specification from
its certificate, assuming its callees' specifications. Composition is a strong induction on
the budget over the whole table. A callee's `reqs` and footprint are instantiated at the
call site with the caller's abstract argument values. The result is either discharged
there, or becomes the caller's own `req`. An indirect call or tail call takes a candidate
list and a control-flow premise (`CfiOk`) that the target is on it.

## Phases

**A. Structural specifications for one function, derived by the checker**
- A1. Exit check: `ra`, `sp`, `gp`, `tp`, `s0`–`s11` restored. Protect the slots that
  save callee-saved registers, not only `ra`.
- A2. Footprints and stack depth. Classify each store as frame, entry-relative, constant or
  unknown. A footprint list is declared in the certificate and the kernel checks it. Add
  disjointness `reqs` to keep frame slots across stores and calls. A store through an
  unknown pointer makes the function ineligible for a derived specification; it needs a
  proved one.
- A3. `ECALL`: halt (code nonzero), write, hint length and read, commit, deferred-proof
  commit and the precompiles. Each has a footprint and the registers it writes, proved
  against riscv-zkvm's `sp1Ecall`.
- A4. The soundness theorem. A valid certificate and the callees' specifications give the
  function's specification. It is stated per budget, so B can compose it.

**B. Composition**
- B1. Call graph and call-site resolution from the image: direct calls, tail calls, and
  constant `jalr` targets.
- B2. The table, and the composition theorem: strong induction on the budget, recursion
  included.
- B3. Indirect calls and tail calls with candidate lists and `CfiOk`. **Done.** The abstract
  domain has value sets (`oneOf`); interfaces carry `vals` premises (a register's entry value
  is one of a list) and `SafeN` carries a control-flow guard (`Env.Cfi`): at a listed `jalr`
  the target is one of its candidates, a premise about runs, not a theorem. The checker takes
  the candidates at an unresolved indirect jump/call on a listed site. Inference collects
  call-site values and resolves them top-down.
- B4. A generator that emits each function's certificate and its table entry. The kernel
  checks the image's derivable functions.

**C. Memory: layout, read-only data, statics**
- C1. Regions from the layout (stack, `.rodata`, `.data`/`.bss`, heap arena, input
  window), with disjointness theorems. **Done.** `Check.Region` (non-wrapping intervals,
  `Disjoint`, `pairwiseOk`, `mem_hits`); `Cases.Zip2005.Regions` names stack, rodata/eh_frame,
  text, statics and heap from the loaded image and proves them pairwise disjoint and within
  `SP1_MAX_MEMORY` by `decide`. (The input window is not a memory region in SP1: hints
  arrive through `HINT_READ` into memory the guest allocates.)
- C2. Memory read-back (`memAt`), the data counterpart of `codeAt_prog`.
- C3. Read-only data stays constant. Statics that a footprint does not cover keep their
  load values. `StaticsOk` holds at `main`'s entry and is preserved by the specifications
  that keep it. **Done for the protected statics.** `Check.Statics`: every precondition puts
  the `Env`'s protected keys outside what the function may write, so a verified call returns
  with them unchanged and at their load values (`Post.regionOk`, `Pre.regionOk`); at load a
  region holds the image's values by definition. zip-2005 protects `std::alloc::HOOK` and
  `std::panicking::HOOK` (`Runtime/STATICS.tsv`; Infer refuses a footprint that would write a
  protected region, since its precondition would be unsatisfiable); `Cases.Zip2005.Statics`
  proves both zero at load (`.bss`), at every verified entry and return (`HooksUnset`). The
  statics the guest does write (allocator, hasher, panic counts) are D's business.
- C4. Constant loads from `.rodata` and indirect-call targets resolved from them. Where
  this resolves a candidate list, it turns `CfiOk` into a theorem. **Done.** Loads through a
  protected address or a set of them yield the initial contents; interfaces carry `cells`
  (an entry doubleword, reached by a path of loads, that the activation relies on staying
  put, optionally one of a candidate set — a vtable held in a struct). Callers instantiate a
  callee's paths through their frame slots and their own cells and discharge the premises.
  The fmt dispatch resolves through `Formatter.buf` this way.

  Remaining uncovered functions (coverage holds at 70 of 304) are the fmt/panic internals
  whose blockers are genuinely program-logic: digit buffers indexed in the frame by a small
  dynamic offset, writes into a heap buffer at `base + len`, and `dyn` calls through a value
  pointer. These belong with the heap and the per-caller reasoning, below the line this
  goal stops at.

**D. The SP1 runtime**
- D0. Port zip-2005's symbolic executor to step-indexed `SafeN` and make it generic.
- D1. Entry: from `image.state` to `main`'s entry, with stack, heap and statics as
  `main`'s specification needs them. **Done.** `Runtime.Entry.entry`: from the loaded state,
  `SafeN` at every `MainEntry input` state gives `SafeN` at load. The path is all constants,
  so the executor runs it on literal states (`_start`, `__start`, the allocator's `init`,
  `Heap::init` and `memset` inlined). `MainEntry` fixes code, `ra`, `sp`, `gp`, all of
  memory (the image plus the run's 31 stores) and the input stream; corollaries give the
  protected regions, `HooksUnset` and the heap's one free block.
- D2. Syscall wrappers: `syscall_halt` (rejects for a nonzero code), `syscall_write`,
  `read_vec_raw`, and the precompile wrappers. **`syscall_write` and `syscall_halt` done**,
  against an owning `Env`: `Env.own`/`Env.inv` (owned statics and a module invariant, in
  every `Pre` and `Post`; interfaces proved without them lift by `Iface.HoldsN.lift`).
  zip-2005 owns the hasher's tag and position (`Owned.env`: `Some`, position below 64; it
  holds at `MainEntry`). `Runtime.SysWrite.holds` keeps the invariant;
  `Runtime.Halt.holds` never accepts with a nonzero code. Open: `read_vec_raw` (a hint
  read into a bump-allocated buffer, so D4) and the precompile wrappers.
- D3. libc: `memcpy`, `memset` (and `memmove`, `memcmp` if reachable), with footprints for
  every length.
- D4. The allocator: `HeapOk` and TLSF `alloc`/`dealloc`/`realloc` against it.
- D5. Panics: every panic entry the program reaches never accepts, under `StaticsOk`,
  `HeapOk` and premises the caller can discharge (the payload's vtable or formatter is one
  of the image's).

**E/F (later).** A specification format for program logic, and the port of zip-2005's
program proofs.

## Rules

- No `sorry`, no `axiom`, no `native_decide`. `bv_decide` is allowed (it adds
  `Lean.ofReduceBool` and `Lean.trustCompiler`); otherwise `#print axioms` shows only
  `propext`, `Classical.choice` and `Quot.sound`.
- Zero build warnings.
- Every remaining premise is in one list with a satisfiability witness: it holds on the
  reference run.
- riscv-zkvm stays unmodified at its pin. zip-2005-asm is not imported.
