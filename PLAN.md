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
  `read_vec_raw`, and the precompile wrappers. **Done.** **`syscall_write` and `syscall_halt`**,
  against an owning `Env`: `Env.own`/`Env.inv` (owned statics and a module invariant, in
  every `Pre` and `Post`; interfaces proved without them lift by `Iface.HoldsN.lift`).
  zip-2005 owns the hasher's tag and position (`Owned.env`: `Some`, position below 64; it
  holds at `MainEntry`). `Runtime.SysWrite.holds` keeps the invariant;
  `Runtime.Halt.holds` never accepts with a nonzero code. **`read_vec_raw` done.**
  `Exec.Hint` gives `HINT_LEN`/`HINT_READ` exactly (the length in `t0`; the payload written
  as little-endian doublewords, the input popped); `Runtime.ReadVec.spec`, from the entry
  and the code alone, returns `{0, 0, 0}` with no hint, or bumps the pointer at `0x78040618`
  (its own region `[0x1C00000000, 1 << 37)`, above the TLSF arena) and returns
  `{ptr, n, cap}` with the hint read there, or calls `core::panicking::panic_fmt` when the
  region is exhausted (`Panic`, for D5). **Precompile wrappers done** by the checker:
  `syscall_pallas_add`/`_double` and `syscall_uint256_mulmod` return, write only `a0`'s
  64 (32) bytes (`Contract.A_7801bf3c`/`bf4c`/`bf5c`); their values are the precompiles'.
- D3. libc: `memcpy`, `memset` (and `memmove`, `memcmp` if reachable), with footprints for
  every length.
- D4. The allocator: `HeapOk` and TLSF `alloc`/`dealloc`/`realloc` against it. **Done.**
  **`alloc`.** `Runtime.Tlsf` models rlsf's heap (`Rep`: control block, bitmaps, segregated free
  lists, physical block chain) with frame (`Shape.congr`) and update lemmas (pop, split,
  mark). `Runtime.Alloc.spec`: from `Rep` and the de Bruijn table in `.rodata`, `alloc`
  returns with `Rep` re-established, used blocks kept, memory outside the allocator's
  doublewords unchanged, and the result null or a fresh block holding `size` bytes at
  `align` (`Grant`). **`dealloc` done.** `Runtime.Tlsf.Free` adds unlinking from any list
  position, merging and pushing; `Runtime.Dealloc.spec`: from `Rep` and a pointer `alloc`
  granted for a used block, `dealloc` coalesces it with its free neighbours, re-establishes
  `Rep`, keeps every other used block, and changes nothing outside the allocator's
  doublewords and the freed block. **`realloc` done.** `Runtime.Realloc.spec` composes
  `Alloc.spec`, `memcpy`'s contract and `Dealloc.spec` through `__rust_realloc`: `Rep`
  re-established, the owned invariant and protected memory kept, every other live byte and
  everything below the heap unchanged, and the result null (every used block kept) or a new
  `Grant` with the old block freed. D4's TLSF is complete.
- D5. Panics: every panic entry the program reaches never accepts, under `StaticsOk`,
  `HeapOk` and premises the caller can discharge (the payload's vtable or formatter is one
  of the image's). **Done modulo one phase-E premise.** `Runtime.Panic`: every panic entry
  the program reaches -- `panic_fmt` (`0x7803de40`), `panic` (`0x7803de20`), `panic_nounwind`
  (`0x7803dcdc`), `assert_failed` (`0x7803dd28`) -- never accepts (`..._neverAccepts`:
  `Safe G False`), given `pwhIface.Holds`: that `panic_with_hook` (`0x7803b8d0`) never
  accepts from its entry. The entry chain down to `panic_with_hook` is checked (the frames
  write only themselves and every path ends in a never-returning call, so `returns := false`);
  `Runtime.SysPanic` proves the tail `sys_panic` -> `syscall_halt(1)` unconditionally. The
  one gap is `panic_with_hook` and the formatting it drives -- `core::fmt::write` growing a
  heap `String` through the allocator -- whose buffer writes go through pointers the checker
  cannot describe. It is stated as an ordinary interface (`returns := false`, so an empty
  footprint is honest) under `Owned.env`, exactly the shape phase E discharges once a
  heap-typed `String`/`Vec` validity invariant over `Rep` is available; its `depth` is an
  over-approximation phase E pins exactly.

  Scope, measured (`INFER_REACH=7803de40`): 131 functions, about 10.5K instructions, are
  reachable from `core::panicking::panic_fmt` (the call graph over-approximates through the
  `vals` candidates of `dyn` calls). 14 have interfaces, and `memcpy`, `alloc`/`dealloc`
  and `compress256` are proved. About 30 have blockers of their own: stores through a
  pointer loaded from memory (a `Vec`/`String` buffer at `ptr + len`, an out-parameter),
  `dyn` calls through a value's vtable, and `fmt::write`'s argument loop. The rest are
  blocked only by their callees. The chain that matters is `panic_fmt`, then
  `rust_begin_unwind`, then `panic_with_hook` (`HOOK` is unset, so `default_hook`, which
  formats to stderr), then `rust_panic`, then `__rust_start_panic`, then
  `zkvm_set_abort_message`, then `sys_panic`, ending at `syscall_halt` with a nonzero code.

  **Blocked on heap-typed specifications (phase E).** Every panic runs the payload's `get`
  (`FormatStringPayload::get`, `0x7803c154`). It starts an empty `String` in its frame and
  calls `core::fmt::write` with `String`'s `Write` vtable. The writes (`write_str`,
  `write_char`) grow the buffer through `finish_grow`, `__rust_alloc` and `__rust_realloc`,
  and store into the heap block at `ptr + len`. A sound "never accepts" needs memory safety
  of that path. Otherwise a store could hit allocator metadata or a saved `ra`, and no
  argument about the halt sites survives a wild return. That needs a `fmt::write`
  specification that is generic in its writer: each `write_str`, and each argument's
  `Display` (writing through the `Formatter`), keeps a "valid `String`" invariant that ties
  a struct in the frame to a used heap block (`Rep`, `Live`). The checker's interfaces
  cannot state that, since their footprints are frame, entry-relative and constant regions.
  It is the per-caller heap reasoning that C4 already set below this goal's line.
  What does not need it: the `read_vec_raw` panic hand-off (`ReadVec.Panic`) and the tail.
  **Tail done:** `Runtime.SysPanic.holds` checks `sys_write` and `sys_panic` against
  `Owned.env` with a table of `SysWrite.holds` and `Halt.holds`. `sys_panic` does not
  return. The next link up, `zkvm_set_abort_message`, calls the payload's `get`, which is
  the `String` path above.

  **E, generic layer done.** The checker's interfaces now carry *writers* (`Iface.strs`:
  a pointer and a kind, in entry terms), and the `Env` a `Model` (`Check/Model.lean`) that
  says, per kind, which doublewords a writer may change (`hit`), which it keeps (`stable`),
  what well-typed means (`writerOk`), and which kinds are structural wrappers of another
  writer (`sub`: a `PadAdapter` around a `String`). `Pre` asks every lent writer to be
  well-typed, its keys outside the function's own writes; `Post` gives each back
  (`Model.Keeps`), and keeps every writer the function was not lent. A callee's writer must
  be one the caller has, or a wrapper built in the caller's frame around one; after the
  call the caller's writers must be recovered. Candidates (`vals`, cells with candidates,
  vtable slots) are now one mechanism (`cands`/`root?`), and an indirect call is checked
  per candidate under the refinement that fixes its target, so a callee's kind can be the
  constant the vtable determines. `Model.trivial` (no writers) is the default; the zip-2005
  table is unchanged under it.

  **E2, typed stores: the checker's side is done; the zip-2005 instance is next.** The
  leaves of the `String` path (`write_str`, `write_char`, `do_reserve_and_handle`,
  `finish_grow`, the payload's `get`, the stderr adapter's `write_fmt`, and the digit
  buffers of `fmt::num`) store at `ptr + len` and at `frame + i`, under bounds the code
  establishes by branching. The checker now has what it needs to check them, generically:
  - *Symbols and facts.* `AVal.sym i j k` is a value the activation knows only through
    facts; `AState.facts` is a list of linear inequalities over ℕ (`LinTerm` with
    nonnegative coefficients), exact results of operations (`Fact.op`) and model atoms.
    A symbol is made at an instruction and killed wherever it is remade (loops:
    `AState.kill`, `killAll` at a call). Facts come from branches (`branchFacts`: `bltu`
    etc. are ℕ comparisons), from loads (`loadBound`), from ALU steps (`Fact.op`), from the
    kinds' invariants and from callees' `post` facts. A branch the facts refute is pruned.
    Facts about symbols nothing holds any more are dropped once they exceed `gcLimit`
    (`AState.gcIf`, at every edge), so the facts do not grow with the path; a kill is
    skipped when nothing mentions the symbol, so the kernel's terms do not grow either
    (the kernel evaluates lazily: rebuilding every register at every instruction made the
    check of `compress256` quadratic).
  - *Certificates.* Entailments are checked, not found (`Fact.lean`): Farkas combinations,
    case splits, built-in consequences of operations, model rules; `Ctx.certs` gives them
    per edge, `Ctx.saturate` runs them, `Thy.ax` supplies the instance's axioms.
  - *Kinds.* `Model.kinds`: fields, stable fields, an invariant, an optional buffer, the
    structural wrapper; `writerOk`/`hit`/`stable`/`fields` are defined from the table.
    A writer's field values are tracked (`AState.wmem`): entry cells at entry, fresh
    symbols with the invariant after a call lent the writer. Frame writers come from
    per-pc hints (`Ctx.fws`), checked by `fwOk`.
  - *Typed stores.* `fieldStore` at a writer's field; `bufStore` inside a writer's buffer
    (`ptr ≤ a ∧ a + n ≤ ptr + cap` among the facts, the writer named by `Ctx.wtr`).
  - *Interfaces.* `pre`: facts over entry values; `post`: facts over exit registers, entry
    values and item contents at exit (`PVal`); `heap`: the callee may change the heap's
    structure. Tail calls and returns check them (`tailOk`, `retOk`).
  - *Annotations* are lists of states per instruction (`annoAt`), edges are checked by
    `leAt` (symbols substituted by `phiOf`), and `Ctx.fill` fills sparse hints; `Infer`
    emits hints only at jump targets, where its join happens.
  Soundness is in parts (`Sound/Core`, `Kn`, `Plain`, `Call`, `Act`), warning-free, with
  the standard axioms plus `bv_decide`'s. `Exec.holdsN_of_inv` takes `Env.Ok` and the
  `post` facts. The zip-2005 table regenerates (68 checked, 2 proved by hand; 620 KB).
  Next: the zip-2005 model instance (`String`/`Vec` kind, the `Formatter` wrapper, the
  stderr adapter as a unit kind, rules), the allocator interfaces with `pre`/`post`
  facts, `Infer`'s certificate search (Fourier–Motzkin) and `wtr`/`fws` emission, the
  leaf checks, and the roots that discharge `pwhIface.Holds`.

**E/F (later).** A specification format for program logic, and the port of zip-2005's
program proofs.

## Rules

- No `sorry`, no `axiom`, no `native_decide`. `bv_decide` is allowed (each use adds a
  `…_native.bv_decide.ax_…` axiom, its trust in the compiled checker); otherwise `#print axioms` shows only
  `propext`, `Classical.choice` and `Quot.sound`.
- Zero build warnings.
- Every remaining premise is in one list with a satisfiability witness: it holds on the
  reference run.
- riscv-zkvm stays unmodified at its pin. zip-2005-asm is not imported.
