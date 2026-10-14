# PLAN

The goal is to take care of the ELF in general. A guest's program logic should only have to
state and prove what its own functions compute. Everything else is a theorem here: the
loaded image, the calling convention, memory footprints, the stack, statics, indirect
control flow, syscalls and the SP1 runtime (entry, allocator, libc routines, panics).

zip-2005 is the worked example. Its program logic, `main` and the crypto, is phase F: the
function-level proofs and the specification live in `Cases/Zip2005/`, and the end theorem is
that an accepting run of the loaded ELF on an input implies `Zip2005.GuestStatement` of the
decoded input. The bar: no hypothesis that the real run does not satisfy, and no contract
quantified over states the run never reaches.

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

**F. The program logic of zip-2005**
- F0. The specification. `Cases/Zip2005/Spec/`: `Zip2005.GuestStatement` over the ironwood
  circuit specifications (`Zcash.Circuits.*`, with `Clean`, `CompElliptic` and `CompPoly`),
  as first-class sources of this repository under their upstream licences; Mathlib is a
  dependency for this directory only. **Done.** (One inherited `native_decide`: the order
  of the Pallas group, `CompElliptic`.) 44 linter warnings in 19 upstream files are to be
  cleaned.
- F1. The symbolic executor as framework code. `AsmVerif/RiscV/Sym/`: the executor
  (`sym_exec`, `sym_close`), over the same judgement as the checker (`SafeN G n P s`,
  `AsmVerif/RiscV/Safe.lean`: one module for `stepsSp1`, `SafeN`, `Safe` and their lemmas;
  a step keeps the budget, so the executor threads `G` and `n` through unchanged and its
  specifications compose with the checker's interfaces directly), with its region, frame, register
  and read-only-data vocabulary, generic in a `Layout` (text window, read-only segment,
  stack top) that `gen-image` emits per image (`Image/Ro.lean`: `layout`, the read-only
  chunks, the layout's constants as rewrite rules). Fetch goes through the packed program
  (`prog_packed`, one shift per instruction rather than a walk of the literal). **Done.**
- F2. The function-level proofs. `Cases/Zip2005/{Blake2b,Bridge,Curve,Field,Kit,Main,Orchard,
  Poseidon,Precompile,Runtime,Sha256,Sinsemilla,Top,Witness}`: `main` and everything it calls,
  down to the precompile wrappers, each function in continuation form over `SafeN G n P`
  for every guard and budget;
  `Bridge` relates the machine-level results to the specification; `Top` composes them from
  the ELF's entry. The composition is conditional on `RunHyps` (`Top/Assumptions.lean`): the
  contracts of the allocator (`halloc*`, `hdealloc*`, `hrealloc*`), of `read_vec_raw`'s I/O
  error path (`hio`), of the lazy table build (`hinit`), of the formatter (`hfmt`), and
  twelve "never accepts" contracts for panic and reject-halt entries; and on an input
  condition (`hbp_eq`, `hokJ2`, `hbp`). **Ported; building.**
- F3. Discharge `RunHyps` from D. Each contract is a theorem of phase D over the same
  `SafeN` (the allocator against `Tlsf.Rep`, `read_vec_raw`, the panic entries modulo
  `pwhIface.Holds`), so what is needed is (a) the checker's `Post` implying each
  contract's footprint and return facts, (b) a heap invariant (`Tlsf.Rep`) and a statics
  invariant threaded through `main` where the contracts need them, (c) the guard: the
  contracts are stated for every `G`, phase D's interfaces for a `G` that implies
  `Env.Cfi`, so the top theorem takes a `G` with that property (or the CFI premise is
  discharged for the guest's indirect jumps). The panic contracts
  as stated (`∀ u, u.pc = entry → u.code = s.code → Safe P u`) are false: they quantify
  over every state at the entry, including one with a custom panic hook installed in the
  static `HOOK` or a formatter pointing at `syscall_halt(0)`, from which an accepting halt
  is reachable. So for an input the statement rejects no state satisfies `RunHyps`, and
  the theorem says nothing about such inputs. They are restated over the statics and the
  heap as `main` keeps them, with the payload pinned to the call sites' constants, which
  is D5's `..._neverAccepts` under `pwhIface.Holds`; the theorem stops being vacuous only
  once that premise is discharged. (The return-address contracts carry `r' &&& ~~~1 = r'`
  already.) Both `Runtime/Start.lean` (the ported `_start`-to-`main` path) and
  `Runtime/Entry.lean` (D1) prove the same path; one goes.
- **Milestone M1 (agreed 2026-10-14): one premise left.** The top theorem from
  `Layout.image.state I` with exactly one remaining premise: `pwhIface.Holds`, that
  `panic_with_hook` (`0x7803b8d0`) never accepts. Every other contract in `RunHyps` is
  restated so it is true of the real run and then discharged from phase D, the input
  condition included, so the theorem is not vacuous for any input except through that one
  stated, true and unproved premise. Order: name the contracts (one definition per shape),
  thread the heap and statics invariants, restate the panic contracts over them with pinned
  payloads, discharge the allocator, I/O, init and halt contracts from D. The premise
  itself is the next milestone, taken on together.

  **M1 design (2026-10-14).** What a restated panic contract must give the proved
  `Runtime.Panic.*_neverAccepts`: the checker's `Pre Owned.env C σ` at the entry, that is
  the image's code, `σ.depth ≤ sp ≤ stackTop` and aligned (from `StackOk`, whose `0x10000`
  slack covers `σ.depth`), the protected statics at their load values (both hooks), the
  owned hasher invariant, and the payload registers in `σ.vals` (the T5 condition, already
  derived from the call sites). So:
  1. *New modules first (cheap rebuilds).* The contracts assume nine more panic or halt
     entries: `assert_failed` (two instances), `panic_const_rem_by_zero`,
     `result::unwrap_failed`, `option::unwrap_failed`, `raw_vec::handle_error`,
     `alloc::handle_alloc_error`, `halt_invalid_hint`, `empty_input_stream_halt`. The
     frame checker's inference gives up on all nine ("recursion"), as it did on the four
     in `Runtime.Panic`. Check them the same way: an interface with `returns := false` and
     pinned `vals`, a certificate against `Runtime.Panic.tbl`. `handle_alloc_error` calls
     `0x7803aebc`, which reads `std::alloc::HOOK` (protected); it needs that frame too.
  2. *Discharge lemmas.* For each contract shape, a theorem from the runtime results:
     panic contracts from `tbl_holds hpwh` plus `StaticsOk` (protected statics and the
     owned invariant, a state predicate) and the stack; the allocator contracts from
     `Alloc.spec`/`Dealloc.spec`/`Realloc.spec` through `__rust_alloc` (`0x7801bcec`) under
     the heap invariant (`Tlsf.Rep` with the guest's live blocks as used blocks). The
     allocator may return null, which the contracts hide; with the real spec the callers'
     null branches go to `handle_alloc_error`, a panic entry.
  3. *The restatement, one rebuild.* Contracts become named definitions taking
     `StaticsOk` (and the heap invariant where they allocate); the executor carries those
     predicates across steps and calls the way it carries `RoImage` (a generic "carried
     invariant" mechanism: a `setMem` lemma for stores outside the regions and an
     `of_unchanged` lemma for calls); function specifications take them as preconditions;
     `main` gets them from `Runtime.Entry` (`MainEntry.prot`, `Owned.mainEntry_inv`, the
     heap's one free block).
  **Finding (2026-10-14): a second formatting path.** `__rust_alloc_error_handler_should_panic`
  (`0x7801aec8`) returns 0 in this binary, so `handle_alloc_error` (`0x7803d1a8`) does not
  panic: `rust_oom` runs `default_alloc_error_hook` (`0x7803af60`), which prints "memory
  allocation of N bytes failed" through `Stderr::write_fmt` (`core::fmt::write` over the
  stderr adapter, no heap `String`) and then aborts. The proved `alloc` may return null, and
  the callers' null branches lead there. So M1 has two premises, both "a formatting path
  never accepts": `panic_with_hook` and the default allocation-error hook (stated at
  `rust_oom`, `0x7803b100`, or at `handle_alloc_error`). The second needs no heap reasoning
  (the stderr adapter is the unit kind E2 already plans) and may be the smaller proof.
  **Finding (2026-10-14): a third.** `hfmt`, the contract that `alloc::fmt::format_inner`
  (`0x7803d1cc`) returns a well-formed heap `String`, is used on the parser's error paths
  (12 files) and by `empty_input_stream_halt`. Proving it is `core::fmt::write` into a heap
  `String`, the same problem as `panic_with_hook`. So M1's premises are three, all phase E:
  `panic_with_hook` never accepts, the default allocation-error hook never accepts, and
  `format_inner` returns a `String`. A `fmt::write` specification generic in its writer is
  the common root they would all follow from.
  **Finding (2026-10-14): the formatting premises must constrain the heap**
  (`Cases/Zip2005/ISSUES.md` #2). `pwhIface.Holds` as stated quantifies over states with an
  arbitrary allocator control block, and is then probably false. M1 states every
  formatting premise, and every restated panic contract, under the heap invariant.
  **M1 implementation (2026-10-14).**
  - *The carried invariant* (`AsmVerif.RiscV.Sym.Carry`): `Carry R Q L s`, every memory
    agreeing with `s`'s off the open addresses (fixed ranges `R`, live buffers `L`)
    satisfies `Q L`. Stores to open addresses and calls whose write set is open keep it;
    the executor carries it as it carries `RoImage`.
  - *The run's invariant* (`Cases.Zip2005.Run.Heap`): `HeapAt L s := Carry ranges Q L s`,
    with `Q L m` the hasher's invariant, `Tlsf.Rep` with the sentinel at `7 << 34 - 32`, and
    each live buffer null or a used block's payload from its start. `q_frame`: `Q` reads
    closed memory only (the control block, headers, back links, free blocks, the hasher's
    tag and position). `mainEntry_heapAt`: it holds, with nothing live, at `main`.
  - *The environment of the premises*: `HeapEnv.env` (hasher and allocator owned) with no
    control-flow premise (`cfi := []`), so the formatting premises are stated for every
    guard and the top theorem keeps an arbitrary `G`. The two `jalr` sites of `Env.cfi` are
    inside `core::fmt::write`, i.e. inside the premises.
  - *Allocator contracts* keep their call-site shapes, plus `HeapAt L` before and
    `HeapAt ((ptr, k) :: L)` after, and admit null (`ptr.toNat = 0 ∨ BASE ≤ ptr.toNat`):
    the callers' null branches reach `handle_alloc_error`. A heap block a contract keeps
    (the `FP_TABLES` tables across `from_iter`'s allocation) is one of `L`'s.
  - *Phase D additions*: `Alloc`/`Dealloc`'s `Out` record the private input (the
    contracts carry it).
  - *`hinit`* (the lazy table build at `0x7801a258`, a "behaves as if built" contract) is
    replaced, not discharged: `0x7801a258` is the call of `SpendValidatingKey::from_bytes`,
    the first decompression, and `EpAffine::from_bytes` (`0x78025a1c`) holds the only call
    of the `Once` slow path (`0x78026250`), whose build `fp_tables_init_spec` proves. So
    segment A2 starts with the `Once` uninitialised and that first call builds the tables.
- F4. The end theorem: from `Layout.image.state I`, an accepting run gives
  `∃ …, Decodes I … ∧ GuestStatement …`, with every premise in one list and a
  satisfiability witness.

## Rules

- No `sorry`, no `axiom`, no `native_decide`. `bv_decide` is allowed (each use adds a
  `…_native.bv_decide.ax_…` axiom, its trust in the compiled checker); otherwise `#print axioms` shows only
  `propext`, `Classical.choice` and `Quot.sound`.
- Zero build warnings.
- Every remaining premise is in one list with a satisfiability witness: it holds on the
  reference run.
- riscv-zkvm stays unmodified at its pin. zip-2005-asm is not imported.
