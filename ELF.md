# The ELF problem

Notes from a `/deep-research` run (2026-10-12; 20 sources fetched, 94 claims extracted, 25
put through 3-vote adversarial verification, 22 confirmed, 3 refuted) plus a reading of
`zip-2005-asm`'s ledger. Each claim says where it comes from:

- **[R]**: confirmed by the research run, with its sources in § Sources.
- **[R?]**: extracted from a fetched source but not verified because of the budget. Re-check before relying on it.
- **[K]**: toolchain knowledge, not checked by the research run. These are the claims to
  test first (§ 7). The research run found almost nothing specific to rustc.

---

## 0. Summary

1. **Yes, a generic framework exists, and its shape is settled.** Verify against an ISA
   model, use an ISA-generic decompiler with certificates, and treat everything the compiler
   tells you as an **untrusted hint with a trusted checker** [R]. The compiler and assembler
   drop out of the trusted base. What stays trusted is the ISA model, the kernel and the
   import of the image. `riscv-zkvm` and `riscv-decomp` already implement the core of this
   for RISC-V.
2. **Trust can be reduced incrementally, and every serious prior system did it that way**
   [R]. Islaris, seL4's SydTV and HolBA each started by trusting a named component and later
   checked it, case by case or per run.
3. **What made zip-2005 vacuous (T1, T4, T5) is a class of whole-program fact**: which
   statics are ever written, where return addresses come from, which code pointers can sit
   in data. Per-function contracts that quantify over "every state at the entry" cannot
   see these facts. The compiler knows all of them, and most are **checkable against the
   image**:
   - the symbol table, DWARF types and statics, and relocations [K];
   - unwind tables [R].

   Verbeek et al. lift binaries by proving exactly three such properties per binary: return
   address integrity, bounded control flow and calling-convention adherence [R?].
4. **Most of the scaffolding can be generated mechanically**, though not the
   specifications. A generator can emit the image facts, the spec headers, the statics
   invariant, the panic-site catalog and the candidate coupling relations. Functional
   postconditions and loop invariants remain work for the agent and the user. Evidence for
   this split: Myreen's `cond` component, HolBA's manual contract translation, and the
   Aeneas-plus-AI-prover results [R / R?].
5. **The most effective lever may be the build, not the proof** [K]. Building with
   `panic=immediate-abort`, a simpler allocator, and debug info turned on would make T1/T5
   disappear rather than solve them. This is possible because zkVM guests are code we
   compile ourselves.

### Tested on zip-2005's guest (2026-10-12)

Details are in [`experiments/zip-2005/RESULTS.md`](experiments/zip-2005/RESULTS.md). Where a
result contradicts a [K] row below, the result wins.

- The build is **bit-reproducible**. A rebuild in another directory matches the pinned sha256.
- **Debug info is not free.** Every debug level changes the loaded image: different
  inlining, a different entry point, and even `debug=1` adds a 3-instruction thunk. Stripping
  afterwards is harmless. **The artifact under proof must be the debug build itself.**
- **DWARF covers only crates compiled in this build.** SP1's prebuilt `std` has none. The
  **symbol table** names and sizes all 18 statics in zip-2005's statics range, including
  five its docs never name.
- **Relocations (`--emit-relocs`), `.stack_sizes` and CFI are free**: the loaded image is
  byte-identical. Relocations give 95 address-taken functions plus `memcpy`'s jump table,
  and `__start`'s `call syscall_halt` is not among them (T5).
- **Return-address integrity holds for all 336 functions**, but only as a dataflow fact.
  `ra` is used as a scratch register, and the machine outliner saves `ra` from an
  out-of-line fragment. `.eh_frame` covers only 138 of the 336 functions; where it exists it
  agrees with the analysis.
- Immediate-abort is **blocked**: there is no `rust-src` for SP1's toolchain.
- **Kernel decoding is affordable.** `decode` of the whole image (41,776 words) checks in
  56 s of kernel time.
- **Return-address integrity is proved in Lean** against `stepSp1` for `memcpy`,
  `Pad::next` and `default_hook`, by one generic soundness theorem plus a kernel-checked
  annotation per function. Store aliasing leaves only named premises: argument footprints,
  statics vs. stack, and two stores through callee-returned pointers.

---

## 1. What went wrong in zip-2005-asm, restated

From `zip-2005-asm/docs/LEDGER.md` and `PLAN.md`:

| Finding | What the contract said | Why it is false | The missing fact |
|---|---|---|---|
| **T1** | `hpanic : ∀ u, u.pc = panic_fmt → u.code = s.code → Safe P u` | `rust_panic_with_hook` reads the hook from a **writable static**. A state whose custom hook halts with code 0 accepts | *The statics the guest never writes keep their load values* |
| **T4** | `halloc`, `hio`, `hdealloc{,_a1}` continue at a free `r'` | `ret` clears bit 0. For an odd `r'` the callee returns to `r'-1`, while the continuation is about a stuck (hence `Safe`) state | *Every return address is a real call site (`jal` pc + 4)* |
| **T5** | `hpanic`, `hunwrap`, `hpaf` close the panic path | Formatters and vtables come **from the caller**, so a state can point one at `__start`'s `call syscall_halt` | *Every code pointer in a `fmt::Arguments` or `&dyn` is one of the rodata constants the compiler emitted* |
| **Heap** | One write set `(0x78040620, 14780694332)` | Covers the TLSF control block, the **statics** and the arena alike | *Where the statics end and the heap begins, and which blocks are live* |
| **Image** | `RoImage`, `CodeAt` | Checked by `check-load` against the interpreter's load | *(already solved by computation)* |

Every row except the last is a fact about **the whole program**: the set of reachable
states, not one function. Quantifying a per-function contract over every state at the
entry is too strong for the real run, and that is exactly how the theorem becomes vacuous.
Prior art fixes it in one of two ways:

- **Prove the fact once per binary**, as a whole-program invariant that every contract can
  assume (Verbeek's three sanity properties [R?]; seL4's preserved initial-state conditions
  [R]).
- **Stop quantifying over a free value.** Use Myreen's "holes", which do not assume the
  call returns [R], or Islaris's `r @@ Q` contracts, whose return address is quantified but
  tied to a continuation the caller proves [R?].

---

## 2. What rustc can tell us: an inventory [K]

None of the rows below were checked by the research run. Each is a toolchain claim to
confirm (§ 7). The column that matters is **"How it is checked"**. A hint enters the proof
in one of two ways:

- **It shapes a statement**: a frame size, a coupling relation, a spec header. If it is
  wrong, a proof fails. Such hints are safe to trust.
- **It becomes a hypothesis**: "this static is never written", "this pointer is in set S".
  If it is wrong, the theorem is vacuous, which is how T1 happened. Such hints must be
  discharged before they reach the top-level theorem.

| Artifact (how to get it) | What it tells us | zip-2005 problem | How it is checked |
|---|---|---|---|
| **Symbol table** (`STT_FUNC`/`STT_OBJECT` with sizes) | Function and static boundaries | Already used (335 functions) | Decode each range; `#guard`/`decide` over the image |
| **Program headers** (`PT_LOAD` flags) | Which segments are R, RW or RX | `RoImage`, heap/statics split | Read off the ELF by the loader (trusted import) |
| **Linker map** (`-C link-arg=-Map=…`) | Which crate/object each symbol and section came from: guest, `core`/`std`, `alloc`, SP1 runtime | Classifying functions into "prove" vs "runtime contract" | Compare addresses with the symbol table. Only affects classification, never a hypothesis |
| **Retained relocations** (`-C link-arg=--emit-relocs`, or `-q`) | **Every word in `.data`/`.rodata` that holds an address, and its target** | **T5**: the closed set of formatter and vtable targets. Indirect-call target sets in general | Recompute: each relocated word must equal `S + A` at its offset. Without relocations it is a heuristic scan |
| **DWARF statics** (`DW_TAG_variable` with `DW_AT_location`) | Name, address, size and **type** of every static | **T1/Heap**: generates `StaticsOk` and the boundary `[0x78048830, 0x78048980)` instead of finding them by hand | Address and size match the symbol table and segment. "Never written" is a *proof obligation*, not a hint |
| **DWARF types** (structs, enums with `DW_TAG_variant_part`, niches) | Field offsets, discriminant encodings, `Option`/`Result` niches, `fmt::Arguments`, `dyn` vtable layout | Region layouts in spec headers (the 1392-byte witness, `noteState`); T5's packed `Arguments` | Shapes statements only. A wrong layout makes a proof fail |
| **Interior mutability in the type** (`UnsafeCell` inside `Mutex`, `RwLock`, atomics, `OnceCell`) | A `static` *without* `UnsafeCell` is immutable in Rust and normally goes to `.rodata`. *With* one, it can be written | **T1**: `panicking::HOOK` is a `RwLock`. The statics that may change are exactly those with `UnsafeCell` (or `static mut`) | Immutable-in-`.rodata` follows from the segment flags plus the memory model. The rest need a proved write-set invariant |
| **Vtable debuginfo** (recent rustc emits `<T as Trait>::{vtable}` symbols/DIEs) | Which rodata blocks are vtables, and for which impl | **T5** (`hunwrap`'s `&dyn Debug`) | Relocations give the slot targets, and DWARF gives their meaning |
| **Panic `Location` constants** (`core::panic::Location`: file, line, column in `.rodata`, passed to every panic) | Each panic call site's source origin | **T1**: a catalog of every panic site and its reason | The bytes are in the image and the call site loads them |
| **MIR** (`--emit=mir`, `-Z dump-mir`) | Panic edges are explicit (`Assert` with `BoundsCheck`, `Overflow`, …); call graph before inlining | Panic catalog; a source-level spec via Charon/Aeneas or hax | Pairing with machine code via line tables. Translation validation, never a hypothesis |
| **Unwind tables** (`.eh_frame`/CFI; `-C force-unwind-tables=yes` if absent under `panic=abort`) | Per pc: the CFA, and where `ra` and the callee-saved registers are saved | **T4**: where the return address lives; `StackOk` frame shapes | Recomputable from ISA semantics plus the calling convention [R]. LLVM has an RFC checker [R?] |
| **Stack sizes** (`-Z emit-stack-sizes` → `.stack_sizes`, nightly) | Static frame size per function | The "Needs 0x470 bytes of stack" side conditions | Matches `addi sp, sp, -N` in the prologue. Shapes statements |
| **Line tables + inline info** (`DW_TAG_inlined_subroutine`) | pc range ↦ source function, including inlined frames | Matching machine regions to source/MIR functions | Hint for pairing only |
| **Location lists** (variable ↦ register/stack slot per pc range) | Candidate **coupling relations** | `riscv-decomp`'s `FindIndex` coupling `x10 = i, x11 = stop, x12 = e` was written by hand | A wrong coupling makes `Cert.Refines` fail to prove. Often `<optimized out>` in release builds [R?: pcode2c] |

### The build switches that do more than the hints

| Switch | Effect | Cost |
|---|---|---|
| `debug = true` (or `2`) in the **release** profile | **Tested: changes the image** (inlining, layout, entry). Debug sections are non-loaded, so *stripping* afterwards changes nothing. Verify the debug build | Every address is re-pinned for an existing proof. Free for a new one |
| `panic = "abort"` plus **immediate-abort** (historically `-Zbuild-std-features=panic_immediate_abort`; newer nightlies are moving it to a panic strategy, so check the toolchain) | Panics become a trap or abort. **No hook, no formatter, no `Arguments`.** T1 and T5 disappear, along with A11 and most of the panic runtime (PLAN item 5d) | Nightly plus `build-std`. Check that SP1's runtime accepts it. Changes the binary under proof, which is fine because we own the build |
| A **bump allocator** instead of `embedded_alloc` TLSF (SP1 has offered both) | `dealloc` is a no-op and `alloc` is about 10 instructions. `HeapOk` becomes "the bump pointer is monotone and below the arena end" | Memory use. Possibly a different guest |
| `-C link-arg=--emit-relocs` | Keeps the relocations, which gives the code-pointer set for T5 | A bigger file; the loaded image is unchanged (check) |
| `-C codegen-units=1`, LTO settings fixed | Stable symbols and layout across rebuilds, so proofs survive | Build time |

None of this needs compiler *correctness*. It needs only that the compiler was used to
produce the bytes we then verify. The bytes are the ground truth, and everything else is
either checked against them or only shapes a statement.

---

## 3. Prior art: is there a generic framework?

| System | What it is | What we take from it |
|---|---|---|
| **Myreen, decompilation into logic** (HOL4; FMCAD 2012) [R] | Machine code plus an ISA model → a logic function plus a certificate (a machine-code Hoare triple), fully automatic. Parametrised by the next-state function; run on ARM, x86, PowerPC and 12k lines of seL4 ARM. Unknown calls become **holes** and are not assumed to return. Side conditions are collected in a `cond` component | This is `riscv-decomp`. `Decomp.Stepper` is already the ISA-generic core. Holes are the principled answer to T4 |
| **Islaris** (Coq/Iris over Sail via Isla; PLDI 2022) [R] | Verifies Armv8-A and RISC-V machine code against Sail, with no trust in compilation or assembly. Isla prunes ISA complexity using configuration constraints, which become `Assume` events to discharge. Return addresses quantified, with `r @@ Q` continuations; memcpy compiled by GCC -O2. Optional per-trace validation of Isla against the Sail-generated Coq, RISC-V only | The model for **stating** runtime contracts with a free return address (T4). The model for "name the TCB, then remove it per trace" |
| **seL4 binary translation validation** (SydTV; PLDI 2013, Sewell thesis 2017) [R] | Removes gcc and the C parser from the TCB by checking each binary against C semantics. Almost fully automatic with SMT. Global addresses are symbolic, filled from the symbol table. Function I/O relations come mostly from the calling convention. **Loaded-image facts stay trusted initial-state assumptions**, proved preserved but assumed at entry. Retargeted to RV64 [R?] | Validates the `check-load` approach. Shows that "assume at entry, prove preserved" is the accepted standard for image facts. Its decompiler heuristics needed retuning for every gcc version [R?], a warning for any DWARF-free heuristic |
| **HolBA** (HOL4; arXiv 2503.14135, 2025) [R] | RISC-V binary → BIR with a simulation theorem; contracts proved by symbolic execution and backlifted to the L3 RISC-V model. Disassembly by objdump with user-supplied bounds; contract translation **manual** (future work); side conditions via Z3 | The current state of the art on RISC-V, and roughly where zip-2005 already is. Its "future work" is our agent opportunity |
| **Verbeek et al., Hoare graphs** (Isabelle; PLDI 2022) [R?] | Stripped x86-64 ELF → an overapproximating Hoare graph, by proving **return address integrity, bounded control flow, calling-convention adherence**. An untrusted tool infers invariants, and Isabelle checks about one theorem per instruction. Lifting scaled to Xen (~400K instructions). Unknown externals assumed to follow System V, with heap and globals destroyed. **No exceptions/unwinding** | The three properties are exactly T4, T5 and the ABI premises, proved once per binary instead of assumed per contract |
| **BIRD** (Coq; TAP 2023) [R?] | Lifting as a chain of small passes, each validated per run as bisimilar. The base level **does not assume that `ret` returns to the caller**, and later passes establish it | The same discipline as T4's fix, with incremental lifting |
| **reopt verifier** (Galois, 2021) [R?] | An untrusted decompiler emits annotations, and a **verifier written in Lean** checks them per basic block with SMT. Soundness of the checking strategy was not yet proved at the time | Lean precedent for an untrusted producer with a checker |
| **linksem** (Lem; OOPSLA 2016) [R] | An ELF and linker model that has served as an emulator's front end for loading an image. Can run as a link checker, but realistic links with libc failed (GNU ld rewrites instructions). RISC-V coverage unverified | A reference if we ever formalise the loader. Expect linker relaxation to be the hard part |
| **CompCertELF** (Coq; OOPSLA 2020) [R?] | Verified compilation down to relocatable ELF, for x86-32 only and a subset. ~23k lines, about one person-year | A cost estimate for the "verify the toolchain" route, and a reason not to take it |
| **Bastian, Kell, Zappa Nardelli, `.eh_frame`** (OOPSLA 2019) [R] | Unwind tables are **redundant with the code**: recomputable from semantics plus the calling convention. clang shipped wrong tables (3/300). Validation was dynamic | DWARF as a checkable hint, with evidence that the check is needed |
| **Debug²** (ASPLOS 2021) [R] | 34 debug-info bugs, **3 in rustc/lldb**, in optimised builds | Do not trust DWARF. The claim that debug builds are a reliable oracle was **refuted** |
| **Aeneas / hax pipelines** (2026) and **Corten** (2026) [R?] | Rust source/MIR → Lean (or Rocq+Iris), with panics as explicit `fail`. AI provers closed structural and arithmetic lemmas, but loop invariants and external-interface axioms stayed manual. Neither reaches the binary; Corten lists compilation to hardware as future work | The **top** of our pipeline: a source-level spec to translation-validate the binary against. Not a substitute for it |

**What follows for asm-verif.** No existing system does all of this in Lean, for three ISAs,
on Rust binaries. The pattern to reimplement is well tested, though:

- **P1. An ISA-generic logic over a next-state function** (Myreen, Islaris). `Decomp.Stepper` already has this shape. x86 and ARM each supply a stepper plus per-instruction specs and an equivalence proof against their Sail model.
- **P2. An untrusted producer with a trusted checker** (reopt, Verbeek, BIRD, `.eh_frame`). `elf2lean` and every hint are untrusted, and Lean checks them.
- **P3. Whole-program sanity properties, proved once per binary** (Verbeek): return address integrity, bounded control flow, ABI adherence, plus the two Rust-specific properties zip-2005 needed, **statics discipline** and **heap discipline**.
- **P4. Image facts assumed at entry and checked by computation** (seL4, `check-load`).
- **P5. Unknown calls as holes or `r @@ Q` continuations, not free `r'`** (Myreen, Islaris).

---

## 4. How much must we trust the compiler?

**For soundness, not at all.** Every system above that verifies against an ISA model
removes the compiler and assembler from the TCB [R]. The irreducible TCB:

1. **The ISA model.** For RISC-V, `riscv-zkvm` ties its hand-written model to Sail with 51
   per-instruction equivalence theorems. x86 and ARM have Sail models too, which is the
   `ISA.md` question.
2. **The Lean kernel** (plus whatever `decide`/`native_decide` brings in; `riscv-decomp`'s
   axiom gate already tracks this).
3. **The import**: that the bytes and load addresses in Lean are the ones the zkVM runs.
   seL4 never removed this either [R]. It can be shrunk by having the zkVM's own loader
   produce the image digest the proof is stated over.
4. **The zkVM's own semantics**: syscalls, the halt and exit-code convention, memory
   initialisation. This is outside the compiler question but inside the TCB.

**For completeness and cost, a lot.** The compiler's information is what makes the
whole-program facts in § 1 cheap to state. Without it they are found by hand, as T1–T5
were, by reading disassembly.

### The trust ladder

Each rung changes the TCB, so each one is a milestone.

| Rung | What is trusted | What changes | zip-2005 today |
|---|---|---|---|
| **0** | ISA model, kernel, import, **plus the runtime contracts as hypotheses** | — | Here (`RunHyps`), vacuous |
| **1** | Same, but **every hypothesis is satisfiable by the real load**. A standing non-vacuity gate probes each contract with states varied only where its premises allow, including on *rejecting* inputs | Catches T1/T4-style falsity mechanically (`probe-contracts.lean` already does this by hand) | PLAN item 4's exit check |
| **2** | Compiler hints enter only as **checked** facts (a computable check over the image, discharged by `decide`/`#guard`): segments, symbol ranges, relocation-derived pointer sets, statics addresses, frame sizes, CFI | `elf2lean` emits `Image.lean` and `Hints.lean`. Nothing from DWARF is a hypothesis | Partly: `check-load` |
| **3** | **Whole-program invariants proved**: RA integrity, bounded indirect control flow, statics discipline (`StaticsOk`), heap discipline (`HeapOk`) | The vacuity class is gone by construction | PLAN items 2–4 |
| **4** | **The runtime is verified once per toolchain build** (memcpy, the allocator, the panic path, SP1 syscalls), keyed by the hash of its bytes and reused across guests | Contracts become theorems. They are the same bytes in every guest built with the same toolchain and features | PLAN item 5 |
| **5** | **Translation validation against the source** (Aeneas/hax extraction of the guest), using line, inline and location tables to pair regions | Specs come from the source instead of being written from the disassembly. Panics become `fail` | Not started |
| **6** | Loader/ELF formalised in Lean; ISA model validated against Sail for every ISA | Only the kernel and Sail remain | RISC-V's Sail tie is done |

Two rules keep this honest:

- **A hint never becomes a hypothesis of the top-level theorem.** It is either checked
  (rung 2) or shapes a statement. Hypotheses come only from the zkVM/ISA TCB, and from
  explicitly named contracts that a gate shows are non-vacuous (rung 1).
- **State the theorem over the bytes, not the build.** Debug info, MIR and relocations are
  all *side inputs*. If a rebuild with them on changes `.text`, use the instrumented build's
  image as the artifact. Do not carry facts across from a different build.

---

## 5. Will the compiler tell us what is provable, so verification mostly solves itself?

Partly, and in a specific way. The compiler tells us **the shape** of every obligation, not
**the content**.

What a generator could emit mechanically from ELF + DWARF + relocations + MIR [K, by
analogy with R]:

1. **Image facts** (`CodeAt`, `RoImage`, `.bss` zeros, segment permissions), proved by
   `decide` over the loaded bytes. This is `check-load`, generalised.
2. **The call graph and its bottom-up order**, with indirect calls resolved against the
   relocation-derived pointer sets (`lake exe callgraph` already does the direct part).
3. **Per-function spec headers**: entry pc, code range, frame size and saved-register
   slots (from CFI or `.stack_sizes`), argument regions and layouts (from DWARF types), the
   callee list, the return-address premise in P5 form. This is step 1 of zip-2005's "How a
   function is proved", which today is done by hand for ~188 functions.
4. **The statics invariant**: every static from DWARF, split by whether its type contains
   `UnsafeCell`. Immutable statics become `RoImage` facts. Mutable ones get a write set
   that must be proved.
5. **The panic catalog**: every `Location` constant and the call sites that load it, with
   the MIR assert kind. Under immediate-abort, this collapses to "every panic is a trap".
6. **Candidate coupling relations** for `Cert.Refines`, from location lists where they
   survive optimisation.
7. **A pairing of machine regions with source functions**, from line and inline tables,
   for rung 5.

What stays with the agent or the user: functional postconditions, loop invariants, the
abstract spec and its refinement, and the arithmetic. Evidence: Myreen's decompiler is
automatic but leaves `cond` side conditions [R]; HolBA's contract translation is manual
[R]; AI provers closed structural lemmas around Aeneas output but not invariants [R?].

**Can it be automated?** The pipeline would look like this:

```
ELF (+ debuginfo, relocs, map, MIR)
  └─ elf2lean (untrusted)        → Image.lean     facts by decide
                                 → Hints.lean     each with a checker
                                 → Skeleton/*.lean spec headers + sorry, in call-graph order
  └─ riscv-decomp extractor      → RecB functions + emitBody_sound certificates (already automatic for ALU loops)
  └─ agent                       → fills postconditions/invariants bottom-up; adversarial
                                   skills attack each contract (non-vacuity probe, rung 1)
  └─ lean-refine                 → refinement to the abstract spec (L3)
```

The Lean kernel checks every output, so an agent that is wrong is safe: it produces a proof
that fails, never a false theorem. The one place an agent can do real damage is **writing
hypotheses**, which is exactly how T1/T4 got in. The non-vacuity gate is therefore part of
the automation, not an optional extra.

---

## 6. What this suggests for asm-verif's design

- **`elf2lean` emits checked facts, not assumptions.** Its output is a Lean file of facts
  over the image, each closed by computation, plus a hints file whose every entry has a
  checker. If a check fails, the hint is dropped and the obligation stays visible.
- **An ISA-independent "whole-program sanity" layer** above `Decomp.Stepper`: RA integrity,
  bounded control flow, ABI adherence, statics discipline, heap discipline. It is proved
  once per binary and assumed by every per-function contract. This is where T1/T4/T5 get
  fixed for all future binaries, not just zip-2005.
- **Runtime contracts follow P5**, never a bare free `r'`.
- **A per-toolchain verified runtime** (rung 4) as its own artifact, keyed by toolchain,
  target and features. Most of zip-2005's 188 reachable functions are runtime, not guest.
- **A build profile that asm-verif prescribes** (§ 2's switch table), so that what the
  verifier needs is present and the panic and allocator surface is as small as possible.

---

## 7. Experiments on zip-2005's guest

**Run 2026-10-12**: 1, 2, 3, 4 and 6 done, 5 blocked. Results are in
[`experiments/zip-2005/RESULTS.md`](experiments/zip-2005/RESULTS.md) and summarised in § 0.
The list below is the original plan.

1. **Debug info is free.** Rebuild with `debug = 2` in the release profile, then diff the
   loaded segments against the current ELF. If they are identical, all of § 2 applies to the
   current proofs.
2. **DWARF reproduces the hand-found statics.** List every `DW_TAG_variable` in
   `[0x78048830, 0x78048980)` and compare with PLAN item 4's list: the hasher, `FP_TABLES`,
   both hooks, the panic counts and the thread statics. Check which contain `UnsafeCell`.
3. **Relocations close T5.** Link with `--emit-relocs` and collect every relocated word in
   `.rodata`/`.data` whose target is in `.text`. Is the formatter/vtable set reachable from
   `hpanic`/`hunwrap`/`hpaf` small and free of `__start`?
4. **Return-address sources.** From the decoded `.text`, every write to `ra` comes from
   `jal`/`jalr` (pc + 4) or a restore from a CFI-described slot. If that holds, RA integrity is a
   decidable property of the image.
5. **Immediate-abort.** Build with immediate-abort panics and count what disappears from
   the dynamic call graph from `main` (currently 188 functions and 36,450 instructions).
   Check that SP1 still accepts the guest.
6. **Stack sizes.** Compare `-Z emit-stack-sizes` output with the frame sizes in existing
   `StackOk` premises.

---

## 8. Open questions

- Is there a RISC-V-capable ELF/loader formalisation worth porting, or should the import
  stay "the zkVM loader's own image, checked by computation"? (Whether linksem covers RISC-V
  is unverified.)
- How should runtime contracts be specified so they are **reusable across ISAs**? Holes in
  Myreen's style, `r @@ Q` in Islaris's, or a single verified runtime per (toolchain, ISA)?
- How much of the pairing in rung 5 survives `opt-level=3` and LTO? Inline info and
  location lists degrade with optimisation [R?].
- Do x86 and ARM bring the same Rust-specific problems? Probably yes: the panic hook and
  allocator statics are in `std`, not the ISA. The unwind story differs, because CFI is
  mandatory on x86-64 Linux.

---

## Sources

Confirmed [R] unless marked.

- Myreen, Gordon, Slind. *Decompilation into logic — improved.* FMCAD 2012. https://www.cs.utexas.edu/~hunt/FMCAD/FMCAD12/016.pdf
- Myreen. Decompilation project page. https://www.cl.cam.ac.uk/~mom22/decompilation
- Armstrong et al. *Islaris: verification of machine code against authoritative ISA semantics.* PLDI 2022. https://www.cl.cam.ac.uk/~jp622/islaris.pdf
- Sewell, Myreen, Klein. *Translation validation for a verified OS kernel.* PLDI 2013. https://www.cl.cam.ac.uk/~mom22/pldi13.pdf
- Sewell. PhD thesis, 2017. https://trustworthy.systems/publications/papers/Sewell:phd.pdf
- Trustworthy Systems, compiler-correctness project page [R?]. https://trustworthy.systems/projects/OLD/compiler-correctness
- Palmskog et al. HolBA RISC-V binary verification. arXiv:2503.14135, 2025. https://export.arxiv.org/pdf/2503.14135
- Bastian, Kell, Zappa Nardelli. *Reliable and fast DWARF-based stack unwinding.* OOPSLA 2019. https://hal-univ-tlse3.archives-ouvertes.fr/INRIA/hal-02297690
- Di Luna et al. *Who's debugging the debuggers? (Debug²).* ASPLOS 2021. https://arxiv.org/abs/2011.13994v2
- Kell, Mulligan, Sewell. *The missing link: explaining ELF static linking, semantically.* OOPSLA 2016. https://www.cl.cam.ac.uk/users/srk31/research/papers/kell16missing-preprint.pdf
- [R?] Verbeek et al. *Formally verified lifting of C-compiled x86-64 binaries.* PLDI 2022. https://www.ssrg.ece.vt.edu/papers/pldi22.pdf
- [R?] BIRD. TAP 2023. https://www.ssrg.ece.vt.edu/papers/tap23-bird.pdf
- [R?] Wang et al. *CompCertELF.* OOPSLA 2020. https://www.cs.yale.edu/flint/certikos/publications/compcertelf.pdf
- [R?] Galois, verifiable binary lifting / reopt (2021). https://www.sos-vo.org/node/75267
- [R?] LLVM RFC: DWARF CFI validation (2025). https://discourse.llvm.org/t/rfc-dwarf-cfi-validation/86936
- [R?] Zucker. *pcode2c and DWARF* (blog, 2024). https://philipzucker.com/pcode2c-dwarf
- [R?] Aeneas/hax + AI provers pipeline. arXiv:2605.30106. https://arxiv.org/pdf/2605.30106
- [R?] Corten: Rust verification in Rocq+Iris. arXiv:2609.04372. https://arxiv.org/pdf/2609.04372

Refuted in verification (do not cite as support): seL4 TV handles callees
compositionally (1–2); unoptimised builds give trustworthy DWARF (1–2); linksem covers
AArch64/AMD64/IA32/Power64 with large-scale differential validation and no RISC-V (0–3).
