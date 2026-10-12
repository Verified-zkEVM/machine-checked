# ELF experiments on zip-2005-asm's guest (2026-10-12)

These experiments test the toolchain claims marked **[K]** in [`../../ELF.md`](../../ELF.md)
against zip-2005-asm's SP1 guest. Nothing in `../../../zip-2005-asm` was modified. Every
build ran from a copy of its workspace.

## Setup

- Guest: `zip-2005-asm/zip-2005` (workspace `Cargo.lock`, `sp1-zkvm` from `dmpierre/sp1@f2328b4`).
- Toolchain: SP1 `succinct` rustc `1.93.0-dev`, target `riscv64im-succinct-zkvm-elf`. SP1's
  own flags include `-C panic=abort`, `-C passes=lower-atomic` and `--image-base=0x78000000`.
- Tools: Homebrew LLVM 22.1.4 (`llvm-readelf`, `llvm-objdump`, `llvm-dwarfdump`, `llvm-nm`).
- Pinned artifact: `zip-2005-asm/artifacts/zip-2005.elf`, sha256 `1112859b…d1fa`.

**The image digest** (`image-digest.sh`) is the entry point plus the sha256 of the
allocated sections, laid out by address. Two ELFs with equal digests load and run
identically, whatever their other sections say. Every comparison below uses it.

## Results

| # | Question | Answer | Evidence |
|---|---|---|---|
| 0 | Is the build reproducible? | **Yes, bit for bit.** A rebuild from a copy in another directory gives the pinned sha256 | `out/baseline.elf` = `1112859b…` |
| 1 | Does debug info leave the loaded image unchanged? | **No. Every debug level changes the image.** Stripping a debug build afterwards *does* leave its image unchanged | See § 1 |
| 2 | Does DWARF reproduce the hand-found statics? | **Partly.** DWARF covers only crates compiled in this build: 4 statics. **The symbol table covers all of them**: 18 named, sized objects that exactly tile zip-2005's statics range `[0x78048830, 0x78048980)`, already in the pinned ELF | See § 2 |
| 3 | Do relocations close T5? | **Yes, for the "which targets" half, and for free.** `--emit-relocs` gives an image identical to the pinned one. 95 address-taken functions, all formatters, vtable methods or a hook, plus `memcpy`'s 7-entry jump table. `__start`'s `call syscall_halt` is not among them | See § 3 |
| 4 | Is return-address integrity a decidable property of the image? | **Yes, by dataflow, not by inspecting individual instructions.** All 336 functions pass. `ra` is used as a scratch register, and the machine outliner moves prologues out of line. CFI agrees on all 138 FDEs | See § 4 |
| 5 | Immediate-abort panics | **Blocked.** SP1's toolchain ships no `rust-src`, so `build-std` needs SP1's fork of the Rust sources | — |
| 6 | Do stack sizes match the code? | **Yes where it can be checked**, at no cost (image identical). Covers only the 169 functions compiled in this build | See § 6 |

### 1. Debug info changes the code

| Variant (how) | Entry | Image vs. baseline |
|---|---|---|
| baseline | `0x7801bcd0` | — |
| `-Cdebuginfo=2` (rustflags) | `0x7801bcec` | `.text` −248 bytes. Different inlining (`prf_nf`, `ExtractedNoteCommitment::from_bytes`, `compress1_loop`, `main` +28 bytes). **No DWARF in the output**: Cargo's release profile strips it (`strip = "debuginfo"` is the default when `debug = false`) |
| `CARGO_PROFILE_RELEASE_DEBUG=2` | `0x7801bcec` | Same shape as the above, different bytes. DWARF present (49 MB) |
| `…DEBUG=line-tables-only` / `line-directives-only` | `0x7801bcf0` | Identical to each other; +100 bytes `.text`; `.eh_frame` changed too |
| `…DEBUG=1` (limited) | `0x7801bcd0` | Same section sizes. **Exactly 3 instructions added**: an unreferenced thunk `<&Fp as Debug>::fmt` (`ld; auipc; jr`). Everything after it shifts by 12 bytes (2 immediates, 1 vtable pointer). Crate hashes change too, since the profile feeds Cargo's metadata hash |
| `…DEBUG=2`, then `llvm-objcopy --strip-debug` / `--strip-all` | `0x7801bcec` | **Identical** to the unstripped debug build |

**Consequence.** "Add debug info, keep the proofs" is false for this toolchain. The rule
has to be: **the artifact under proof is the build that produced the DWARF.** Strip it
afterwards if you like, since that is proven harmless. For zip-2005 that means re-pinning
every address. For asm-verif it means the build profile is part of the pipeline from the
start.

### 2. Statics: the symbol table, not DWARF

`dwarf-statics.py` over the `DEBUG=2` build's RW segment finds exactly four statics:
`EMBEDDED_RESERVED_INPUT_PTR`, `INNER_HEAP` (`CELL`), `PUBLIC_VALUES_HASHER`, and
`FP_TABLES`' `LAZY` (`CELL`). SP1's prebuilt `std` has no DWARF, so **every `std` static is
missing**: both `HOOK`s, the panic counts, the thread statics.

The **symbol table** of the pinned ELF lists all of them. In `[0x78048830, 0x78048980)`:

```
78048830  0x78  PUBLIC_VALUES_HASHER            78048928  0x08  panic_count::GLOBAL_PANIC_COUNT
780488a8  0x50  FP_TABLES (Lazy)                78048930  0x10  panic_count::LOCAL_PANIC_COUNT
780488f8  0x01  stdio::OUTPUT_CAPTURE_USED      78048940  0x01  default_hook::FIRST_PANIC
78048900  0x08  stdio::OUTPUT_CAPTURE           78048948  0x18  panicking::HOOK
78048908  0x01  panic::SHOULD_CAPTURE           78048960  0x08  thread::current::id::ID
78048910  0x08  ThreadId::new::COUNTER          78048968  0x01  backtrace::lock::LOCK
78048918  0x01  default_alloc_error_hook::PREV_ALLOC_FAILURE
78048920  0x08  alloc::HOOK                     78048970  0x08  main_thread::MAIN
                                                78048978  0x08  thread::current::CURRENT
```

Five of these are never named in zip-2005's docs or proofs: `FIRST_PANIC`,
`PREV_ALLOC_FAILURE`, `backtrace::lock::LOCK`, `ThreadId::new::COUNTER`, `main_thread::MAIN`.
`StaticsOk` can be generated from this table: one region per symbol, gaps are padding.

Two more facts:
- **The `UnsafeCell` heuristic is incomplete.** `PUBLIC_VALUES_HASHER` is a `static mut`
  and carries no `UnsafeCell`.
- "Which statics are written" stays a proof obligation either way. The symbol table names
  the regions; it does not say which of them the program writes.

### 3. Code pointers: relocations

`-Clink-arg=--emit-relocs` gives a **loaded image identical to the pinned ELF**, plus
`.rela.text` (3,045 relocations) and `.rela.rodata` (196).

- **`.rodata`**: 88 code-pointer relocations to 79 distinct targets. 72 are function
  entries: 32 formatters, 6 `drop_in_place`, the rest panic-payload / `io::Write` / `Any`
  vtable methods and two Poseidon closures. The other 7 are `R_RISCV_32` entries of
  **`memcpy`'s jump table**.
- **`.text`**: 16 functions have their address built in code (`PCREL_HI20` to an entry,
  not a `CALL_PLT`). All are formatters, plus `std::alloc::default_alloc_error_hook`.
- **`0x7801bea0`** (`__start`'s `call syscall_halt`, the address T5's counterexample used)
  is **not** a target.

That gives the whole-program "bounded control flow" set: about 95 address-taken
functions plus one jump table. T5's premise becomes "every formatter or vtable pointer
lies in this set". Two obligations remain for the proof:
- code pointers are only ever copied from these sources (never computed);
- none of these functions reaches an accepting halt.

`out/code-pointer-targets.txt` lists them.

### 4. Return-address integrity

`ra-check.py` runs a forward dataflow over each function's CFG. Its state: `sp` and `s0`
offsets from the entry `sp`, whether `ra` holds the entry value, and which stack slots do.
At every `ret`, tail call, or jump out of the function it requires `ra` = entry `ra` and
`sp` = entry `sp`.

```
functions: 336
    284  ok
     46  no exit (diverges / panics only)
      6  ok, but has indirect jumps (not followed)
eh_frame FDEs matching a function start: 138 of 138; ra-slot disagreements with CFI: 0
```

Two things this experiment found that the notes did not predict:

- **`ra` is a general-purpose register to the compiler.** Some functions write it with
  `add`, `addi`, `slli`, `srliw`, `or`, `lbu` between saving and restoring it. Integrity is
  therefore a dataflow fact: "every write to `ra` is a call" is false.
- **The machine outliner makes prologues interprocedural.** `default_hook` and
  `panic_with_hook` save `ra` and `s0`–`s5` through `jalr t0, OUTLINED_FUNCTION_0`, a
  fragment that stores into the *caller's* frame and returns via `t0`. Until outlined
  calls were modelled, the check flagged `default_hook`.

`.eh_frame` describes only 138 of the 336 functions. Where it exists it agrees with the
analysis everywhere, so it is a useful cross-check but cannot be the source.

**For T4.** The target has no C extension, so every pc is 4-aligned, and every `ra` a call
sets is `jalr`-pc + 4. Given this property, `r' &&& ~~~1 = r'` holds at every real return.

**Not sound as it stands**, and the gaps are exactly the proof obligations:
- stores through bases other than `sp`/`s0` are assumed not to hit the `ra` slot;
- callees are assumed to preserve `sp`, `s0` and the caller's frame;
- the 6 functions with jump tables are not followed past the indirect jump (§ 3 gives the
  targets, for `memcpy` at least).

### 6. Stack sizes

`RUSTC_BOOTSTRAP=1` plus `-Zemit-stack-sizes` gives an **identical image** and a
`.stack_sizes` section with 169 entries, for functions compiled in this build only. Against
the first `addi sp, sp, -N` of each function, 152 agree. The 6 that disagree are frames
over 2047 bytes, which need two `sp` adjustments (`main` is 4256 bytes), and outlined
prologues. Both are limits of the comparison heuristic. The section is a hint for our
crates, and `ra-check`'s `sp` tracking checks it.

## What this changes in ELF.md

- **Debug info is not free** (the [K] claim was false). The verified artifact must be the
  debug build.
- **The symbol table is the primary source of static and function boundaries.** DWARF adds
  types for our crates only, unless `std` is rebuilt, which is blocked here.
- **Relocations, `.stack_sizes` and CFI are free.** They come with a byte-identical image.
- **Return-address integrity needs a dataflow checker that knows about outlined
  fragments**, which is a design input for the verified checker (plan step 3).

## Reproduce

```bash
export WORK=/some/scratch/dir                    # the workspace copy and cargo target
./build-variant.sh baseline                      # must match the pinned sha256
CARGO_PROFILE_RELEASE_DEBUG=2 ./build-variant.sh profdebug2
./build-variant.sh relocs -Clink-arg=--emit-relocs
RUSTC_BOOTSTRAP=1 ./build-variant.sh stacksizes -Zemit-stack-sizes,-Clink-arg=--emit-relocs
./image-digest.sh out/*.elf
./section-diff.sh out/baseline.elf out/prof-1.elf
llvm-dwarfdump --debug-info out/profdebug2.elf | python3 -I dwarf-statics.py 78040520 78048888
llvm-objdump -d --no-show-raw-insn -M no-aliases out/baseline.elf > out/baseline.dis
llvm-nm -S --defined-only out/baseline.elf > out/baseline.nm
llvm-dwarfdump --eh-frame out/baseline.elf > out/baseline.eh
python3 -I ra-check.py out/baseline.dis out/baseline.nm out/baseline.eh
```

`--rustflags` values must be single tokens (`-Cdebuginfo=2`, not `-C debuginfo=2`):
`cargo prove build` passes each one to rustc as one argument. `out/` is ignored and holds
about 184 MB of builds.

---

# Step 2 (minimal): kernel decoding (2026-10-12)

Is it affordable to check `decode` of the image in the kernel, instead of trusting
`check-generated`? `lake exe gen-image` (`Tools/GenImage.lean`, which calls riscv-zkvm's
`parseElf64` and `decode`) emits one module per function under `Cases/Zip2005/Image/`. Each
holds `words`, `packed` (the same words as one `Nat`) and `prog` (the decoding, as a
literal). `time-decode.sh` times `decodeWords words = prog` alone, net of the ~0.33 s import
baseline.

- The generator agrees with zip-2005: 306 functions, 41,776 words, 3 that decode to `none`.
- Elaborating a data module costs about 1.3 ms per word. All 306 build in 15 s in parallel.

| Function | Words | `List` + `decide +kernel` | packed `Nat` | `List` + `rfl` |
|---|---|---|---|---|
| `default_hook` | 80 | 0.14 s, 442 MB | 0.16 s | 0.28 s |
| `memcpy` | 510 | 0.63 s, 576 MB | 1.2 s, 721 MB | 1.0 s |
| `main` | 949 | 1.3 s, 747 MB | 2.2 s, 967 MB | 1.9 s |
| `blake2b compress1_loop` | 2809 | 3.1 s, 1.2 GB | 8.2 s, 2.3 GB | 6.2 s |
| largest (`Fp` op) | 4424 | 1.7 s, 865 MB | 10.6 s, 3.0 GB | 5.8 s |
| **all 306** | **41,776** | **56 s total**, worst 8.0 s / 2.3 GB (`sha256::compress256`) | | |

**Verdict: affordable.** Use the `List` form with `decide +kernel`. The packed `Nat` loses
because every word extraction shifts the whole number.

# Step 3 spike: return-address integrity in Lean (2026-10-12)

## What was built

- **`AsmVerif/RiscV/Frame/Domain.lean`**: a computable frame analysis.
  - Abstract values: `lin r k` (entry value of `r` plus `k`), `const c`, `top`. Slots map
    frame offsets to abstract values.
  - Calls are a contract macro-step. Outlined fragments are executed in place.
  - `Fn.valid` checks a per-instruction annotation in one pass.
- **`AsmVerif/RiscV/Frame/Sound.lean`**: `integrity`, proved against riscv-zkvm's `stepSp1`.
  Along any `Run` of one activation, every step that leaves the function (a `ret`, or a
  non-call step whose target is outside it) ends with `ra` and `sp` at their entry values.
  49 theorems, no `sorry`, axioms `propext`/`Classical.choice`/`Quot.sound` only.
- **`Cases/Zip2005/Frame/{Memcpy,PadNext,DefaultHook}.lean`**: `integrity_of_run` for the
  three functions. The annotation is generated by `Gen.lean` (untrusted) and re-checked by
  `decide +kernel`.

1,613 lines in all; zero warnings.

## What each function's theorem rests on

| Function | Words | Kernel `valid` | Premises left |
|---|---|---|---|
| `memcpy` | 510 | 22 s, 6.5 GB | **none** beyond the image. The jump table is handled as an "anywhere" edge, since `ra`/`sp` are never written |
| sinsemilla `Pad::next` | 471 | 19 s, 5.8 GB | **43 `Req`s**: each store through `self` (`a0 + k`) misses the `ra` save slot, i.e. "`self` is not in this frame". **1** call (a panic) assumed not to return |
| `default_hook` | 80 | 1.9 s, 0.8 GB | **4 `Req`s**: statics `OUTPUT_CAPTURE_USED` and `OUTPUT_CAPTURE` are not the `ra` slot (stack ∩ `.bss` = ∅). **2 residuals**: stores through pointers a callee returned (`0x7803b774`, `0x7803b798`) |

Every theorem also takes the call contract `CallRet` for each call inside `Run`. The callee
returns to the next instruction, keeps the code, `sp` and `s0`–`s11`, and leaves the
caller's saved `ra` alone.

## What the spike taught

1. **The crux works.** Store aliasing, `ra` as a scratch register, outlined prologues and
   jump tables are all discharged against the real `stepSp1`, by one generic soundness proof
   plus a kernel-checked certificate per function.
2. **Run the fixpoint outside the kernel.** Running `analyze` in the kernel took 593 s /
   26 GB for `Pad::next`, and overflowed the kernel's recursion limit on `memcpy` (fuel
   recursion). With a generated annotation the kernel only runs `valid`: 19 s, about 30×
   better. Next optimisation: sparse annotations (32-register lists per instruction dominate;
   at block heads only, or as diffs) and relocation-derived jump-table targets instead of
   "anywhere".
3. **Store aliasing does not reduce to nothing locally.** It reduces to three kinds of named
   premise, each with an obvious owner in the whole-program layer:
   - footprint premises on arguments (`self` vs. frame): the caller discharges them;
   - statics vs. stack: one global fact about the memory map;
   - residuals through callee-returned pointers: a callee postcondition, "the pointer I
     return is not into your frame".
4. **Only protect the return-address slot.** Protecting every spilled register made
   `Pad::next` owe 559 premises. Protecting only `ra` slots (forgetting others, which is
   sound) brings it to 43.
5. **Lean proof engineering.** A nested constructor pattern (`.lin .x2 k`) in a definition
   makes `split` expand riscv-zkvm's 32-way `Reg` case tree (max recursion). Test such cases
   with `if` (`AVal.frameOff?`). An abstract register file must be data (`List`), not a
   closure, or evaluation of repeated joins blows up.

## Not covered, by design of the spike

- `ECALL` inside a checked function (it is rejected).
- Fragments that owe premises.
- Composing `CallRet` with the callee's own `integrity_of_run`, which is the next step. The
  `pc`/`sp` half of `CallRet` is exactly what `integrity` gives the callee. The `s0`–`s11`
  and slot-preservation half needs a callee-saved analysis and a footprint, built the same
  way.

## Reproduce

```bash
lake exe gen-image experiments/zip-2005/out/relocs.elf experiments/zip-2005/out/baseline.nm \
  Cases/Zip2005/Image Cases.Zip2005.Image
experiments/zip-2005/time-decode.sh list $(cut -f1 Cases/Zip2005/Image/INDEX.tsv)
lake env lean --run Cases/Zip2005/Frame/Gen.lean      # regenerate the annotations
lake build Cases.Zip2005.Frame.Memcpy Cases.Zip2005.Frame.PadNext Cases.Zip2005.Frame.DefaultHook
```

---

# Item 1: a kernel-checked loader in place of `check-load` (2026-10-12)

- **`AsmVerif/RiscV/Load.lean`**: a total loader mirroring riscv-zkvm's `Interpreter.load`.
  - An `Image` is an entry point, code chunks tiling the executable segments, and data
    chunks (doublewords, with `.bss` as a zero count).
  - `Image.state` is the starting `MachineState`.
  - `Image.codeAt_prog` (proved once): in an image passing `codeWF`, a function's chunk
    plus `decodeWords ws = prog` put `prog` at `base + 4 j`.
- **`AsmVerif/RiscV/Frame/Image.lean`**:
  - `stepSp1_code`: no SP1 step changes code, including syscalls, hint reads and precompiles.
  - `codeOk_of_image`: discharges the frame theorems' `CodeOk` premise from an image.
- **`gen-image`** now also emits `Data_<i>` (one per segment) and `Layout` (`image : Image`).
  It **cross-checks** that image against riscv-zkvm's `Interpreter.load`, entry by entry in
  both directions: **41,780 code entries and 36,144 memory doublewords agree**. The tiling
  is 306 function chunks plus one gap, which is `__start` (`0x7801bcd0`, no sized symbol).
- **`Cases/Zip2005/Loaded.lean`**: `codeWF` and four decodings by `decide +kernel` (3.5 s,
  1 GB for the whole file). It restates the three integrity theorems from the loaded guest:
  any state `stepsSp1 n (image.state input)` reaches has the image's code, so `CodeOk` is no
  longer a premise.

**What moved out of the trusted base.** zip-2005's `check-load` evaluated predicates on
`Interpreter.load` in compiled code. Here every fact about the loaded state is a kernel
theorem about a 20-line total loader. The one executable step left is the generator's claim
that the two loaders agree on this ELF; it is checked exhaustively, and narrower than
`check-load`'s predicates. Both loaders share the same trust in how SP1 loads a guest.

**Not yet:** memory read-back lemmas (`memAt`) for statics and `.rodata`. Nothing proved so
far needs them; item 2's statics premises will.

---

# Coverage sweep: the frame checker over the whole binary (2026-10-12)

`lake exe frame-sweep ELF NM OUT.tsv` (`Tools/FrameSweep.lean`) runs the analysis and
`Fn.valid` in compiled code over every function, offering each the image's outlined
fragments. The full binary takes 2 s.

**290 of 304 functions check**, covering 40,596 of the 41,776 function words (97%).

The 14 that do not fall into three kinds:

| Kind | Count | Functions | Fix |
|---|---|---|---|
| `ecall` | 6 | `syscall_halt`, `syscall_write`, `read_vec_raw`, `syscall_pallas_add`/`_double`, `syscall_uint256_mulmod` | model `ECALL` (changes `t0` and memory only; needs an `sp1Ecall` register lemma) |
| undecodable word | 3 | `rust_panic`, `panic_with_hook`, `__rust_end_short_backtrace` (`unimp` pads after noreturn calls) | an undecodable word traps: no successors (as in `stepSp1`) |
| exit check | 5 | `core::fmt::{write, Formatter::pad, pad_integral, write_prefix, PadAdapter::write_char}` | indirect tail calls through vtables, treated as "anywhere" edges; need relocation-derived targets plus a control-flow premise |

Premises among the 290 that check:

| | Functions | Total |
|---|---|---|
| None at all | 159 | — |
| `Req`s (entry-register footprint) | 106 | 886 |
| Residuals (stores through unknown pointers) | 48 | 229 |
| Calls assumed not to return | 89 | 89 |

This is the size of the obligation the whole-program layer has to discharge.
