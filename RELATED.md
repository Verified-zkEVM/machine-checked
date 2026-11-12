# Related work

A survey of work on formally verifying machine code (binaries and assembly rather than source),
written to inform MachineChecked's design. For each line of work it says what is verified, in
which prover, what is trusted, which techniques it uses, how mature it is, and what
MachineChecked can borrow. The layers referred to throughout are those of
[`ROADMAP.md`](ROADMAP.md): -1 (ELF and context), 0 (ISA), 0.5 (low logical program), 1
(structured logical program), 2 (specification refinement).

> **How to read this document (compiled 2026-11-12).** It was assembled from a multi-agent
> literature search: 5 search angles, 23 sources fetched, 101 claims extracted, and 25 of them
> put to a 3-vote adversarial check (24 confirmed, 1 refuted). Each entry is marked:
>
> - ✔ **checked**: the specific claims were extracted from, or verified against, the primary
>   source linked (the paper, the project README or the preprint).
> - ○ **background**: included for completeness from general knowledge of the field, and *not*
>   checked in this pass. Treat the details as pointers to read, not as citations.
>
> Several sources describe themselves (READMEs, abstracts), and the 2026 zkVM projects change
> quickly. Re-check status before relying on any of it.

---

## Contents

1. [The landscape at a glance](#1-the-landscape-at-a-glance)
2. [Decompilation into logic and translation validation](#2-decompilation-into-logic-and-translation-validation)
3. [Program logics over authoritative ISA specifications](#3-program-logics-over-authoritative-isa-specifications)
4. [The Lean ecosystem](#4-the-lean-ecosystem)
5. [Binary lifting and verified decompilation](#5-binary-lifting-and-verified-decompilation)
6. [Instruction-set models and how they are validated](#6-instruction-set-models-and-how-they-are-validated)
7. [Verified assembly, cryptography and verified compilers](#7-verified-assembly-cryptography-and-verified-compilers)
8. [AI-assisted machine-code proof](#8-ai-assisted-machine-code-proof)
9. [Lessons for MachineChecked, layer by layer](#9-lessons-for-machinechecked-layer-by-layer)
10. [Open questions this survey raises](#10-open-questions-this-survey-raises)
11. [Gaps in this survey](#11-gaps-in-this-survey)
12. [Bibliography](#12-bibliography)

---

## 1. The landscape at a glance

Where the main systems sit relative to MachineChecked's stack.

| system | object verified | prover | ISA(s) | compiler / assembler trusted? | ISA model | nearest MachineChecked layer |
| --- | --- | --- | --- | --- | --- | --- |
| Myreen's decompiler (HOL4) ✔ | machine code | HOL4 | ARM, x86, PowerPC | no | Fox ARM, Sarkar x86, Leroy PowerPC | lift 1 + 0.5→1 |
| Proof-producing compilation, CC 2009 ✔ | generated machine code | HOL4 | ARM, x86, PowerPC | no (nasm, gas untrusted) | as above | layer 2 pattern |
| seL4 binary TV, PLDI 2013 ✔ | gcc ARM binary vs C | HOL4 + Isabelle + SMT | ARMv7 (later RV64) | no | Cambridge ARM | whole stack |
| Islaris, PLDI 2022 ✔ | machine code | Coq / Iris + Isla (SMT) | Armv8-A, RISC-V | no | full Sail models | 0 + program logic |
| s2n-bignum ✔ | object code of hand-written asm | HOL Light | x86-64, AArch64 | no | hand-written HOL Light models | 0 / 0.5 |
| Relational Hoare logic, CAV 2025 ✔ | pairs of asm routines | HOL Light | x86-64, AArch64 | no | as s2n-bignum | program logics (1) |
| Bignum-Lean ✔ | s2n-bignum port | Lean 4 | AArch64 (x86 planned) | no | ported from s2n-bignum | 0 / 0.5 |
| LNSym ✔ | AArch64 machine code (crypto) | Lean 4 | AArch64 | no | own Lean model, hardware-tested | 0 tactics |
| sp1-lean / sp1-clean-native ✔ | SP1 zkVM circuits vs ISA | Lean 4 | RV64 | n/a | Sail RV64 in Lean | beside layer 0 |
| zisk-fv ✔ | ZisK zkVM circuit vs ISA | Lean 4 | RV64IM | n/a | Sail RV64 in Lean | beside layer 0 |
| Jolt-QED ✔ | Jolt bytecode expansions | Lean 4 | RV64 | n/a | Sail RISC-V in Lean | lift 1 pattern |
| VT Hoare graphs, PLDI 2022 ✔ | stripped x86-64 ELF | Isabelle/HOL | x86-64 | no | ~120 instructions, hand-written | lift 1 |
| FoxDec 2.0 / 3.0 ✔ | x86-64 ELF | Isabelle/HOL + TV | x86-64 | no | Isabelle x86 + Ghidra P-Code | 0.5 analogue |
| McSema validation, PLDI 2020 ✔ | lifter output (LLVM IR) | K + SMT | x86-64 | n/a | K-x86 | lift 1 validation |
| ACL2 x86isa ✔ | x86 machine code incl. syscalls | ACL2 | x86-64 | no | own, co-simulated vs silicon | 0 + context (-1) |
| Sail models ✔ | ISA specifications | → Isabelle, HOL4, Coq, Lean | Arm, RISC-V, CHERI, MIPS | — | — | 0 |
| Arm ASL / MRA ✔ | ISA specification | — (executable) | Armv8-A, v8-M | — | — | 0 (root of trust) |
| Anthropic / Theorem (2026) ✔ (secondary) | static musl RISC-V binaries | Rocq | RISC-V | no | — | whole stack, AI-driven |
| CakeML / Silver / Pancake ○ | compiler output | HOL4 | several, incl. RISC-V | verified compiler | HOL4 L3 models | 0.5 / 1 inspiration |
| Jasmin ○ | compiler output | Coq (EasyCrypt) | x86-64 (more recently others) | verified compiler | Jasmin's x86 semantics | 0.5 (linear Jasmin) |
| Vale ○ | assembly | Dafny / F* | x86-64, ARM | assembler-printing trusted | hand-written | — |
| Bedrock2 + riscv-coq ○ | compiler output | Coq | RISC-V | verified compiler | riscv-coq | 1 (logic), 0 |
| Kraken (x64) | assembly | Lean 4 | x86-64 | assembler and linker trusted | hand-written, SDM-checked, SDE-fuzzed | 0 (chosen, `docs/ISA.md`) |
| DeepMind arm64-semantics | bytes | Lean 4 | AArch64 | no | hand-written from ASL, tested vs Sail-arm | 0 (chosen, `docs/ISA.md`) |

The Kraken and arm64-semantics rows come from this repository's own `docs/ISA.md`. They are not
re-surveyed here.

---

## 2. Decompilation into logic and translation validation

This is MachineChecked's closest intellectual ancestor. The pattern is: run untrusted tools,
then produce a proof that ties their output to the ISA model, so that the tools drop out of the
trusted base.

### 2.1 Decompilation into logic (Myreen, Gordon, Slind; HOL4) ✔

- **What:** a fully automatic, proof-producing tool inside HOL4. It translates concrete machine
  code into *functions defined in the logic*, with a correspondence (certificate) theorem
  proved for each. Properties proved about the extracted functions carry over to the machine
  code, so verifiers "only deal with tractable extracted models of the machine code rather than
  the concrete code itself".
- **Technique:** compose per-instruction machine-code Hoare triples (separation-logic-style `*`
  assertions) into one-pass triples, then instantiate a loop rule to get tail-recursive
  functions. The decompiler takes the ISA model as a parameter, so the same tool serves ARM, x86
  and PowerPC. A 2012 revision ("Decompilation into Logic — Improved", FMCAD 2012) replaced
  the original machine-code Hoare logic with a simpler one that is faster to mechanise.
- **Caveat:** an extracted function holds only under side conditions (memory layout, alignment,
  termination), and these still have to be discharged.
- **Downstream:** proof-producing synthesis, binary translation, Jitawa/CakeML, and the seL4
  binary verification (§2.3).
- **Borrow:** this is the template for the 0.5 → 1 lift. Lift a function (blocks and loops)
  into an ordinary Lean function, plus a simulation theorem generated by a tactic or
  metaprogram, so that users prove specifications about the Lean function. The
  `LogicalProgram` sketch in `docs/LogicalMachine.md` already points this way.
- **Critique worth knowing:** the s2n-bignum relational-logic paper (§3.3) argues that the
  Myreen–Gordon logic lacks a *conjunction rule*, and that this "significantly increases the
  proof burden". Keep this in mind when designing layer 1's logic.

Link: <https://www.cl.cam.ac.uk/~mom22/decompilation>

### 2.2 Extensible proof-producing compilation (Myreen, Slind, Gordon; CC 2009) ✔

- **What:** compiles tail-recursive HOL4 functions to ARM, x86 or PowerPC in three stages:
  1. *generate* code, without proof;
  2. *decompile* the machine code, with proof, into `f'`;
  3. *certify*: prove `f = f'`.
- **Trust:** "these tools do not need to be trusted… The trusted computing base (TCB) of our
  compiler is HOL4 and the specifications of the target machine languages". The off-the-shelf
  assemblers (nasm, gas) are untrusted, because wrong code makes the certification fail. The
  certification phase was about 100 lines of ML.
- **Implicit trust point:** the machine code still has to be read into HOL4 correctly. In
  MachineChecked that is layer -1, the ELF loader (see the trust ladder in `docs/ELF.md` §4).
- **Borrow:** the generate / decompile / prove-equal pattern is the layer-2 refinement story in
  miniature. For CatCrypt-style kernels, with a reference function in Lean and a compiled
  binary, layer 2 can be exactly this: lift, then prove the lifted function equals the
  reference.

Links: <https://www.cl.cam.ac.uk/~mom22/extensible-compilation.pdf>,
DOI [10.1007/978-3-642-00722-4_2](https://doi.org/10.1007/978-3-642-00722-4_2)

### 2.3 Translation validation for seL4 (Sewell, Myreen, Klein; PLDI 2013) ✔

- **What:** extends seL4's C-level functional correctness proof (about 9,500 lines of C) to the
  binary (about 11,736 ARM instructions). It proves that the binary refines the C semantics, so
  unmodified gcc 4.5.1 at `-O1`, and most of `-O2`, is no longer trusted.
- **Pipeline:** three proof systems. The binary is decompiled into HOL4 with Myreen's tool,
  against the Cambridge ARM model. The C goes through Norrish's C parser in Isabelle/HOL. Both
  are translated into a common CFG graph language, and refinement is discharged with the SMT
  solvers Z3 and SONOLAR.
- **Coverage:** all of `-O1`. At `-O2`, all but 3 routines (98%). The failures are mostly in
  *finding split points*, caused by loop unrolling and loop-invariant code motion. A full run
  with certificates adds 6–8 hours.
- **Technique to note:** the decompiler had to learn the ARM C calling convention and treat the
  **stack as a separate data structure**, so that binary functions line up with C functions.
- **Trust:** moves to the binary-verification tool and to "the import of an executable file
  into hexadecimal numbers into the theorem prover". The initial memory layout is *assumed*.
  This is the same layer -1 gap MachineChecked names. Trustworthy Systems report that the
  toolchain was later ported to 64-bit RISC-V.
- **Borrow:**
  - stack-as-separate-object is the layer-1 move "frames become locals" (`ROADMAP.md`);
  - split-point discovery is where optimised code breaks decompilation, so plan for loop
    invariants supplied by the user or a hint file;
  - SMT for graph refinement is the step MachineChecked would do in-kernel (`bv_decide`,
    `grind`) to keep solvers out of the trusted base.
- **Further reading:** Sewell's PhD thesis (Trustworthy Systems) is the longer account.

Links: <https://www.cl.cam.ac.uk/~mom22/pldi13.pdf>,
<https://trustworthy.systems/projects/TS/compiler-correctness>

### 2.4 CakeML, Silver and Pancake ○

- **CakeML** is a verified ML compiler in HOL4 that emits machine code for several ISAs,
  including RISC-V. Its backend is built on the same decompilation and ISA-model heritage
  (L3 models by Fox).
- **Silver** is a verified processor with a verified CakeML compilation stack on top of it
  ("Verified compilation on a verified processor", PLDI 2019). It is an end-to-end stack down
  to hardware.
- **Pancake** is a low-level systems language in the CakeML ecosystem, verified down through
  CakeML's backend. `ROADMAP.md` already names it as the inspiration for layer 1.
- **Borrow:** CakeML's intermediate languages (in particular the low, register-level ones near
  `stackLang`, `labLang` and `asm`) are a mature reference for exactly the abstractions layers
  0.5 and 1 need: labels, stack frames, calling conventions, and ISA-parametric assembly. The
  difference is direction: CakeML compiles down with a proof, and MachineChecked lifts up with
  a proof.

---

## 3. Program logics over authoritative ISA specifications

### 3.1 Islaris (Sammler et al.; PLDI 2022) ✔

- **What:** describes itself as the first system to verify machine code "above these complete
  and authoritative real-world ISA specifications": full Sail Armv8-A (from Arm's ASL) and Sail
  RISC-V.
- **Technique:** Isla, an SMT-based symbolic executor, runs the Sail model under constraints
  on the system configuration (for example a fixed exception level) and produces small
  per-instruction *traces*. Proofs are then done in a new Iris separation logic in Coq over
  those traces.
- **Why pruning:** the full models are huge. Armv8.5-A is 113k and RISC-V 14k non-whitespace
  lines of Sail. In the Sail-generated Coq Armv8-A model "even simple definition unfoldings
  take an unreasonably long time or fail to terminate".
- **Trust:** Isla and the SMT solver join the TCB; the separation logic does not. Post-hoc
  translation validation of Isla traces against the Sail-generated Coq model was done **only
  for RISC-V**, and the paper reports it infeasible for Armv8-A because of model size.
- **Case studies:** a relocation-parametric exception handler from pKVM, unaligned access
  faults, memory-mapped IO, and Clang-compiled C with inline assembly and function pointers.
- **Scope:** single-threaded; no self-modifying code; no address translation.
- **Borrow:**
  1. Expect the same unfolding cost from arm64-semantics and Kraken in Lean. Plan
     *configuration-specialised, pre-simplified per-instruction lemmas* (an Isla trace is
     essentially such a lemma), generated once and cached.
  2. Islaris's trace validation is the counterpart of lift 1's per-instruction proofs against
     riscv-zkvm. Doing them in-kernel, as MachineChecked already does, keeps the SMT solver out
     of the TCB, which is what Islaris could not do for Arm.
  3. Its systems features (exception vectors, MMIO) are a guide for when a context (layer -1)
     goes beyond zkVM user code.

Links: <https://pub.ista.ac.at/~msammler/paper/islaris.pdf>,
DOI [10.1145/3519939.3523434](https://doi.org/10.1145/3519939.3523434),
artifact record <https://research-explorer.ista.ac.at/record/17502>

### 3.2 s2n-bignum (AWS; HOL Light) ✔

- **What:** cryptographic big-integer routines written directly in machine code, callable from
  C, with separate API-compatible x86-64 and AArch64 versions. Each routine has a HOL Light
  proof about "the actual object file generated by the build process", so the assembler is
  untrusted.
- **Scale:** the core logic and tactics are about 10k lines of HOL Light. They verify 615 Arm
  and x86 routines, covering 1013 functional properties in about 860k lines of proof (figures
  from the CAV 2025 paper, §3.3).
- **Trust:** formal models of how each processor executes code; the project notes that these
  simplify and idealise the hardware. Constant time is a design goal but "is not actually
  rigorously machine-checked at present" (README). §3.3 partly addresses this.
- **Borrow:** it is the industrial benchmark for the x86-64 and AArch64 targets in
  `ROADMAP.md`. Its routines are natural first targets once Kraken and arm64-semantics are
  required, and its specifications can be ported as the layer-2 specifications.

Links: <https://github.com/awslabs/s2n-bignum> (mirror read: <https://github.com/jargh/s2n-bignum>)

### 3.3 Relational Hoare logic for machine code (Mazzucato et al.; CAV 2025) ✔

- **What:** a relational Hoare logic for realistically modelled machine code, fully formalised
  in HOL Light (CMU, Stanford, AWS; authors include Barrett, Harrison and Pasareanu). Applied to
  s2n-bignum, it proves (a) the **constant-time discipline** and (b) **equivalence** between
  optimised routines and verification-friendly ones. The optimised versions came from an
  autovectoriser, the SLOTHY scheduler and a memory-instruction optimiser.
- **Size:** the relational core adds 1,704 lines; 15 routine pairs were proved equivalent in
  about 19k lines of proof.
- **Logic:** handles indirect branches and self-modifying code. The relational triple
  (`ensures2`) commutes, composes and supports contract unification.
- **Borrow:**
  - the answer to the roadmap's open question on **constant time**: a relational logic over a
    leakage-instrumented semantics, at layer 0.5 or 1;
  - "prove the optimised code equivalent to a simple version, then verify the simple version"
    is a cheap refinement route for layer 2;
  - the conjunction-rule critique of Myreen's logic (§2.1) is a design input for layer 1.

Links: <https://assets.amazon.science/56/20/f6b40ee84e7b8633ca1053499aff/relational-hoare-logic.pdf>,
arXiv [2505.14348](https://arxiv.org/abs/2505.14348)

---

## 4. The Lean ecosystem

The pieces nearest to MachineChecked, and the most likely to be shared.

### 4.1 LNSym (AWS-originated; `leanprover/LNSym`) ✔

- **What:** a symbolic simulator for Armv8 AArch64 machine code in Lean 4 (authors include
  Shilpi Goel and Siddharth Bhat), used for crypto routines in AWS-LC such as SHA-512.
- **Structure:** `Arm/` (its own hand-written formalisation of a *subset* of AArch64, mostly the
  instructions its crypto targets use), `Specs/`, `Proofs/` and `Tests/`. It runs **conformance
  tests against real hardware** when built on an AArch64 machine, has ELF-loading tests for
  AWS-LC, and includes a simulator benchmark. Apache-2.0.
- **Not:** derived from ASL or Sail. The sources disagree on how recently it was active; check
  before depending on it.
- **Borrow:** its symbolic-simulation tactics, state and memory representation, and use of
  `bv_decide`, for the AArch64 layer-0 tooling. Its model is also a third reference to
  cross-test against arm64-semantics, alongside Sail-arm.

Link: <https://github.com/leanprover/LNSym>

### 4.2 Bignum-Lean (`cslib-community/bignum`) ✔

- **What:** a Lean 4 port of parts of s2n-bignum, AArch64 only so far (x86-64 planned).
  Its immediate goal is to port the relational Hoare formalism of §3.3. Early stage; it builds
  on recent toolchains (v4.28 up to v4.34 release candidates). Apache-2.0.
- **Borrow:** the most direct overlap with the s2n-bignum-style targets in `ROADMAP.md`.
  Coordinate on the specifications, and possibly on a relational logic, rather than duplicating
  them.

Link: <https://reservoir.lean-lang.org/@arademaker/bignum>

### 4.3 Sail RISC-V in Lean, and zkVM verification ✔

The Lean zkVM-verification projects have converged on **a Sail-derived RV64 model in Lean** as
the reference semantics. riscv-zkvm, MachineChecked's RISC-V backend, belongs to the same
family (`docs/ISA.md`: "tied to Sail").

- **sp1-lean / sp1-clean-native (Succinct).** Verifies SP1 Hypercube RISC-V chips (ALU, Mul,
  DivRem, shifts, Branch, Jal/Jalr, UType, Load/Store), written in the Verified-zkEVM **Clean**
  DSL, against `LeanRV64D` from `succinctlabs/sail-riscv-lean` and `rems-project/lean-sail`.
  Per-chip soundness is axiom-clean and sorry-free, and there is a trace-level bus-composition
  layer. It is **not end-to-end** yet, and five completeness proofs are deferred. It is on
  Lean v4.28; MachineChecked is on v4.33.1.
  <https://reservoir.lean-lang.org/@succinctlabs/sp1-clean-native>
- **zisk-fv (eth-act).** Verifies the ZisK zkVM circuit against Sail RV64IM, compiled to Lean
  from pinned sail-riscv sources with Sail's Lean backend (Sail 0.20.x; build OCaml 5.x, since
  OCaml 4.14 overflows the stack, rems-project/sail#1674). It is under construction and makes
  no security-assurance claim, but it has already found bugs in ZisK v0.17.0 that led to five
  upstream fixes. *A stronger claim about its headline trace-level theorem was refuted 0–3 in
  verification, so describe it only as work in progress.*
  <https://awesome.ecosyste.ms/projects/github.com%2Feth-act%2Fzisk-fv>
- **Jolt-QED (Biswas, Dao, Ross, Thaler; ePrint 2026/2157).** Extends an earlier Lean
  translation of the Sail RISC-V spec to define the Jolt ISA. A generator runs Jolt's
  *untrusted* Rust bytecode expander and emits its output as Lean programs, which are then
  proved: 51 of 58 expansions are equivalent to the RISC-V instruction they replace. This is
  translation validation of an untrusted tool, at instruction granularity, in Lean, and the
  closest analogue to lift 1's per-instruction lemmas.
  <https://eprint.iacr.org/2026/2157>
- **risc0-lean4.** A Lean 4 model of the RISC Zero zkVM, with executable RV32IM emulation and
  FRI-verifier parts; its meta-theory is still being developed.
  <https://reservoir.lean-lang.org/@risc0/risc0-lean4>
- **evm.asm (Verified-zkEVM / zkSecurity).** An experimental verified macro assembler: EVM
  opcodes written as RV64IM macros and proved in Lean 4, with separation-logic-style
  specifications of code fragments. Its `regen-sail-model.sh` and `PROVENANCE.toml` show one
  way to import and pin the Sail model. The project's direction is under reconsideration.
  <https://reservoir.lean-lang.org/@Verified-zkEVM/EvmAsm>
- **Borrow:**
  - a **shared per-instruction lemma library** (decode + execute = closed form) over the Sail
    RV64 Lean model. It is needed by lift 1 here, by Jolt-QED and by the circuit projects, so
    it is worth upstreaming, subject to toolchain alignment;
  - the zisk-fv / evm.asm **provenance discipline** (pinned Sail revision, regeneration script,
    recorded provenance) for layer 0's trust story;
  - Jolt-QED's *generator emits Lean, Lean checks it* is the same architecture as `Tools/`
    (ELF to Lean, contract inference).

### 4.4 Kraken and DeepMind arm64-semantics

Already chosen as the x86-64 and AArch64 layer-0 models. See `docs/ISA.md` for the reasoning,
which is not repeated here. Two lessons from this survey bear on them:

- Islaris's unfolding problem (§3.1) and VT's coverage bottleneck (§5.1) pull in opposite
  directions. A full model removes the coverage bottleneck but brings the unfolding cost back.
  Both Kraken (`SymM`, `grind`, `mvcgen`) and arm64-semantics' `ProofLib` exist to manage that
  cost. Measure it early on a real target.
- Kraken verifies *assembly*, so on x86-64 the assembler and linker are trusted. Every system in
  §2 and §5 that closes that gap does it by **reading the bytes back** (decompiling with proof,
  or FoxDec 3.0's binary-to-binary TV). That is the route to "checking the assembly against the
  bytes of the binary", which `docs/ISA.md` lists as later work.

### 4.5 Other Lean and Coq work worth knowing ○

- **Aeneas** (Ho, Protzenko): Rust → pure Lean functional models. Relevant as a possible
  source-level specification for layer 2 when the binary was compiled from Rust (SP1 guests
  are Rust). zisk-fv reportedly uses Aeneas-extracted code.
- **Bedrock2 + riscv-coq** (MIT, Coq): a low-level language with a separation-logic program
  logic and a verified compiler to a RISC-V model, used in end-to-end hardware/software
  verification. The best-developed example of a *program logic for a C-like language over
  RISC-V*, so a design reference for layer 1, though it goes downward.
- **Lean MLIR** (Bhat et al.): verified peephole rewrites and SSA reasoning in Lean. It may be
  relevant if layer 0.5 or 1 adopts SSA-style operations.
- **Verified-zkEVM rust-lean** (arXiv 2605.30106): a Rust-to-Lean pipeline with AI provers,
  as a possible source of layer-2 specifications. Not checked.

---

## 5. Binary lifting and verified decompilation

The main lesson of this section is that **unverified lifters are wrong in practice**. The
systems that reach scale with guarantees all *validate* the lifter's output against a formal
ISA model.

### 5.1 Formally verified lifting of C-compiled x86-64 binaries (Verbeek, Bockenek, Fu, Ravindran; PLDI 2022) ✔

- **What:** lifts *stripped* x86-64 ELF binaries to **Hoare graphs**: vertices hold predicates
  over registers, flags and memory (with aliasing models), and edges are instructions.
- **Two steps:**
  1. an unverified extraction, proven correct only on paper, that also checks *return-address
     integrity*, *bounded control flow* and *calling-convention adherence*;
  2. every edge exported as an **independent Hoare triple** to Isabelle/HOL and proved
     automatically, in parallel ("thousands of mutually independent theorems, generally one
     per instruction").
- **Scale:** step 1 on Xen: 45 binaries, 2,115 of 2,151 functions (98%), about 400K
  instructions. Step 2 only on some CoreUtils binaries (gzip, tar, hexdump), because the
  Isabelle semantics covered only **about 120 x86-64 instructions**, with floating point as
  uninterpreted functions.
- **Assumptions:** unknown external functions are assumed to follow System V, and the
  assumption is emitted as explicit proof obligations. Partially overlapping memory regions are
  handled by destroying their contents. A function is rejected if return-address integrity
  cannot be proven.
- **Scope:** single-threaded, C-compiled ELF only.
- **Borrow:**
  - **per-instruction, independently checkable obligations** suit Lean's parallel elaboration.
    This is a real option for lift 1 at whole-binary scale (zip-2005);
  - the *sanity properties* (return-address integrity, bounded control flow, calling
    convention) as explicit lifting preconditions. These are what `Architecture.md`'s
    structural specification (`ra`, callee-saved registers, footprint `W`) and `CfiOk`
    already state;
  - "external calls are assumed to follow the ABI, as explicit obligations" matches the plan
    for system calls as external calls with specifications;
  - the bottleneck was **ISA coverage, not automation**. Full models (Kraken, arm64-semantics,
    Sail RV64) remove it.

Links: <https://www.ssrg.ece.vt.edu/papers/pldi22.pdf>,
DOI [10.1145/3519939.3523702](https://doi.org/10.1145/3519939.3523702); memory proofs: TACAS 2020
<https://www.ssrg.ece.vt.edu/papers/tacas20.pdf>

### 5.2 FoxDec 2.0 / 3.0 (Virginia Tech SSRG) ✔

- **FoxDec 2.0:** builds the Hoare graph by symbolic execution with formal instruction
  semantics. The graph is claimed to overapproximate all executions, and each transition is
  proved as a Hoare triple in Isabelle/HOL, so the construction algorithm leaves the TCB.
- **FoxDec 3.0:** lifts x86-64 binaries to a **machine-independent IR** (now NASM; formerly C),
  recompiles it, and proves the original and recompiled *binaries* equivalent by translation
  validation. That removes both the lifter and the compiler from the TCB. Ghidra is used only
  as a disassembler (via P-Code).
- **Publications:** PLDI 2022 (§5.1); *Verifiably Correct Lifting of Position-Independent
  x86-64 Binaries to Symbolized Assembly* (CCS 2024); *A Formal Semantics for P-Code* (VSTTE
  2022, §5.4); *Formally Verified Binary-level Pointer Analysis* (ICSE 2025).
- **Scale and scope:** case studies on GNU CoreUtils, OpenSSL, x86-64 seL4 and Xen (about 450K
  instructions), and a patch to wget fixing CVE-2019-5953. Sequential, C (no C++), System V
  AMD64 ABI only. Actively developed.
- **Trust that remains:** Ghidra's disassembly and P-Code semantics, the equivalence checker,
  the Isabelle x86 semantics and the export pipeline.
- **Borrow:** FoxDec 3.0's "machine-independent IR" is the closest analogue to layer 0.5.
  MachineChecked's version is stronger: the simulation is proved in Lean against a full ISA
  model, rather than going through Ghidra P-Code and an external equivalence checker. The CCS
  2024 *symbolisation* work (recovering which constants are addresses) is the problem layer 1
  meets when it turns addresses into variables. The ICSE 2025 pointer analysis is relevant to
  footprints `W`.

Link: <https://github.com/ssrg-vt/FoxDec>

### 5.3 Scalable validation of binary lifters (Dasgupta, Dinesh, Venkatesh, Adve, Fletcher; PLDI 2020) ✔

- **What:** translation validation of x86-64 instructions lifted to LLVM IR by **McSema**,
  against the K-framework x86-64 semantics (§6.4). The authors call it the first
  single-instruction TV on an ISA as large as x86-64.
- **Results:** per-instruction validation found **29 previously unknown bugs** in McSema, a
  mature lifter. A *compositional lifter* composes validated per-instruction IR into a
  reference translation, and comparison with McSema's output is reduced to a
  **graph-isomorphism check** after normalising transformations, avoiding full SMT
  equivalence. It proved 2,254 of 2,348 functions (about 96%) on LLVM's single-source suite.
- **Borrow:** confirms the per-instruction granularity of lift 1. The compositional-lifter
  idea (build a reference translation from proved per-instruction pieces, then compare
  structurally) is also how a fast, untrusted lifter could be checked rather than verified.
  Note that "unverified lifters are unreliable" is an extrapolation from one lifter, though it
  is consistent with §5.4.

Link: <https://pldi20.sigplan.org/details/pldi-2020-papers/4/Scalable-Validation-of-Binary-Lifters>

### 5.4 Ghidra P-Code: semantics and verified lifting (Naus, Verbeek, Walker, Atla, Ravindran) ✔

- **A Formal Semantics for P-Code (VSTTE 2022).** P-Code had no formal semantics and limited
  documentation. The authors *extend* P-Code (arguing it cannot be given an executable
  semantics as it stands) and define a complete, executable semantics, validated by an
  interpreter. Building it **uncovered several issues in Ghidra, P-Code and its
  documentation**.
- **Formally Verified Binary Lifting to P-Code (CCS 2024 poster).** Proves automatically in
  Isabelle that each x86-64 instruction and its P-Code lifting are equivalent, against
  **machine-learned x86-64 semantics** chosen to be close to CPU behaviour. It found
  shortcomings in Ghidra's lifting. A prototype; no coverage numbers.
- **Borrow:** a warning that an IR without a formal semantics cannot be an ISA-independent
  layer. Layer 0.5's `Op.lean` should stay *defined*, not documented. It also suggests that
  learned or fuzzed semantics are being used as an oracle, which is related to Kraken's
  SDE fuzzing.

Links: <https://research.ou.nl/en/publications/a-formal-semantics-forp-code/>,
<https://research.ou.nl/en/publications/poster-formally-verified-binary-lifting-to-p-code/>

### 5.5 Unverified lifters and disassemblers ○

These are useful as *untrusted oracles* (for CFG recovery, indirect-jump candidate lists and
symbolisation) whose output is then checked in Lean:

- **ddisasm** (GrammaTech; Datalog-based disassembly and reassembly, USENIX Security 2020): good
  CFG and symbolisation.
- **McSema / Remill** (Trail of Bits): lifting to LLVM IR. Remill is the per-instruction
  semantics library underneath McSema, and the subject of §5.3.
- **angr** (UCSB; S&P 2016) and **BAP/BIL** (CMU; CAV 2011): binary analysis platforms with
  their own IRs (VEX, BIL).
- **Borrow:** candidate lists for `Ligoto` (roadmap step 1) and indirect calls (`CfiOk`) can
  come from any of these, provided Lean checks the premise.

---

## 6. Instruction-set models and how they are validated

Every result in MachineChecked is only as good as layer 0. This section is about **how existing
models earned trust**, which is what the trust ladder in `docs/ELF.md` §4 has to argue.

### 6.1 Sail (Armstrong et al.; POPL 2019) ✔

- Sail models of ARMv8-A, RISC-V, MIPS and CHERI-MIPS are complete enough to **boot operating
  systems**: Linux on ARMv8-A, FreeBSD on (CHERI-)MIPS, seL4 and Linux on RISC-V. The ARMv8-A
  model was about 23k lines in 2019 (113k non-whitespace for Armv8.5-A by Islaris's count).
- ARMv8-A is translated **automatically** from Arm's authoritative ASL (`asl_to_sail`), and one
  variant is tested against Arm's Architecture Validation Suite. Sail RISC-V is hand-written and
  is RISC-V International's official formal spec.
- From one source Sail generates C and OCaml emulators and prover definitions. In 2019 these
  were Isabelle and HOL4 (Coq for MIPS only). A **Lean backend now exists** (used by zisk-fv,
  sp1-lean and Jolt-QED, §4.3) but is not in the 2019 paper.
- Effects are translated through two monads: a **state monad** for sequential semantics, and a
  **free-monad-style effect datatype** (`Read_mem`, `Write_reg`, `Barrier`, …) for concurrent
  and relaxed-memory semantics.
- **Borrow:** the two-monad split is a clean answer to "how does a syscall or MMIO step look at
  layer 0": an effect left open and interpreted by the context (layer -1). It also matters if
  concurrency ever comes into scope.

Links: <https://www.cl.cam.ac.uk/~pes20/sail/sail-popl2019.pdf>,
<https://www.cl.cam.ac.uk/~pes20/sail/popl2019.html>; tutorial:
<https://fm.csl.sri.com/SSFT19/sail-riscv-cheri-ssft-2019-slides.pdf>; REMS overview:
<https://www.cl.cam.ac.uk/~pes20/rems/index_task2.html>

### 6.2 Arm ASL and the Machine Readable Architecture (Reid; FMCAD 2016) ✔

- A 5-year project changed Arm's process so that executable ASL specifications are generated
  from the same sources as the documentation. They cover v8-A and v8-M, including system-level
  semantics (protection and exceptions).
- Trust came from testing against Arm's internal conformance suites, simulators and silicon
  (v8-A: about 11k test programs, over 2 billion instructions), and that testing **found bugs in
  all of those artifacts, the specification included**. The specs were also used to verify Arm
  processors by bounded model checking (ISA-Formal, CAV 2016). A follow-up, *Who guards the
  guards?* (OOPSLA 2017), validates the specification formally.
- **Borrow:** ASL is the root of trust for arm64-semantics (written from ASL, tested against
  Sail-arm). Reid's point that *the specification had bugs too* argues for keeping
  differential testing in CI, not running it once.

Links: <https://alastairreid.github.io/papers/FMCAD_16>; ASLi: <https://alastairreid.github.io/using-asli>

### 6.3 ACL2 x86isa (Goel, Hunt, Kaufmann, Ghosh; FMCAD 2014) ✔

- An executable, interpreter-style operational semantics for x86-64: a semantic function per
  instruction, a fetch-decode-execute `step` and an `n`-step `run`. In 2014 it covered 121
  user-level instructions (223 opcodes), all addressing modes, IA-32e paging and FS/GS
  segmentation, in about 40k lines of ACL2. It is still maintained (2025 ACL2 Workshop update),
  and the Sail x86 fragment was translated from it.
- **Validation by co-simulation against silicon** (GDB, Intel Pin). For example, a SAT solver
  ran 9,142,833,444 instructions on the model with exactly the same effects on registers and
  memory as the real machine. Simulation speed: about 3.3M instructions/s (programmer level).
- **System calls, two modes:** in *logical* mode the state carries an `env` field (a file-system
  abstraction plus an oracle) for reasoning. In *execution* mode, raw Lisp calls the host OS.
  A correspondence property ties the two, and only syscalls differ between them. Modelled:
  read, write, open, close, lseek, dup, link, unlink.
- **Case study:** a GCC-compiled word-count program (50 instructions, 166 bytes) that makes
  system calls, proved correct. The authors describe this as a first.
- **Borrow:** the two-mode syscall design maps directly onto the layer -1 context parameter. An
  SP1 or leanVM context could give syscalls a *logical* oracle semantics for proofs and an
  *executable* one for testing ELFs, with a stated correspondence. Co-simulation against real
  execution (here: SP1's executor) is the cheap way to raise trust in the loader and context.

Links: <https://www.cs.utexas.edu/~hunt/FMCAD/FMCAD14/proceedings/18_goel.pdf>;
2025 update: <https://www.cs.utexas.edu/~moore/acl2/workshop-2025/slides/x86-model-updates-workshop-2025.pdf>

### 6.4 K-x86 (Dasgupta, Park, Kasampalis, Adve, Roşu; PLDI 2019) ○

- An executable K semantics of every non-deprecated sequential user-level Haswell instruction:
  3,155 variants across 774 mnemonics. Tested on more than 7,000 instruction tests and the GCC
  torture suite, it found bugs in the Intel manual and in other semantics, and it can be
  exported as SMT theories. It builds on Heule et al.'s stratified synthesis. (The search
  result reported these details, but the primary page could not be fetched, so they are
  unchecked.)
- **Borrow:** a coverage yardstick and a differential-testing oracle for Kraken.

Links: <https://fsl.cs.illinois.edu/publications/dasgupta-park-kasampalis-adve-rosu-2019-pldi.html>,
<https://github.com/kframework/X86-64-semantics>, arXiv [1903.06407](https://arxiv.org/abs/1903.06407)

### 6.5 Other models ○

- **CompCert's Asm** (Coq): the target semantics of a verified compiler. Assembly and linking
  are outside CompCert's proof, which is a familiar version of Kraken's trusted-assembler gap.
- **L3 models** (Fox; HOL4): the ARM, x86 and RISC-V models under CakeML and Myreen's work.
- **riscv-coq** (MIT): the RISC-V model under Bedrock2.

---

## 7. Verified assembly, cryptography and verified compilers ○

All of these are background, apart from s2n-bignum (§3.2–3.3). They matter because
MachineChecked's targets (CatCrypt kernels, s2n-bignum-style routines, hashes) are their home
ground.

| system | approach | relation to MachineChecked |
| --- | --- | --- |
| **Jasmin** (Coq; CCS 2017 onward) | a low-level crypto language with a verified compiler to assembly, constant-time preservation results, EasyCrypt for specifications | layer 0.5 *is* linear Jasmin (`ROADMAP.md`); CatCrypt is ported from its ecosystem (`docs/notes/CATCRYPT-PORT.md`) |
| **Vale** (Dafny / F*; USENIX Security 2017) | verified assembly with a hand-written x86/ARM semantics, printed to assembler text | assembly-level like Kraken; the printer and assembler are trusted |
| **CryptoLine** | algebraic and bit-vector verification of low-level crypto code (field arithmetic) | the kind of decision procedure for carry chains (`feMul121666`) that `bv_decide` plus ring normalisation would need |
| **Fiat Cryptography** (Coq; S&P 2019) | generates field arithmetic by verified synthesis | its specifications and templates are reference specifications for layer 2 |
| **SLOTHY** | constraint-solver instruction scheduling of crypto kernels | produces optimised code that then needs an equivalence proof (§3.3) |

---

## 8. AI-assisted machine-code proof

### 8.1 s2n-bignum-bench (Rao, Harrison, Kong, Lee, Lipizzi; 2026) ✔

- About 2,300 HOL Light proof obligations taken from s2n-bignum's machine-code proofs. The model
  is given a formal specification and must produce a proof script that HOL Light accepts
  within a timeout. The authors call it the first public benchmark of its kind.
- The search summary reported frontier LLMs solving at most 6.35% zero-shot. That figure was
  not re-checked against the paper.
- The arXiv page lists it as an **AIPV 2026 workshop paper**; the search result's "NeurIPS
  2026" was wrong.
- **Borrow:** the obligations MachineChecked generates (per-instruction lemmas, contract-table
  entries, loop invariants at Lprog) are a natural Lean benchmark of the same kind, and a
  natural place to point proof agents.

Link: <https://arxiv.org/abs/2603.14628>

### 8.2 Anthropic and Theorem: crash-freedom of RISC-V binaries in Rocq (2026) ✔ (secondary source)

- Reported: Claude was used to prove crash-freedom at the RISC-V assembly level for **239 entry
  points across 123 OSS-Fuzz libraries**, about **180M lines of Rocq** in total (about 600k per
  binary), limited to **single-threaded static RISC-V binaries linked against musl**. The
  safety notion is ASan-based and weaker than full correctness ("'Formally verified' does not
  mean 'bug-free'"). Real bugs were found, including an out-of-bounds write in a decompressor.
- **Caveat:** this comes from a news summary (aiweekly.co). Read the primary post
  (anthropic.com/research/formal-verification) before citing figures.
- **Borrow:** it is the same shape as MachineChecked (a static RISC-V ELF, a machine model, a
  whole-binary theorem) and shows that machine-generated proofs at that scale are now
  practical. The proof sizes also argue for keeping per-function obligations small and
  independent (§5.1).

Link: <https://aiweekly.co/alerts/anthropic-theorem-use-claude-to-verify-123-oss-libraries>;
related practitioner account: <https://blog.zksecurity.xyz/posts/end-coding> (not checked)

---

## 9. Lessons for MachineChecked, layer by layer

| layer / roadmap item | lesson | from |
| --- | --- | --- |
| **-1 ELF and context** | Every system leaves loading trusted, or assumes the initial layout (seL4 TV states this outright). Making the loader checked rather than trusted is new ground, so say so in the trust ladder. | §2.2, §2.3 |
| -1 syscalls | Use a logical oracle semantics for proofs and an executable semantics for testing, with a stated correspondence (ACL2 x86isa). For effects at layer 0, use an open effect datatype interpreted by the context (Sail's second monad). | §6.3, §6.1 |
| **0 ISA** | Trust is earned by *ongoing* differential testing against hardware, executors or other specs, and that testing finds bugs in the specs too. Keep provenance pinned and regenerable (zisk-fv, evm.asm). | §6.2, §6.3, §4.3 |
| 0 proof cost | Full authoritative models are expensive to unfold. Precompute configuration-specialised, simplified per-instruction lemmas (Islaris traces, done in-kernel). Measure this early for arm64-semantics and Kraken. | §3.1 |
| **lift 1 (0 → 0.5)** | Per-instruction granularity is the consensus (Islaris, VT, Dasgupta, Jolt-QED). Independent obligations parallelise. A shared Sail-RV64 per-instruction lemma library is worth upstreaming. | §3.1, §5.1, §5.3, §4.3 |
| lift 1, indirect jumps | Get candidate lists from untrusted tools (ddisasm, Ghidra) and check them. Make return-address integrity and bounded control flow explicit preconditions (VT). | §5.1, §5.5 |
| **0.5 shared IR** | An IR without a formal semantics is a liability (P-Code). FoxDec 3.0 is the nearest analogue; MachineChecked's in-Lean simulation is the stronger form. | §5.2, §5.4 |
| **lift 2 (0.5 → 1)** | Myreen-style decompilation into ordinary Lean functions with a correspondence theorem. Treat the stack as a separate object. Split-point (loop-head) discovery is where optimised code breaks, so allow hints. | §2.1, §2.3 |
| **1 program logics** | Include a conjunction rule. A relational logic covers constant time and equivalence. Bedrock2 and Pancake are the design references. | §3.3, §2.4, §4.5 |
| **2 refinement** | Generate, decompile, prove equal (CC 2009). Prove optimised code equivalent to a simple version, then verify the simple one (relational logic). Fiat, Jasmin/EasyCrypt and hash-specs supply specifications. | §2.2, §3.3, §7 |
| **x86-64 assembler gap** | Close it by reading the bytes back and proving them against the assembly (decompile-with-proof or binary TV), as every byte-level system does. | §4.4, §5.2 |
| **targets** | s2n-bignum routines (and the Bignum-Lean port) are the obvious shared targets for AArch64 and x86-64. | §3.2, §4.2 |
| **proof automation / AI** | Obligation corpora are becoming benchmarks, and machine-generated whole-binary proofs are now practical. Keep obligations small and uniform so agents can discharge them. | §8 |

---

## 10. Open questions this survey raises

1. **Unfolding cost in Lean.** How far do arm64-semantics and Kraken suffer the model-size
   problem Islaris reported for Sail-generated Coq Armv8-A? Do Lean's `decide`, `bv_decide` and
   compiled evaluation make full-model unfolding practical without SMT-style pruning?
2. **Sharing with the zkVM projects.** Can per-instruction Sail-equivalence lemmas and the
   lean-sail runtime be shared with sp1-lean, zisk-fv and Jolt-QED? What toolchain or fork
   alignment would it take (sp1-lean is on v4.28 with a Succinct fork; MachineChecked depends on
   riscv-zkvm, not on sail-riscv-lean directly)?
3. **Shape of lift 2.** Hoare-graph-style independent per-instruction obligations (VT;
   parallel, but with flat structure), or Myreen-style whole-function decompiled terms with one
   correspondence theorem (more structure, but harder with loops and indirect jumps)? Probably
   the first for lift 1 and the second for lift 2, which is the current split.
4. **Trusted loading.** No surveyed system verifies ELF-to-memory-image loading. Is there prior
   work this pass missed (for example in the CakeML or seL4 build chains)?
5. **Constant time.** Does layer 0.5 need a leakage trace now, so that a relational logic
   (§3.3) can sit at layer 1 later without redoing lift 1?

---

## 11. Gaps in this survey

The adversarial check covered only part of what was asked for. These topics are in the document
as ○ background, or not at all, and would repay a focused follow-up:

- CakeML and Silver in detail; Pancake's intermediate languages.
- ASL-to-Sail tooling; ISA-Formal; *Who guards the guards?*
- seL4's later binary-verification work (Sewell's thesis, the RV64 port) and Tuch–Klein–Norrish
  memory models for C (POPL 2007).
- K-x86's primary paper (the fetch failed), CompCert Asm, Bedrock2 and riscv-coq.
- ddisasm, Remill, angr, BAP in any depth.
- Lean MLIR, Aeneas and Kraken (beyond `docs/ISA.md`), DeepMind's arm64-semantics (beyond
  `docs/ISA.md`), RISC Zero, OpenVM, ArkLib, zkLean.
- Vale, Jasmin, CryptoLine and Fiat (only summarised in §7).
- Prior work on verified or checked ELF loaders.

Dates: the Islaris and VT figures are from 2022; the zkVM projects are from late 2026 and change
quickly. The "first" priority claims (Islaris, Dasgupta et al., ACL2 x86isa, s2n-bignum-bench)
are the authors' own claims at the time of publication.

---

## 12. Bibliography

Primary sources checked in this pass:

- M. O. Myreen et al. *Decompilation into Logic.* Project page.
  <https://www.cl.cam.ac.uk/~mom22/decompilation>
- M. O. Myreen, K. Slind, M. J. C. Gordon. *Extensible proof-producing compilation.* CC 2009.
  DOI 10.1007/978-3-642-00722-4_2. <https://www.cl.cam.ac.uk/~mom22/extensible-compilation.pdf>
- T. Sewell, M. O. Myreen, G. Klein. *Translation Validation for a Verified OS Kernel.* PLDI
  2013. <https://www.cl.cam.ac.uk/~mom22/pldi13.pdf>
- M. Sammler, A. Hammond, R. Lepigre, B. Campbell, J. Pichon-Pharabod, D. Dreyer, D. Garg,
  P. Sewell. *Islaris: Verification of Machine Code Against Authoritative ISA Semantics.* PLDI
  2022. DOI 10.1145/3519939.3523434. <https://pub.ista.ac.at/~msammler/paper/islaris.pdf>
- F. Verbeek, J. Bockenek, Z. Fu, B. Ravindran. *Formally Verified Lifting of C-compiled x86-64
  Binaries.* PLDI 2022. DOI 10.1145/3519939.3523702.
  <https://www.ssrg.ece.vt.edu/papers/pldi22.pdf>
- Virginia Tech SSRG. *FoxDec.* <https://github.com/ssrg-vt/FoxDec>
- S. Dasgupta, S. Dinesh, D. Venkatesh, V. Adve, C. Fletcher. *Scalable Validation of Binary
  Lifters.* PLDI 2020.
  <https://pldi20.sigplan.org/details/pldi-2020-papers/4/Scalable-Validation-of-Binary-Lifters>
- N. Naus, F. Verbeek, D. Walker, B. Ravindran. *A Formal Semantics for P-Code.* VSTTE 2022.
  <https://research.ou.nl/en/publications/a-formal-semantics-forp-code/>
- N. Naus, F. Verbeek, S. Atla, B. Ravindran. *Poster: Formally Verified Binary Lifting to
  P-Code.* CCS 2024. DOI 10.1145/3658644.3691386.
  <https://research.ou.nl/en/publications/poster-formally-verified-binary-lifting-to-p-code/>
- A. Armstrong et al. *ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS.* POPL 2019.
  <https://www.cl.cam.ac.uk/~pes20/sail/sail-popl2019.pdf>
- A. Reid. *Trustworthy Specifications of ARM v8-A and v8-M System Level Architecture.* FMCAD
  2016. <https://alastairreid.github.io/papers/FMCAD_16>
- S. Goel, W. A. Hunt Jr., M. Kaufmann, S. Ghosh. *Simulation and Formal Verification of x86
  Machine-Code Programs that make System Calls.* FMCAD 2014.
  <https://www.cs.utexas.edu/~hunt/FMCAD/FMCAD14/proceedings/18_goel.pdf>
- AWS. *s2n-bignum.* <https://github.com/awslabs/s2n-bignum>
- D. Mazzucato, A. Mohamed, J. Lee, C. Barrett, J. Grundy, J. Harrison, C. Pasareanu.
  *Relational Hoare Logic for Realistically Modelled Machine Code.* CAV 2025. arXiv 2505.14348.
  <https://assets.amazon.science/56/20/f6b40ee84e7b8633ca1053499aff/relational-hoare-logic.pdf>
- B. Rao, J. Harrison, S. Kong, J. Lee, C. Lipizzi. *s2n-bignum-bench.* AIPV 2026. arXiv
  2603.14628. <https://arxiv.org/abs/2603.14628>
- *Bignum-Lean.* <https://reservoir.lean-lang.org/@arademaker/bignum>
- *LNSym.* <https://github.com/leanprover/LNSym>
- Succinct. *sp1-clean-native / sp1-lean.* <https://reservoir.lean-lang.org/@succinctlabs/sp1-clean-native>
- eth-act. *zisk-fv.* <https://awesome.ecosyste.ms/projects/github.com%2Feth-act%2Fzisk-fv>
- Biswas, Dao, Ross, Thaler. *Jolt-QED: Formally Verifying Bytecode Expansions in Lean.* IACR
  ePrint 2026/2157. <https://eprint.iacr.org/2026/2157>

Secondary or search-level only (not fetched and checked):

- *Anthropic and Theorem use Claude to verify 123 OSS libraries* (news summary).
  <https://aiweekly.co/alerts/anthropic-theorem-use-claude-to-verify-123-oss-libraries>
- risc0-lean4 <https://reservoir.lean-lang.org/@risc0/risc0-lean4>; evm.asm
  <https://reservoir.lean-lang.org/@Verified-zkEVM/EvmAsm>
- K-x86 <https://github.com/kframework/X86-64-semantics>; S. Dasgupta's PhD thesis (UIUC)
- FMCAD 2012 *Decompilation into Logic — Improved*
  <https://www.cs.utexas.edu/~hunt/FMCAD/FMCAD12/016.pdf>; TACAS 2020
  <https://www.ssrg.ece.vt.edu/papers/tacas20.pdf>; CCS 2024 symbolisation
  <https://vtechworks.lib.vt.edu/items/ac0811bd-d8cb-4662-b466-ec55ab79f2dd>
- Sewell's PhD thesis <https://trustworthy.systems/publications/papers/Sewell:phd.pdf>
- ACL2 x86 model 2025 update
  <https://www.cs.utexas.edu/~moore/acl2/workshop-2025/slides/x86-model-updates-workshop-2025.pdf>
