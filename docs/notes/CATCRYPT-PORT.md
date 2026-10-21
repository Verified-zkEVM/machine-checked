> **Status (2026-10-21): archived; largely done.** The port it describes landed: Lprog is the logical machine, its operations are shared (`MachineChecked/Lprog/Op.lean`), the correspondence is `MachineChecked/Ascent`, and the CatCrypt kernels are proved through the lift. References below to `docs/PLAN.md`, `RiscV/Corres`, `CorresIsa` and the small x86 model describe the state when it was written. What remains is in [`ROADMAP.md`](../../ROADMAP.md).

# CatCrypt port: taking what we need from catcrypt-compiler

A roadmap, 2026-10-19, revised 2026-10-20. **The port is the next work in `docs/PLAN.md`
and has the highest priority.** This document sets out what catcrypt-compiler has, what
MachineChecked takes from it, and the order of work.

**The arrangement.** We port, we do not depend. spitters has said to take what we need
from catcrypt-compiler. Code we take is copied into this repository and becomes ours, to be
changed and improved freely until it fits MachineChecked. We do not `require`
catcrypt-compiler, or the *CatCrypt Machine* package its draft README proposes, and nothing
here waits on upstream changes. Whatever we improve can be offered back, but the port never
depends on that.

**Decisions (2026-10-20).**
1. **Lprog is our logical machine**, to be iterated on. The typed-variable
   `LogicalProgram` of `docs/LogicalMachine.md` is a possible later refinement, not a
   prerequisite.
2. **Mathlib may be imported**, by the framework as well as by the case studies.
3. **ISA models may be trusted for the initial port**, provided each is named on the trust
   ladder. Every ISA model is to be formally verified against its canonical spec in the end.
   Where a verified model exists we use it: riscv-zkvm for RISC-V.
4. **CatCrypt's `CorresIsa` is our ascent.** `riscv-decomp` is dropped. We do not take it as
   a dependency.
5. **Simplest wins.** Where catcrypt-compiler's version of something is better than ours, we
   overwrite ours. Nothing here is kept for its own sake.
6. **Toolchain: the newest Lean we can reach** (§3, P1). Versions are not a blocker.
7. **riscv-zkvm is the one RV64 backend**, and `stepSp1` is the one step function (§3, P2).

Sources read:
- catcrypt-compiler at `master` `69ffea9f` (local checkout `../catcrypt-compiler`).
- The draft README *CatCrypt Machine* (2026-10-19), for what its authors consider the
  reusable machine layer.
- riscv-zkvm at our pin `4634e41b`, and its branches and tags as of 2026-10-20.
- Our `README.md`, `docs/PLAN.md`, `docs/ELF.md`, `docs/LogicalMachine.md`, `docs/ISA.md`,
  `docs/QUESTIONS.md` and `docs/TO-VERIFY.md`.

## 1. What catcrypt-compiler has

catcrypt-compiler is a verified compiler (hax/Rust → LowCT → SSA → Jasmin dialect → Lprog →
x86-64 / AArch64 / RV64 bytes) together with an *ascent* route for code it did not emit
(s2n-bignum `bignum_montmul_p384`, the Ed25519 blocks, CryptOpt). It is about 1.3M lines,
on Lean v4.33.1 with Mathlib, and requires catcryptCore, Veir, ParamTransfer, CompPoly and
hax-lean. Its Ascent descends from Sebastian Graf's
[sgraf812/ascent](https://github.com/sgraf812/ascent) (`PROVENANCE.md`, `ASCENT.md`), the
Ascent that `README.md` wants to stay compatible with. The machine layer:

| Level | What it is | Key names |
| --- | --- | --- |
| Lprog | A mirror of Jasmin's `linear.v`: labelled linear instructions (`Lopn`, `Lcall`, `Lret`, `Lgoto`, `Lcond`, `Ligoto`, `Lsyscall`). Registers and opcodes are `String`s; memory is named arrays (`String → Int → BitVec 64`); there are flags `zf`/`cf` | `VIR/JasminLprogExport/Types`, `VIR/LprogIsa` (`Isa`, `lsemFuelMemF`) |
| Address machine | Lprog bodies over byte addresses, deterministic | `runA`, `image_addr_simBW` |
| Bytes | Encoder and decoder with round trips | `encodeLfundefBytes`, `decodeLprog_encodeLfundefBytes` |
| Decoded machine | `IsaMachine`: `exec`, `decode`, `act`, leakage. The **pc is an index into a `List Instr`** | `VIR/IsaMachine` (`Halts`, `RunL`), `VIR/IsaAsmSim` |
| Separation logic | `SAssert`, total deterministic `Triple`, the frame rule, `ContractSpec`/`SContract`, System V ABI, `LinkedFn.contract` | `SepLogic/*` |
| Ascent | `CorresM` / `CorresIsa` (fuelled, total), Floyd labels, procedure specs, `corres_sym_rv`, `isa_cutpoints` | `HaxAscent/Ascent/*`, `HaxAscent/` |
| TV, CT | `ownedCheckM` translation validation; `bytesCTCheck` leakage under DOITM, DIT or Zkt | `X86Backend/OwnedLprogTV*`, `CT/*` |

(The `VIR/*` modules are under `CatCrypt/Crypto/SecureCompilation/`.)

Per ISA:
- **x86-64** is the most complete: about 50 instruction forms. The model is transcribed
  from Jasmin's Rocq semantics and proved equal to Sail-x86 bodies for the core ALU only.
- **RV64** on `master` is small: `add sub sltu and or xor mul mulhu li mv slli srli`,
  `ld sd addi bne`. It is proved equal to a *hand-pasted excerpt* of sail-riscv-lean
  (`9eba3f07`), and that excerpt is trusted.
- **AArch64** is a hand-written model and is trusted.

An unmerged RV64 stack sits in the local checkout, on the `dhsorens/catcrypt-compiler`
remote: `rv64-g1-fieldmul` through `rv64-g5-x25519`, 13 commits, about 9.9k lines, from
2026-10-01. It adds:
- `Memory64`, a byte memory shared with the x86 address machine;
- `RiscvMem64` and `RiscvPc64`, which run from a byte program counter with `bne`, `jal`
  and `jalr`;
- `SailRiscvPc64Refinement`, the `ld sd bne jal jalr` Sail clauses;
- the X25519 ladder at bytes.

Its machine (`Memory64`, `RiscvMem64`, `RiscvPc64`, the Sail refinement) is not taken:
riscv-zkvm's `MachineState` already has a byte PC, byte memory and `jal`/`jalr` (§3, P2). Its
proofs, the X25519 ladder above all, are worth porting onto riscv-zkvm.

## 2. How the two fit

| MachineChecked today | catcrypt-compiler | Verdict |
| --- | --- | --- |
| riscv-zkvm `MachineState` / `stepSp1`: full RV64IM + SP1 ecalls, 51 Sail-equivalence instructions, the generated Sail tree pinned | `RiscvModel64`: 16 instructions, a transcribed Sail excerpt | **riscv-zkvm is the one RV64 backend.** Ported RV64 proofs are rewritten against it. `RiscvModel64`, the Sail excerpt and the `rv64-g*` machine are not taken (AGENTS.md: no second machine semantics) |
| x86, ARM: READMEs only; `docs/ISA.md` leaves the canonical spec open | x86 (Sail-tied for the ALU only), AArch64 (trusted) | **Take them** as the initial x86/ARM bottoms, trusted and named on the trust ladder. Each is to be verified against its canonical spec later (§3, P6) |
| `SafeN G n P` / `Iface.HoldsN`: partial, step-indexed, over accepting states, with a control-flow guard `G`; recursion and CFI | `CorresIsa` / `Triple` / `ContractSpec`: total, fuelled, deterministic | Complementary. A total correspondence implies our continuation spec for code without halts (§3, P3). `SafeN` stays the judgement of the top theorem |
| Frame checker, footprints, contract table, `Carry` | `SAssert` footprints, `Triple.frame`, `LinkedFn.contract`, `abiPre` | A contract is a table entry, whichever tool proved it. Where CatCrypt's separation logic states or proves an entry more simply, it replaces ours |
| `Sym` executor (works on about 300 rustc functions) | `corres_sym_rv`, `RvSym`, `isa_cutpoints` (works on kernels) | `CorresIsa` is the ascent for new proofs. Existing `Sym` proofs are replaced where `CorresIsa` is simpler, and kept where they already work and nothing simpler exists |
| ELF loader, `gen-image`, hints (trust-ladder rung 2) | Encodes its own output; decodes bytes it printed | Ours. CatCrypt has no rustc-ELF story |
| Trust-ladder rung 5 (translation validation against the source) is not started | hax front, `haxToLowCT`, a differential oracle, `CERTIFYING_THIRD_PARTY_CODE.md` | **Take it** as the source of specs (§3, P5) |
| — | Leakage and CT | Not needed for zkVM soundness; useful for native x86/ARM targets |

Not taken: `riscv-decomp` (decision 4), and riscv-zkvm's own program logic
`RiscvZkvm.Rv64.Logic`. We import riscv-zkvm's machine (`Rv64`, `Interpreter`), not its
logic.

**Lprog as the logical machine.** Lprog replaces addresses with labels, has explicit
`Lcall`/`Lret`/`Lcond`/`Ligoto`, runs one body on three ISAs through `Isa`, and is the form
CatCrypt's translation validation and descent already speak. It sits after register
allocation, so it is lower than the typed-variable `LogicalProgram` sketched in
`docs/LogicalMachine.md`. That is acceptable: we start from Lprog and iterate. Three gaps
have to be closed for decompiled rustc output, and since the code is ours, we close them in
place:

1. **Memory.** Lprog's operands are named arrays (`base[idx]`, `String → Int → BitVec 64`).
   Rust guests do pointer arithmetic over flat memory: heap blocks, `a0 + k`, statics at
   constant addresses. We add a flat operand, e.g. `mem (base : String) (off : Int) (width)`
   evaluated against riscv-zkvm's byte memory.
2. **Flags.** `zf`/`cf` are x86-shaped. We make the flag and arithmetic step a parameter of
   `Isa`, which the draft README also plans. RV64 has no flags.
3. **Direction.** CatCrypt's arrows are forward simulations (an Lprog run is matched by a
   machine run). That is the descent direction. For third-party bytes we need either the
   backward direction or determinism plus Lprog progress, to get *every* machine run. SP1's
   step is deterministic given the input stream, so the second option is available.

The stack:

```
Lean spec (Zip2005.GuestStatement, hax reference `denote'`)
        ▲  CorresIsa / CorresM, separation logic      (ported Ascent)
Lprog over flat memory (labels, Lcall/Lret)            ← the logical machine
        ▲  lift: address → label, jal/jalr → Lcall/Lret, proved by simulation
riscv-zkvm stepSp1 on the loaded image
        ▲  ELF load, hints checked
ELF
```

## 3. Plan

The phases are numbered P1–P6 so they do not collide with `docs/PLAN.md`'s A–F. Each ends in
a stated theorem with `#print axioms` clean under our rules. Ported code goes under
`MachineChecked/` (ISA-independent at the top level, RISC-V under `MachineChecked/RiscV`).

**P1. Intake and toolchain.**
- Take files, not the package. Each ported file passes the gates before it lands: no
  `sorry`, no `axiom`, no `native_decide`, zero warnings. 623 catcrypt-compiler files use
  `native_decide`, so the last gate filters what we can take, or means reproving.
- Mathlib is allowed (decision 2). Add it to `MachineChecked`'s imports where ported code
  needs it.
- A `Tools/AxiomGate` check over every ported theorem and every bridge theorem.
- Record provenance: the catcrypt-compiler commit each file came from, and that it has since
  diverged. A short `PROVENANCE` note per ported directory is enough. Check catcrypt-compiler's
  `LICENSE` and `THIRD_PARTY_NOTICES.md` for what that note must carry.
- First candidates: `LprogIsa`, `IsaMachine`, `IsaAsmSim`, `IsaBackend`, `PassChain`,
  `JasminLsemAddrRun`, `CorresIsa`, `CorresHoare`, `CorresSymEngine`, `ContractOfCorres`,
  `SepLogic/*`, `RvIsa`, `RvMach`, `RvSym`. These have no `native_decide` in-file
  (spot-checked); their closure is unchecked. `SailRiscvDecoder64` is not taken, since
  riscv-zkvm's decoder is the one decoder.
- **Toolchain.** Aim for the newest Lean the dependencies allow. As of 2026-10-20:
  - We are on v4.33.0, Lean's latest stable is v4.35.0, and Mathlib `master` is on
    v4.36.0-rc1.
  - riscv-zkvm is what binds us. Our pin `4634e41b` is on its `sp1-backend` branch, which is
    on v4.33.0 and is the only place `stepSp1` exists. Its `main` and release `v0.4.0` are
    on v4.33.1 but have no SP1 backend. riscv-zkvm's toolchain follows evm-asm's, so it
    will not race ahead.
  - So: v4.33.1 is reachable as soon as the SP1 backend sits on a riscv-zkvm revision at
    v4.33.1, whether by a merge to `main` or a rebased branch. We re-pin to that revision,
    unmodified. Going past v4.33.1 waits on riscv-zkvm.
  - Ported code moves to whatever toolchain we are on. catcrypt-compiler's v4.33.1 does not
    constrain us.

**P2. One RV64 backend: riscv-zkvm.** Every ported RV64 proof is rewritten against
riscv-zkvm. A good reason would be needed to deviate from this, and none is known.
riscv-zkvm stays unmodified at its pin (`docs/PLAN.md` Rules).
1. Generalise the ported `IsaMachine` (or add a sibling) to a byte program counter and a code
   map, the shape of riscv-zkvm's `MachineState`, where `pc : Word` and
   `code : Word → Option Instr`.
2. Define the RV64 instance `zkvmMach` on riscv-zkvm: `MState := MachineState`, decoder
   riscv-zkvm's `decode`, and **step `stepSp1` itself**, for guests and kernels alike. There
   is no second "ecall-free" step. That a kernel body contains no `ECALL` is a fact about its
   code, checked over the image by `decide`. Under it, `stepSp1` at every fetch in the body
   reduces by unfolding to its non-`ECALL` branch: `execInstrBr` behind `memOkSp1`
   (`Rv64/StepOn.lean`). If a separate step ever earns its place, it is defined here and
   proved equal to `stepSp1`, never upstreamed: riscv-zkvm's surface is evm-asm's public API
   (its README, "Downstream compatibility").
3. Port CatCrypt's RV64 proofs onto `zkvmMach`: `RvIsa`, `RvMach`, `RvSym`,
   `corres_sym_rv`, the field-multiplication kernels, and the X25519 ladder from
   `rv64-g5`.
4. `RiscvModel64`, the hand-pasted sail-riscv-lean excerpt and `SailRiscvPc64Refinement` are
   not ported. While a proof is being moved, a per-instruction equality between CatCrypt's
   `RvInstr` and riscv-zkvm's `Instr` may serve as local scaffolding. It is deleted once
   nothing uses it, and no final theorem depends on it.
- *Exit:* a ported RV64 correctness theorem (e.g. `feMul_correct` at bytes) is a statement
  about `stepSp1` runs, and the repository has no other RV64 semantics.

**P3. The bridge judgement.**
- `Iface.of_corres`: from a `CorresIsa` (or `ContractSpec`) on `zkvmMach` for a body that
  has no `ECALL`, together with a footprint and the callee-saved facts, derive our
  continuation spec, for every guard `G`:

      ∀ P n s, s.pc = entry → pre s → (∀ t, post s t → SafeN G n P t) → SafeN G n P s

  Total-to-partial is the easy direction, using determinism and the absence of an accepting
  halt inside the body. The footprint maps to `Unchanged`, and callee-saved registers map to
  `CalleeSaved`. A body with an indirect jump also needs its candidate list, and the guard
  has to imply `Env.Cfi` at that site, as in `docs/PLAN.md` B3.
- *Exit:* one zip-2005 leaf, such as a Blake2b compression or a Pallas field
  multiplication, is proved with `CorresIsa` and enters the contract table in place of its
  `Sym` proof. Comparing the two settles where `Sym` is replaced (decision 5).

**P4. Lprog as the logical machine.**
1. Add a flat-memory operand to the ported Lprog, and make flags a parameter of `Isa`.
2. A lifter from a decoded function in our image (the frame checker's CFG and call-site
   resolution already exist) to an Lprog body. The lift is proved by simulation: determinism
   plus Lprog progress gives every machine run. Indirect jumps become `Ligoto` with our
   candidate lists; `CfiOk` carries over.
3. Function specs are stated once at Lprog. `CorresIsa` proves them, and P3 carries them
   down.
- *Exit:* one non-leaf zip-2005 function with a loop is specified and proved at Lprog and
  discharged into the table.

**P5. Descent meets ascent.**
- A CatCrypt-compiled RV64 kernel linked into an SP1 guest. Its `haxc_contract` /
  `LinkedFn.contract`, restated over `stepSp1`, becomes a table entry through P3, with no
  ascent proof for that function at all. This needs the compiler's RV64 correctness
  theorems ported onto riscv-zkvm as in P2.
- hax extraction of guest functions as the spec source: trust-ladder rung 5 (`docs/ELF.md`
  §4). Run the differential oracle before proving, and prove against `denote'`.

**P6. Other ISAs.** Port CatCrypt's x86-64 and AArch64 models as the bottoms behind
`MachineChecked/X86` and `MachineChecked/ARM`, and generalise `Tools/Elf` and `gen-image`
per ISA.
- Both are trusted for now, and named as such on the trust ladder (`docs/ELF.md` §4, TCB
  item 1): x86-64 is Sail-tied for the core ALU only, and AArch64 is hand-written.
- Each is to be formally verified against its canonical spec (`docs/ISA.md`), the way
  riscv-zkvm is tied to Sail. A verified model that already exists is preferred over the
  ported one.
- x86 coverage, about 50 forms, is far short of rustc output, so x86 guests need more
  instructions before they can be loaded.

## 4. Rules for the port

- `docs/PLAN.md` Rules hold for everything we take: no `sorry`, no `axiom`, no
  `native_decide`; `bv_decide` allowed; zero warnings.
- Ported code is ours: we change, rename and restructure it as MachineChecked needs. Where
  catcrypt-compiler's version is better than ours, ours is overwritten. No phase waits on
  catcrypt-compiler upstream.
- riscv-zkvm is the only RV64 semantics, unmodified at its pin, with `stepSp1` as the one
  step. An equivalence to another RV64 model is only migration scaffolding, never a final
  dependency.
- A trusted ISA model is named on the trust ladder before any claim rests on it.
- zip-2005's top theorem keeps its form. Ported work enters only as proofs of table entries,
  never as a new premise.

## 5. Open questions

1. How large is the `native_decide` and Mathlib closure of the first candidates? The first
   intake will measure it.
2. Can the SP1 backend be put on a riscv-zkvm revision at v4.33.1 (P1)? That is riscv-zkvm's
   call, not ours.
3. Does CatCrypt's Jasmin dialect `Com` (or LowCT) serve as the next rung above Lprog, when
   one is wanted?
