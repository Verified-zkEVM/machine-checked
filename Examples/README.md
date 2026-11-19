# Examples

Small functions in C and Rust, compiled for RV64IM, taken through
`decompile --to lean --proved`, and verified down to riscv-zkvm's machine. The sources are
those of [braid](https://github.com/dhsorens/braid)'s examples, so the two projects can be
compared function by function.

```
src/c/, src/rust/   the sources
build.sh            compile every source and write its Lean modules
elf/                the binaries, as build.sh made them
Gen/<Module>/       the binary as Lean: its words, checked against the ELF, and each
                    function's lift (written by decompile; do not edit)
<Module>.lean       specifications and proofs
Kit.lean            two facts about bytes that several examples use
```

## What is verified

Every name in the table is a function with a contract at the low logical program
(`<function>_contract`, proved with `lsym`) and the same statement about the machine alone
(`<function>_correct`, through `SafeN.of_isa_contract`).

| Source | Proofs | Functions |
| --- | --- | --- |
| `c/basic.c` | [`Basic.lean`](Basic.lean) | `add3`, `max_u64`, `sum_to` |
| `c/memory.c` | [`Memory.lean`](Memory.lean) | `swap`, `sum_array`, `max2`, `max3` |
| `c/bytes.c` | [`Bytes.lean`](Bytes.lean) | `str_len`, `fill`, `count_ones` |
| `rust/basic.rs` | [`RustBasic.lean`](RustBasic.lean) | `add3`, `max_u64`, `gcd`, `sum_slice` |
| `c/mem.c` | [`Mem.lean`](Mem.lean) | `copy_bytes`, `equal_bytes` |
| `c/limbs.c` | [`Limbs.lean`](Limbs.lean) | `add_limbs` |
| `c/crc32.c` | [`Crc32.lean`](Crc32.lean) | `crc32` |
| `c/chacha20.c` | [`ChaCha20.lean`](ChaCha20.lean) | `quarter_round` |
| `c/sha256.c` | [`Sha256.lean`](Sha256.lean) | `sha256_round`, `sha256_schedule` |

That is 21 functions. Each file checks in 3 to 12 seconds, with no limit raised. The proofs
use no `sorry` and no axiom beyond Lean's three and `bv_decide`'s certificates
(`scripts/AxiomCheckCases.lean`); CI builds them on every pull request.

Not verified yet:

| Function | Instructions | State |
| --- | --- | --- |
| `chacha20_block` (`c/chacha20.c`) | 226 | Lifted (`Gen/ChaCha20/F1.lean`); no proof written or tried. Its loop body is 162 straight-line instructions; at the default limits `lsym` steps 100 in one go and not 200 (`docs/design/Automation.md`). |
| `sha256_compress` (`c/sha256.c`) | 130 | Lifted (`Gen/Sha256/F2.lean`); no proof written or tried. It calls the schedule and runs the round 64 times, both inlined, in a frame of 320 bytes. |

Nothing was left out by the lift: every function of every source is in `Gen/`. The
sources use 32-bit arithmetic that clang compiles to `srliw`, `addiw`, `lw` and `sw`, which
riscv-zkvm's machine has.

What the examples exercise:

- **Straight-line code** (`add3`).
- **A branch** (`max_u64`, `max2`): `bltu` over a move.
- **A loop the compiler removed** (`sum_to`): the binary multiplies at double width and
  shifts. The specification is the sum, and a lemma connects the two.
- **Loads and stores** (`swap`), with `a = b` allowed.
- **A loop over an array** (`sum_array`, `sum_slice`): a pointer walk to an end pointer in C,
  a byte count down to zero in Rust.
- **A loop over bytes** (`str_len`, `fill`, `copy_bytes`, `equal_bytes`).
- **A loop that needs a measure** (`gcd`, `count_ones`): strong induction.
- **A call with a stack frame, and a tail call through a register** (`max3`), proved through
  `max2`'s contract.
- **Arithmetic on many limbs** (`add_limbs`): the result is stated on the numbers the limbs
  represent.
- **A table in read-only data** (`crc32`): the precondition says memory holds the table; that
  its addresses are valid and aligned is proved.
- **32-bit words in memory** (`quarter_round`, `sha256_round`): rotations as two shifts and
  an `or`, related to `rotateLeft` and `rotateRight` by `bv_decide`. `sha256_round` is 57
  instructions without a branch, which `lsym` steps in one go, and keeps `s0` in a frame.

`Cases/Hardening` has what these leave out: signed arithmetic and division at its edges, every
load width, recursion, a function that never returns, `-O0` code, and two functions of an SP1
guest's runtime (`memcmp`, `write_vectored`).

## A theorem

Euclid's algorithm, written in Rust (`src/rust/basic.rs`):

```lean
theorem gcd_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10010#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = BitVec.ofNat 64 (Nat.gcd (s.getReg .x10).toNat (s.getReg .x11).toNat) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s
```

Read it as: a machine `s` at `gcd`'s entry, with the binary's functions in its code
(`Loaded fns s`), is safe if every state `t` it may return in is. Such a state is at the return
address, has the greatest common divisor in `a0`, and has the memory `s` had. `SafeN` is
safety of riscv-zkvm's `stepSp1` for `k` steps (`MachineChecked/RiscV/Safe.lean`); nothing in
the statement is about the lift. It says what holds if the function returns, not that it
does.

## Writing a proof

A proof file imports the module `decompile` wrote and states a contract for a function by
its index (`Gen/<Module>.lean` lists them):

```lean
import Examples.Gen.Basic
import Examples.Kit

namespace Examples.Basic

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Gen.Basic

theorem add3_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' => r' .x10 = regs .x10 + regs .x11 + regs .x12 ∧
      (∀ r, r ≠ .x10 → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f0_eq with [hra, hsp]
  apply hk
  exact ⟨by simp only [lsym_simp]; ac_rfl, fun r h => by simp [lsym_simp, h], rfl⟩
```

The precondition says the return address and the stack pointer are the frame's. `lsym`
steps the body; what is left is the postcondition. `add3_correct`, under it in the file,
carries the contract to the machine in five lines.

Habits from these proofs:

- **A loop is a lemma.** State it at the loop's head from an arbitrary iteration, prove it
  by induction on what is left to do, and use it from the contract. `lsym … stop [p]` leaves
  the goal at the head.
- **`stop [p]` and a frame's position count entries of the body, not labels.** Every
  instruction of a lifted body has a label before it, so label `k` is at position `2k`. With
  the label's number, `lsym` steps from another instruction and the goal is well typed but
  about the wrong place.
- **A memory access needs no precondition.** A load or a store that would trap is safe, so
  `lsym` gives the access's check as a hypothesis on the path after it. State validity in a
  precondition only when a caller should know it.
- **Arithmetic goes in lemmas of its own.** `bv_omega` and `bv_decide` are fast on a small
  goal and slow inside a stepped one.
- **Keep equations out of the context `lsym` runs in.** Its `simp` uses every hypothesis, so
  an equation between addresses there is a rewrite rule, and can keep it from ending
  (`sha256_schedule`). State such facts as theorems and use them after `lsym`.
- **Say what the compiler did.** `add_limbs`'s carry is `s < a` in the binary, where the
  source has `s < carry`; the lemma is about the binary's.

`docs/design/Automation.md` describes `lsym`.

## Building

```sh
lake build Examples         # check every image and every proof
lake build decompile        # the tool build.sh uses
Examples/build.sh           # compile every source and write Gen/ again
Examples/build.sh memory    # one example
```

`build.sh` needs clang with the RISC-V target, a RISC-V linker (`RV_LD`, by default
`riscv64-elf-ld`) and, for the Rust example, rustc with the target
`riscv64imac-unknown-none-elf`. The binaries and `Gen/` are in the repository, so `lake build
Examples` needs none of them. They were built with clang 22.1.4, GNU ld 2.46 and rustc
1.98.1, at `-O1`.

Rust reaches RV64IM through LLVM IR: rustc writes the IR and clang compiles it, so that the
code has no compressed instructions, which riscv-zkvm's machine does not have.

`decompile` reports `__SDATA_BEGIN__: not in an executable segment` for some of the binaries.
It is a symbol GNU ld defines, not a function, and nothing of the source is left out.
