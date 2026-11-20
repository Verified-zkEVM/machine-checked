# Examples

Compiled code, taken through `decompile --to lean --proved`, and verified down to riscv-zkvm's
machine. There are three groups:

- **The ladder**: small functions in C and Rust, from straight-line code to a round of
  SHA-256. The sources are those of [braid](https://github.com/dhsorens/braid)'s examples, so
  the two projects can be compared function by function. This is the place to start.
- **Stress tests**: small C programs chosen to break the tools.
- **Guest code**: functions of an SP1 guest's runtime, as rustc compiled them, and the loaded
  image of a leanVM guest.

```
src/c/, src/rust/            the sources
build.sh                     compile every source and write every Image
elf/                         the binaries
<Module>/RiscV/Image.lean    the binary as Lean: the list of its functions by index
<Module>/RiscV/Image/        its words, checked against the ELF (Words.lean), and each
                             function's lift (F<i>.lean); written by decompile, do not edit
<Module>/RiscV/Proofs.lean   specifications and proofs
Spec.lean                    the functions the specifications are stated with (umax, wsum,
                             wgcd, ones, sumTo, the SHA-256 round, ...): about words and
                             lists, with no instruction set in them
Kit.lean                     facts about a machine state several modules use: the bytes of a
                             region, a byte or a 32-bit word read after one was written
LeanVM/                      a leanVM guest, in the layout of its own generator
```

A module is one binary. Its directory is `<Module>/RiscV/` because the code is RISC-V and the
proofs are about that code; the specifications in `Spec.lean` are not.

## What is verified

### The ladder

Every name in the table is a function with a contract at the low logical program
(`<function>_contract`, proved with `lsym`) and the same statement about the machine alone
(`<function>_correct`, through `SafeN.of_isa_contract`).

| Source | Proofs | Functions |
| --- | --- | --- |
| `c/basic.c` | [`Basic/RiscV/Proofs.lean`](Basic/RiscV/Proofs.lean) | `add3`, `max_u64`, `sum_to` |
| `c/memory.c` | [`Memory/RiscV/Proofs.lean`](Memory/RiscV/Proofs.lean) | `swap`, `sum_array`, `max2`, `max3` |
| `c/bytes.c` | [`Bytes/RiscV/Proofs.lean`](Bytes/RiscV/Proofs.lean) | `str_len`, `fill`, `count_ones` |
| `rust/basic.rs` | [`RustBasic/RiscV/Proofs.lean`](RustBasic/RiscV/Proofs.lean) | `add3`, `max_u64`, `gcd`, `sum_slice` |
| `c/mem.c` | [`Mem/RiscV/Proofs.lean`](Mem/RiscV/Proofs.lean) | `copy_bytes`, `equal_bytes` |
| `c/limbs.c` | [`Limbs/RiscV/Proofs.lean`](Limbs/RiscV/Proofs.lean) | `add_limbs` |
| `c/crc32.c` | [`Crc32/RiscV/Proofs.lean`](Crc32/RiscV/Proofs.lean) | `crc32` |
| `c/chacha20.c` | [`ChaCha20/RiscV/Proofs.lean`](ChaCha20/RiscV/Proofs.lean) | `quarter_round` |
| `c/sha256.c` | [`Sha256/RiscV/Proofs.lean`](Sha256/RiscV/Proofs.lean) | `sha256_round`, `sha256_schedule` |

That is 21 functions. Each file checks in 3 to 12 seconds, with no limit raised.

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

### Stress tests

Small C programs, compiled by clang at `-O2` (`*_o0.c` at `-O0`). Each was chosen to break
something: every width of load and store, division at its edges, the high half of products, a
jump table, recursion, a function that never returns, calls through registers, registers kept
across a call, `-O0` code that keeps everything in memory, and 290 instructions of
straight-line code. What broke is in [What was found](#what-was-found).

Each function in the table is proved with `lsym` against what C says it computes, as a
statement at the low logical program (`<function>_spec` or `<function>_contract`). Unlike
the ladder's, they have no `_correct` theorem about the machine alone.

| Source | Proofs | Functions |
| --- | --- | --- |
| `c/branches.c` | [`Branches/RiscV/Proofs.lean`](Branches/RiscV/Proofs.lean) | `max2` (a signed branch), `clamp`, `count_down` (a bit length that clang compiles to a population count, by `bv_decide`) |
| `c/widths.c` | [`Widths/RiscV/Proofs.lean`](Widths/RiscV/Proofs.lean) | `load_s8`, `load_u8`, `load_s16`, `load_u16`, `load_s32`, `load_u32`: loads of every width, signed and unsigned |
| `c/arith.c` | [`Arith/RiscV/Proofs.lean`](Arith/RiscV/Proofs.lean) | `sdiv`, `srem`, `udiv` (by zero and at `INT64_MIN / -1`), `mulhi`, `smulhi` (the high half of 128-bit products), `rotl`, `abs_branchless` |
| `c/calls.c` | [`Calls/RiscV/Proofs.lean`](Calls/RiscV/Proofs.lean) | `inc`, `twice_inc` (a call and a tail call with `ra` saved in a frame), `tail_inc`, `apply`, `apply_inc` (a tail call through a register, `jr t1`, to a function passed as a value), `sum4`, `keep` (four registers kept across a call), `stop` (a function that never returns), `checked_div` (a call to it) |
| `c/rec.c` | [`Rec/RiscV/Proofs.lean`](Rec/RiscV/Proofs.lean) | `fib`: recursion, by induction on the argument, through a loop around the recursive call, with a frame condition |
| `c/branches_o0.c`, `c/calls_o0.c`, `c/switch.c`, `c/big.c` | none: `BranchesO0`, `CallsO0`, `Switch` and `Big` have an Image only | |

`branches.c` and `widths.c` were `basics.c` and `mem.c` before they came here, where those
names are the ladder's. `add3`, the unsigned maximum, the sum of an array and `swap` are proved
in the ladder, not here.

### Guest code

Functions of the runtime of an SP1 guest, for every input, down to the machine. The guest is
`k_u128` (`elf/k_u128.elf`), one of the Rust guests of `scripts/decompile-check/rust/`, built
for SP1 by rustc. The lift takes 156 of its functions; the Image keeps their words and the four functions below
(`Sp1Runtime/RiscV/Image.lean` says which). `memcmp` is from an ELF of its own: `c/memcmp.c` is
`memcmp` as a byte loop, which clang compiles to the twelve instructions rustc's
`compiler_builtins` has for it in an SP1 guest, with two of the increments in another order.

| Source | Proofs | Functions |
| --- | --- | --- |
| `c/memcmp.c` (`elf/memcmp.elf`) | [`Sp1Runtime/RiscV/Memcmp.lean`](Sp1Runtime/RiscV/Memcmp.lean) | `memcmp(a, b, n)`, for every length: the byte loop by induction (`loop`), its contract at Lprog (`contract`), and the same statement over riscv-zkvm's machine (`safe`) |
| `elf/k_u128.elf` | [`Sp1Runtime/RiscV/WriteVectored.lean`](Sp1Runtime/RiscV/WriteVectored.lean) | `write_vectored` of the guest's standard error (`F104`): a loop, a call to `sys_write` (`F24`, `sw_spec`), which tail-calls `syscall_write` (`F11`, `scw_spec`), which makes the system call. Its contract at Lprog (`contract`) and the same statement over the machine (`spec`) |
| `elf/k_u128.elf` | [`Sp1Runtime/RiscV/Udivti3.lean`](Sp1Runtime/RiscV/Udivti3.lean) | `__udivti3` (`F155`), from a contract of its callee `u128_div_rem`, which is assumed: a far call (`auipc`, `jalr`), with the result returned through a pointer into its frame |

[`LeanVM/`](LeanVM/README.md) is a guest of a second target, leanVM, computing BLAKE2s. Its
image is loaded and its decoding checked (`LeanVM/Blake2s/Loaded.lean`); nothing about its
behaviour is proved.

zip-2005, an SP1 guest that checks a Zcash Orchard statement, has its verification in its own
repository, [zip-2005-asm](https://github.com/dhsorens/zip-2005-asm). The tag `with-zip2005`
is the last tree here that has it and the CatCrypt kernels.

The proofs of all three groups use no `sorry` and no axiom beyond Lean's three and
`bv_decide`'s certificates (`scripts/AxiomCheck.lean`, `scripts/AxiomCheckExamples.lean`). CI
(`.github/workflows/ci.yml`) builds them on every pull request, with the framework and the
tools (`lake build MachineChecked Tools Examples`), and fails on any warning.

## Not verified

Every function that is lifted and has no proof, by module. `_start` is each stress test's
entry, an empty loop.

The ladder:

- `ChaCha20`: `chacha20_block`, 226 instructions (`ChaCha20/RiscV/Image/F1.lean`). No proof
  written or tried. Its loop body is 162 straight-line instructions; at the default limits
  `lsym` steps 100 in one go and not 200 (`docs/design/Automation.md`).
- `Sha256`: `sha256_compress`, 130 instructions (`Sha256/RiscV/Image/F2.lean`). No proof
  written or tried. It calls the schedule and runs the round 64 times, both inlined, in a
  frame of 320 bytes.
- `RustBasic`: `rust_begin_unwind`, the panic handler: a jump to itself, which none of the
  others calls.

Nothing of the ladder was left out by the lift: every function of every source has its module.
The sources use 32-bit arithmetic that clang compiles to `srliw`, `addiw`, `lw` and `sw`, which
riscv-zkvm's machine has.

Stress tests:

- `Branches`: `add3`, `umax2`, `sum`, `_start`.
- `BranchesO0` (image only): `add3`, `max2`, `umax2`, `clamp`, `sum`, `count_down`, `_start`.
- `Widths`: `set_bytes`, `copy_bytes`, `str_len`, `store_widths`, `read_le32`, `swap`,
  `_start`.
- `Arith`: `popcount`, `_start`. Four more functions of `arith.c` use 32-bit operations
  (`add32`, `shl32`, `sra32`, `div32`) and are not lifted at all (finding 2).
- `Calls`: `fact`, `_start`.
- `CallsO0` (image only): `inc`, `twice_inc`, `fact`, `apply`, `apply_inc`, `sum4`, `keep`,
  `tail_inc`, `stop`, `checked_div`, `_start`.
- `Rec`: `_start`.
- `Switch` (image only): `classify`, `_start`.
- `Big` (image only): `mix`, `_start`.

Guest code:

- `Sp1Runtime`: `_start` of `memcmp.elf`. Of `k_u128.elf`, the other 152 functions the lift
  takes, whose modules are not kept (`build.sh` writes them and keeps five files). One of
  them is `u128_div_rem`, which `__udivti3` calls: its contract is an assumption of
  `udivti3_contract`. Three more functions contain `unimp` and are not lifted at all
  (finding 14).
- `LeanVM`: loaded, nothing proved.

## What was found

The stress tests' findings, in the order they were found. "Fixed" entries name the test that
now covers them.

| # | kind | finding | status |
| --- | --- | --- | --- |
| 1 | interface | `decompile --to lean` accepted only a one-word namespace, so its modules could not sit inside a library (`Examples.Arith.RiscV.Image`). | Fixed: a dotted namespace is a module path under `OUTDIR` (`Tools/Test/ToLean.lean`). |
| 2 | gap | The `--proved` lift skips any function using one of the nine 32-bit operations riscv-zkvm's machine lacks (`addw`, `sllw`, `sraw`, `sraiw`, `mulw`, `divw`, `divuw`, `remw`, `remuw`): four of `arith.c`'s twelve. The error said only "a word does not decode". | Message fixed: it names the instruction, its address and the reason. The gap remains; riscv-zkvm's machine would need the nine. |
| 3 | friction | Generated modules named functions by index only (`f4_eq`, the frame `⟨4, 0, …⟩`), and `F10.lean` sorted before `F2.lean`. | Fixed: the top module lists each index with its symbol and address. |
| 4 | friction | An unsigned branch condition came out as `x.ult y = true`, which `simp` does not relate to `x < y`. | Fixed: `BitVec.ult_iff_lt` and the `= false` forms are in `lsym_simp`. |
| 5 | gap | An index scaled by a shift (`slli a1, a1, 3`) became `ofNat n <<< 3`, not the region lemmas' `ofNat (8 * n)`. | Fixed: `addr_ofNat_shl` in `lsym_addr`. `write_vectored` no longer needs its own lemma for this. |
| 6 | bug | After a call through a contract, the callee's postcondition (`hret`) was named but not used, so goals such as reading back a saved `ra` or a tail call's precondition were left open. | Fixed: each step after a call uses its `hret`. Three existing proofs no longer pass `hret` by hand. |
| 7 | bug | A postcondition stated by a definition (`FibPost k …`) stayed folded in `hret`, so none of it was usable. | Fixed: `lsym` unfolds `hret` with the lemmas given in `with`. |
| 8 | gap | A loop that never ends (`j .`, any function that does not return) could not be proved safe: every step rule keeps the budget. | Fixed: `SafeN.label_spend` spends one unit at a label; `stop_contract` is proved by induction on the budget. |
| 9 | friction | `simp only [lsym_simp]` left `if Reg.x2 = Reg.x10 then …` undecided; the needed simprocs are only in the default simp set. | Fixed: `reduceCtorEq` and `reduceIte` are in `lsym_simp`. |
| 10 | friction | `bv_omega` after `lsym` hangs or fails on facts it proves instantly in isolation: it takes every hypothesis, and `lsym` leaves many (each memory check, each `hret`). | Open. Workaround: state the arithmetic as separate lemmas (as `Rec/RiscV/Proofs.lean` does). |
| 11 | upstream | Plain `simp` on `(t + 18446744073709551584#64).toNat` (the normal form of `t - 32`) produces a proof the kernel times out on; `bv_omega` proves the same fact at once. | Open, in Lean. Workaround: avoid `simp` on `toNat` of a sum with a large literal. |
| 12 | friction | Hypotheses `lsym` added shadowed each other: four loads gave `hm✝²`, `hm✝¹`, `hm✝`, `hm`. | Fixed: the latest keeps the plain name and earlier ones are `hm_1`, `hm_2`, … oldest first (likewise `hc_…`, `hret_…`). Only names of that exact form are counted or renamed, so a proof's own `hm_spec` is left alone. `memcmp`'s `rename_i` became `hc_1` (`Tools/Test/Lsym.lean`). |
| 13 | scale | 290 straight-line instructions (`mix`) take 45 s to step, with `maxHeartbeats` raised tenfold. | Open: planned fix is to use `SafeN.block` in `lsym`. |
| 14 | gap | In rustc's output for SP1, the `--proved` lift skips every function containing `unimp` (`0xc0001073`, the illegal instruction compilers emit for a trap, e.g. Rust's `abort` or `unreachable!`): 142 of the 6,738 functions in 41 guests, including each guest's panic machinery, a `main` and several `sort`s. The error said "no instruction of RV64IM". | Message fixed: it names `unimp`. The gap remains: riscv-zkvm's decoder has no instruction for it. The lift could treat it as a trap, with `Equiv.lean` extended. |
| 15 | friction | A hypothesis passed to `lsym` with the literal `0` does not close a side condition that `simp` has written as `0#128`: the two do not match as a rewrite. | Open. Workaround: write `0#128` in the contract (`Sp1Runtime/RiscV/Udivti3.lean`). |

### What held

Tested and found correct:

- The lift's meaning of every operation, checked against C: division by zero gives `-1` and
  remainder gives the dividend, as RISC-V specifies; overflow; `mulh`'s logical shift, which
  agrees once truncated.
- Sign and zero extension on every load.
- Reading back through stores, including two stores to one address.
- A tail call through a register to a function whose address was passed as a value, resolved
  through the contract over all candidates.
- `-O0` code with a frame pointer, closed by `lsym` and one `simp`.
- Loops found without `stop`.
- The trace saying why each remaining goal was left.

### Rust guests

The 41 Rust guests of `scripts/decompile-check/rust/`, built for SP1 by rustc at
`opt-level = 3`: 6,738 functions, 475,144 instructions lifted. The `--proved` lift takes
6,561 functions and skips 177, each with its reason:

| reason skipped | functions |
| --- | --- |
| `unimp` (a trap) | 142: three of the runtime's panic functions in each guest (123), and 19 others, including a `main` and several `sort` instances |
| `addw` | 20 |
| `sraiw` | 5 |
| `sllw`, `divuw` | 4 each |
| `divw`, `remuw` | 1 each |

`--to lean --proved` on six of them, every module built (so the kernel checked each
function's lift), eight at a time on an Apple M3 Max:

| guest | functions | instructions | modules built | wall time | slowest function |
| --- | --- | --- | --- | --- | --- |
| `k_alloc` | 159 | 11,617 | all | 46 s | 22 s |
| `k_btree` | 161 | 13,115 | all | 39 s | 13 s |
| `k_dyn` | 168 | 11,169 | all | 37 s | 12 s |
| `k_fmt` | 230 | 16,940 | all | 51 s | 13 s |
| `k_i128` | 157 | 11,522 | all | 45 s | 19 s |
| `k_sort` | 170 | 13,345 | all | 38 s | 13 s |

### AArch64 and x86-64

The stress tests' C sources, compiled bare at `-O2` for AArch64 and x86-64, through `decompile --to
lean` (whole-program lift; `--proved` is RISC-V only). Every function decodes and lifts. Every
`abort` is either a function's end (one each) or an x86-64 divide error (`div` and `idiv` trap
on zero and on a quotient too large, and the lift says so). Every module written builds, so
the kernel checked each lift. Build times on an Apple M3 Max, one module at a time:

| program | AArch64 | x86-64 |
| --- | --- | --- |
| `arith` | 13 s | 24 s |
| `branches` | 11 s | 27 s |
| `calls` | 14 s | 36 s |
| `widths` | 14 s | 28 s |
| `rec` | 5 s | 6 s |
| `switch` | 3 s | 4 s |

These are not proved with `lsym`: neither instruction set yet has an Lprog instance backed by
its machine semantics ([`docs/design/Automation.md`](../docs/design/Automation.md)), so a
proof would be about a model, not the machine.

## A theorem

Euclid's algorithm, written in Rust (`src/rust/basic.rs`):

```lean
theorem gcd_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10010#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = wgcd (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s
```

Read it as: a machine `s` at `gcd`'s entry, with the binary's functions in its code
(`Loaded fns s`), is safe if every state `t` it may return in is. Such a state is at the return
address, has the greatest common divisor in `a0` (`wgcd`, in `Spec.lean`: `Nat.gcd` of the two
words), and has the memory `s` had. `SafeN` is
safety of riscv-zkvm's `stepSp1` for `k` steps (`MachineChecked/RiscV/Safe.lean`); nothing in
the statement is about the lift. It says what holds if the function returns, not that it
does.

## Writing a proof

A proof file imports the Image `decompile` wrote and states a contract for a function by
its index (`<Module>/RiscV/Image.lean` lists them):

```lean
import Examples.Basic.RiscV.Image
import Examples.Spec
import Examples.Kit

namespace Examples.Basic.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Basic.RiscV.Image

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
- **A specification that is not about the machine goes in `Spec.lean`.** A function on words
  or lists (`umax`, `wsum`, `crc32Spec`) says what the source computes on any instruction set.
  What reads a `MachineState` (`bytesAt`, `StrAt`) stays with the proofs or in `Kit.lean`.

`docs/design/Automation.md` describes `lsym`.

## Building

```sh
lake build Examples                  # check every image and every proof
lake build decompile                 # the tool build.sh uses
LIFT_ONLY=1 Examples/build.sh        # write every Image again, from the ELFs in elf/
LIFT_ONLY=1 Examples/build.sh Memory # one module
Examples/build.sh                    # compile every source as well
```

The binaries and the Images are in the repository, so `lake build Examples` needs no compiler.
The proofs are about the ELFs that are in
`elf/`: another compiler or linker gives other code and other addresses, so compile again only
to change them.

To compile, `build.sh` needs clang with the RISC-V target, a RISC-V linker (`RV_LD`, by default
`riscv64-elf-ld`), `ld.lld` (`LLD`) and, for the Rust example, rustc with the target
`riscv64imac-unknown-none-elf`.

| Group | Compiled | Linked |
| --- | --- | --- |
| the ladder | clang 22.1.4 at `-O1` (rustc 1.98.1 for Rust) | GNU ld 2.46, text at `0x10000` |
| stress tests, `memcmp.c` | clang 22.1 at `-O2`, `*_o0.c` at `-O0` | `ld.lld`, text at `0x1000` |
| `k_u128.elf` | rustc, for SP1; not compiled by `build.sh` | |

Rust reaches RV64IM through LLVM IR: rustc writes the IR and clang compiles it, so that the
code has no compressed instructions, which riscv-zkvm's machine does not have.

`decompile` reports `__SDATA_BEGIN__: not in an executable segment` for some of the binaries.
It is a symbol GNU ld defines, not a function, and nothing of the source is left out.

For a binary of your own, see "Adding an example" in
[`CONTRIBUTING.md`](../CONTRIBUTING.md).
