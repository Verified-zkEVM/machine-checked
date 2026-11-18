# Hardening: the tools on code written to break them

Small C programs, compiled by clang for RV64IM, lifted with `decompile --to lean --proved` and
proved with `lsym`. Each was chosen to break something: every width of load and store,
division at its edges, the high half of products, a jump table, recursion, a function that
never returns, calls through registers, registers kept across a call, `-O0` code that keeps
everything in memory, and 290 instructions of straight-line code. The findings are listed
below, with what was done about each.

The proofs use no `sorry` and no axioms beyond Lean's three and `bv_decide`'s certificates
(`scripts/AxiomCheck.lean`). Each file checks in 3 to 5 s. Build: `lake build Cases.Hardening`,
which CI runs on every pull request.

| file | contents |
| --- | --- |
| `src/*.c` | The programs. `*_o0.c` is built at `-O0`, the rest at `-O2`. |
| `elf/*.elf` | The ELFs `build.sh` made (clang 22.1, `--target=riscv64-unknown-elf -march=rv64im`), and `k_u128.elf`, one of the Rust guests below. |
| `Gen/` | `decompile --to lean --proved` of each ELF, as written. Do not edit. `BasicsO0`, `CallsO0`, `Switch` and `Big` are generated but not used by a proof here, so only CI's `full` job builds them. |
| `build.sh` | Rebuilds `elf/` and `Gen/` from `src/`. Needs clang with the RISC-V target and `ld.lld`. |
| `Basics.lean` | Signed and unsigned branches, `clamp`, a loop over memory (`sum`), and a bit length that clang compiles to a population count (`count_down`, by `bv_decide`). |
| `Mem.lean` | Loads of every width, signed and unsigned; `swap`, including `a = b`. |
| `Arith.lean` | Division and remainder by zero and at `INT64_MIN / -1`, the high half of signed and unsigned 128-bit products, a rotation, a branchless absolute value: each against C. |
| `Calls.lean` | Contracts: a call and a tail call with `ra` saved in a frame, a tail call through a register (`jr t1`) to a function passed as a value, four registers kept across a call, a function that never returns, and a call to it. |
| `Guest.lean` | `__udivti3` from a Rust guest built for SP1 (`elf/k_u128.elf`), through an assumed contract of its callee: a far call (`auipc`, `jalr`), with the result returned through a pointer into its frame. |
| `Rec.lean` | Recursive `fib`: its contract, by induction on the argument, through a loop around the recursive call, with a frame condition. |

## Findings

In the order they were found. "Fixed" entries name the test that now covers them.

| # | kind | finding | status |
| --- | --- | --- | --- |
| 1 | interface | `decompile --to lean` accepted only a one-word namespace, so its modules could not sit inside a library (`Cases.Hardening.Gen.Arith`). | Fixed: a dotted namespace is a module path under `OUTDIR` (`Tools/Test/ToLean.lean`). |
| 2 | gap | The `--proved` lift skips any function using one of the nine 32-bit operations riscv-zkvm's machine lacks (`addw`, `sllw`, `sraw`, `sraiw`, `mulw`, `divw`, `divuw`, `remw`, `remuw`): four of `arith.c`'s twelve. The error said only "a word does not decode". | Message fixed: it names the instruction, its address and the reason. The gap remains; riscv-zkvm's machine would need the nine. |
| 3 | friction | Generated modules named functions by index only (`f4_eq`, the frame `⟨4, 0, …⟩`), and `F10.lean` sorted before `F2.lean`. | Fixed: the top module lists each index with its symbol and address. |
| 4 | friction | An unsigned branch condition came out as `x.ult y = true`, which `simp` does not relate to `x < y`. | Fixed: `BitVec.ult_iff_lt` and the `= false` forms are in `lsym_simp`. |
| 5 | gap | An index scaled by a shift (`slli a1, a1, 3`) became `ofNat n <<< 3`, not the region lemmas' `ofNat (8 * n)`. | Fixed: `addr_ofNat_shl` in `lsym_addr`. `write_vectored` no longer needs its own lemma for this. |
| 6 | bug | After a call through a contract, the callee's postcondition (`hret`) was named but not used, so goals such as reading back a saved `ra` or a tail call's precondition were left open. | Fixed: each step after a call uses its `hret`. Three existing proofs no longer pass `hret` by hand. |
| 7 | bug | A postcondition stated by a definition (`FibPost k …`) stayed folded in `hret`, so none of it was usable. | Fixed: `lsym` unfolds `hret` with the lemmas given in `with`. |
| 8 | gap | A loop that never ends (`j .`, any function that does not return) could not be proved safe: every step rule keeps the budget. | Fixed: `SafeN.label_spend` spends one unit at a label; `stop_contract` is proved by induction on the budget. |
| 9 | friction | `simp only [lsym_simp]` left `if Reg.x2 = Reg.x10 then …` undecided; the needed simprocs are only in the default simp set. | Fixed: `reduceCtorEq` and `reduceIte` are in `lsym_simp`. |
| 10 | friction | `bv_omega` after `lsym` hangs or fails on facts it proves instantly in isolation: it takes every hypothesis, and `lsym` leaves many (each memory check, each `hret`). | Open. Workaround: state the arithmetic as separate lemmas (as `Rec.lean` does). |
| 11 | upstream | Plain `simp` on `(t + 18446744073709551584#64).toNat` (the normal form of `t - 32`) produces a proof the kernel times out on; `bv_omega` proves the same fact at once. | Open, in Lean. Workaround: avoid `simp` on `toNat` of a sum with a large literal. |
| 12 | friction | Hypotheses `lsym` added shadowed each other: four loads gave `hm✝²`, `hm✝¹`, `hm✝`, `hm`. | Fixed: the latest keeps the plain name and earlier ones are `hm_1`, `hm_2`, … oldest first (likewise `hc_…`, `hret_…`). Only names of that exact form are counted or renamed, so a proof's own `hm_spec` is left alone. `memcmp`'s `rename_i` became `hc_1` (`Tools/Test/Lsym.lean`). |
| 13 | scale | 290 straight-line instructions (`mix`) take 45 s to step, with `maxHeartbeats` raised tenfold. | Open: planned fix is to use `SafeN.block` in `lsym`. |
| 14 | gap | In rustc's output for SP1, the `--proved` lift skips every function containing `unimp` (`0xc0001073`, the illegal instruction compilers emit for a trap, e.g. Rust's `abort` or `unreachable!`): 142 of the 6,738 functions in 41 guests, including each guest's panic machinery, a `main` and several `sort`s. The error said "no instruction of RV64IM". | Message fixed: it names `unimp`. The gap remains: riscv-zkvm's decoder has no instruction for it. The lift could treat it as a trap, with `Equiv.lean` extended. |
| 15 | friction | A hypothesis passed to `lsym` with the literal `0` does not close a side condition that `simp` has written as `0#128`: the two do not match as a rewrite. | Open. Workaround: write `0#128` in the contract (`Guest.lean`). |

## What held

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

## Rust guests

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

## AArch64 and x86-64

The same C sources, compiled bare at `-O2` for AArch64 and x86-64, through `decompile --to
lean` (whole-program lift; `--proved` is RISC-V only). Every function decodes and lifts. Every
`abort` is either a function's end (one each) or an x86-64 divide error (`div` and `idiv` trap
on zero and on a quotient too large, and the lift says so). Every module written builds, so
the kernel checked each lift. Build times on an Apple M3 Max, one module at a time:

| program | AArch64 | x86-64 |
| --- | --- | --- |
| `arith` | 13 s | 24 s |
| `basics` | 11 s | 27 s |
| `calls` | 14 s | 36 s |
| `mem` | 14 s | 28 s |
| `rec` | 5 s | 6 s |
| `switch` | 3 s | 4 s |

These are not proved with `lsym`: neither instruction set yet has an Lprog instance backed by
its machine semantics ([`docs/design/Automation.md`](../../docs/design/Automation.md)), so a
proof would be about a model, not the machine.
