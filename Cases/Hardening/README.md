# Hardening: the tools on code written to break them

Small C programs, compiled by clang for RV64IM, taken through `decompile --to lean --proved`
and proved with `lsym`. Each was chosen to break something rather than to show it working:
every width of load and store, division at its edges, the high half of products, a jump table,
recursion, a function that never returns, calls through registers, registers kept across a
call, `-O0` code that goes through memory for everything, and 290 instructions of straight-line
code. What went wrong is in the table below, with what was done about it.

| file | what |
| --- | --- |
| `src/*.c` | the programs; `*_o0.c` is built at `-O0`, the rest at `-O2` |
| `elf/*.elf` | the ELFs, as `build.sh` made them (clang 22.1, `--target=riscv64-unknown-elf -march=rv64im`) |
| `Gen/` | `decompile --to lean --proved` of each ELF, as written (do not edit) |
| `build.sh` | rebuilds `elf/` and `Gen/` from `src/` (needs clang with the RISC-V target, and an `ld.lld`) |
| `Basics.lean` | branches signed and unsigned, `clamp`, a loop over memory (`sum`), and a bit-length that clang compiles to a population count (`count_down`), by `bv_decide` |
| `Mem.lean` | loads of every width, signed and not; `swap`, with `a = b` allowed |
| `Arith.lean` | division and remainder by zero and at `INT64_MIN / -1`, the high half of 128-bit products signed and not, a rotation, an absolute value without a branch: each against C |
| `Calls.lean` | contracts: a call and a tail call with `ra` in a frame, a tail call through a register (`jr t1`) to a function passed as a value, four registers kept across a call, a function that never returns and a call of it |
| `Rec.lean` | `fib`, recursive: its contract by induction on the argument, through a loop around the recursive call, with a frame condition |

Every function of `Gen/` builds (the kernel checks each lift), and every theorem is proved: no
`sorry`, and no axiom beyond Lean's three and, where `bv_decide` closed a goal, its
certificates, as elsewhere in the repository (`scripts/AxiomCheck.lean`). The proofs check in
3 to 5 s a file. CI builds them on every pull request.

## What was found

Bugs, gaps and friction, in the order they were met. "Fixed" means fixed in this round, with
the test that would have caught it.

| # | kind | what | done |
| --- | --- | --- | --- |
| 1 | interface | `decompile --to lean` took only a one-word namespace, so its modules could not sit inside a library (`Cases.Hardening.Gen.Arith`) | fixed: a dotted namespace is a module path under `OUTDIR` (`Tools/Test/ToLean.lean`) |
| 2 | gap | the `--proved` lift leaves out any function with one of the nine 32-bit operations riscv-zkvm's machine lacks (`addw`, `sllw`, `sraw`, `sraiw`, `mulw`, `divw`, `divuw`, `remw`, `remuw`): four of `arith.c`'s twelve. It said only "a word does not decode" | message fixed: it names the instruction, its address and why; the gap stays (riscv-zkvm's machine would need the nine) |
| 3 | friction | the generated modules name functions by index only (`f4_eq`, the frame `⟨4, 0, …⟩`), and `F10.lean` sorts before `F2.lean` | fixed: the top module lists each index with its symbol and address |
| 4 | friction | an unsigned branch's condition came back as `x.ult y = true`, which `simp` does not relate to `x < y` | fixed: `BitVec.ult_iff_lt` and the `= false` forms in `lsym_simp` |
| 5 | gap | an index scaled by a shift (`slli a1, a1, 3`) was `ofNat n <<< 3`, not the region lemmas' `ofNat (8 * n)` | fixed: `addr_ofNat_shl` in `lsym_addr` (and `write_vectored`'s hand lemma for it is no longer needed) |
| 6 | bug | after a call through a contract, the callee's postcondition (`hret`) was named but not used: a frame's `ra` read back after the call, a tail call's precondition, were left open | fixed: each step on a path past a call uses its `hret` (and earlier calls' keep their own names, `hret_1`, …); three existing proofs lost a `hret` they had to pass by hand |
| 7 | bug | a postcondition stated by a definition (`FibPost k …`) stayed folded in `hret`, so nothing of it was usable | fixed: `lsym` unfolds `hret` by the lemmas given in `with` |
| 8 | gap | a loop that never ends (`j .`, any function that does not return) could not be proved safe: every step rule keeps the budget | fixed: `SafeN.label_spend` spends one unit at a label; `stop_contract` is proved by induction on the budget |
| 9 | friction | `simp only [lsym_simp]` left `if Reg.x2 = Reg.x10 then …` undecided (the simproc is in the default set only) | fixed: `reduceCtorEq`, `reduceIte` in `lsym_simp` |
| 10 | friction | `bv_omega` inside a proof `lsym` has stepped hangs or fails where the same fact alone is instant: it takes every hypothesis, and `lsym` leaves many (each memory check, each `hret`) | open: state the arithmetic as lemmas of its own (`Rec.lean` does) |
| 11 | upstream | plain `simp` on `(t + 18446744073709551584#64).toNat` (the normal form of `t - 32`) gives a proof the kernel times out on; `bv_omega` proves the same fact at once | open, Lean's: avoid `simp` on `toNat` of a sum with a large literal |
| 12 | friction | the hypotheses `lsym` adds still hide each other: four loads give `hm✝²`, `hm✝¹`, `hm✝`, `hm` | open (#44 left it: renaming changes what existing proofs refer to) |
| 13 | scale | 290 straight-line instructions (`mix`) step in 45 s, with `maxHeartbeats` raised tenfold | open: `SafeN.block`, as planned |

What held up, tested and not found wanting: the lift's meaning of every operation checked
against C (division by zero gives `-1` and remainder the dividend, as RISC-V says; the
overflow; `mulh`'s logical shift, the same once truncated); sign and zero extension of every
load; read-back through stores, including two stores to one address; a tail call through a
register to a function whose address was passed as a value, resolved through the contract
with all candidates; `-O0` code with a frame pointer, closed by `lsym` and one `simp`; loops
found without `stop`; and the trace saying why each goal was left.

## The other instruction sets

The same sources for AArch64 and x86-64 (bare, `-O2`), through `decompile --to lean` (the
lift of whole programs; `--proved` is RISC-V's): every function decodes and lifts, and every
`abort` is either a function's end (one each) or an x86-64 divide error (`div` and `idiv`
trap on zero and on a quotient too large, and the lift says so). Every module written builds,
so the kernel checks each lift (Apple M3 Max, one module at a time):

| program | AArch64 | x86-64 |
| --- | --- | --- |
| `arith` | 13 s | 24 s |
| `basics` | 11 s | 27 s |
| `calls` | 14 s | 36 s |
| `mem` | 14 s | 28 s |
| `rec` | 5 s | 6 s |
| `switch` | 3 s | 4 s |

These are not proved with `lsym`: neither instruction set has an Lprog instance backed by its
machine yet (`docs/design/Automation.md`), so a proof there would be about a model.
