# Lprog

The logical machine: the intermediate layer between an instruction set's machine and the
program logics. Lprog is linear Jasmin. A body is a list of instructions: operations,
labels, gotos, conditional jumps, calls and returns. Labels replace addresses, and control
flow is explicit.

## Files

| file | contents | depends on an ISA? |
| --- | --- | --- |
| `Syntax.lean` | Operands, instructions (`LinstrR`), bodies, functions, programs. The operation type is a parameter. | no |
| `Sem.lean` | `Isa`: an instruction set supplies the operation type, the state beside the registers, and the meaning of operations and conditions. Control flow is shared. Defines `step`, `run`, `steps`, the correspondence `CorresIsa`, and the run predicates `Reaches` and `Halts`. | no |
| `RiscV.lean` | `rvIsa`, the RISC-V instance. An operation is a riscv-zkvm `Instr` that does not transfer control, run by riscv-zkvm's own `execInstrBr` behind SP1's memory check. `Agree` says when two machine states look the same to an instruction. | RISC-V |
| `Lift.lean` | `lift`: a decoded function becomes an Lprog body. `Sim` relates Lprog states to machine states, and the simulation (`sim_step`, `sim_run`, `sim_steps`) carries every Lprog run down to a `stepSp1` run (`reach_of_corresIsa`, `reach_of_reaches`, `SafeN.of_reaches`). It also holds the rules for running a body (`reaches_label`, `reaches_opn`, `reaches_cond`, `reaches_goto`, `halts_ret`), and `sim_return` for resuming after a call out of the function. | RISC-V |

## Using it

A function is proved at Lprog by running its lifted body with the `reaches_*` rules, and the
result is carried to the machine by `SafeN.of_reaches`. A call to another function stops the
Lprog run. The call is taken over the machine with the callee's specification, and
`sim_return` resumes at Lprog after it. Worked examples:
- `Cases/Zip2005/Runtime/MemcmpLprog.lean`: a loop, for every length.
- `Cases/Zip2005/Runtime/WriteVectored.lean`: a loop and a call.

## Instruction sets

`Syntax` and `Sem` are where other instruction sets meet the framework. An x86-64 or AArch64
instance is an `Isa` plus a lift and a simulation like `RiscV.lean` and `Lift.lean`. Proofs
written against the shared control flow then carry over.

Lprog sits after register allocation. A higher, typed logical program is sketched in
`docs/LogicalMachine.md` as a possible later rung.

The syntax is ported from catcrypt-compiler. Its semantics there is tied to an x86 Jasmin
interpreter, so `Sem.lean` is new.
