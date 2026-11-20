# Lprog

Layer 0.5 of the [roadmap](../../ROADMAP.md): the low logical program. Modules are `Lprog.*`
in the package [`lprog`](../README.md); declarations are in the namespace `Lprog`. Nothing here
depends on an instruction set's machine. AArch64 and x86-64 registers are here because they
are only names; RISC-V's depend on riscv-zkvm and are in
[`lprog-riscv`](../../lprog-riscv/README.md).

## The language

Lprog is modelled on Jasmin's linear language (`Linear.lcmd`, as ported in catcrypt-compiler). A body is a list of instructions: operations, labels, gotos,
conditional jumps, calls, tail calls, returns and external calls. Labels replace addresses and
control flow is explicit, but there are still registers and flat memory.

One language serves every ISA because control flow and operations are shared. The operations
(`Op.lean`) are bitvector expressions over registers and immediates, loads, stores, and
conditions comparing two operands. An instruction set supplies only its register type, its
memory (with the checks its execution context makes), and a lift from its machine code.

The design is [`docs/design/Lprog.md`](../../docs/design/Lprog.md).

## Files

| file | contents |
| --- | --- |
| `Expr.lean` | Expressions over registers and immediates (`Width`, `UnOp`, `BinOp`, `Expr`) and their evaluation, generic in the register type. |
| `Syntax.lean` | Operands; call targets (a function, or an expression with candidates); instructions (`LinstrR`: operations, labels, gotos, conditional and indirect jumps, calls, tail calls, returns, external calls, `Labort`); functions with a stack bound (`Lfundef`); programs (`Lprog`). Operation and register types are parameters. |
| `Sem.lean` | `Isa`: operation and register types, link and stack registers, non-register state, and the meaning of operations and conditions. A state is a stack of frames (function, pc, return value, sp at the call), the registers and the rest. `step` is a relation whose outcomes are a state with the events the step made observable, `trap`, or `wrong`. A return goes `wrong` unless the link register and sp are as the call left them. The execution `Context` gives external calls (the only steps that produce events) and acceptance. `Isa.system` is the program as an `Ascent.System`, for refinement and equivalence. `Isa.SafeN` is `Ascent.SafeN` at this step with events forgotten, with one rule per instruction (`SafeN.opn`, `cond`, `call`, `tail`, `ret`, `ext`, ...). |
| `Op.lean` | The shared operations `Op` (`set`, `load`, `store`, `skip`), an ISA's memory `Mem`, conditions (`condEval`), and `Isa.ofOps`, the instruction set built from these operations and a memory. |
| `Text.lean` | A text format for programs over the shared operations. `print` gives a program's tokens and `parse` reads them back (`parse_print`). `toText` and `ofText` go through text; `lake exe decompile` checks the round trip when it writes. An instruction set names its registers with `RegText`. |
| `Build.lean` | Expressions and operations as lifts write them: short names, 0/1 values and selection by them, and operations the shared set lacks written out (byte and bit reversal, count leading zeros). |
| `Linked.lean` | The lift of a program as a compiler links it, for any instruction set (`liftProgram`): functions as runs of instructions at addresses, labels, calls and tail calls among them, computed jumps among the candidate addresses the program holds as values, and a label to give up at. An instruction set supplies the lift of one instruction. Not proved. |
| `Dead.lean` | `dropDead`: removes writes to registers an instruction set names (its flags) that nothing reads. Assumes nothing about code outside the function. Not proved. |
| `Block.lean` | `Isa.runStraight`, the operations of a straight-line piece run in order, and `SafeN.block`, which steps over the whole piece at once. |
| `Contract.lean` | `Isa.Contract`: a function's contract over the register file. |
| `Tactic.lean`, `LsymAttr.lean` | `lsym`: symbolic execution of a body, on every branch, up to a loop head, a call or a return's continuation; `lsym_simp`, the simp set it normalises with. See [`docs/design/Automation.md`](../../docs/design/Automation.md). |
| `Ascent/` | Generic runs, `SafeN`, refinement and equivalence (`Refines`, `Equivalent`), and correspondence (`Corres`); namespace `Lprog.Ascent`. See [`Ascent/README.md`](Ascent/README.md). |
| `ARM/Reg.lean`, `X86/Reg.lean` | AArch64 and x86-64 registers at Lprog, with their names (`RegText`); namespaces `Lprog.ARM`, `Lprog.X86`. |

## Adding an instruction set

An instruction set provides `Isa.ofOps Reg link sp M mem` (its registers, state and memory), a
lift from its decoded code to Lprog bodies, and a simulation that carries every Lprog run down
to its machine. A function is then proved by reasoning about its lifted body at Lprog, and the
result transfers to the machine.

| ISA | instance | lift | simulation |
| --- | --- | --- | --- |
| RISC-V | [`lprog-riscv`](../../lprog-riscv/README.md) | [`MachineChecked/RiscV/Lift`](../../MachineChecked/RiscV/Lift/README.md) | yes |
| AArch64 | `ARM/Reg.lean` | [`MachineChecked/ARM`](../../MachineChecked/ARM/README.md) | no |
| x86-64 | `X86/Reg.lean` | [`MachineChecked/X86`](../../MachineChecked/X86/README.md) | no |

## Worked examples (RISC-V)

- `Examples/Sp1Runtime/RiscV/Memcmp.lean`: a loop, for every length. A good first read.
- `Examples/Sp1Runtime/RiscV/WriteVectored.lean`: a loop, a call to another lifted function
  through its contract, a tail call and a system call.
- `Examples/Widths/RiscV/Proofs.lean`: loads and stores of every width.
- `MachineChecked/RiscV/Lift/Block.lean`: straight-line blocks, proved over the machine.

The layer above is the structured logical program (layer 1,
[`MachineChecked/Logical`](../../MachineChecked/Logical/README.md)), sketched in
[`docs/LogicalMachine.md`](../../docs/LogicalMachine.md).

## Provenance

The syntax is ported from catcrypt-compiler (licence:
[`Ascent/LICENSE-catcrypt`](Ascent/LICENSE-catcrypt)).
Its semantics there is tied to an x86 Jasmin interpreter, so `Sem.lean`, `Op.lean` and
`Expr.lean` are new, as are the call, tail-call, external-call and abort instructions.
