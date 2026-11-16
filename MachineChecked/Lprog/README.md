# Lprog

**Layer 0.5 of the [roadmap](../../ROADMAP.md): the low logical program.** Nothing here
depends on an instruction set.

Lprog is linear Jasmin: a body is a list of instructions (operations, labels, gotos,
conditional jumps, calls, tail calls, returns and external calls). Labels replace addresses,
and control flow is explicit. It still has registers and flat memory. What makes it one language for every ISA:
control flow is shared, and so are the operations (`Op.lean`): bitvector expressions over
registers and immediates, loads, stores, and conditions comparing two operands. An
instruction set supplies only its register type, its memory (with the checks its execution
context makes), and a lift from its machine code.

## Files

| file | contents |
| --- | --- |
| `Expr.lean` | Expressions over registers and immediates: `Width`, `UnOp`, `BinOp`, `Expr`, and their evaluation. Generic in the register type. |
| `Syntax.lean` | Operands, call targets (a function, or an expression with candidates), instructions (`LinstrR`: operations, labels, gotos, conditional and indirect jumps, calls, tail calls, returns, external calls, `Labort`), functions with a stack bound (`Lfundef`), programs (`Lprog`). The operation and register types are parameters. |
| `Sem.lean` | `Isa`: the operation and register types, the link and stack registers, the state beside the registers, and the meaning of operations and conditions. A state is a stack of frames (function, pc, return value, sp at the call), the registers and the rest. `step` is a relation whose outcomes are a state with the events the step made observable, `trap` or `wrong`; a return goes `wrong` unless the link register and sp are as the call left them. The execution `Context` gives external calls, the only steps that make events, and accepting. `Isa.system` is the program as an `Ascent.System`, for refinement and equivalence. `Isa.SafeN` is `Ascent.SafeN` at this step with its events forgotten, with one rule per instruction (`SafeN.opn`, `cond`, `call`, `tail`, `ret`, `ext`, …). |
| `Text.lean` | A text format for programs over the shared operations. `print` gives a program's tokens and `parse` reads them back (`parse_print`); `toText` and `ofText` are the same through text, with the round trip checked by the tool that writes it (`lake exe decompile`). An instruction set names its registers (`RegText`). |
| `Op.lean` | The shared operations: `Op` (`set`, `load`, `store`, `skip`), an ISA's memory `Mem`, conditions (`condEval`), and `Isa.ofOps`, the instruction set over these operations and a memory. |
| `Build.lean` | Expressions and operations as the lifts write them: short names, values that are 0 or 1 and the choice by one, and what the shared operations lack written out in them (a reversal of bytes or bits, a count of leading zeros). |
| `Linked.lean` | The lift of a program as a compiler links it, for any instruction set (`liftProgram`): functions as runs of instructions at addresses, labels, calls and tail calls among them, computed jumps among the candidates the program holds as values, and a label to give up at. An instruction set gives the lift of one instruction. Nothing is proved of it yet. |
| `Dead.lean` | `dropDead`: a body without the writes, to registers an instruction set names (its flags), that nothing reads. It assumes nothing of what is outside the function. Nothing is proved of it yet. |

## Using it

An instruction set joins by giving `Isa.ofOps Reg link sp M mem` (its registers, state and memory), a lift from its
decoded code to Lprog bodies, and a simulation that carries every Lprog run down to its
machine. RISC-V's is [`../RiscV/Lprog`](../RiscV/Lprog/README.md). AArch64
([`../ARM/Lprog`](../ARM/README.md)) and x86-64 ([`../X86/Lprog`](../X86/README.md)) have their
registers and their lift, for `decompile`, and no simulation yet. A function is then proved
by running its lifted body at Lprog, and the result transfers to the machine.

Worked examples, all RISC-V:
- `Cases/Zip2005/Runtime/MemcmpLprog.lean`: a loop, for every length. A good first read.
- `Cases/Zip2005/Runtime/WriteVectored.lean`: a loop, a call to another lifted function
  through its contract, a tail call and a system call.
- `Cases/Zip2005/Runtime/BlackBox.lean`: a store and a load through the stack.
- `Cases/CatCrypt/`: straight-line kernels (`RiscV/Lprog/Block.lean`, over the machine).

Above this layer is the structured logical program (layer 1, `../Logical`), not started;
`docs/LogicalMachine.md` sketches it.

The syntax is ported from catcrypt-compiler (see `../Ascent/LICENSE-catcrypt`). Its semantics
there is tied to an x86 Jasmin interpreter, so `Sem.lean`, `Op.lean` and `Expr.lean` are new;
the call, tail-call, external-call and abort instructions are new too. `docs/design/Lprog.md`
is the design.
