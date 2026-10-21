# Lprog

**Layer 0.5 of the [roadmap](../../ROADMAP.md): the low logical program.** Nothing here
depends on an instruction set.

Lprog is linear Jasmin: a body is a list of instructions (operations, labels, gotos,
conditional jumps, calls and returns). Labels replace addresses, and control flow is
explicit. It still has registers and flat memory. What makes it one language for every ISA:
control flow is shared, and so are the operations (`Op.lean`): bitvector expressions over
registers and immediates, loads, stores, and conditions comparing two operands. An
instruction set supplies only its register names, its memory (with the checks its execution
context makes), and a lift from its machine code.

## Files

| file | contents |
| --- | --- |
| `Syntax.lean` | Operands, instructions (`LinstrR`), bodies, functions, programs. The operation type is a parameter. |
| `Sem.lean` | `Isa`: an operation type, the state beside the registers, and the meaning of operations and conditions. `step` is shared control flow; runs are the generic ones of `../Ascent` (`Isa.Reaches`, `Isa.Halts`). |
| `Op.lean` | The shared operations: `Width`, `UnOp`, `BinOp`, `Expr`, `Op` (`set`, `load`, `store`, `skip`), an ISA's memory `Mem`, conditions (`condEval`), and `Isa.ofOps`, the instruction set over these operations and a memory. |

## Using it

An instruction set joins by giving `Isa.ofOps M mem` (its state and memory), a lift from its
decoded code to Lprog bodies, and a simulation that carries every Lprog run down to its
machine. RISC-V's is [`../RiscV/Lprog`](../RiscV/Lprog/README.md). A function is then proved
by running its lifted body at Lprog, and the result transfers to the machine.

Worked examples, all RISC-V:
- `Cases/Zip2005/Runtime/MemcmpLprog.lean`: a loop, for every length. A good first read.
- `Cases/Zip2005/Runtime/WriteVectored.lean`: a loop and a call out of the function.
- `Cases/Zip2005/Runtime/BlackBox.lean`: a store and a load through the stack.
- `Cases/CatCrypt/`: straight-line kernels (`RiscV/Lprog/Block.lean`).

Above this layer is the structured logical program (layer 1, `../Logical`), not started;
`docs/LogicalMachine.md` sketches it.

The syntax is ported from catcrypt-compiler (see `../Ascent/LICENSE-catcrypt`). Its semantics
there is tied to an x86 Jasmin interpreter, so `Sem.lean` and `Op.lean` are new.
