# RiscV/Lift

**The lift from layer 0 to layer 0.5 for RISC-V** (lift 1 of the
[roadmap](../../../ROADMAP.md)): riscv-zkvm's decoded instructions into the low logical
program, with the theorems that anything proved of the lifted program holds of the machine,
and that the two are equivalent to an observer.

What a proof at Lprog needs of RISC-V is in the package
[`lprog-riscv`](../../../lprog-riscv/README.md), not here: RISC-V as an instruction set of Lprog
(`rvIsa`, `opOf` and `opOf_spec`, `Agree`), SP1's execution context (`sp1Ctx`) and
`sp1Ecall_agree`.

| file | contents |
| --- | --- |
| `Lift.lean` | `Fn` (a function: name, base address, decoded instructions, stack bound) and `liftProg`: every function becomes an Lprog body. Branches and `jal x0` become gotos, `jal ra` and `jalr ra` calls, `jalr x0` to a function a tail call, `jalr x0, 0(ra)` a return, `ecall` an external call, and anything else `Labort`. `LSafeN fs` is the judgement for the lifted program, under SP1's execution context (`sp1Ctx`, in `lprog-riscv`). |
| `Transfer.lean` | The simulation (`Sim`, `back_step`) and the transfer theorem: `SafeN` at Lprog for every budget gives `SafeN` over `stepSp1` (`transfer`). For a call of one function: `SafeN.of_lift`, and `SafeN.of_contract`, which turns a contract at Lprog into the machine-level continuation form callers use. |
| `Equiv.lean` | The lift as an equivalence (`Ascent.Equivalent`). The machine, as a system that stops where the outermost function returns (`msys`), refines the lifted program, with `wrong` at Lprog as undefined behaviour (`refines_lift`); a lifted program that never goes `wrong` refines the machine (`lift_refines`). From a function's entry: `equivalent_of_entry`. |
| `Flat.lean` | The lift of code without functions (`Code.liftFlat`): one body, `jal` as a goto or an external call, `jalr` as an indirect jump among the addresses the code forms. For code that does not follow the calling convention, such as Flapjack's. Nothing is proved of it yet. |
| `Decode.lean` | A word of code, decoded for the two lifts of whole binaries (`decodeWord`): riscv-zkvm's instruction, or one of the nine 32-bit operations of RV64IM its `Instr` lacks (`addw`, `sllw`, `sraw`, `sraiw`, `mulw`, `divw`, `divuw`, `remw`, `remuw`), as a shared operation. |
| `Whole.lean` | The lift of a program as a compiler links it (`Whole.liftWhole`), by the lift of linked programs that every instruction set shares (`Lprog/Linked.lean` in the package `lprog`): what `liftProg` does, and far calls (`auipc` then `jalr`), jump tables, indirect calls and tail calls among all functions, calls that link through another register than `ra`, and words that are no instruction. For what rustc emits. Nothing is proved of it yet. |
| `Table.lean` | The instructions of RV64IM by kind, each with whether the lift of whole programs takes it, said by the lift itself: the table of [`../LIMITS.md`](../LIMITS.md). |
| `Rules.lean` | One rule per lifted instruction, stated on the machine state the Lprog state stands for: `lsafe_opn`, `lsafe_auipc`, `lsafe_cond`, `lsafe_ret`, `lsafe_call`, `lsafe_tail`, and SP1's `WRITE` (`lsafe_write`). |
| `Block.lean` | Straight-line code: a pure block reaches the fold of `execInstrBr` over the machine (`reaches_block`), and as a correspondence, `corres_block`. The registers of a block as one named value per instruction (`stepRegs`, `regs_run`), for `bv_decide`. |

A proof states a contract for a function at Lprog (`∀ G n Q`, a precondition, and a
continuation from every state after the return), proves it with the generic rules
(`Lprog.SafeN.label`, `goto`, …) and the rules above, and transfers it with
`SafeN.of_contract`. A call to another lifted function uses that function's contract.
`Cases/Zip2005/Runtime/WriteVectored.lean` is the worked example.

Straight-line blocks are proved over the machine, not through the lift: a lifted program
cannot yet hand control back to code outside it. `docs/design/Lprog.md` (As built) lists this
and the other departures from the design.
