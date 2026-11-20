# RiscV/Lift

Lift 1 for RISC-V (layer 0 to layer 0.5 of the [roadmap](../../../ROADMAP.md)): riscv-zkvm's
decoded instructions into Lprog, with proofs that anything proved of the lifted program holds
of the machine, and that the two are equivalent to an observer.

What a proof at Lprog needs of RISC-V is in the package
[`lprog-riscv`](../../../lprog-riscv/README.md): RISC-V as an Lprog instruction set (`rvIsa`,
`opOf` and `opOf_spec`, `Agree`), SP1's execution context (`sp1Ctx`), and `sp1Ecall_agree`.

## Proved

| file | contents |
| --- | --- |
| `Lift.lean` | `Fn` (a function: name, base address, decoded instructions, stack bound) and `liftProg`, which makes every function an Lprog body. Branches and `jal x0` become gotos; `jal ra` and `jalr ra` calls; `jalr x0` to a function a tail call; `jalr x0, 0(ra)` a return; `ecall` an external call; anything else `Labort`. `LSafeN fs` is the judgement for the lifted program under SP1's context (`sp1Ctx`). |
| `Transfer.lean` | The simulation (`Sim`, `back_step`) and the transfer theorem `transfer`: `SafeN` at Lprog for every budget gives `SafeN` over `stepSp1`. For a call of one function: `SafeN.of_lift`, and `SafeN.of_contract`, which turns a contract at Lprog into the continuation form callers use at machine level. |
| `Contract.lean` | A contract at Lprog (`Isa.Contract`, as `lsym` proves it), over the machine: `Loaded fs s` (the functions of `fs` are in the code of `s`, each at its address) and `SafeN.of_isa_contract`, which takes the contract as it is, with its precondition read off the machine's registers and memory. |
| `Equiv.lean` | The lift as an equivalence (`Ascent.Equivalent`). The machine, as a system that stops when the outermost function returns (`msys`), refines the lifted program, with `wrong` at Lprog as undefined behaviour (`refines_lift`). A lifted program that never goes `wrong` refines the machine (`lift_refines`). From a function's entry: `equivalent_of_entry`. |
| `Rules.lean` | One rule per lifted instruction, stated on the machine state the Lprog state represents: `lsafe_opn`, `lsafe_auipc`, `lsafe_cond`, `lsafe_ret`, `lsafe_call`, `lsafe_tail`, and SP1's `WRITE` (`lsafe_write`). |
| `Block.lean` | Straight-line code over the machine: a pure block reaches the fold of `execInstrBr` (`reaches_block`), and as a correspondence, `corres_block`. The registers of a block as one named value per instruction (`stepRegs`, `regs_run`), for `bv_decide`. |

## Not proved (used by the decompiler)

| file | contents |
| --- | --- |
| `Whole.lean` | The lift of a program as a compiler links it (`Whole.liftWhole`), for rustc output. Built on the shared lift of linked programs (`Lprog/Linked.lean` in [`lprog`](../../../lprog/README.md)). Beyond `liftProg` it handles far calls (`auipc` then `jalr`), jump tables, indirect calls and tail calls among all functions, calls that link through a register other than `ra`, and words that are not instructions. |
| `Flat.lean` | The lift of code without functions (`Code.liftFlat`): one body, `jal` as a goto or an external call, `jalr` as an indirect jump among the addresses the code computes. For code that does not follow the calling convention, such as Flapjack's. |
| `Decode.lean` | Decoding a word for the two whole-binary lifts (`decodeWord`): riscv-zkvm's instruction, or one of the nine RV64IM 32-bit operations its `Instr` lacks (`addw`, `sllw`, `sraw`, `sraiw`, `mulw`, `divw`, `divuw`, `remw`, `remuw`), as a shared operation. Tested against SP1's executor. |
| `Table.lean` | Each RV64IM instruction kind and whether the whole-program lift takes it, computed from the lift. Generates the table in [`../LIMITS.md`](../LIMITS.md). |

## Writing a proof through the lift

State a contract for a function at Lprog (`∀ G n Q`, a precondition, and a continuation from
every state after the return). Prove it with the generic rules (`Lprog.SafeN.label`, `goto`,
...) and the rules above, or with `lsym` applying them. A contract stated as an `Isa.Contract`
goes to the machine by `SafeN.of_isa_contract` (`Contract.lean`); one with a postcondition
over a machine state by `SafeN.of_contract`. A call to another lifted function uses that
function's contract. The worked examples are [`docs/Walkthrough.md`](../../../docs/Walkthrough.md)
(`gcd`, through `SafeN.of_isa_contract`) and `Cases/Hardening/WriteVectored.lean` (a loop, a
call and a system call, through `SafeN.of_contract`).

Straight-line blocks are proved over the machine, not through the lift, because a lifted
program cannot yet return control to code outside it. The "As built" section of
[`docs/design/Lprog.md`](../../../docs/design/Lprog.md) lists this and the other departures
from the design.
