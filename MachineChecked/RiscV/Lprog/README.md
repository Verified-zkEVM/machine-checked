# RiscV/Lprog

**The lift from layer 0 to layer 0.5 for RISC-V** (lift 1 of the
[roadmap](../../../ROADMAP.md)): riscv-zkvm's decoded instructions into the low logical
program, with the theorems that anything proved of the lifted program holds of the machine,
and that the two are equivalent to an observer.

| file | contents |
| --- | --- |
| `Instance.lean` | `rvIsa`, RISC-V on SP1 as `Isa.ofOps`: riscv-zkvm's own `Reg`, `ra` as the link register, `sp` as the stack register, and memory `rvMem` (riscv-zkvm's, behind SP1's check). `opOf` translates each instruction that does not transfer control into a shared operation; `opOf_spec` proves the translation agrees with riscv-zkvm's `execInstrBr`, and fails exactly when `memOkSp1` does. `Agree` says when two machine states look the same to an instruction. The registers' names in Lprog text are `x0` to `x31`. |
| `Lift.lean` | `Fn` (a function: name, base address, decoded instructions, stack bound) and `liftProg`: every function becomes an Lprog body. Branches and `jal x0` become gotos, `jal ra` and `jalr ra` calls, `jalr x0` to a function a tail call, `jalr x0, 0(ra)` a return, `ecall` an external call, and anything else `Labort`. `sp1Ctx` is SP1's execution context: an external call steps as riscv-zkvm's `sp1Ecall`, and `HALT` with exit code 0 accepts. `LSafeN fs` is the judgement for the lifted program. |
| `Transfer.lean` | The simulation (`Sim`, `back_step`) and the transfer theorem: `SafeN` at Lprog for every budget gives `SafeN` over `stepSp1` (`transfer`). For a call of one function: `SafeN.of_lift`, and `SafeN.of_contract`, which turns a contract at Lprog into the machine-level continuation form callers use. |
| `Ecall.lean` | SP1's `ecall` cannot tell agreeing machine states apart (`sp1Ecall_agree`): every reader it uses sees only what `Agree` fixes, and every writer keeps `Agree`. |
| `Equiv.lean` | The lift as an equivalence (`Ascent.Equivalent`). The machine, as a system that stops where the outermost function returns (`msys`), refines the lifted program, with `wrong` at Lprog as undefined behaviour (`refines_lift`); a lifted program that never goes `wrong` refines the machine (`lift_refines`). From a function's entry: `equivalent_of_entry`. |
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
