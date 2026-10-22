# RiscV/Lprog

**The lift from layer 0 to layer 0.5 for RISC-V** (lift 1 of the
[roadmap](../../../ROADMAP.md)): riscv-zkvm's decoded instructions into the low logical
program, with the theorem that anything proved of the lifted program holds of the machine.

| file | contents |
| --- | --- |
| `Instance.lean` | `rvIsa`, RISC-V on SP1 as `Isa.ofOps`: registers `x0`..`x31`, memory `rvMem` (riscv-zkvm's, behind SP1's check). `opOf` translates each instruction that does not transfer control into a shared operation; `opOf_spec` proves the translation agrees with riscv-zkvm's `execInstrBr`, and fails exactly when `memOkSp1` does. `Agree` says when two machine states look the same to an instruction. |
| `Lift.lean` | `lift`: a decoded function becomes an Lprog body. `Sim` relates Lprog states to machine states; the simulation (`sim_step`, `sim_steps`) carries every Lprog run down to `stepSp1` (`reach_of_reaches`, `reach_of_halts`, `SafeN.of_lift`). The rules for running a body (`reaches_label`, `reaches_opn`, `reaches_cond`, `reaches_goto`, `halts_ret`), and `sim_return` for resuming after a call out of the function. |
| `Block.lean` | Straight-line code through the lift: a pure block runs at Lprog to the fold of `execInstrBr` (`reaches_pure`), carried down as `reaches_block` and as a correspondence, `corres_block`. The registers of a block as one named value per instruction (`stepRegs`, `regs_run`), for `bv_decide`. |

What the lift covers today: straight-line operations, conditional branches, `jal x0` (a
jump) and `jalr x0, 0(ra)` (a return). Anything else (calls, indirect jumps, system calls)
lifts to an instruction with no step, so a run at Lprog stops there; a call is taken over
the machine with the callee's specification, and `sim_return` resumes at Lprog after it.
Lifting calls, indirect jumps (with candidate lists) and system calls (as external calls with
specifications) is the next step of the roadmap.
