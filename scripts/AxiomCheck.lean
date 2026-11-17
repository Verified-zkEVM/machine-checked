/-
  The axiom check run by CI (`.github/workflows/ci.yml`).

  `#print axioms` on the main theorems of the framework. CI fails if any of them depends on
  an axiom other than `propext`, `Classical.choice`, `Quot.sound`, or the certificate axioms
  `bv_decide` adds. Add a theorem here when it becomes a main result. The case studies' main
  theorems are in `AxiomCheckCases.lean`, run by CI's on-demand `full` job.
-/

import MachineChecked
import Tools.ToLean
import LprogRiscV.Lsym
import Tools.Test.Lsym
import Tools.Test.LsymX86

-- the lift
#print axioms Lprog.parse_print
#print axioms Lprog.RiscV.opOf_spec
#print axioms MachineChecked.RiscV.Lift.transfer
#print axioms MachineChecked.RiscV.Lift.SafeN.of_lift
#print axioms MachineChecked.RiscV.Lift.SafeN.of_contract
#print axioms Lprog.RiscV.sp1Ecall_agree
#print axioms MachineChecked.RiscV.Lift.refines_lift
#print axioms MachineChecked.RiscV.Lift.lift_refines
#print axioms MachineChecked.RiscV.Lift.equivalent_of_entry
#print axioms MachineChecked.RiscV.Lift.lsafe_call
#print axioms MachineChecked.RiscV.Lift.lsafe_write
#print axioms MachineChecked.RiscV.Lift.corres_block

-- decompile --to lean: a function's theorem from its parts
#print axioms Tools.ToLean.flatten_chunks
#print axioms Tools.ToLean.getElem?_eq_of_chunks

-- lsym: a straight-line block in one step, and the rules in the form the tactic applies
#print axioms Lprog.SafeN.block
#print axioms Lprog.SafeN.opn'
#print axioms Lprog.SafeN.cond'
#print axioms Lprog.SafeN.call_contract
#print axioms Lprog.SafeN.tail_contract

-- contracts over the register file, and calls through them, on two instruction sets
#print axioms Lprog.Isa.Contract.run
#print axioms Lprog.RiscV.contract_of_agree
#print axioms Tools.Test.Lsym.f_contract
#print axioms Tools.Test.LsymX86.p_eq
#print axioms Tools.Test.LsymX86.f_contract
