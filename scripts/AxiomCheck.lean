/-
  The axiom check run by CI (`.github/workflows/ci.yml`).

  `#print axioms` on the main theorems of the framework. CI fails if any of them depends on
  an axiom other than `propext`, `Classical.choice`, `Quot.sound`, or the certificate axioms
  `bv_decide` adds. Add a theorem here when it becomes a main result. The case studies' main
  theorems are in `AxiomCheckCases.lean`, run by CI's on-demand `full` job.
-/

import MachineChecked

-- the lift
#print axioms MachineChecked.RiscV.Lprog.opOf_spec
#print axioms MachineChecked.RiscV.Lprog.transfer
#print axioms MachineChecked.RiscV.Lprog.SafeN.of_lift
#print axioms MachineChecked.RiscV.Lprog.SafeN.of_contract
#print axioms MachineChecked.RiscV.Lprog.lsafe_call
#print axioms MachineChecked.RiscV.Lprog.lsafe_write
#print axioms MachineChecked.RiscV.Lprog.corres_block
