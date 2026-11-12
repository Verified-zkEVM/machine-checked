/-
  The axiom check run by CI (`.github/workflows/ci.yml`).

  `#print axioms` on the main theorems of the framework and of the quick case studies. CI
  fails if any of them depends on an axiom other than `propext`, `Classical.choice`,
  `Quot.sound`, or the certificate axioms `bv_decide` adds. Add a theorem here when it
  becomes a main result.
-/

import MachineChecked
import Cases.CatCrypt
import Cases.Zip2005.Runtime.MemcmpLprog
import Cases.Zip2005.Runtime.WriteVectored
import Cases.Zip2005.Runtime.BlackBox

-- the lift
#print axioms MachineChecked.RiscV.Lprog.opOf_spec
#print axioms MachineChecked.RiscV.Lprog.transfer
#print axioms MachineChecked.RiscV.Lprog.SafeN.of_lift
#print axioms MachineChecked.RiscV.Lprog.SafeN.of_contract
#print axioms MachineChecked.RiscV.Lprog.lsafe_call
#print axioms MachineChecked.RiscV.Lprog.lsafe_write
#print axioms MachineChecked.RiscV.Lprog.corres_block

-- the CatCrypt kernels
#print axioms Cases.CatCrypt.Cswap.corres
#print axioms Cases.CatCrypt.AddP256.corres
#print axioms Cases.CatCrypt.FeAdd.corres
#print axioms Cases.CatCrypt.FeSub.corres

-- zip-2005 functions proved through the lift
#print axioms Cases.Zip2005.MemcmpLprog.safe
#print axioms Cases.Zip2005.WriteVectored.contract
#print axioms Cases.Zip2005.WriteVectored.spec
#print axioms Cases.Zip2005.black_box_spec
