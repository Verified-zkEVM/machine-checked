/-
  The case studies' axiom check, run by CI's on-demand `full` job (`.github/workflows/ci.yml`),
  after the case studies are built. The same rule as `AxiomCheck.lean`: only `propext`,
  `Classical.choice`, `Quot.sound` and `bv_decide`'s certificate axioms.
-/

import Cases.CatCrypt
import Cases.Zip2005.Runtime.MemcmpLprog
import Cases.Zip2005.Runtime.WriteVectored
import Cases.Zip2005.Runtime.BlackBox

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
