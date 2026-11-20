/-
  The case studies' axiom check, run by CI (`.github/workflows/ci.yml`) after the case studies
  are built. The same rule as `AxiomCheck.lean`: only `propext`, `Classical.choice`,
  `Quot.sound` and `bv_decide`'s certificate axioms.
-/

import Cases.Hardening
import Cases.LeanVM.Blake2s.Loaded

-- functions of an SP1 guest's runtime, proved with `lsym` and carried to the machine
#print axioms Cases.Hardening.Memcmp.contract
#print axioms Cases.Hardening.Memcmp.safe
#print axioms Cases.Hardening.WriteVectored.scw_spec
#print axioms Cases.Hardening.WriteVectored.sw_spec
#print axioms Cases.Hardening.WriteVectored.contract
#print axioms Cases.Hardening.WriteVectored.spec

-- leanVM's Blake2s guest: the loaded image
#print axioms Cases.LeanVM.Blake2s.Loaded.codeWF
