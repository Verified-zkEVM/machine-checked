/-
  The axioms of the contracts proved here. CI allows Lean's three and the certificates of
  `bv_decide`, as for the rest of the repository (`scripts/AxiomCheck.lean`).
-/

import LeanVerifiers

open LeanVerifiers.ARM

#print axioms memcpy_contract
#print axioms keccak_f_contract
