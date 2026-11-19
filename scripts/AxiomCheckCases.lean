/-
  The examples' and the case studies' axiom check, run by CI (`.github/workflows/ci.yml`) after
  they are built. The same rule as `AxiomCheck.lean`: only `propext`, `Classical.choice`,
  `Quot.sound` and `bv_decide`'s certificate axioms.
-/

import Examples
import Cases.Hardening
import Cases.LeanVM.Blake2s.Loaded

-- the examples: each function's theorem over the machine (its contract is under it)
-- Examples/Basic.lean
#print axioms Examples.Basic.add3_correct
#print axioms Examples.Basic.max_u64_correct
#print axioms Examples.Basic.sum_to_correct

-- Examples/Memory.lean
#print axioms Examples.Memory.swap_correct
#print axioms Examples.Memory.sum_array_correct
#print axioms Examples.Memory.max2_correct
#print axioms Examples.Memory.max3_correct

-- Examples/Bytes.lean
#print axioms Examples.Bytes.str_len_correct
#print axioms Examples.Bytes.fill_correct
#print axioms Examples.Bytes.count_ones_correct

-- Examples/RustBasic.lean
#print axioms Examples.RustBasic.add3_correct
#print axioms Examples.RustBasic.max_u64_correct
#print axioms Examples.RustBasic.gcd_correct
#print axioms Examples.RustBasic.sum_slice_correct

-- Examples/Mem.lean
#print axioms Examples.Mem.copy_bytes_correct
#print axioms Examples.Mem.equal_bytes_correct

-- Examples/Limbs.lean
#print axioms Examples.Limbs.add_limbs_correct

-- Examples/Crc32.lean
#print axioms Examples.Crc32.crc32_correct

-- Examples/ChaCha20.lean
#print axioms Examples.ChaCha20.quarter_round_correct

-- Examples/Sha256.lean
#print axioms Examples.Sha256.sha256_round_correct

-- functions of an SP1 guest's runtime, proved with `lsym` and carried to the machine
#print axioms Cases.Hardening.Memcmp.contract
#print axioms Cases.Hardening.Memcmp.safe
#print axioms Cases.Hardening.WriteVectored.scw_spec
#print axioms Cases.Hardening.WriteVectored.sw_spec
#print axioms Cases.Hardening.WriteVectored.contract
#print axioms Cases.Hardening.WriteVectored.spec

-- leanVM's Blake2s guest: the loaded image
#print axioms Cases.LeanVM.Blake2s.Loaded.codeWF
