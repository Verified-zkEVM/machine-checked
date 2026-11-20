/-
  The examples' axiom check, run by CI (`.github/workflows/ci.yml`) after
  they are built. The same rule as `AxiomCheck.lean`: only `propext`, `Classical.choice`,
  `Quot.sound` and `bv_decide`'s certificate axioms.
-/

import Examples

-- the ladder: each function's theorem over the machine (its contract is under it)
-- Examples/Basic/RiscV/Proofs.lean
#print axioms Examples.Basic.RiscV.add3_correct
#print axioms Examples.Basic.RiscV.max_u64_correct
#print axioms Examples.Basic.RiscV.sum_to_correct

-- Examples/Memory/RiscV/Proofs.lean
#print axioms Examples.Memory.RiscV.swap_correct
#print axioms Examples.Memory.RiscV.sum_array_correct
#print axioms Examples.Memory.RiscV.max2_correct
#print axioms Examples.Memory.RiscV.max3_correct

-- Examples/Bytes/RiscV/Proofs.lean
#print axioms Examples.Bytes.RiscV.str_len_correct
#print axioms Examples.Bytes.RiscV.fill_correct
#print axioms Examples.Bytes.RiscV.count_ones_correct

-- Examples/RustBasic/RiscV/Proofs.lean
#print axioms Examples.RustBasic.RiscV.add3_correct
#print axioms Examples.RustBasic.RiscV.max_u64_correct
#print axioms Examples.RustBasic.RiscV.gcd_correct
#print axioms Examples.RustBasic.RiscV.sum_slice_correct

-- Examples/Mem/RiscV/Proofs.lean
#print axioms Examples.Mem.RiscV.copy_bytes_correct
#print axioms Examples.Mem.RiscV.equal_bytes_correct

-- Examples/Limbs/RiscV/Proofs.lean
#print axioms Examples.Limbs.RiscV.add_limbs_correct

-- Examples/Crc32/RiscV/Proofs.lean
#print axioms Examples.Crc32.RiscV.crc32_correct

-- Examples/ChaCha20/RiscV/Proofs.lean
#print axioms Examples.ChaCha20.RiscV.quarter_round_correct

-- Examples/Sha256/RiscV/Proofs.lean
#print axioms Examples.Sha256.RiscV.sha256_round_correct
#print axioms Examples.Sha256.RiscV.sha256_schedule_correct

-- guest code (`Examples/Sp1Runtime`): functions of an SP1 guest's runtime, proved with `lsym`
-- and carried to the machine
#print axioms Examples.Sp1Runtime.RiscV.Memcmp.contract
#print axioms Examples.Sp1Runtime.RiscV.Memcmp.safe
#print axioms Examples.Sp1Runtime.RiscV.WriteVectored.scw_spec
#print axioms Examples.Sp1Runtime.RiscV.WriteVectored.sw_spec
#print axioms Examples.Sp1Runtime.RiscV.WriteVectored.contract
#print axioms Examples.Sp1Runtime.RiscV.WriteVectored.spec

-- leanVM's Blake2s guest: the loaded image
#print axioms Examples.LeanVM.Blake2s.Loaded.codeWF
