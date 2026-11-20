/-
  The examples' axiom check, run by CI (`.github/workflows/ci.yml`) after they are built. The
  same rule as `AxiomCheck.lean`: only `propext`, `Classical.choice`, `Quot.sound` and
  `bv_decide`'s certificate axioms. Each function's theorem over the machine is printed; its
  contract at Lprog is under it.
-/

import Examples

-- the ladder
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
#print axioms Examples.ChaCha20.RiscV.chacha20_block_correct
-- Examples/Sha256/RiscV/Proofs.lean
#print axioms Examples.Sha256.RiscV.sha256_schedule_correct
#print axioms Examples.Sha256.RiscV.sha256_round_correct
#print axioms Examples.Sha256.RiscV.sha256_compress_correct

-- stress tests
-- Examples/Branches/RiscV/Proofs.lean
#print axioms Examples.Branches.RiscV.add3_correct
#print axioms Examples.Branches.RiscV.max2_correct
#print axioms Examples.Branches.RiscV.umax2_correct
#print axioms Examples.Branches.RiscV.clamp_correct
#print axioms Examples.Branches.RiscV.sum_correct
#print axioms Examples.Branches.RiscV.count_down_correct
-- Examples/BranchesO0/RiscV/Proofs.lean
#print axioms Examples.BranchesO0.RiscV.add3_correct
#print axioms Examples.BranchesO0.RiscV.max2_correct
#print axioms Examples.BranchesO0.RiscV.umax2_correct
#print axioms Examples.BranchesO0.RiscV.clamp_correct
#print axioms Examples.BranchesO0.RiscV.count_down_correct
#print axioms Examples.BranchesO0.RiscV.sum_correct
-- Examples/Widths/RiscV/Proofs.lean
#print axioms Examples.Widths.RiscV.set_bytes_correct
#print axioms Examples.Widths.RiscV.copy_bytes_correct
#print axioms Examples.Widths.RiscV.str_len_correct
#print axioms Examples.Widths.RiscV.load_s8_correct
#print axioms Examples.Widths.RiscV.load_u8_correct
#print axioms Examples.Widths.RiscV.load_s16_correct
#print axioms Examples.Widths.RiscV.load_u16_correct
#print axioms Examples.Widths.RiscV.load_s32_correct
#print axioms Examples.Widths.RiscV.load_u32_correct
#print axioms Examples.Widths.RiscV.store_widths_correct
#print axioms Examples.Widths.RiscV.read_le32_correct
#print axioms Examples.Widths.RiscV.swap_correct
-- Examples/Arith/RiscV/Proofs.lean
#print axioms Examples.Arith.RiscV.gives_correct
#print axioms Examples.Arith.RiscV.sdiv_correct
#print axioms Examples.Arith.RiscV.srem_correct
#print axioms Examples.Arith.RiscV.udiv_correct
#print axioms Examples.Arith.RiscV.mulhi_correct
#print axioms Examples.Arith.RiscV.smulhi_correct
#print axioms Examples.Arith.RiscV.rotl_correct
#print axioms Examples.Arith.RiscV.popcount_correct
#print axioms Examples.Arith.RiscV.abs_branchless_correct
-- Examples/Calls/RiscV/Proofs.lean
#print axioms Examples.Calls.RiscV.inc_correct
#print axioms Examples.Calls.RiscV.twice_inc_correct
#print axioms Examples.Calls.RiscV.fact_correct
#print axioms Examples.Calls.RiscV.tail_inc_correct
#print axioms Examples.Calls.RiscV.checked_div_correct
#print axioms Examples.Calls.RiscV.apply_correct
#print axioms Examples.Calls.RiscV.apply_inc_correct
#print axioms Examples.Calls.RiscV.sum4_correct
#print axioms Examples.Calls.RiscV.keep_correct
-- Examples/CallsO0/RiscV/Proofs.lean
#print axioms Examples.CallsO0.RiscV.inc_correct
#print axioms Examples.CallsO0.RiscV.twice_inc_correct
#print axioms Examples.CallsO0.RiscV.sum4_correct
#print axioms Examples.CallsO0.RiscV.checked_div_correct
#print axioms Examples.CallsO0.RiscV.apply_correct
#print axioms Examples.CallsO0.RiscV.apply_inc_correct
#print axioms Examples.CallsO0.RiscV.tail_inc_correct
#print axioms Examples.CallsO0.RiscV.keep_correct
#print axioms Examples.CallsO0.RiscV.fact_correct
-- Examples/Rec/RiscV/Proofs.lean
#print axioms Examples.Rec.RiscV.fib_correct
-- Examples/Switch/RiscV/Proofs.lean
#print axioms Examples.Switch.RiscV.classify_correct
-- Examples/Big/RiscV/Proofs.lean
#print axioms Examples.Big.RiscV.mix_correct

-- guest code: an SP1 guest's runtime
-- Examples/Sp1Runtime/RiscV/Memcmp.lean
#print axioms Examples.Sp1Runtime.RiscV.Memcmp.memcmp_correct
-- Examples/Sp1Runtime/RiscV/WriteVectored.lean
#print axioms Examples.Sp1Runtime.RiscV.WriteVectored.write_vectored_correct
-- Examples/Sp1Runtime/RiscV/Udivti3.lean
#print axioms Examples.Sp1Runtime.RiscV.Udivti3.udivti3_correct

-- leanVM's Blake2s guest: the loaded image
#print axioms Examples.LeanVM.Blake2s.Loaded.codeWF
