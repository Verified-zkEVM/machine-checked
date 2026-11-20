/-
  The axiom check run by CI (`.github/workflows/ci.yml`).

  `#print axioms` on the main theorems of the framework. CI fails if any of them depends on
  an axiom other than `propext`, `Classical.choice`, `Quot.sound`, or the certificate axioms
  `bv_decide` adds. Add a theorem here when it becomes a main result. The case studies' main
  theorems are in `AxiomCheckCases.lean`.
-/

import MachineChecked
import Tools.ToLean
import LprogRiscV.Lsym
import Tools.Test.Lsym
import Tools.Test.LsymX86
import Cases.Hardening

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
#print axioms Lprog.addr_neg_add_cancel
#print axioms Lprog.addr_add_neg_cancel
#print axioms Lprog.SafeN.label_spend
#print axioms Lprog.ult_eq_false
#print axioms Lprog.ule_eq_false
#print axioms Lprog.addr_ofNat_shl
#print axioms Lprog.SafeN.call_contract
#print axioms Lprog.SafeN.tail_contract

-- contracts over the register file, and calls through them, on two instruction sets
#print axioms Lprog.Isa.Contract.run
#print axioms Lprog.RiscV.contract_of_agree
#print axioms Tools.Test.Lsym.f_contract
#print axioms Tools.Test.LsymX86.p_eq
#print axioms Tools.Test.LsymX86.f_contract

-- the hardening examples (`Cases/Hardening`)
#print axioms Cases.Hardening.Basics.sum_spec
#print axioms Cases.Hardening.Basics.count_down_spec
#print axioms Cases.Hardening.Mem.swap_spec
#print axioms Cases.Hardening.Arith.sdiv_spec
#print axioms Cases.Hardening.Arith.smulhi_spec
#print axioms Cases.Hardening.Calls.keep_contract
#print axioms Cases.Hardening.Calls.stop_contract
#print axioms Cases.Hardening.Calls.apply_inc_contract
#print axioms Cases.Hardening.Rec.fib_contract
#print axioms Cases.Hardening.Guest.udivti3_contract
#print axioms Tools.Test.Lsym.l2_safe
#print axioms Tools.Test.Lsym.l2_safe'
