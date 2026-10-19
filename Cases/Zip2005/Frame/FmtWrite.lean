import MachineChecked.RiscV.Frame.Sound
import Cases.Zip2005.Frame.Fns
import Cases.Zip2005.Frame.FmtWriteAnno

namespace Cases.Zip2005.Frame.FmtWrite

open RiscvZkvm.Rv64 MachineChecked.RiscV.Frame

abbrev fn : Fn := Fns.fmtWrite

/-- The kernel re-checks the generated annotation. -/
theorem valid : fn.valid anno = true := Fn.validFast_sound (by decide +kernel)

theorem reqs_nil : fn.collect anno (·.reqs) = [] := by decide +kernel

theorem residual_nil : fn.collect anno (·.residual) = [] := by decide +kernel

/-- **`core::fmt::write` preserves `ra` and `sp`** at every exit, given the control-flow
    premise `hcfi`: its indirect jump (the vtable tail call at `0x7803e914`) does not land
    inside the function. Without it the jump could land on any instruction, and the
    analysis cannot show `ra` restored everywhere. The relocations of the `--emit-relocs`
    build back the premise: no code address the program materialises lies inside
    `core::fmt::write`. -/
theorem integrity_of_run (E : Ent) {s0 s s' : MachineState}
    (hpc : s0.pc = fn.base) (hE : ∀ r, r ≠ .x0 → s0.getReg r = E r) (hc : CodeOk fn s0)
    (hcfi : ∀ s, Run fn anno E s0 s → CfiOk fn s)
    (hr : Run fn anno E s0 s) {i : Nat} {ins : Instr}
    (hi : fn.idx? s.pc = some i) (hins : fn.instrAt? i = some ins)
    (hleave : ins = .JALR .x0 .x1 0 ∨ (¬ IsCall ins ∧ ¬ IsOutlined ins ∧ fn.idx? s'.pc = none))
    (hst : stepSp1 s = some s') : s'.getReg .x1 = E .x1 ∧ s'.getReg .x2 = E .x2 :=
  integrity valid (reqOk_of_report (by rw [reqs_nil]; simp))
    (fun s _ => resOk_of_report residual_nil s) hcfi
    (entry_inv valid (by decide +kernel) hpc hE hc) hr hi hins hleave hst

end Cases.Zip2005.Frame.FmtWrite
