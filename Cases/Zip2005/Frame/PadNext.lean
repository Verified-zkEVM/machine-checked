import MachineChecked.RiscV.Frame.Sound
import Cases.Zip2005.Frame.Fns
import Cases.Zip2005.Frame.PadNextAnno

namespace Cases.Zip2005.Frame.PadNext

open RiscvZkvm.Rv64 MachineChecked.RiscV.Frame

abbrev fn : Fn := Fns.padNext

/-- The kernel re-checks the generated annotation. -/
theorem valid : fn.valid anno = true := Fn.validFast_sound (by decide +kernel)

theorem residual_nil : fn.collect anno (·.residual) = [] := by decide +kernel

/-- **sinsemilla `Pad::next` preserves `ra` and `sp`** at every exit, given the 43 premises
    `hreq`: each store through `self` (`a0 + k`) misses the doubleword where `ra` is saved.
    That is "`self` does not overlap this frame", a fact about the caller. The one call whose
    return address lies outside the function (a panic) is assumed not to return. -/
theorem integrity_of_run (E : Ent) {s0 s s' : MachineState}
    (hpc : s0.pc = fn.base) (hE : ∀ r, r ≠ .x0 → s0.getReg r = E r) (hc : CodeOk fn s0)
    (hreq : ∀ q ∈ fn.collect anno (·.reqs), q.Holds E)
    (hr : Run fn anno E s0 s) {i : Nat} {ins : Instr}
    (hi : fn.idx? s.pc = some i) (hins : fn.instrAt? i = some ins)
    (hleave : ins = .JALR .x0 .x1 0 ∨ (¬ IsCall ins ∧ ¬ IsOutlined ins ∧ fn.idx? s'.pc = none))
    (hst : stepSp1 s = some s') : s'.getReg .x1 = E .x1 ∧ s'.getReg .x2 = E .x2 :=
  integrity valid (reqOk_of_report hreq) (fun s _ => resOk_of_report residual_nil s)
    (fun s _ => cfiOk_none rfl s) (entry_inv valid (by decide +kernel) hpc hE hc)
    hr hi hins hleave hst

end Cases.Zip2005.Frame.PadNext
