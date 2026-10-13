import AsmVerif.RiscV.Frame.Sound
import Cases.Zip2005.Frame.Fns
import Cases.Zip2005.Frame.DefaultHookAnno

namespace Cases.Zip2005.Frame.DefaultHook

open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame

abbrev fn : Fn := Fns.defaultHook

/-- The kernel re-checks the generated annotation. -/
theorem valid : fn.valid anno = true := Fn.validFast_sound (by decide +kernel)

/-- **`std::panicking::default_hook` preserves `ra` and `sp`** at every exit, its outlined
    prologue included, given: the 4 premises `hreq` (two statics, `OUTPUT_CAPTURE_USED` and
    `OUTPUT_CAPTURE`, are not the doubleword where `ra` is saved: stack and `.bss` are
    disjoint); and the residual premise `hres` at the two stores through pointers a callee
    returned (`0x7803b774`, `0x7803b798`). -/
theorem integrity_of_run (E : Ent) {s0 s s' : MachineState}
    (hpc : s0.pc = fn.base) (hE : ∀ r, r ≠ .x0 → s0.getReg r = E r) (hc : CodeOk fn s0)
    (hreq : ∀ q ∈ fn.collect anno (·.reqs), q.Holds E)
    (hres : ∀ s, Run fn anno E s0 s → ResOk fn anno E s)
    (hr : Run fn anno E s0 s) {i : Nat} {ins : Instr}
    (hi : fn.idx? s.pc = some i) (hins : fn.instrAt? i = some ins)
    (hleave : ins = .JALR .x0 .x1 0 ∨ (¬ IsCall ins ∧ ¬ IsOutlined ins ∧ fn.idx? s'.pc = none))
    (hst : stepSp1 s = some s') : s'.getReg .x1 = E .x1 ∧ s'.getReg .x2 = E .x2 :=
  integrity valid (reqOk_of_report hreq) hres (fun s _ => cfiOk_none rfl s)
    (entry_inv valid (by decide +kernel) hpc hE hc) hr hi hins hleave hst

end Cases.Zip2005.Frame.DefaultHook
