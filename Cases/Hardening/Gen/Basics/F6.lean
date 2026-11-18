/-
  Cases.Hardening.Gen.Basics.F6

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.Basics.Words

namespace Cases.Hardening.Gen.Basics

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f6_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lgoto 0]

/-- The function "_start", lifted. -/
def f6 : Lfundef (Op Reg) Reg :=
  { name := "_start", addr := 4396, depth := 0,
    body := List.flatten [f6_0] }

kernel_eq f6_head : (liftProg fns)[6]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f6.name, f6.addr, f6.depth)

kernel_eq f6_parts : (liftProg fns)[6]?.map (fun g => chunks chunk g.body) =
    some [f6_0]

/-- **`f6` is the lift of the ELF's words.** -/
theorem f6_eq : (liftProg fns)[6]? = some f6 :=
  getElem?_eq_of_chunks f6_head f6_parts rfl

end

end Cases.Hardening.Gen.Basics
