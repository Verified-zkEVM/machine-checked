/-
  Cases.Hardening.Gen.Arith.F8

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Cases.Hardening.Gen.Arith.Words

namespace Cases.Hardening.Gen.Arith

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f8_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lgoto 0]

/-- The function "_start", lifted. -/
def f8 : Lfundef (Op Reg) Reg :=
  { name := "_start", addr := 4276, depth := 0,
    body := List.flatten [f8_0] }

kernel_eq f8_head : (liftProg fns)[8]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f8.name, f8.addr, f8.depth)

kernel_eq f8_parts : (liftProg fns)[8]?.map (fun g => chunks chunk g.body) =
    some [f8_0]

/-- **`f8` is the lift of the ELF's words.** -/
theorem f8_eq : (liftProg fns)[8]? = some f8 :=
  getElem?_eq_of_chunks f8_head f8_parts rfl

end

end Cases.Hardening.Gen.Arith
