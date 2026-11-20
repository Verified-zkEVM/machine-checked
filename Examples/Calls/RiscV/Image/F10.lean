/-
  Examples.Calls.RiscV.Image.F10

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Calls.RiscV.Image.Words

namespace Examples.Calls.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f10_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lgoto 0]

/-- The function "_start", lifted. -/
def f10 : Lfundef (Op Reg) Reg :=
  { name := "_start", addr := 4336, depth := 0,
    body := List.flatten [f10_0] }

kernel_eq f10_head : (liftProg fns)[10]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f10.name, f10.addr, f10.depth)

kernel_eq f10_parts : (liftProg fns)[10]?.map (fun g => chunks chunk g.body) =
    some [f10_0]

/-- **`f10` is the lift of the ELF's words.** -/
theorem f10_eq : (liftProg fns)[10]? = some f10 :=
  getElem?_eq_of_chunks f10_head f10_parts rfl

end

end Examples.Calls.RiscV.Image
