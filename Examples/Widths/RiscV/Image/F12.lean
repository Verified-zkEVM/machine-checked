/-
  Examples.Widths.RiscV.Image.F12

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.Widths.RiscV.Image.Words

namespace Examples.Widths.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f12_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lgoto 0]

/-- The function "_start", lifted. -/
def f12 : Lfundef (Op Reg) Reg :=
  { name := "_start", addr := 4312, depth := 0,
    body := List.flatten [f12_0] }

kernel_eq f12_head : (liftProg fns)[12]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f12.name, f12.addr, f12.depth)

kernel_eq f12_parts : (liftProg fns)[12]?.map (fun g => chunks chunk g.body) =
    some [f12_0]

/-- **`f12` is the lift of the ELF's words.** -/
theorem f12_eq : (liftProg fns)[12]? = some f12 :=
  getElem?_eq_of_chunks f12_head f12_parts rfl

end

end Examples.Widths.RiscV.Image
