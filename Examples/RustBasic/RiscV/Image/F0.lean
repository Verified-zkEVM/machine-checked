/-
  Examples.RustBasic.RiscV.Image.F0

  Written by `decompile --to lean`. Do not edit: the theorems below check it.
-/

import Examples.RustBasic.RiscV.Image.Words

namespace Examples.RustBasic.RiscV.Image

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

-- data for the kernel, not code to run: the code generator does not take terms this large
noncomputable section

def f0_0 : Lcmd (Op Reg) Reg :=
  [LinstrR.Llabel (LabelKind.internal) 0, LinstrR.Lgoto 0]

/-- The function "_RNvCs1njKG4L9aB3_7___rustc17rust_begin_unwind", lifted. -/
def f0 : Lfundef (Op Reg) Reg :=
  { name := "_RNvCs1njKG4L9aB3_7___rustc17rust_begin_unwind", addr := 65536, depth := 0,
    body := List.flatten [f0_0] }

kernel_eq f0_head : (liftProg fns)[0]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f0.name, f0.addr, f0.depth)

kernel_eq f0_parts : (liftProg fns)[0]?.map (fun g => chunks chunk g.body) =
    some [f0_0]

/-- **`f0` is the lift of the ELF's words.** -/
theorem f0_eq : (liftProg fns)[0]? = some f0 :=
  getElem?_eq_of_chunks f0_head f0_parts rfl

end

end Examples.RustBasic.RiscV.Image
