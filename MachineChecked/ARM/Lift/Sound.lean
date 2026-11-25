/-
  MachineChecked.ARM.Lift.Sound

  The lift of AArch64 against arm64-semantics, an instruction at a time: the operations the
  lift writes for an instruction (`ops`) compute what the machine's execution of it
  (`Arm64.execInstWithSvc`) does. This is milestone M4 of `docs/NativeVerifiers.md`, in
  progress: the kinds of instruction proved are the modules below.
-/

import MachineChecked.ARM.Lift.Sound.Basic
import MachineChecked.ARM.Lift.Sound.AddSub
import MachineChecked.ARM.Lift.Sound.Logical
import MachineChecked.ARM.Lift.Sound.Move
import MachineChecked.ARM.Lift.Sound.Compare
import MachineChecked.ARM.Lift.Sound.Arith
import MachineChecked.ARM.Lift.Sound.Memory
