/-
  MachineChecked.RiscV.Lift.Contract

  A contract at Lprog (`Lprog.Isa.Contract`), carried to riscv-zkvm's machine.

  `SafeN.of_contract` (`Transfer.lean`) takes a postcondition over a machine state. A contract
  proved with `lsym` has its precondition and postcondition over Lprog's register file and
  memory; `SafeN.of_isa_contract` takes it as it is.

  ## Main definitions

  * `Loaded`: the functions of a program are in the machine's code

  ## Main results

  * `SafeN.of_isa_contract`: a contract at Lprog, over the machine
-/

import MachineChecked.RiscV.Lift.Transfer
import Lprog.Contract

namespace MachineChecked.RiscV.Lift

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog Lprog.RiscV Lprog.RiscV.Machine

/-- The functions `fs` are in the machine's code, each at its address. -/
def Loaded (fs : List Fn) (s : MachineState) : Prop :=
  ∀ f ∈ fs, CodeAt f.base f.prog s

/-- **A contract over the machine.** A machine at the entry of function `g`, with the program
    loaded and the contract's precondition true of its registers and memory, is safe if every
    state it may return in is: one at `ra &&& ~~~1` that agrees with registers and a memory the
    postcondition holds of. -/
theorem SafeN.of_isa_contract {fs : List Fn} (hok : ProgOk fs) {g : Nat} {fn : Fn}
    (hg : fs[g]? = some fn) {s : MachineState} (hpc : s.pc = fn.base) (hcode : Loaded fs s)
    {Pre : Word → Word → (Reg → Word) → MachineState → Prop}
    {Post : Word → Word → (Reg → Word) → MachineState → (Reg → Word) → MachineState → Prop}
    (hcon : rvIsa.Contract (liftProg fs) sp1Ctx g Pre Post)
    (hpre : Pre (s.getReg .x1) (s.getReg .x2) (regsOf s) s)
    {G : MachineState → Prop} {N : Nat} {P : Prop}
    (hk : ∀ t r' m', Agree (ofParts r' m') t → t.pc = s.getReg .x1 &&& ~~~1#64 →
      Post (s.getReg .x1) (s.getReg .x2) (regsOf s) s r' m' → SafeN G N P t) :
    SafeN G N P s :=
  SafeN.of_lift
    (Q := fun s' => s'.stack = [] ∧ Post (s.getReg .x1) (s.getReg .x2) (regsOf s) s s'.regs s'.m)
    hok hg hpc hcode
    (fun k => hcon _ k _ _ _ [] _ _ hpre fun _ _ hp => Lprog.SafeN.returned ⟨rfl, hp⟩)
    (fun _ hne hq => absurd hq.1 hne) (fun s' t _ hag hpc' hq => hk t s'.regs s'.m hag hpc' hq.2)

end MachineChecked.RiscV.Lift
