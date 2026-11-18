/-
  Tools.Test.LsymX86

  `lsym` on a second instruction set, x86-64: two functions lifted from their bytes by the
  x86-64 lift, `f` calling `g`, each with a contract over the register file (`Isa.Contract`),
  `f`'s proved through `g`'s. Nothing of `lsym` is RISC-V's: the instruction set adds its
  instance to `lsym_simp`, as `LprogRiscV.Lsym` does for RISC-V.

  x86-64 has no instance at Lprog backed by a machine yet (`docs/design/Automation.md`), so the
  instance here is a model for the test: the shared operations over x86-64's registers, `ra` the
  link register and `rsp` the stack pointer as the lift has them, and a memory of doublewords by
  address (an access of another width faults). The lift's term is the kernel's: `p_eq` checks it
  against the lift of the bytes.
-/

import Lprog.Tactic
import Tools.Program

namespace Tools.Test.LsymX86

open Lprog Lprog.X86 Tools.Program

/-- A memory of doublewords by address; any other width faults. -/
def dwMem : Mem (BitVec 64 → BitVec 64) where
  load w a m := if w = .b8 then some (m a) else none
  store w a v m := if w = .b8 then some (fun b => if b = a then v else m b) else none

/-- x86-64 over the shared operations, with that memory. -/
abbrev x86Isa : Isa := Isa.ofOps Reg .ra .rsp (BitVec 64 → BitVec 64) dwMem

/-- No external calls. -/
def ctx : Context x86Isa Unit := ⟨fun _ _ _ _ => False, fun _ _ _ => False⟩

-- the instruction set's definitions in `lsym`'s simp set
attribute [lsym_simp] x86Isa dwMem

/-- `f`: `call g; lea eax, [rax + 1]; ret`, at `0x1000`; `g`: `mov eax, 5; ret`, at `0x2000`. -/
def code : List Entry := [("f", 0x1000, [0xe8, 0xfb, 0x0f, 0x00, 0x00, 0x8d, 0x40, 0x01, 0xc3], []),
  ("g", 0x2000, [0xb8, 0x05, 0x00, 0x00, 0x00, 0xc3], [])]

/-- `f`, lifted: the call pushes the return address and pops it after. -/
def fF : Lfundef (Op Reg) Reg :=
  { name := "f", addr := 0x1000, depth := 0
    body := [.Llabel .internal 0,
      .Lopn (.set .rsp (.bin .sub (.reg .rsp) (.imm 8))),
      .Lopn (.store .b8 (.reg .rsp) (.imm 0x1005)),
      .Lcall 0x1005 (.direct 1),
      .Lopn (.set .rsp (.bin .add (.reg .rsp) (.imm 8))),
      .Llabel .internal 1,
      .Lopn (.set .rax (.un (.zext .b4) (.bin .add (.reg .rax) (.imm 1)))),
      .Llabel .internal 2,
      .Lopn (.load .ra .b8 false (.reg .rsp)), .Lret, .Labort] }

/-- `g`, lifted: the return reads its address from the stack. -/
def gF : Lfundef (Op Reg) Reg :=
  { name := "g", addr := 0x2000, depth := 0
    body := [.Llabel .internal 0, .Lopn (.set .rax (.imm 5)), .Llabel .internal 1,
      .Lopn (.load .ra .b8 false (.reg .rsp)), .Lret, .Labort] }

def p : Lprog (Op Reg) Reg := [fF, gF]

/-- The terms are the x86-64 lift of the bytes. -/
theorem p_eq : (x86Program code 0x1000 []).lift = p := by decide +kernel

theorem hf0 : p[0]? = some fF := rfl
theorem hf1 : p[1]? = some gF := rfl

/-- **`g`'s contract**: with its return address at the top of the stack, it returns with `eax`
    5, the memory as it was, and every register but `rax` and `ra` kept. -/
theorem g_contract : x86Isa.Contract p ctx 1
    (fun ret top regs m => regs .rsp = top ∧ m top = ret)
    (fun _ _ regs m r' m' => r' .rax = 5 ∧ m' = m ∧ ∀ r, r ≠ .rax → r ≠ .ra → r' r = regs r) := by
  intro G N Q ret top rest regs m ⟨hsp, hm⟩ hk
  lsym hf1 with [hsp, hm]
  apply hk
  exact ⟨by simp [lsym_simp], rfl, fun r h1 h2 => by simp [lsym_simp, h1, h2]⟩

/-- **`f`'s contract, through `g`'s**: it returns with `eax` 6. The call, its push and its pop
    are stepped by `lsym`, with no rule by hand. -/
theorem f_contract : x86Isa.Contract p ctx 0
    (fun ret top regs m => regs .rsp = top ∧ m top = ret)
    (fun _ _ _ _ r' _ => r' .rax = 6) := by
  intro G N Q ret top rest regs m ⟨hsp, hm⟩ hk
  lsym hf0 with [hsp, hm] using [g_contract]
  apply hk; simp [lsym_simp]

end Tools.Test.LsymX86
