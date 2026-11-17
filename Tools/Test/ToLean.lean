/-
  Tools.Test.ToLean

  Checks of `decompile --to lean` (`Tools/ToLean.lean`), run when the module is built: a body in
  parts, the theorem of a function from its parts, and that a changed term fails the check a
  written module makes of it.

  A written module checks its function `f<i>` by `decide +kernel` on two statements
  (`f<i>_head`, `f<i>_parts`). Here the same statements are made of a small program: of its
  own lift they are proved, and of the lift with one instruction changed the kernel proves
  them false.
-/

import Tools.ToLean

namespace Tools.Test.ToLean

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter Lprog MachineChecked.RiscV.Lift Tools.ToLean

/-! ## A body in parts -/

#guard chunks 2 [1, 2, 3, 4, 5] == [[1, 2], [3, 4], [5]]
#guard chunks 2 [1, 2, 3, 4] == [[1, 2], [3, 4]]
#guard chunks 3 ([] : List Nat) == []
#guard (chunks 128 (List.range 1000)).length == 8
#guard (chunks 128 (List.range 1000)).flatten == List.range 1000
#guard (chunks 128 (List.range 1000)).all (·.length ≤ 128)

/-! ## A small program -/

/-- `addi sp, sp, -16; addi a0, zero, 7; addi sp, sp, 16; ret` at `0x1000`. -/
def fns : List Fn :=
  [{ name := "f", base := 0x1000
     prog := (([0xff010113, 0x00700513, 0x01010113, 0x00008067] : List Nat).map
       (BitVec.ofNat 32) |>.mapM decode).getD [] }]

#guard (fns.head?.map (·.prog.length)) == some 4

/-- The lift, as a written module would give it: its body in one part. -/
def f : Lfundef (Op Reg) Reg :=
  match (liftProg fns)[0]? with
  | some g => { g with body := List.flatten [g.body] }
  | none => { name := "", addr := 0, body := [] }

/-- The same with the immediate of the instruction at index 3 of its body changed: `a0 = 8`,
    not `7`. -/
def changed : Lfundef (Op Reg) Reg :=
  { f with body := f.body.set 3 (.Lopn (.set .x10 (.imm 8))) }

#guard f.body.length == 8
#guard f.body[3]? != changed.body[3]?

-- the two statements a written module makes, and the theorem from them
theorem f_head : (liftProg fns)[0]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f.name, f.addr, f.depth) := by
  decide +kernel

theorem f_parts : (liftProg fns)[0]?.map (fun g => chunks chunk g.body) = some [f.body] := by
  decide +kernel

theorem f_eq : (liftProg fns)[0]? = some f :=
  getElem?_eq_of_chunks f_head f_parts (by simp [f])

-- a changed term fails: the kernel proves its statement false
theorem changed_parts_false :
    (liftProg fns)[0]?.map (fun g => chunks chunk g.body) ≠ some [changed.body] := by
  decide +kernel

theorem changed_ne : (liftProg fns)[0]? ≠ some changed := by
  rw [f_eq]; decide +kernel

/-! ## What goes into a written module as text

A symbol's name is any bytes of the ELF. In a comment it is escaped (`commentSafe`), so that a
name that would close the comment cannot put Lean into the module: the module written for a
function with such a name (`evil`) has as many comment ends as for a plain name, apart from
the one inside the name's string literal (`name := …`), where it is no comment end. -/

def evil : String := "a-/ #eval IO.println \"run at build time\" /--"

#guard !((commentSafe evil).splitOn "-/").length > 1
#guard !((commentSafe evil).splitOn "/-").length > 1
#guard !((commentSafe "a\nb").contains '\n')
#guard (((functionModule "NS" 1 0 { f with name := evil }).replace (reprStr evil) "").splitOn
    "-/").length == ((functionModule "NS" 1 0 f).splitOn "-/").length

/-! ## The namespace -/

#guard validNs "Blake2s"
#guard validNs "Zip_2005"
#guard !validNs ""
#guard !validNs "blake2s"
#guard !validNs "A.B"
#guard !validNs "../X"
#guard !validNs "A/B"
#guard !validNs "A-B"
#guard !validNs "Aé"

end Tools.Test.ToLean
