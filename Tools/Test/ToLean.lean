/-
  Tools.Test.ToLean

  Checks of `decompile --to lean` (`Tools/ToLean.lean`), run when the module is built: a body in
  parts, the theorem of a function from its parts, and that a changed term fails the check a
  written module makes of it.

  A written module checks its function `f<i>` by `kernel_eq` on two statements (`f<i>_head`,
  `f<i>_parts`): the kernel checks `Eq.refl` by evaluation. Here the same statements are made
  of a small program: of its own lift they are proved, and of the lift with one instruction
  changed the kernel proves them false.

  For the other routes (the lift of whole programs, and Pancake), a written module checks its
  terms against `program.lift` or `program.toPancake`, the program an instruction set builds
  from its input (`Tools.Program`). Here the kernel evaluates those on a small program of each
  instruction set, including the removal of dead flag writes (AArch64, x86-64) and lift 2, and
  refutes a changed term.
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

/-! ## The words the `--proved` lift takes

An instruction, and `unimp`, which it lifts as a trap; not `addw` (`0x00c5853b`), a 32-bit
operation riscv-zkvm's machine lacks, nor the word 0, which is no instruction. -/

#guard taken 0x00008067#32 && taken unimp && !taken 0x00c5853b#32 && !taken 0#32

/-! ## A small program -/

/-- `addi sp, sp, -16; addi a0, zero, 7; addi sp, sp, 16; ret` at `0x1000`. -/
def fns : List Fn :=
  [{ name := "f", base := 0x1000
     prog := ([0xff010113, 0x00700513, 0x01010113, 0x00008067] : List Nat).map
       (BitVec.ofNat 32) |>.map decode }]

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
kernel_eq f_head : (liftProg fns)[0]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (f.name, f.addr, f.depth)

kernel_eq f_parts : (liftProg fns)[0]?.map (fun g => chunks chunk g.body) = some [f.body]

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
#guard validNs "A.B"
#guard validNs "Examples.Arith.RiscV.Image"
#guard !validNs "A..B"
#guard !validNs "A."
#guard !validNs ".A"
#guard !validNs "A.b"
#guard nsPath "out" "A.B" == System.FilePath.mk "out/A/B"
#guard !validNs "../X"
#guard !validNs "A/B"
#guard !validNs "A-B"
#guard !validNs "Aé"

/-! ## The other routes -/

section Routes
open Tools.Program

/-- `addi a0, zero, 7; ret`, `mov w0, #7; ret` and `mov eax, 7; ret`, each a function `f` at
    `0x1000`. -/
def rvCode : List Entry := [("f", 0x1000, [0x13, 0x05, 0x70, 0x00, 0x67, 0x80, 0x00, 0x00], [])]
def armCode : List Entry := [("f", 0x1000, [0xe0, 0x00, 0x80, 0x52, 0xc0, 0x03, 0x5f, 0xd6], [])]
def x86Code' : List Entry := [("f", 0x1000, [0xb8, 0x07, 0x00, 0x00, 0x00, 0xc3], [])]

-- the kernel evaluates each instruction set's lift of whole programs: decoding, the tree maps
-- of `Linked.liftProgram`, and for AArch64 and x86-64 `dropDead`
theorem rv_len : (riscvProgram rvCode 0x1000 []).lift.map (·.body.length) = [5] := by decide +kernel
theorem arm_len : (armProgram armCode 0x1000 []).lift.map (·.body.length) = [5] := by decide +kernel
theorem x86_len : (x86Program x86Code' 0x1000 []).lift.map (·.body.length) = [6] := by decide +kernel

/-- The AArch64 lift, as a written module would give it. -/
def armF : Lfundef (Op Lprog.ARM.Reg) Lprog.ARM.Reg :=
  { name := "f", addr := 0x1000, depth := 0
    body := List.flatten [[.Llabel .internal 0, .Lopn (.set .x0 (.imm 7)), .Llabel .internal 1, .Lret, .Labort]] }

theorem armF_head : (armProgram armCode 0x1000 []).lift[0]?.map (fun g => (g.name, g.addr, g.depth)) =
    some (armF.name, armF.addr, armF.depth) := by
  decide +kernel

theorem armF_parts : (armProgram armCode 0x1000 []).lift[0]?.map (fun g => chunks chunk g.body) =
    some [[.Llabel .internal 0, .Lopn (.set .x0 (.imm 7)), .Llabel .internal 1, .Lret, .Labort]] := by
  decide +kernel

theorem armF_eq : (armProgram armCode 0x1000 []).lift[0]? = some armF :=
  getElem?_eq_of_chunks armF_head armF_parts rfl

-- a changed term fails: `x0 = 8`
theorem armF_changed : (armProgram armCode 0x1000 []).lift[0]?.map (fun g => chunks chunk g.body) ≠
    some [[.Llabel .internal 0, .Lopn (.set .x0 (.imm 8)), .Llabel .internal 1, .Lret, .Labort]] := by
  decide +kernel

-- lift 2, evaluated by the kernel through `kernel_eq`: 38 declarations and 3 places where the
-- program may give up
kernel_eq rv_pancake : (riscvProgram rvCode 0x1000 []).toPancake.toOption.map
    (fun (d, n) => (d.length, n.length)) = some (38, 3)

-- the names lift 2 gives functions, evaluated by the kernel: a function named `f` is `f_f`
kernel_eq rv_names : MachineChecked.Logical.names (riscvProgram rvCode 0x1000 []).lift = #["f_f"]

-- the memory, flat and back
#guard pairsOf (flatMemory [(8, 1), (16, 2)]) == [(8, 1), (16, 2)]

end Routes

/-! ## What `kernel_eq` refuses

`#refused cmd` elaborates `cmd` with the kernel's check waited for (`Elab.async` off), fails
unless it logs an error, and leaves the environment and the messages as they were: a
declaration the kernel refuses is otherwise kept as an axiom of its own name, for what follows
it to elaborate. -/

open Lean Elab Command in
elab "#refused " cmd:command : command => do
  let env ← getEnv
  let msgs := (← get).messages
  modify fun s => { s with messages := {} }
  withScope (fun sc => { sc with opts := Elab.async.set sc.opts false }) (elabCommand cmd)
  let errs := (← get).messages.toList.filter (·.severity == .error)
  setEnv env
  modify fun s => { s with messages := msgs }
  if errs.isEmpty then throwError "#refused: {cmd} was accepted"

#refused kernel_eq bad_arith : 2 + 2 = 5
-- a count off by one, of lift 2
#refused kernel_eq bad_pancake : (Tools.Program.riscvProgram rvCode 0x1000 []).toPancake.toOption.map
    (fun (d, n) => (d.length, n.length)) = some (38, 4)
-- a changed term, as `--proved` checks a function's parts
#refused kernel_eq bad_parts : (liftProg fns)[0]?.map (fun g => chunks chunk g.body) =
    some [changed.body]
-- not an equation, and an equation with a hole
#refused kernel_eq not_eq : 2 + 2 ≠ 5
#refused kernel_eq hole : 2 + 2 = _
-- an unknown name: an error, not a theorem stated with `sorry`
#refused kernel_eq unknown : noSuchConstant = 1

end Tools.Test.ToLean
