/-
  MachineChecked.RiscV.Lprog.Whole

  The lift of a whole RISC-V program as a compiler links it: RISC-V's instructions in the
  lift of linked programs (`Lprog/Linked.lean`).

  `liftProg` (`Lift.lean`) lifts `jal ra` calls, `jalr x0, 0(ra)` returns and jumps inside a
  function, and it is the lift the theorems are about. What rustc and its linker emit needs
  more, and `liftWhole` lifts it:

  * **a far call or jump**, `auipc r` then `jalr _, off(r)`: the target is known, so the call
    is of that one function (an indirect call with one candidate: arriving at the `jalr` any
    other way, with another value in `r`, goes `wrong`);
  * **a jump table**, `jalr x0` to an address loaded from data, and **an indirect call**: a
    computed jump (`Linked.jump`), and a call among all the functions;
  * **a call that links through another register than `ra`** (`jal t0`, as the compiler's
    outlined code is called): Lprog's calls link through one register, so this is a jump, and
    the code it reaches is lifted as a further part of the calling function (`parts`), with
    the `jalr` that returns from it a comparison with each such call's return address;
  * **the operations riscv-zkvm lacks** (`Decode.lean`);
  * **a word that is no instruction** is `Labort`.

  A `jalr` whose target and link are one register reads its target into `x0` first, which no
  lifted code reads otherwise.

  Nothing is proved of `liftWhole` yet, as of `liftFlat` (`Flat.lean`).

  ## Main definitions

  * `Fun`, `liftWhole`
-/

import MachineChecked.Lprog.Linked
import MachineChecked.RiscV.Lprog.Lift
import MachineChecked.RiscV.Lprog.Decode

namespace MachineChecked.RiscV.Lprog

open RiscvZkvm.Rv64 MachineChecked.Lprog
open MachineChecked.Lprog.Linked (At Cx)

/-- A function of a whole program. -/
abbrev Fun := Linked.Fun Decoded

namespace Whole

/-- The address a `jalr _, off(rs)` jumps to, when the instruction before it is the `auipc`
    that sets `rs`. -/
def paired (prev : Option (At Decoded)) (rs : Reg) (off : BitVec 12) : Option Word :=
  match prev with
  | some ⟨a, _, .instr (.AUIPC rd imm)⟩ =>
    if rd = rs ∧ rs ≠ .x0 then some ((a + auipcOff imm + signExtend12 off) &&& ~~~1#64) else none
  | _ => none

/-- Each instruction of a part with the one before it. -/
def withPrev (p : List (At Decoded)) : List (At Decoded × Option (At Decoded)) :=
  p.zip (none :: p.map some)

/-- The addresses a part jumps to with a link register other than `ra`. -/
def altCalls (p : List (At Decoded)) : List Word :=
  (withPrev p).filterMap fun (i, prev) => match i.instr with
    | .instr (.JAL rd off) => if rd = .x0 ∨ rd = .x1 then none else some (i.addr + signExtend21 off)
    | .instr (.JALR rd rs off) => if rd = .x0 ∨ rd = .x1 then none else paired prev rs off
    | _ => none

/-- The return addresses of those jumps. -/
def altRets (p : List (At Decoded)) : List Word :=
  p.filterMap fun i => match i.instr with
    | .instr (.JAL rd _) | .instr (.JALR rd _ _) => if rd = .x0 ∨ rd = .x1 then none else some i.next
    | _ => none

/-- The parts of a function: its own code, then the code its jumps with another link
    register reach, and theirs. -/
def parts (fns : List Fun) (f : Fun) : List (List (At Decoded)) :=
  let rec go (fuel : Nat) (done todo : List (List (At Decoded))) : List (List (At Decoded)) :=
    match fuel, todo with
    | 0, _ | _, [] => done
    | fuel + 1, p :: todo =>
      let have_ := (done ++ p :: todo).filterMap fun q => q.head?.map (·.addr)
      let new := (altCalls p).eraseDups.filterMap fun a =>
        if have_.contains a then none else (fns.find? (·.addr == a)).map (·.code)
      go fuel (done ++ [p]) (todo ++ new)
  go 8 [] [f.code]

/-- A branch to the address `t`. -/
def liftBr (cx : Cx) (op : String) (a b : Reg) (t : Word) : LinstrR (Op Reg) Reg :=
  match cx.label t with
  | some l => .Lcond (.cmp op (opnd a) (opnd b)) l
  | none => .Labort

/-- One instruction, after `prev` in its part. -/
def liftI (cx : Cx) (prev : Option (At Decoded)) (i : At Decoded) : Lcmd (Op Reg) Reg :=
  match i.instr with
  | .none => [.Labort]
  | .op o => [.Lopn o]
  | .instr ins =>
    let pc := i.addr
    let link (rd : Reg) : Lcmd (Op Reg) Reg := if rd = .x0 then [] else [.Lopn (.set rd (.imm i.next))]
    if opnOk ins then [.Lopn (opOf ins)] else
    match ins with
    | .AUIPC rd imm => [.Lopn (.set rd (.imm (pc + auipcOff imm)))]
    | .BEQ a b off => [liftBr cx "eq" a b (pc + signExtend13 off)]
    | .BNE a b off => [liftBr cx "ne" a b (pc + signExtend13 off)]
    | .BLT a b off => [liftBr cx "lt" a b (pc + signExtend13 off)]
    | .BGE a b off => [liftBr cx "ge" a b (pc + signExtend13 off)]
    | .BLTU a b off => [liftBr cx "ltu" a b (pc + signExtend13 off)]
    | .BGEU a b off => [liftBr cx "geu" a b (pc + signExtend13 off)]
    | .JAL rd off =>
      let t := pc + signExtend21 off
      if rd = .x1 then match cx.entry t with
        | some f => [.Lcall i.next (.direct f)]
        | none => [.Labort]
      else match cx.label t, cx.entry t with
        | some l, _ => link rd ++ [.Lgoto l]
        | none, some f => [if rd = .x0 then .Ltail (.direct f) else .Labort]
        | none, none => [.Labort]
    | .JALR rd rs off =>
      let e := jalrTgt rs off
      let known := paired prev rs off
      -- the functions it may reach: the one at a known target, or any
      let fns := match known with
        | some t => (cx.entry t).toList
        | none => cx.all
      if rd = .x0 ∧ rs = .x1 ∧ off = 0 then [.Lret]
      else if rd = .x1 then [if fns = [] then .Labort else .Lcall i.next (.indirect e fns)]
      else
        let locals := match known with
          | some t => ((cx.label t).map (t, ·)).toList
          | none => cx.cands
        Linked.jump .x0 e (link rd) locals
          (if rd = .x0 ∧ (locals.isEmpty ∨ known.isNone) then fns else [])
    | .ECALL => [.Lext 0]
    | _ => [.Labort]

end Whole

/-- **A whole program, lifted.** -/
def liftWhole (fns : List Fun) : Lprog (Op Reg) Reg :=
  Linked.liftProgram Whole.liftI fns Whole.parts Whole.altRets

end MachineChecked.RiscV.Lprog
