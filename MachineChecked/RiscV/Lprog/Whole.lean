/-
  MachineChecked.RiscV.Lprog.Whole

  The lift of a whole program as a compiler links it: functions, with what `liftProg` does not
  cover.

  `liftProg` (`Lift.lean`) lifts `jal ra` calls, `jalr x0, 0(ra)` returns and jumps inside a
  function, and it is the lift the theorems are about. What rustc and its linker emit needs
  more, and `liftWhole` lifts it:

  * **a far call or jump**, `auipc r` then `jalr _, off(r)`: the target is known, so the call
    is of that one function (an indirect call with one candidate: arriving at the `jalr` any
    other way, with another value in `r`, goes `wrong`);
  * **a jump table**, `jalr x0` to an address loaded from data: a comparison with each address
    in the function that the program holds as a value (`Fun.targets`), then, for a pointer
    to a function, an indirect tail call among all the functions;
  * **a call that links through another register than `ra`** (`jal t0`, as the compiler's
    outlined code is called): Lprog's calls link through one register, so this is a jump, and
    the code it reaches is lifted as a further part of the calling function, with the `jalr`
    that returns from it a comparison with each such call's return address;
  * **the operations riscv-zkvm lacks** (`Decode.lean`);
  * **a word that is no instruction** is `Labort`, and so is running off the end of a part.

  A `jalr` whose target and link are one register reads its target into `x0` first, which no
  lifted code reads otherwise.

  `Fun.targets` is a hint, from whoever builds the `Whole` (`Tools/`). It only narrows the
  candidates of a computed jump: one that reaches an address it misses goes `wrong`, so a
  wrong hint makes the lifted program refuse, not misbehave.

  Nothing is proved of `liftWhole` yet, as of `liftFlat` (`Flat.lean`).

  ## Main definitions

  * `Part`, `Fun`, `Whole`, `liftWhole`
-/

import MachineChecked.RiscV.Lprog.Lift
import MachineChecked.RiscV.Lprog.Decode

namespace MachineChecked.RiscV.Lprog

open RiscvZkvm.Rv64 MachineChecked.Lprog

/-- A run of code: where it is, and its decoded words. -/
structure Part where
  base : Word
  prog : List Decoded
  deriving Inhabited

namespace Part

/-- The index of the instruction at address `a`. -/
def indexOf (p : Part) (a : Word) : Option Nat :=
  let d := (a - p.base).toNat
  if d % 4 = 0 ∧ d / 4 < p.prog.length then some (d / 4) else none

/-- The address of instruction `k`. -/
def addrOf (p : Part) (k : Nat) : Word := p.base + BitVec.ofNat 64 (4 * k)

/-- The address a `jalr _, off(rs)` at `k` jumps to, when the instruction before it is the
    `auipc` that sets `rs`. -/
def paired (p : Part) (k : Nat) (rs : Reg) (off : BitVec 12) : Option Word :=
  match k, rs with
  | _, .x0 | 0, _ => none
  | k + 1, rs => match p.prog[k]? with
    | some (.instr (.AUIPC rd imm)) =>
      if rd = rs then some ((p.addrOf k + auipcOff imm + signExtend12 off) &&& ~~~1#64) else none
    | _ => none

/-- The addresses the part jumps to with a link register other than `ra`. -/
def altCalls (p : Part) : List Word :=
  p.prog.zipIdx.filterMap fun (i, k) => match i with
    | .instr (.JAL rd off) => if rd = .x0 ∨ rd = .x1 then none else some (p.addrOf k + signExtend21 off)
    | .instr (.JALR rd rs off) => if rd = .x0 ∨ rd = .x1 then none else p.paired k rs off
    | _ => none

/-- The return addresses of those jumps. -/
def altRets (p : Part) : List Word :=
  p.prog.zipIdx.filterMap fun (i, k) => match i with
    | .instr (.JAL rd _) | .instr (.JALR rd _ _) =>
      if rd = .x0 ∨ rd = .x1 then none else some (p.addrOf k + 4)
    | _ => none

end Part

/-- A function of a whole program. -/
structure Fun where
  name : String
  part : Part
  /-- Addresses inside the function that the program holds as values: where its jump tables
      lead. A hint. -/
  targets : List Word := []

/-- A whole program: its functions. -/
structure Whole where
  fns : List Fun

namespace Whole

variable (w : Whole)

/-- The index of the function whose entry is `a`. -/
def entryOf (a : Word) : Option Nat := w.fns.findIdx? (·.part.base == a)

/-- The parts of a function: its own, then the code its jumps with another link register
    reach, and theirs. -/
def parts (f : Fun) : List Part :=
  let rec go (fuel : Nat) (done todo : List Part) : List Part :=
    match fuel, todo with
    | 0, _ | _, [] => done
    | fuel + 1, p :: todo =>
      let new := p.altCalls.eraseDups.filterMap fun a =>
        if (done ++ p :: todo).any (·.base == a) then none
        else (w.entryOf a).bind fun g => w.fns[g]?.map (·.part)
      go fuel (done ++ [p]) (todo ++ new)
  go 8 [] [f.part]

/-- The label of the instruction at `a` among `ps`: its index, counting through the parts. -/
def labelOf (ps : List Part) (a : Word) : Option LLabel :=
  let rec go (off : Nat) : List Part → Option LLabel
    | [] => none
    | p :: ps => match p.indexOf a with
      | some k => some (off + k)
      | none => go (off + p.prog.length) ps
  go 0 ps

/-- A branch to the address `t`. -/
def liftBr (ps : List Part) (op : String) (a b : Reg) (t : Word) : LinstrR (Op Reg) Reg :=
  match labelOf ps t with
  | some l => .Lcond (.cmp op (opnd a) (opnd b)) l
  | none => .Labort

/-- A computed jump: `x0` holds the target, `rd` gets the link. A comparison with each
    address of `locals`, then a tail call among `fns` if there are any. -/
def liftJump (pc : Word) (rd : Reg) (e : Expr Reg) (locals : List (Word × LLabel)) (fns : List Nat) :
    Lcmd (Op Reg) Reg :=
  if rd = .x0 ∧ locals = [] then [if fns = [] then .Labort else .Ltail (.indirect e fns)] else
  [.Lopn (.set .x0 e)] ++
  (if rd = .x0 then [] else [.Lopn (.set rd (.imm (pc + 4)))]) ++
  locals.map (fun (a, l) => .Lcond (.cmp "eq" (.reg .x0) (.imm (a.toNat : Int))) l) ++
  [if fns = [] then .Labort else .Ltail (.indirect (.reg .x0) fns)]

/-- One instruction, at index `k` of part `p` of a function with parts `ps` and computed-jump
    candidates `cs`. -/
def liftI (ps : List Part) (cs : List (Word × LLabel)) (p : Part) (k : Nat) :
    Decoded → Lcmd (Op Reg) Reg
  | .none => [.Labort]
  | .op o => [.Lopn o]
  | .instr i =>
    let pc := p.addrOf k
    if opnOk i then [.Lopn (opOf i)] else
    match i with
    | .AUIPC rd imm => [.Lopn (.set rd (.imm (pc + auipcOff imm)))]
    | .BEQ a b off => [liftBr ps "eq" a b (pc + signExtend13 off)]
    | .BNE a b off => [liftBr ps "ne" a b (pc + signExtend13 off)]
    | .BLT a b off => [liftBr ps "lt" a b (pc + signExtend13 off)]
    | .BGE a b off => [liftBr ps "ge" a b (pc + signExtend13 off)]
    | .BLTU a b off => [liftBr ps "ltu" a b (pc + signExtend13 off)]
    | .BGEU a b off => [liftBr ps "geu" a b (pc + signExtend13 off)]
    | .JAL rd off =>
      let t := pc + signExtend21 off
      if rd = .x1 then match w.entryOf t with
        | some f => [.Lcall (pc + 4) (.direct f)]
        | none => [.Labort]
      else match labelOf ps t, w.entryOf t with
        | some l, _ => (if rd = .x0 then [] else [.Lopn (.set rd (.imm (pc + 4)))]) ++ [.Lgoto l]
        | none, some f => [if rd = .x0 then .Ltail (.direct f) else .Labort]
        | none, none => [.Labort]
    | .JALR rd rs off =>
      let e := jalrTgt rs off
      let known := p.paired k rs off
      -- the functions it may reach: the one at a known target, or any
      let fns := match known with
        | some t => (w.entryOf t).toList
        | none => List.range w.fns.length
      if rd = .x0 ∧ rs = .x1 ∧ off = 0 then [.Lret]
      else if rd = .x1 then [if fns = [] then .Labort else .Lcall (pc + 4) (.indirect e fns)]
      else
        let locals := match known with
          | some t => ((labelOf ps t).map (t, ·)).toList
          | none => cs
        liftJump pc rd e locals (if rd = .x0 ∧ locals.isEmpty ∨ rd = .x0 ∧ known.isNone then fns else [])
    | .ECALL => [.Lext 0]
    | _ => [.Labort]

/-- A function, lifted: a label before each instruction of each part, and `Labort` where a
    part ends. -/
def liftFun (f : Fun) : Lfundef (Op Reg) Reg :=
  let ps := w.parts f
  let cs := ((f.targets ++ ps.flatMap (·.altRets)).eraseDups.filterMap fun a =>
    (labelOf ps a).map (a, ·))
  let rec go (off : Nat) : List Part → Lcmd (Op Reg) Reg
    | [] => []
    | p :: rest =>
      (p.prog.zipIdx.map fun (i, k) => .Llabel .internal (off + k) :: w.liftI ps cs p k i).flatten ++
        .Labort :: go (off + p.prog.length) rest
  { name := f.name, addr := f.part.base, body := go 0 ps }

/-- **A whole program, lifted.** -/
def liftWhole : Lprog (Op Reg) Reg := w.fns.map w.liftFun

end Whole

end MachineChecked.RiscV.Lprog
