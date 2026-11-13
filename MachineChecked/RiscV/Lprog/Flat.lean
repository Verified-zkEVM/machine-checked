/-
  MachineChecked.RiscV.Lprog.Flat

  The lift of code that has no functions: one body, and computed jumps.

  `liftProg` (`Lift.lean`) lifts code that follows the calling convention: `jal ra` calls and
  `jalr x0, 0(ra)` returns. A compiler need not: Flapjack's code sets a return address with
  `auipc`/`addi`, jumps, and returns through whichever register holds the address; it has no
  function boundaries left, and reaches its execution environment by jumping to fixed
  addresses outside the code. `liftFlat` lifts such code as one body:

  * an operation, `auipc` and a branch as in `liftProg`; a word that is no instruction is
    `Labort`;
  * `jal` to an instruction is a goto (after writing the link register, if it has one), and
    `jal` to an entry of the environment (`Code.entry`) is `Lext`, then a jump to `ra`;
  * `jalr` is an indirect jump, `Ligoto`, among the candidates `cands`: the addresses the
    code itself forms, each an `auipc` and the `addi` after it. A jump to any other address
    goes `wrong`, as a jump outside its candidates does.

  Nothing is proved of `liftFlat` yet. The simulation of `Transfer.lean` and the equivalence
  of `Equiv.lean` are about `liftProg`; theirs for `liftFlat` is the inverse theorem's part of
  `docs/design/Decompiler.md` (phase 4).

  ## Main definitions

  * `Code`, `cands`, `liftFlat`
-/

import MachineChecked.RiscV.Lprog.Lift

namespace MachineChecked.RiscV.Lprog

open RiscvZkvm.Rv64 MachineChecked.Lprog

/-- Code without function boundaries: where it is, its instructions, and the entries of its
    execution environment, by address. -/
structure Code where
  base : Word
  /-- The decoded words; `none` is a word that is no instruction. -/
  prog : List (Option Instr)
  /-- The entry of the environment at an address outside the code. -/
  entry : Word → Option Nat

namespace Code

variable (c : Code)

/-- The index of the instruction at address `a`. -/
def indexOf (a : Word) : Option Nat :=
  let d := (a - c.base).toNat
  if d % 4 = 0 ∧ d / 4 < c.prog.length then some (d / 4) else none

/-- The address the code forms at instruction `k`, if that is an `auipc`: with the `addi`
    after it, when there is one into the same register. -/
def formed (k : Nat) : Option Word :=
  match c.prog[k]? with
  | some (some (.AUIPC rd imm)) =>
    let v := c.base + BitVec.ofNat 64 (4 * k) + auipcOff imm
    match c.prog[k + 1]? with
    | some (some (.ADDI rd' rs off)) => if rd' = rd ∧ rs = rd then some (v + signExtend12 off) else some v
    | _ => some v
  | _ => none

/-- **The candidates of a computed jump**: the instructions whose addresses the code forms,
    each with its address. -/
def cands : List (Word × LLabel) :=
  ((List.range c.prog.length).filterMap fun k =>
    (c.formed k).bind fun a => (c.indexOf a).map fun l => (a, l)).eraseDups

/-- One instruction, at index `k`. -/
def liftI (cs : List (Word × LLabel)) (k : Nat) : Option Instr → Lcmd (Op Reg) Reg
  | none => [.Labort]
  | some i =>
    let pc := c.base + BitVec.ofNat 64 (4 * k)
    let len := c.prog.length
    let link (rd : Reg) : Lcmd (Op Reg) Reg := if rd = .x0 then [] else [.Lopn (.set rd (.imm (pc + 4)))]
    if opnOk i then [.Lopn (opOf i)] else
    match i with
    | .JAL rd off =>
      if jumpOk k len (signExtend21 off) then link rd ++ [.Lgoto (tgt k (signExtend21 off))]
      else match c.entry (pc + signExtend21 off) with
        | some n => link rd ++ [.Lext n, .Ligoto (.reg .x1) cs]
        | none => [.Labort]
    | .JALR rd rs off =>
      if rd = rs ∧ rd ≠ .x0 then [.Labort] else link rd ++ [.Ligoto (jalrTgt rs off) cs]
    | .ECALL => [.Labort]
    | i => [liftCtl [] len k pc i]

/-- **Code without functions, lifted**: one function, a label before each instruction. -/
def liftFlat (name : String) : Lprog (Op Reg) Reg :=
  let cs := c.cands
  [{ name, addr := c.base
     body := (c.prog.zipIdx.map fun (i, k) => .Llabel .internal k :: c.liftI cs k i).flatten }]

end Code

end MachineChecked.RiscV.Lprog
