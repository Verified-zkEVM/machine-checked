/-
  Lprog.Linked

  The lift of a program as a compiler links it, for any instruction set: what is the same
  whichever the instructions are.

  A linked program is functions, each a run of instructions at addresses. Lifting it is
  lifting each instruction, given what the program around it is (`Cx`): which address is an
  instruction of the same function, and so a label; which is the entry of a function, and so
  a call or a tail call; and where a computed jump may go. An instruction set gives the lift
  of one instruction (`liftProgram`'s argument) and nothing else. RISC-V's is
  `RiscV/Lift/Whole.lean`, AArch64's `ARM/Lift/Lift.lean`.

  * Instruction `k` of a function, counting through its parts, is at label `k`.
  * A function is one part, its own code, unless the instruction set says more
    (`parts`: RISC-V's calls that link through another register reach code that is lifted
    as a further part of the caller).
  * After each part comes `Labort`: running off its end is not lifted.
  * An instruction that is lifted but for some of its runs (a division that faults) jumps
    to `Cx.abort` on those: a label after everything else, with `Labort`, there only if some
    instruction asks for it.
  * **A computed jump** (`jump`) compares its target with each candidate in the function, then
    is a tail call among the functions. The candidates are the addresses inside the function
    that the program holds as values (`Fun.targets`, a hint from whoever builds the program)
    and what the instruction set adds. A hint only narrows: a jump to an address it misses
    goes `wrong`, so a wrong hint makes the lifted program refuse, not misbehave.

  Nothing is proved of it yet.

  ## Main definitions

  * `At`, `Fun`, `Cx`, `jump`, `liftProgram`
-/

import Lprog.Op
import Std.Data.HashMap

namespace Lprog.Linked

/-- An instruction where it is: its address and its length in bytes. -/
structure At (I : Type) where
  addr : BitVec 64
  size : Nat
  instr : I
  deriving Inhabited

/-- The address after the instruction. -/
def At.next {I : Type} (a : At I) : BitVec 64 := a.addr + BitVec.ofNat 64 a.size

/-- A function of a linked program. -/
structure Fun (I : Type) where
  name : String
  code : List (At I)
  /-- Addresses inside the function that the program holds as values: where its jump tables
      lead. A hint. -/
  targets : List (BitVec 64) := []
  deriving Inhabited

/-- The address of a function: of its first instruction. -/
def Fun.addr {I : Type} (f : Fun I) : BitVec 64 := (f.code.head?.map (·.addr)).getD 0

/-- What the lift of an instruction may ask of the program around it. -/
structure Cx where
  /-- The label of the instruction of this function at an address. -/
  label : BitVec 64 → Option LLabel
  /-- The function whose entry is an address. -/
  entry : BitVec 64 → Option Nat
  /-- Where a computed jump of this function may go, inside it. -/
  cands : List (BitVec 64 × LLabel)
  /-- Every function: where an indirect call may go. -/
  all : List Nat
  /-- A label at which the function gives up (`Labort`): where an instruction goes when it
      finds, as it runs, that it is not lifted (a division that faults). -/
  abort : LLabel

variable {Reg : Type}

/-- **A computed jump** to the value of `e`: a comparison with each address of `locals`, then
    a tail call among `fns`, or `Labort` if there are none. The target waits in `scratch`,
    a register the instruction set keeps for this, while `between` runs (the write of a
    link). -/
def jump (scratch : Reg) (e : Expr Reg) (between : Lcmd (Op Reg) Reg)
    (locals : List (BitVec 64 × LLabel)) (fns : List Nat) : Lcmd (Op Reg) Reg :=
  if between.isEmpty ∧ locals.isEmpty then [if fns.isEmpty then .Labort else .Ltail (.indirect e fns)] else
  [.Lopn (.set scratch e)] ++ between ++
  locals.map (fun (a, l) => .Lcond (.cmp "eq" (.reg scratch) (.imm (a.toNat : Int))) l) ++
  [if fns.isEmpty then .Labort else .Ltail (.indirect (.reg scratch) fns)]

variable {I : Type}

/-- **A linked program, lifted.** `liftI cx prev i` lifts instruction `i`, which comes after
    `prev` in its part. `parts fns f` are the parts of `f` (its own code first), and
    `extra part` the addresses in a part that a computed jump may reach beside the hints. -/
def liftProgram (liftI : Cx → Option (At I) → At I → Lcmd (Op Reg) Reg)
    (fns : List (Fun I))
    (parts : List (Fun I) → Fun I → List (List (At I)) := fun _ f => [f.code])
    (extra : List (At I) → List (BitVec 64) := fun _ => []) : Lprog (Op Reg) Reg :=
  let entries : Std.HashMap (BitVec 64) Nat :=
    Std.HashMap.ofList (fns.zipIdx.reverse.map fun (f, k) => (f.addr, k))
  fns.map fun f =>
    let ps := parts fns f
    let labels : Std.HashMap (BitVec 64) Nat :=
      Std.HashMap.ofList (ps.flatten.zipIdx.reverse.map fun (a, k) => (a.addr, k))
    let cx : Cx :=
      { label := (labels[·]?), entry := (entries[·]?), all := List.range fns.length
        abort := ps.flatten.length
        cands := (f.targets ++ ps.flatMap extra).eraseDups.filterMap fun a => labels[a]?.map (a, ·) }
    let rec go (off : Nat) : List (List (At I)) → Lcmd (Op Reg) Reg
      | [] => []
      | p :: rest =>
        let prevs : List (Option (At I)) := none :: p.map some
        ((p.zip prevs).zipIdx.map fun ((i, prev), k) =>
            .Llabel .internal (off + k) :: liftI cx prev i).flatten ++
          .Labort :: go (off + p.length) rest
    let body := go 0 ps
    -- the label to give up at, if an instruction asks for it
    let asked := body.any fun
      | .Lgoto l | .Lcond _ l => l == cx.abort
      | _ => false
    { name := f.name, addr := f.addr
      body := body ++ if asked then [.Llabel .internal cx.abort, .Labort] else [] }

end Lprog.Linked
