/-
  MachineChecked.RiscV.Lprog.Table

  The instructions of RV64IM by kind, for the table of `../LIMITS.md`: which kinds the lift
  of whole programs takes, said by the lift itself.

  `kind` names the kind of a word of code: the name of its instruction. `samples` has one
  word of each kind. A kind is lifted if the lift of its sample has no `Labort` (`rows`), so
  the table cannot say more than the lift does.

  ## Main definitions

  * `kind`, `samples`, `rows`
-/

import MachineChecked.RiscV.Lprog.Whole

namespace MachineChecked.RiscV.Lprog.Table

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter MachineChecked.Lprog

/-- **The kind of a word of code.** A word that is no instruction of RV64IM that the
    decoders know is of the last kind. -/
def kind (w : BitVec 32) : String :=
  match decode w, wordOps w with
  | some i, _ => (((reprStr i).splitOn " ").head!.splitOn ".").getLast!
  | none, some (name, _) => name
  | none, none => "(no instruction of RV64IM)"

/-- **One word of each kind**: the forms of RV64IM with registers `x10`, `x11`, `x12` and
    small constants (`jalr` as the return it most often is), then words that are instructions
    of other extensions, and none. -/
def samples : List (BitVec 32) :=
  let w (n : Nat) : BitVec 32 := BitVec.ofNat 32 n
  -- `rd` is x10, `rs1` x11, `rs2` x12
  let r (op f3 f7 : Nat) := w (op ||| (10 <<< 7) ||| (f3 <<< 12) ||| (11 <<< 15) ||| (12 <<< 20) ||| (f7 <<< 25))
  let i (op f3 imm : Nat) := w (op ||| (10 <<< 7) ||| (f3 <<< 12) ||| (11 <<< 15) ||| (imm <<< 20))
  -- a store or a branch: `rs1` and `rs2`, and 8 in the low field of the offset
  let s (op f3 : Nat) := w (op ||| (8 <<< 7) ||| (f3 <<< 12) ||| (11 <<< 15) ||| (12 <<< 20))
  ([(0, 0), (0, 0x20), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (5, 0x20), (6, 0), (7, 0)].map fun (f3, f7) => r 0x33 f3 f7) ++
  ((List.range 8).map fun f3 => r 0x33 f3 1) ++
  ([(0, 0), (0, 0x20), (1, 0), (5, 0), (5, 0x20)].map fun (f3, f7) => r 0x3B f3 f7) ++
  ([0, 4, 5, 6, 7].map fun f3 => r 0x3B f3 1) ++
  ([0, 2, 3, 4, 6, 7].map fun f3 => i 0x13 f3 5) ++ [i 0x13 1 3, i 0x13 5 3, i 0x13 5 (0x400 + 3)] ++
  [i 0x1B 0 5, i 0x1B 1 3, i 0x1B 5 3, i 0x1B 5 (0x400 + 3)] ++
  ((List.range 7).map fun f3 => i 0x03 f3 8) ++ ((List.range 4).map fun f3 => s 0x23 f3) ++
  ([0, 1, 4, 5, 6, 7].map fun f3 => s 0x63 f3) ++
  [w 0x12345537, w 0x12345517, w 0x008000ef, w 0x00008067, w 0x00000073, w 0x00100073, w 0x0ff0000f,
   -- `csrrw`, `lr.w`, `fadd.s`, and nothing
   w 0x34051573, w 0x1005252f, w 0x00c58553, w 0]

/-- **The kinds, each with whether the lift takes it**: lifted at an address from which every
    branch has somewhere to go. -/
def rows : List (String × Bool) :=
  let cx : Linked.Cx := { label := fun _ => some 0, entry := fun _ => some 0, cands := [], all := [0] }
  samples.map fun w =>
    (kind w, !(Whole.liftI cx none { addr := 0x1000, size := 4, instr := decodeWord w }).any (· matches .Labort))

end MachineChecked.RiscV.Lprog.Table
