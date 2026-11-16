/-
  MachineChecked.X86.Lift.Table

  The instructions of x86-64 by kind, for the table of `../LIMITS.md`: which kinds the lift
  takes, said by the lift itself.

  `kind` names the kind of an instruction: its name in Intel's syntax, with a note where the
  lift tells forms of one name apart. `samples` has one instruction of each kind. A kind is
  lifted if the lift of its sample has no `Labort` (`rows`), so the table cannot say more
  than the lift does. Bytes the decoder does not read (`Instr.lean` says which) are of the
  last kind.

  ## Main definitions

  * `kind`, `samples`, `rows`
-/

import MachineChecked.X86.Lift.Lift

namespace MachineChecked.X86.Lift.Table

open Lprog

/-- The last part of a constructor's name, as `Repr` prints it. -/
def bare {α : Type} [Repr α] (a : α) : String :=
  ((reprStr a).splitOn ".").getLast!

/-- **The kind of an instruction.** -/
def kind : Option Instr → String
  | none => "(bytes the decoder does not read)"
  | some i => match i with
    | .mov .. => "mov"
    | .movx signed _ ssz .. => if !signed then "movzx" else if ssz = .d then "movsxd" else "movsx"
    | .lea .. => "lea"
    | .alu op .. => bare op
    | .test .. => "test"
    | .unary op .. => bare op
    | .shift op .. => bare op
    | .shiftd left sz .. => (if left then "shld" else "shrd") ++ (if sz = .w then " (16 bits)" else "")
    | .mul signed .. => if signed then "imul (one operand)" else "mul"
    | .div signed .. => if signed then "idiv" else "div"
    | .imul .. => "imul"
    | .push _ => "push"
    | .pop _ => "pop"
    | .xchg .. => "xchg"
    | .jcc c _ => "j" ++ bare c
    | .jmp _ => "jmp"
    | .jmpTo _ => "jmp (through a register or memory)"
    | .call _ => "call"
    | .callTo _ => "call (through a register or memory)"
    | .ret => "ret"
    | .setcc c _ => "set" ++ bare c
    | .cmov c .. => "cmov" ++ bare c
    | .widenA sz => (match sz with | .w => "cbw" | .d => "cwde" | _ => "cdqe")
    | .widenD sz => (match sz with | .w => "cwd" | .d => "cdq" | _ => "cqo")
    | .bswap .. => "bswap"
    | .scan op .. => bare op
    | .bit op .. => bare op
    | .movs _ rep => if rep then "rep movs" else "movs"
    | .stos _ rep => if rep then "rep stos" else "stos"
    | .cld => "cld"
    | .std => "std"
    | .leave => "leave"
    | .syscall => "syscall"
    | .int3 => "int3"
    | .ud2 => "ud2"
    | .nop => "nop"

/-- **One instruction of each kind.** -/
def samples : List (Option Instr) :=
  let a : Loc := .reg 0
  let b : Src := .loc (.reg 1)
  let ccs : List Cc := [.o, .no, .b, .ae, .e, .ne, .be, .a, .s, .ns, .p, .np, .l, .ge, .le, .g]
  let all : List Instr :=
    [.mov .q a b, .movx false .d .b 0 (.reg 1), .movx true .q .b 0 (.reg 1), .movx true .q .d 0 (.reg 1),
     .lea .q 0 { base := some 1, index := none, disp := 8 }] ++
    (([.add, .or, .adc, .sbb, .and, .sub, .xor, .cmp] : List Alu).map fun op => .alu op .q a b) ++
    [.test .q a b] ++
    (([.not, .neg, .inc, .dec] : List Unary).map fun op => .unary op .q a) ++
    (([.rol, .ror, .shl, .shr, .sar] : List Shift).map fun op => .shift op .q a (.imm 3)) ++
    [.shiftd true .q a 1 (.imm 3), .shiftd false .q a 1 (.imm 3), .shiftd true .w a 1 (.imm 3),
     .shiftd false .w a 1 (.imm 3), .mul false .q (.reg 1), .mul true .q (.reg 1), .div false .q (.reg 1),
     .div true .q (.reg 1), .imul .q 0 (.loc a) b, .push b, .pop a, .xchg .q a 1] ++
    (ccs.map fun c => .jcc c 0) ++
    [.jmp 0, .jmpTo a, .call 0, .callTo a, .ret] ++
    (ccs.map fun c => .setcc c a) ++ (ccs.map fun c => .cmov c .q 0 (.reg 1)) ++
    [.widenA .w, .widenA .d, .widenA .q, .widenD .w, .widenD .d, .widenD .q, .bswap .q 0] ++
    (([.bsf, .bsr, .tzcnt, .lzcnt] : List Scan).map fun op => .scan op .q 0 (.reg 1)) ++
    (([.bt, .bts, .btr, .btc] : List BitOp).map fun op => .bit op .q a b) ++
    [.movs .b false, .movs .b true, .stos .b false, .stos .b true, .cld, .std, .leave, .syscall,
     .int3, .ud2, .nop]
  all.map some ++ [none]

/-- **The kinds, each with whether the lift takes it**: lifted at an address from which every
    branch has somewhere to go. -/
def rows : List (String × Bool) :=
  let cx : Linked.Cx :=
    { label := fun _ => some 0, entry := fun _ => some 0, cands := [], all := [0], abort := 1 }
  samples.map fun i =>
    (kind i, !(liftI cx none { addr := 0x1000, size := 1, instr := i }).any (· matches .Labort))

end MachineChecked.X86.Lift.Table
