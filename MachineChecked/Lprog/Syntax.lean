/-
  MachineChecked.Lprog.Syntax

  Ported from catcrypt-compiler `CatCrypt/Crypto/SecureCompilation/VIR/JasminLprogExport/Types.lean`
  at `69ffea9f` (MIT, Copyright (c) 2024-2026 CatCrypt Contributors; see
  `MachineChecked/Ascent/LICENSE-catcrypt`). Changed: the namespace; registers are of a type
  `Reg` the instruction set chooses, not `String`s; `Lopn` carries one operation of a type `Op`
  (catcrypt-compiler carries a mnemonic `String` with destination and source operand lists;
  here the operation names its own registers, see `Lprog.Op`); the array operands are dropped,
  since memory is flat; an operand `cmp` is added, so that an instruction set without flags
  (RISC-V) can state a branch condition; a function has a name, the address a pointer to it
  holds, a body and a stack bound, and none of catcrypt-compiler's other fields; calls name a
  function of the program or compute a target, and `Ltail`, `Lext` and `Labort` are added;
  `Lalign`, `LstoreLabel` and `Lsyscall` are dropped.
-/

import MachineChecked.Lprog.Expr

/-!
# Lprog: the linear IR of Jasmin, as MachineChecked's logical machine

A mirror of Jasmin's linear IR (`proofs/lang/linear.v`): labels, operands, instructions,
function bodies and programs. Registers are of a type `Reg`, labels are `Nat`s, functions are
named by their index in the program, and operations are of a type `Op` the instruction set
chooses. Labels replace addresses inside a function, and `Lcall`/`Ltail`/`Lret`/`Lcond`/
`Lgoto`/`Ligoto` make control flow explicit. What an operation does, and what a condition
means, is up to an instruction set (`MachineChecked.Lprog.Isa`).

Addresses survive only as values: a pointer to a function (`Lfundef.addr`), the return address
a call writes to the link register, and the candidates of an indirect jump. Code compares them
and stores them, so they are part of the program.
-/

namespace MachineChecked.Lprog

/-- A label. -/
abbrev LLabel := Nat

/-- Internal or external label (`label_kind`). -/
inductive LabelKind where
  | internal
  | external
  deriving DecidableEq, Repr

/-- An operand. -/
inductive LOperand (Reg : Type) where
  /-- A register. -/
  | reg (r : Reg)
  /-- An immediate. -/
  | imm (value : Int)
  /-- A comparison `op` of two operands, as a branch condition. -/
  | cmp (op : String) (a b : LOperand Reg)
  deriving DecidableEq, Repr

/-- What a call calls. -/
inductive Target (Reg : Type) where
  /-- The function with this index in the program. -/
  | direct (f : Nat)
  /-- The function among `cands` whose address is the value of `e`. -/
  | indirect (e : Expr Reg) (cands : List Nat)
  deriving DecidableEq, Repr

/-- An instruction (`Linear.linstr_r`), over operations `Op` and registers `Reg`. -/
inductive LinstrR (Op Reg : Type) where
  /-- An operation: it names the registers and memory it reads and writes. -/
  | Lopn (opn : Op)
  | Llabel (kind : LabelKind) (lbl : LLabel)
  | Lgoto (lbl : LLabel)
  /-- Jump to `lbl` when `cond` holds. -/
  | Lcond (cond : LOperand Reg) (lbl : LLabel)
  /-- An indirect jump: to the label paired with the value of `e`. -/
  | Ligoto (e : Expr Reg) (cands : List (BitVec 64 × LLabel))
  /-- Call `target`, with `ret` in the link register. -/
  | Lcall (ret : BitVec 64) (target : Target Reg)
  /-- Call `target` in place of the current function, returning to its caller. -/
  | Ltail (target : Target Reg)
  | Lret
  /-- A call into the execution environment (a system call). -/
  | Lext
  /-- A point the program must not reach: the lift's marker for what it does not cover. -/
  | Labort
  deriving DecidableEq, Repr

/-- A function body (`Linear.lcmd`). -/
abbrev Lcmd (Op Reg : Type) := List (LinstrR Op Reg)

/-- A function definition (`Linear.lfundef`). -/
structure Lfundef (Op Reg : Type) where
  name : String
  /-- The value a pointer to the function holds. -/
  addr : BitVec 64
  body : Lcmd Op Reg
  /-- The most stack the function uses below its entry stack pointer, callees excluded. An
      annotation for contracts: no step reads it. -/
  depth : Nat := 0
  deriving Repr

/-- A program (`Linear.lprog`): its functions, named by index. -/
abbrev Lprog (Op Reg : Type) := List (Lfundef Op Reg)

end MachineChecked.Lprog
