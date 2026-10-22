/-
  MachineChecked.Lprog.Syntax

  Ported from catcrypt-compiler `CatCrypt/Crypto/SecureCompilation/VIR/JasminLprogExport/Types.lean`
  at `69ffea9f` (MIT, Copyright (c) 2024-2026 CatCrypt Contributors; see
  `MachineChecked/Ascent/LICENSE-catcrypt`). Changed: the namespace; the instruction-info,
  alignment and stack fields of `Lfundef` that no semantics here reads are dropped; `Lopn`
  carries one operation of a type `Op` (catcrypt-compiler carries a mnemonic `String` with
  destination and source operand lists; here the operation names its own registers, see
  `Lprog.Op`); the array operands are dropped, since memory is flat; an operand `cmp` is added,
  so that an instruction set without flags (RISC-V) can state a branch condition.
-/

/-!
# Lprog: the linear IR of Jasmin, as MachineChecked's logical machine

A mirror of Jasmin's linear IR (`proofs/lang/linear.v`): labels, operands, instructions,
function bodies and programs. Registers are `String`s, labels `Nat`s, and operations are of
a type `Op` the instruction set chooses.
Labels replace addresses and `Lcall`/`Lret`/`Lcond`/`Lgoto`/`Ligoto` make control flow
explicit. What an operation does, and what a condition means, is up to an instruction set
(`MachineChecked.Lprog.Isa`).
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
inductive LOperand where
  /-- A named register. -/
  | reg (name : String)
  /-- An immediate. -/
  | imm (value : Int)
  /-- A comparison `op` of two operands, as a branch condition. -/
  | cmp (op : String) (a b : LOperand)
  deriving DecidableEq, Repr

/-- An instruction (`Linear.linstr_r`), over operations `Op`. -/
inductive LinstrR (Op : Type) where
  /-- An operation: it names the registers and memory it reads and writes. -/
  | Lopn (opn : Op)
  | Lsyscall (name : String)
  /-- Call the function at `target`, the return address into `ra` (or onto the stack). -/
  | Lcall (ra : Option String) (target : String × LLabel)
  | Lret
  | Lalign
  | Llabel (kind : LabelKind) (lbl : LLabel)
  | Lgoto (target : String × LLabel)
  /-- An indirect jump. -/
  | Ligoto (target : LOperand)
  | LstoreLabel (dst : String) (lbl : LLabel)
  /-- Jump to `lbl` when `cond` holds. -/
  | Lcond (cond : LOperand) (lbl : LLabel)
  deriving DecidableEq, Repr

/-- A function body (`Linear.lcmd`). -/
abbrev Lcmd (Op : Type) := List (LinstrR Op)

/-- A function definition (`Linear.lfundef`), with the fields a semantics reads. -/
structure Lfundef (Op : Type) where
  lfd_arg : List String := []
  lfd_body : Lcmd Op := []
  lfd_res : List String := []
  lfd_callee_saved : List String := []
  deriving Repr

/-- A program (`Linear.lprog`). -/
structure Lprog (Op : Type) where
  lp_funcs : List (String × Lfundef Op) := []
  deriving Repr

end MachineChecked.Lprog
