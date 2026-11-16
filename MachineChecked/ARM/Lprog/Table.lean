/-
  MachineChecked.ARM.Lprog.Table

  The instructions of AArch64 by kind, for the table of `../LIMITS.md`: which kinds the lift
  takes, said by the lift itself.

  `kind` names the kind of an instruction: its architectural name, with the form of its
  operands where the lift tells forms apart. `samples` has one instruction of each kind. A
  kind is lifted if the lift of its sample has no `Labort` (`rows`), so the table cannot say
  more than the lift does; that every instruction of a kind is lifted as its sample is, is
  read off `Lift.lean`, where the cases are by kind.

  ## Main definitions

  * `kind`, `samples`, `rows`
-/

import MachineChecked.ARM.Lprog.Lift

namespace MachineChecked.ARM.Lprog.Table

open MachineChecked.Lprog
open Arm64 (Instr)

/-- The last part of a constructor's name, as `Repr` prints it. -/
def bare {α : Type} [Repr α] (a : α) : String :=
  ((reprStr a).splitOn ".").getLast!

/-- The name of a load or store of one register. -/
def access (load : Bool) (sz : Arm64.MemWidth) (signed : Bool) : String :=
  (if load then "LDR" else "STR") ++ (if signed then "S" else "") ++ match sz with
    | .B8 => "B"
    | .H16 => "H"
    | .W32 => if signed then "W" else ""
    | .X64 => ""

/-- **The kind of an instruction.** A word that is no instruction is of the last kind. -/
def kind : Option Instr → String
  | none => "(no instruction of arm64-semantics)"
  | some i => match i with
    | .adr page .. => if page then "ADRP" else "ADR"
    | .addSubImm _ op .. => s!"{bare op} (immediate)"
    | .addSubShift _ op .. => s!"{bare op} (shifted register)"
    | .addSubExt _ op .. => s!"{bare op} (extended register)"
    | .addSubCarry _ op .. => match op with
      | .ADD => "ADC" | .ADDS => "ADCS" | .SUB => "SBC" | .SUBS => "SBCS"
    | .logicalImm _ op .. => s!"{bare op} (immediate)"
    | .logicalShift _ op .. => s!"{bare op} (shifted register)"
    | .moveWide _ op .. => bare op
    | .bitfield _ op .. => bare op
    | .extr .. => "EXTR"
    | .b _ => "B"
    | .bl _ => "BL"
    | .bCond .. => "B.cond"
    | .cbz _ nz .. => if nz then "CBNZ" else "CBZ"
    | .tbz _ nz .. => if nz then "TBNZ" else "TBZ"
    | .br _ => "BR"
    | .blr _ => "BLR"
    | .ret rn => if rn = Arm64.Reg.x30 then "RET" else "RET (another register than x30)"
    | .nop => "NOP"
    | .hint _ => "HINT (other than NOP)"
    | .barrier .. => "CLREX, DSB, DMB, ISB"
    | .sysReg .. => "MRS, MSR"
    | .dcZva _ => "DC ZVA"
    | .system isHalt _ => if isHalt then "BRK" else "SVC"
    | .udf _ => "UDF"
    | .condCompareReg _ isSub .. => (if isSub then "CCMP" else "CCMN") ++ " (register)"
    | .condCompareImm _ isSub .. => (if isSub then "CCMP" else "CCMN") ++ " (immediate)"
    | .condSelect _ op .. => bare op
    | .dataProc1 _ op .. => bare op
    | .dataProc2 _ op .. => bare op
    | .dataProc3 _ op .. => bare op
    | .crc32 .. => "CRC32, CRC32C"
    | .ldr _ sz signed .. => access true sz signed
    | .ldrLit _ signed .. => if signed then "LDRSW (literal)" else "LDR (literal)"
    | .str sz .. => access false sz false
    | .ldp _ signed .. => if signed then "LDPSW" else "LDP"
    | .stp .. => "STP"
    | .ldnp .. | .stnp .. => "LDNP, STNP"
    | .ldarStlr .. | .ldxr .. | .stxr .. | .ldxp .. | .stxp .. | .cas .. | .casp ..
    | .atomicRmw .. | .ldapr .. | .ldapurStlur .. => "atomic, exclusive and ordered loads and stores"
    | .prfm .. | .prfmLit .. => "PRFM"
    | _ => "SIMD, floating point and cryptography"

/-- **One instruction of each kind.** -/
def samples : List (Option Instr) :=
  let x (k : Nat) : Arm64.Reg := .gpr (BitVec.ofNat 5 k)
  let v : Arm64.VReg := default
  let m : Arm64.AddrMode := .Offset (x 1) 8
  let all : List Instr :=
    [.adr false (x 0) 8, .adr true (x 0) 0x1000] ++
    (([.ADD, .ADDS, .SUB, .SUBS] : List Arm64.AddSubOp).flatMap fun op =>
      ([.addSubImm .W64 op (x 0) (x 1) 1 false, .addSubShift .W64 op (x 0) (x 1) (x 2) .LSL 0,
        .addSubExt .W64 op (x 0) (x 1) (x 2) .UXTW 0, .addSubCarry .W64 op (x 0) (x 1) (x 2)] : List Instr)) ++
    (([.AND, .ORR, .EOR, .ANDS] : List Arm64.LogicalOp).map fun op => .logicalImm .W64 op (x 0) (x 1) 0xff) ++
    (([.AND, .BIC, .ORR, .ORN, .EOR, .EON, .ANDS, .BICS] : List Arm64.LogicalOp).map fun op =>
      .logicalShift .W64 op (x 0) (x 1) (x 2) .LSL 0) ++
    (([.MOVN, .MOVZ, .MOVK] : List Arm64.MoveWideOp).map fun op => .moveWide .W64 op (x 0) 1 0) ++
    (([.SBFM, .BFM, .UBFM] : List Arm64.BitfieldOp).map fun op => .bitfield .W64 op (x 0) (x 1) 0 7) ++
    [.extr .W64 (x 0) (x 1) (x 2) 8, .b 0, .bl 0, .bCond .EQ 0, .cbz .W64 false (x 0) 0,
     .cbz .W64 true (x 0) 0, .tbz .W64 false (x 0) 3 0, .tbz .W64 true (x 0) 3 0, .br (x 1),
     .blr (x 1), .ret (x 30), .ret (x 1), .nop, .hint 1, .barrier 0 4, .sysReg true 0 (x 0),
     .dcZva (x 0), .system false 0, .system true 0, .udf 0,
     .condCompareReg .W64 true (x 0) (x 1) 0 .EQ, .condCompareReg .W64 false (x 0) (x 1) 0 .EQ,
     .condCompareImm .W64 true (x 0) 1 0 .EQ, .condCompareImm .W64 false (x 0) 1 0 .EQ] ++
    (([.CSEL, .CSINC, .CSINV, .CSNEG] : List Arm64.CondSelectOp).map fun op =>
      .condSelect .W64 op (x 0) (x 1) (x 2) .EQ) ++
    (([.RBIT, .REV16, .REV32, .REV, .CLZ, .CLS] : List Arm64.DataProc1Op).map fun op =>
      .dataProc1 .W64 op (x 0) (x 1)) ++
    (([.UDIV, .SDIV, .LSLV, .LSRV, .ASRV, .RORV] : List Arm64.DataProc2Op).map fun op =>
      .dataProc2 .W64 op (x 0) (x 1) (x 2)) ++
    (([.MADD, .MSUB, .SMADDL, .SMSUBL, .UMADDL, .UMSUBL, .SMULH, .UMULH] : List Arm64.DataProc3Op).map fun op =>
      .dataProc3 .W64 op (x 0) (x 1) (x 2) (x 3)) ++
    [.crc32 false .B8 (x 0) (x 1) (x 2),
     .ldr .W64 .X64 false (x 0) m, .ldr .W32 .W32 false (x 0) m, .ldr .W32 .H16 false (x 0) m,
     .ldr .W32 .B8 false (x 0) m, .ldr .W64 .W32 true (x 0) m, .ldr .W64 .H16 true (x 0) m,
     .ldr .W64 .B8 true (x 0) m, .ldrLit .W64 false (x 0) 8, .ldrLit .W64 true (x 0) 8,
     .str .X64 (x 0) m, .str .W32 (x 0) m, .str .H16 (x 0) m, .str .B8 (x 0) m,
     .ldp .W64 false (x 0) (x 2) m, .ldp .W64 true (x 0) (x 2) m, .stp .W64 (x 0) (x 2) m,
     .ldnp .X64 (x 1) (x 0) (x 2) 0, .ldxr .X64 false (x 1) (x 0), .prfm 0 m,
     .ldrSimd .D64 v m]
  all.map some ++ [none]

/-- **The kinds, each with whether the lift takes it**: lifted at an address from which every
    branch has somewhere to go. -/
def rows : List (String × Bool) :=
  let cx : Linked.Cx := { label := fun _ => some 0, entry := fun _ => some 0, cands := [], all := [0], abort := 1 }
  samples.map fun i =>
    (kind i, !(liftI cx none { addr := 0x1000, size := 4, instr := i }).any (· matches .Labort))

end MachineChecked.ARM.Lprog.Table
