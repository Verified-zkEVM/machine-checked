/-
  MachineChecked.ARM.Lprog.Lift

  The lift of AArch64: its instructions in the lift of linked programs
  (`Lprog/Linked.lean`), over the shared operations.

  The instructions are arm64-semantics' (`Arm64.Instr`, decoded by its `Arm64.decode`). The
  lift takes the integer instructions a compiler emits and nothing of SIMD, floating point,
  atomics or system registers: those are `Labort`.

  * **Registers.** A 32-bit form reads the low half of its registers and writes its result
    zero-extended. The zero register reads as zero, and a write to it is dropped.
  * **Flags** are four registers, `nf`, `zf`, `cf` and `vf`, each 0 or 1. An instruction that
    sets them computes its result into `t0` first, then each flag from the operands and
    `t0`, then writes its destination, so that an operand that is also the destination is
    read before it is written.
  * **A condition** is an expression over the flags that is 0 or 1 (`cond`). A conditional
    branch on one flag is a comparison of it; on several, of `t0` after the expression is
    written there. A conditional select is the bitwise choice `b ^ ((a ^ b) & -c)`.
  * **What the shared operations lack** is written out in them: a rotation as two shifts, a
    byte or bit reversal as masks and shifts in `t0`, a count of leading zeros as six
    halving steps in `t0` and `t1`. Division by zero gives zero, as on AArch64.
  * **Memory.** The addressing modes are sums; a mode that writes back does so before or
    after the access as it says. An access need not be aligned.
  * **Control.** `b` and `b.cond` to an instruction of the function are jumps; `bl` to a
    function is a call, linked through `x30`, and `b` to one a tail call; `blr` is an indirect
    call and `br` a computed jump (`Linked.jump`, with `t2` for the target); `ret` through
    `x30` is a return; `svc` is the external call. `brk` and whatever else is not above are
    `Labort`.

  Nothing is proved of it. It is checked by running (`scripts/decompile-check`), against
  another machine than arm64-semantics'.

  ## Main definitions

  * `liftI`, `liftArm`
-/

import MachineChecked.ARM.Arm64
import MachineChecked.ARM.Lprog.Reg
import MachineChecked.Lprog.Linked
import MachineChecked.Lprog.Build

namespace MachineChecked.ARM.Lprog

open MachineChecked.Lprog
open MachineChecked.Lprog.Build
open MachineChecked.Lprog.Linked (At Cx)
open Arm64 (Instr RegWidth MemWidth CondCode ShiftType ExtendType AddrMode)

abbrev E := Expr Reg
abbrev O := Op Reg

/-- Reversals and counts in `t0`, with `t1` beside it. -/
def reverseBytes := Build.reverseBytes Reg.t0
def reverseBits := Build.reverseBits Reg.t0
def countLeadingZeros := Build.countLeadingZeros Reg.t0 Reg.t1

/-! ## Widths -/

/-- The low `w` bits, zero-extended. -/
def trunc (w : RegWidth) (a : E) : E := if w = .W32 then z32 a else a

/-- The low `w` bits, sign-extended. -/
def signed (w : RegWidth) (a : E) : E := if w = .W32 then s32 a else a

/-! ## Registers -/

/-- A register read at 64 bits. -/
def rd : Arm64.Reg → E
  | .gpr i => .reg (.ofGpr i)
  | .sp => .reg .sp
  | .xzr => num 0

/-- A register read at width `w`. -/
def rdw (w : RegWidth) (r : Arm64.Reg) : E :=
  match r with
  | .xzr => num 0
  | r => trunc w (rd r)

/-- A write of `e`, already of the width, to a register. -/
def wr : Arm64.Reg → E → List O
  | .gpr i, e => [.set (.ofGpr i) e]
  | .sp, e => [.set .sp e]
  | .xzr, _ => []

/-- The register a load goes to: `t0` for the zero register. -/
def dest : Arm64.Reg → Reg
  | .gpr i => .ofGpr i
  | .sp => .sp
  | .xzr => .t0

/-! ## Flags and conditions -/

/-- A condition: 0 or 1. -/
def cond : CondCode → E
  | .EQ => .reg .zf
  | .NE => flip (.reg .zf)
  | .CS => .reg .cf
  | .CC => flip (.reg .cf)
  | .MI => .reg .nf
  | .PL => flip (.reg .nf)
  | .VS => .reg .vf
  | .VC => flip (.reg .vf)
  | .HI => band (.reg .cf) (flip (.reg .zf))
  | .LS => bor (flip (.reg .cf)) (.reg .zf)
  | .GE => flip (bxor (.reg .nf) (.reg .vf))
  | .LT => bxor (.reg .nf) (.reg .vf)
  | .GT => band (flip (.reg .zf)) (flip (bxor (.reg .nf) (.reg .vf)))
  | .LE => bor (.reg .zf) (bxor (.reg .nf) (.reg .vf))
  | .AL | .NV => num 1

/-- A jump to `l` if the condition holds. -/
def branch (c : CondCode) (l : LLabel) : Lcmd O Reg :=
  let on (f : Reg) (op : String) : Lcmd O Reg := [.Lcond (.cmp op (.reg f) (.imm 0)) l]
  match c with
  | .EQ => on .zf "ne" | .NE => on .zf "eq"
  | .CS => on .cf "ne" | .CC => on .cf "eq"
  | .MI => on .nf "ne" | .PL => on .nf "eq"
  | .VS => on .vf "ne" | .VC => on .vf "eq"
  | .AL | .NV => [.Lgoto l]
  | c => [.Lopn (.set .t0 (cond c)), .Lcond (.cmp "ne" (.reg .t0) (.imm 0)) l]

/-- The flags `N` and `Z` of the result in `t0`. -/
def setNZ (w : RegWidth) : List O :=
  [.set .nf (bit (.reg .t0) (w.bits - 1)), .set .zf (isZero (.reg .t0))]

/-- The flags of `a + b` or `a - b`, the result being in `t0`; `a` and `b` are of the width. -/
def addSubFlags (w : RegWidth) (isSub : Bool) (a b : E) : List O :=
  let r : E := .reg .t0
  setNZ w ++
  [.set .cf (if isSub then flip (.bin .ult a b)
      else if w = .W32 then bit (add a b) 32 else .bin .ult r a),
   .set .vf (bit (if isSub then band (bxor a b) (bxor a r) else band (bxor a r) (bxor b r)) (w.bits - 1))]

/-- `a + b` or `a - b` into `dst`, with the flags if `flags`. -/
def addSub (w : RegWidth) (isSub flags : Bool) (dst : Arm64.Reg) (a b : E) : List O :=
  let r := trunc w (if isSub then sub a b else add a b)
  if flags then .set .t0 r :: addSubFlags w isSub a b ++ wr dst (.reg .t0) else wr dst r

/-- `a + b + C` into `dst`, with the flags if `flags`: `b` is the second operand, already
    inverted for a subtraction. -/
def addCarry (w : RegWidth) (flags : Bool) (dst : Arm64.Reg) (a b : E) : List O :=
  if !flags then wr dst (trunc w (add (add a b) (.reg .cf))) else
  (if w = .W32 then
    [.set .t1 (add (add a b) (.reg .cf)), .set .t0 (z32 (.reg .t1)), .set .cf (bit (.reg .t1) 32)]
   else
    [.set .t1 (add a b), .set .t0 (add (.reg .t1) (.reg .cf)),
     .set .cf (bor (.bin .ult (.reg .t1) a) (.bin .ult (.reg .t0) (.reg .t1)))]) ++
  [.set .vf (bit (band (bxor a (.reg .t0)) (bxor b (.reg .t0))) (w.bits - 1))] ++
  setNZ w ++ wr dst (.reg .t0)

/-! ## Operands -/

/-- A register shifted by a constant, at width `w`. -/
def shifted (w : RegWidth) (ty : ShiftType) (n : Nat) (r : Arm64.Reg) : E :=
  let x := rdw w r
  if n = 0 then x else
  match ty with
  | .LSL => trunc w (shl x n)
  | .LSR => lshr x n
  | .ASR => trunc w (ashr (signed w x) n)
  | .ROR => trunc w (bor (lshr x n) (shl x (w.bits - n)))

/-- A register extended and shifted left. -/
def extended (ext : ExtendType) (n : Nat) (r : Arm64.Reg) : E :=
  let x := rd r
  shl (match ext with
    | .UXTB => .un (.zext .b1) x
    | .UXTH => .un (.zext .b2) x
    | .UXTW => z32 x
    | .UXTX | .SXTX => x
    | .SXTB => .un (.sext .b1) x
    | .SXTH => .un (.sext .b2) x
    | .SXTW => s32 x) n

/-- The width of a memory access. -/
def width : MemWidth → Width
  | .B8 => .b1
  | .H16 => .b2
  | .W32 => .b4
  | .X64 => .b8

/-- An addressing mode: the operations before the access, the address, and those after. -/
def address : AddrMode → List O × E × List O
  | .Offset b off | .UnscaledOffset b off => ([], add (rd b) (.imm off), [])
  | .PreIndex b off => (wr b (add (rd b) (.imm off)), rd b, [])
  | .PostIndex b off => ([], rd b, wr b (add (rd b) (.imm off)))
  | .RegOffset b i ext n => ([], add (rd b) (extended ext n i), [])

/-! ## Instructions -/

/-- An instruction that does not transfer control, as operations; `none` if it is not
    lifted. `pc` is its address. -/
def ops (pc : BitVec 64) : Instr → Option (List O)
  | .nop => some []
  | .adr page dst off => some (wr dst (.imm ((if page then pc &&& ~~~0xfff#64 else pc) + off)))
  | .addSubImm w op dst rn imm12 shift12 =>
    let b := num (if shift12 then imm12.toNat * 4096 else imm12.toNat)
    some (addSub w (op matches .SUB | .SUBS) op.setsFlags dst (rdw w rn) b)
  | .addSubShift w op dst rn rm ty n =>
    some (addSub w (op matches .SUB | .SUBS) op.setsFlags dst (rdw w rn) (shifted w ty n rm))
  | .addSubExt w op dst rn rm ext n =>
    some (addSub w (op matches .SUB | .SUBS) op.setsFlags dst (rdw w rn) (trunc w (extended ext n rm)))
  | .addSubCarry w op dst rn rm =>
    let b := if op matches .SUB | .SUBS then trunc w (bnot (rdw w rm)) else rdw w rm
    some (addCarry w op.setsFlags dst (rdw w rn) b)
  | .logicalImm w op dst rn mask =>
    -- the decoder gives the pattern over 64 bits whatever the width
    logical w op dst (rdw w rn) (.imm (if w = .W32 then mask &&& 0xffffffff#64 else mask))
  | .logicalShift w op dst rn rm ty n => logical w op dst (rdw w rn) (shifted w ty n rm)
  | .moveWide w op dst imm16 hw =>
    let v := imm16.toNat * 2 ^ hw
    some (wr dst (match op with
      | .MOVZ => num v
      | .MOVN => trunc w (bnot (num v))
      | .MOVK => bor (band (rdw w dst) (trunc w (bnot (num (0xffff * 2 ^ hw))))) (num v)))
  | .bitfield w op dst rn immr imms =>
    -- a field of `len` bits, from bit `from_` of the source to bit `to` of the destination
    let (len, from_, to) := if imms ≥ immr then (imms - immr + 1, immr, 0) else (imms + 1, 0, w.bits - immr)
    let field := band (lshr (rdw w rn) from_) (ones len)
    some (wr dst (match op with
      | .UBFM => shl field to
      | .SBFM => trunc w (shl (ashr (shl (lshr (rdw w rn) from_) (64 - len)) (64 - len)) to)
      | .BFM => bor (band (rdw w dst) (trunc w (bnot (shl (ones len) to)))) (shl field to)))
  | .extr w dst rn rm lsb =>
    some (wr dst (if lsb = 0 then rdw w rm
      else trunc w (bor (lshr (rdw w rm) lsb) (shl (rdw w rn) (w.bits - lsb)))))
  | .condSelect w op dst rn rm c =>
    let b := rdw w rm
    some (wr dst (choose (cond c) (rdw w rn) (match op with
      | .CSEL => b
      | .CSINC => trunc w (add b (num 1))
      | .CSINV => trunc w (bnot b)
      | .CSNEG => trunc w (.un .neg b))))
  | .condCompareReg w isSub rn rm nzcv c => some (condCompare w isSub (rdw w rn) (rdw w rm) nzcv c)
  | .condCompareImm w isSub rn imm5 nzcv c =>
    some (condCompare w isSub (rdw w rn) (num imm5.toNat) nzcv c)
  | .dataProc1 w op dst rn =>
    let x := rdw w rn
    some (match op with
      | .REV => .set .t0 x :: reverseBytes (if w = .W32 then 2 else 3) ++ wr dst (.reg .t0)
      | .REV16 => .set .t0 x :: reverseBytes 1 ++ wr dst (.reg .t0)
      | .REV32 => .set .t0 x :: reverseBytes 2 ++ wr dst (.reg .t0)
      | .RBIT => .set .t0 x :: reverseBits ++ wr dst (lshr (.reg .t0) (64 - w.bits))
      | .CLZ => .set .t0 x :: countLeadingZeros ++ wr dst (sub (.reg .t0) (num (64 - w.bits)))
      | .CLS =>
        -- the leading bits equal to the sign: the leading zeros of `x ^ (x >> 1)`, less one
        .set .t0 (trunc w (bxor x (ashr (signed w x) 1))) :: countLeadingZeros ++
          wr dst (sub (.reg .t0) (num (64 - w.bits + 1))))
  | .dataProc2 w op dst rn rm =>
    let a := rdw w rn
    let b := rdw w rm
    let amount := band b (num (w.bits - 1))
    some (wr dst (match op with
      | .UDIV => band (.bin .divu a b) (.un .neg (nonZero b))
      | .SDIV => trunc w (band (.bin .div (signed w a) (signed w b)) (.un .neg (nonZero b)))
      | .LSLV => trunc w (.bin .shl a amount)
      | .LSRV => .bin .lshr a amount
      | .ASRV => trunc w (.bin .ashr (signed w a) amount)
      | .RORV =>
        trunc w (bor (.bin .lshr a amount)
          (.bin .shl a (band (sub (num w.bits) amount) (num (w.bits - 1)))))))
  | .dataProc3 w op dst rn rm ra =>
    let a := rdw w rn
    let b := rdw w rm
    some (wr dst (match op with
      | .MADD => trunc w (add (rdw w ra) (.bin .mul a b))
      | .MSUB => trunc w (sub (rdw w ra) (.bin .mul a b))
      | .SMADDL => add (rd ra) (.bin .mul (s32 (rd rn)) (s32 (rd rm)))
      | .SMSUBL => sub (rd ra) (.bin .mul (s32 (rd rn)) (s32 (rd rm)))
      | .UMADDL => add (rd ra) (.bin .mul (z32 (rd rn)) (z32 (rd rm)))
      | .UMSUBL => sub (rd ra) (.bin .mul (z32 (rd rn)) (z32 (rd rm)))
      | .SMULH => .bin .mulh (rd rn) (rd rm)
      | .UMULH => .bin .mulhu (rd rn) (rd rm)))
  | .ldr w sz sgn rt mode =>
    let (pre, a, post) := address mode
    some (pre ++ [.load (dest rt) (width sz) sgn a] ++
      (if sgn ∧ w = .W32 then [.set (dest rt) (z32 (.reg (dest rt)))] else []) ++ post)
  | .ldrLit w sgn rt off =>
    some [.load (dest rt) (if w = .W64 ∧ !sgn then .b8 else .b4) sgn (.imm (pc + off))]
  | .str sz rt mode =>
    let (pre, a, post) := address mode
    some (pre ++ [.store (width sz) a (rd rt)] ++ post)
  | .ldp w sgn rt1 rt2 mode =>
    let (pre, a, post) := address mode
    let sz : Width := if w = .W32 ∨ sgn then .b4 else .b8
    -- the address is read before either register is written
    some (pre ++ [.set .t2 a, .load (dest rt1) sz sgn (.reg .t2),
      .load (dest rt2) sz sgn (add (.reg .t2) (num sz.bytes))] ++ post)
  | .stp w rt1 rt2 mode =>
    let (pre, a, post) := address mode
    let sz : Width := if w = .W32 then .b4 else .b8
    -- the registers are read before the base is written back
    some ([.set .t0 (rd rt1), .set .t1 (rd rt2)] ++ pre ++
      [.store sz a (.reg .t0), .store sz (add a (num sz.bytes)) (.reg .t1)] ++ post)
  | _ => none
where
  /-- A logical operation into `dst`. -/
  logical (w : RegWidth) (op : Arm64.LogicalOp) (dst : Arm64.Reg) (a b : E) : Option (List O) :=
    let nb := trunc w (bnot b)
    let r := match op with
      | .AND | .ANDS => band a b
      | .BIC | .BICS => band a nb
      | .ORR => bor a b
      | .ORN => bor a nb
      | .EOR => bxor a b
      | .EON => bxor a nb
    some (if op matches .ANDS | .BICS then
      .set .t0 r :: setNZ w ++ [.set .cf (num 0), .set .vf (num 0)] ++ wr dst (.reg .t0)
    else wr dst r)
  /-- A conditional comparison: the flags of `a - b` or `a + b` if the condition holds, and
      `nzcv` if not. -/
  condCompare (w : RegWidth) (isSub : Bool) (a b : E) (nzcv : BitVec 4) (c : CondCode) : List O :=
    let keep (f : Reg) (k : Nat) : O :=
      .set f (choose (.reg .t1) (.reg f) (num (if nzcv.getLsbD k then 1 else 0)))
    [.set .t1 (cond c), .set .t0 (trunc w (if isSub then sub a b else add a b))] ++
    addSubFlags w isSub a b ++ [keep .nf 3, keep .zf 2, keep .cf 1, keep .vf 0]

/-- One instruction. A word that is no instruction is `none`. -/
def liftI (cx : Cx) (_ : Option (At (Option Instr))) (i : At (Option Instr)) : Lcmd O Reg :=
  let pc := i.addr
  let to (off : BitVec 64) (k : LLabel → Lcmd O Reg) : Lcmd O Reg :=
    match cx.label (pc + off) with
    | some l => k l
    | none => [.Labort]
  match i.instr with
  | none => [.Labort]
  | some (.b off) =>
    match cx.label (pc + off), cx.entry (pc + off) with
    | some l, _ => [.Lgoto l]
    | none, some f => [.Ltail (.direct f)]
    | none, none => [.Labort]
  | some (.bl off) =>
    match cx.entry (pc + off) with
    | some f => [.Lcall i.next (.direct f)]
    | none => [.Labort]
  | some (.bCond c off) => to off (branch c)
  | some (.cbz w nz rt off) => to off fun l =>
    let test (r : Reg) : Lcmd O Reg := [.Lcond (.cmp (if nz then "ne" else "eq") (.reg r) (.imm 0)) l]
    match w, rt with
    | _, .xzr => if nz then [] else [.Lgoto l]
    | .W64, .gpr k => test (.ofGpr k)
    | _, r => .Lopn (.set .t0 (rdw w r)) :: test .t0
  | some (.tbz _ nz rt b off) => to off fun l =>
    [.Lopn (.set .t0 (bit (rd rt) b)), .Lcond (.cmp (if nz then "ne" else "eq") (.reg .t0) (.imm 0)) l]
  | some (.br rn) => Linked.jump .t2 (rd rn) [] cx.cands cx.all
  | some (.blr rn) => [.Lcall i.next (.indirect (rd rn) cx.all)]
  | some (.ret rn) => if rn = Arm64.Reg.x30 then [.Lret] else [.Labort]
  | some (.system isHalt _) => [if isHalt then .Labort else .Lext 0]
  | some ins =>
    match ops pc ins with
    | some os => os.map .Lopn
    | none => [.Labort]

/-- A function of an AArch64 program. -/
abbrev Fun := Linked.Fun (Option Instr)

/-- **An AArch64 program, lifted.** -/
def liftArm (fns : List Fun) : Lprog O Reg := Linked.liftProgram liftI fns

end MachineChecked.ARM.Lprog
