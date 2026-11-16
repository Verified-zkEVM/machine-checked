/-
  MachineChecked.X86.Lift.Lift

  The lift of x86-64: its instructions (`Instr.lean`) in the lift of linked programs
  (`Lprog/Linked.lean`), over the shared operations.

  * **Registers.** An operand of 32 bits is the low half of its register, and a write of one
    clears the high half; a write of 8 or 16 bits leaves the rest of the register. A value
    read is zero-extended.
  * **Memory.** An operand in memory is loaded into `t4` (the destination) or `t5` (the
    source), and its address is a sum. An access need not be aligned.
  * **Flags** are `cf`, `zf`, `sf` and `ovf`, each 0 or 1, and `pf`. An instruction that sets
    them computes its result into `t0`, then the flags from the operands and `t0`, then
    writes its destination. The parity flag is seldom read, so `pf` is the result itself,
    and its parity is worked out where a condition reads it. The auxiliary flag is not kept. Where the processor leaves a
    flag undefined, the lift leaves it as it was or gives it the value the usual processors
    do; no compiled program reads it.
  * **A shift by `cl`** changes the flags only if the count is not zero: each flag is the
    choice between its new and its old value.
  * **Multiplication and division** use `rdx:rax` as the processor does. A division of 128
    bits by 64 is long division by digits of 32 bits, written out. A division that faults
    on the processor (by zero, or with a quotient that does not fit) jumps to `Cx.abort`:
    the lifted program gives up there.
  * **The string instructions** `movs` and `stos` go by `df`; with `rep`, the instruction is
    a loop: at its own label, it leaves if `rcx` is zero, and else does one step and jumps
    back to itself.
  * **Calls.** x86-64 keeps a return address on the stack and Lprog in a link register, so
    the lift has one of its own, `ra`. `call` pushes the return address and is `Lcall`,
    after which the lift pops the address again; `ret` loads the address at the stack
    pointer into `ra` and is `Lret`, without popping. So a function returns with the stack
    pointer as it was called with, as `Lret` asks, and to the address its caller pushed, or
    the caller gives up. A `jmp` to a function is a tail call.
  * **Control.** A jump to an instruction of the function is a jump, and a conditional
    jump to another function is a tail call on the condition; `jmp` through a
    register or memory is a computed jump (`Linked.jump`, with `t2`); `syscall` is the
    external call. `int3`, `ud2`, and bytes that are no instruction are `Labort`.

  Nothing is proved of it, and it is not yet compared with Kraken's semantics. It is checked
  by running (`scripts/decompile-check`) against another machine.

  ## Main definitions

  * `liftI`, `liftX86`
-/

import MachineChecked.X86.Lift.Instr
import Lprog.X86.Reg
import Lprog.Linked
import Lprog.Build

namespace MachineChecked.X86.Lift

open Lprog.X86
open Lprog
open Lprog.Build
open Lprog.Linked (At Cx)

abbrev E := Expr Reg
abbrev O := Op Reg

/-! ## Sizes -/

def width : Size → Width
  | .b => .b1
  | .w => .b2
  | .d => .b4
  | .q => .b8

/-- The low bits of the size, zero-extended; and sign-extended. -/
def low (sz : Size) (e : E) : E := if sz = .q then e else .un (.zext (width sz)) e
def sext (sz : Size) (e : E) : E := if sz = .q then e else .un (.sext (width sz)) e

/-- The top bit of a value of the size: 0 or 1. -/
def msb (sz : Size) (e : E) : E := bit e (sz.bits - 1)

/-- The number whose only bit is the top bit of the size. -/
def top (sz : Size) : E := num (2 ^ (sz.bits - 1))

def r (x : Reg) : E := .reg x
def g (n : Fin 16) : E := .reg (.ofGpr n)

/-- 1 if `a` and `b` are equal. -/
def same (a b : E) : E := isZero (bxor a b)

/-! ## Operands -/

/-- The address an operand names. -/
def addr (a : Addr) : E :=
  let parts : List E := (a.base.map g).toList ++
    (a.index.map fun (i, s) => shl (g i) s).toList ++ (if a.disp = 0 then [] else [.imm a.disp])
  match parts with
  | [] => num 0
  | p :: ps => ps.foldl add p

/-- A place read at a size: what loads it, if it is memory (into `t`), and its value. -/
def rdLoc (sz : Size) (t : Reg) : Loc → List O × E
  | .reg n => ([], low sz (g n))
  | .high n => ([], band (lshr (g (n.castLE (by omega))) 8) (num 0xff))
  | .mem a => ([.load t (width sz) false (addr a)], r t)

/-- An operand read at a size. -/
def rdSrc (sz : Size) (t : Reg) : Src → List O × E
  | .loc l => rdLoc sz t l
  | .imm v => ([], .imm (if sz = .q then v else v &&& BitVec.ofNat 64 (2 ^ sz.bits - 1)))

/-- A value of the size (zero-extended) written to a place. -/
def wr (sz : Size) (l : Loc) (v : E) : List O :=
  match l with
  | .reg n =>
    let x := Reg.ofGpr n
    if sz = .q ∨ sz = .d then [.set x v]
    else [.set x (bor (band (r x) (bnot (ones sz.bits))) v)]
  | .high n =>
    let x := Reg.ofGpr (n.castLE (by omega))
    [.set x (bor (band (r x) (bnot (num 0xff00))) (shl v 8))]
  | .mem a => [.store (width sz) (addr a) v]

/-! ## Flags -/

/-- Whether the low byte of `e` has an even number of bits set: the low four bits of
    `e ^ (e >> 4)` have its parity, and index a table of the parities of sixteen numbers. -/
def parity (e : E) : E := flip (bit (.bin .lshr (num 0x6996) (band (bxor e (lshr e 4)) (num 15))) 0)

/-- The zero and sign flags of the result in `t0`, and the result for its parity. -/
def setZS (sz : Size) : List O :=
  [.set .zf (isZero (r .t0)), .set .sf (msb sz (r .t0)), .set .pf (r .t0)]

/-- **A condition**: 0 or 1. -/
def cond : Cc → E
  | .o => r .ovf
  | .no => flip (r .ovf)
  | .b => r .cf
  | .ae => flip (r .cf)
  | .e => r .zf
  | .ne => flip (r .zf)
  | .be => bor (r .cf) (r .zf)
  | .a => flip (bor (r .cf) (r .zf))
  | .s => r .sf
  | .ns => flip (r .sf)
  | .p => parity (r .pf)
  | .np => flip (parity (r .pf))
  | .l => bxor (r .sf) (r .ovf)
  | .ge => flip (bxor (r .sf) (r .ovf))
  | .le => bor (r .zf) (bxor (r .sf) (r .ovf))
  | .g => flip (bor (r .zf) (bxor (r .sf) (r .ovf)))

/-- The condition that holds when `c` does not. -/
def Cc.not : Cc → Cc
  | .o => .no | .no => .o | .b => .ae | .ae => .b | .e => .ne | .ne => .e | .be => .a | .a => .be
  | .s => .ns | .ns => .s | .p => .np | .np => .p | .l => .ge | .ge => .l | .le => .g | .g => .le

/-- A branch to `l` on a condition. -/
def branch (c : Cc) (l : LLabel) : Lcmd O Reg :=
  let on (f : Reg) (op : String) : Lcmd O Reg := [.Lcond (.cmp op (.reg f) (.imm 0)) l]
  match c with
  | .o => on .ovf "ne" | .no => on .ovf "eq"
  | .b => on .cf "ne" | .ae => on .cf "eq"
  | .e => on .zf "ne" | .ne => on .zf "eq"
  | .s => on .sf "ne" | .ns => on .sf "eq"
  | _ => [.Lopn (.set .t0 (cond c)), .Lcond (.cmp "ne" (.reg .t0) (.imm 0)) l]

/-! ## Arithmetic -/

/-- An operation of two operands, `a` and `b` of the size: the result into `t0`, and the
    flags. `adc` and `sbb` read `cf` before they write it. -/
def aluOps (op : Alu) (sz : Size) (a b : E) : List O :=
  let t : E := r .t0
  let wide := sz = .q
  let addOvf : O := .set .ovf (msb sz (band (bxor a t) (bxor b t)))
  let subOvf : O := .set .ovf (msb sz (band (bxor a b) (bxor a t)))
  let logic (e : E) : List O := [.set .t0 e, .set .cf (num 0), .set .ovf (num 0)]
  (match op with
    | .add => [.set .t0 (low sz (add a b)), .set .cf (if wide then .bin .ult t a else bit (add a b) sz.bits), addOvf]
    | .adc =>
      if wide then
        [.set .t1 (add a b), .set .t0 (add (r .t1) (r .cf)),
         .set .cf (bor (.bin .ult (r .t1) a) (.bin .ult t (r .t1))), addOvf]
      else [.set .t1 (add (add a b) (r .cf)), .set .t0 (low sz (r .t1)), .set .cf (bit (r .t1) sz.bits), addOvf]
    | .sub | .cmp => [.set .t0 (low sz (sub a b)), .set .cf (.bin .ult a b), subOvf]
    | .sbb =>
      if wide then
        [.set .t2 (r .cf), .set .t1 (sub a b), .set .t0 (sub (r .t1) (r .t2)),
         .set .cf (bor (.bin .ult a b) (.bin .ult (r .t1) (r .t2))), subOvf]
      else [.set .t1 (sub (sub a b) (r .cf)), .set .t0 (low sz (r .t1)), .set .cf (bit (r .t1) sz.bits), subOvf]
    | .and => logic (band a b)
    | .or => logic (bor a b)
    | .xor => logic (bxor a b)) ++ setZS sz

/-- A shift of `a` (of the size) by a count that is not zero: the result into `t0`, with the
    new carry and overflow flags. `n` is the count, below the size of the registers, and
    `n1` the count less one. A rotation is by the count modulo the size, in `t2`. -/
def shiftOps (op : Shift) (sz : Size) (a n n1 : E) : List O × E × E :=
  let t : E := r .t0
  let by_ (f : BinOp) (x y : E) : E := .bin f x y
  let back : E := band (sub (num sz.bits) (r .t2)) (num 63)
  match op with
  | .shl => ([.set .t0 (low sz (by_ .shl a n))],
      bit (by_ .lshr a (band (sub (num sz.bits) n) (num 63))) 0, bxor (msb sz t) (r .cf))
  | .shr => ([.set .t0 (by_ .lshr a n)], bit (by_ .lshr a n1) 0, msb sz a)
  | .sar => ([.set .t0 (low sz (by_ .ashr (sext sz a) n))], bit (by_ .ashr (sext sz a) n1) 0, num 0)
  | .rol => ([.set .t2 (band n (num (sz.bits - 1))),
      .set .t0 (low sz (bor (by_ .shl a (r .t2)) (by_ .lshr a back)))], bit t 0, bxor (msb sz t) (r .cf))
  | .ror => ([.set .t2 (band n (num (sz.bits - 1))),
      .set .t0 (low sz (bor (by_ .lshr a (r .t2)) (by_ .shl a back)))], msb sz t, bxor (msb sz t) (bit t (sz.bits - 2)))

/-- A count: what computes it (into `t1`, for `cl`), the count, the count less one, and
    whether it is known not to be zero. A count is taken modulo 64, or 32 below 64 bits. -/
def count (sz : Size) : Count → List O × E × E × Bool
  | .imm n =>
    let m := n % (if sz = .q then 64 else 32)
    ([], num m, num (m - 1), m != 0)
  | .cl =>
    ([.set .t1 (band (g 1) (num (if sz = .q then 63 else 31)))], r .t1,
      band (sub (r .t1) (num 1)) (num 63), false)

/-- A flag set to `e`, or left as it is when the count in `t1` is zero. -/
def setIf (known : Bool) (f : Reg) (e : E) : O :=
  .set f (if known then e else choose (nonZero (r .t1)) e (r f))

/-- The quotient and remainder of the 128 bits `rdx:rax` by the 64 bits of `t5`, into `rax`
    and `rdx`, for `rdx` below `t5`: long division by two digits of 32 bits each, the
    divisor first shifted up until its top bit is set. Each digit of the quotient is an
    estimate from the top digit of the divisor, then corrected down at most twice. -/
def divWide : List O :=
  let vn1 : E := lshr (r .t5) 32
  let vn0 : E := z32 (r .t5)
  let big (e : E) : E := nonZero (lshr e 32)
  -- whether the estimate `q`, with remainder `t1`, is too large for the next digit `d`
  let over (q d : E) : E := bor (big q) (.bin .ult (add (shl (r .t1) 32) d) (.bin .mul q vn0))
  let digit (q : Reg) (num_ d : E) : List O :=
    [.set q (.bin .divu num_ vn1), .set .t1 (sub num_ (.bin .mul (r q) vn1)),
     .set .t2 (over (r q) d), .set q (sub (r q) (r .t2)), .set .t1 (add (r .t1) (.bin .mul (r .t2) vn1)),
     .set .t2 (band (band (r .t2) (flip (big (r .t1)))) (over (r q) d)), .set q (sub (r q) (r .t2))]
  let rax : E := r .rax
  let rdx : E := r .rdx
  [.set .t0 (r .t5)] ++ countLeadingZeros .t0 .t1 ++
  [.set .t4 (r .t0), .set .t5 (.bin .shl (r .t5) (r .t4)),
   .set .rdx (bor (.bin .shl rdx (r .t4)) (.bin .lshr (lshr rax 1) (sub (num 63) (r .t4)))),
   .set .rax (.bin .shl rax (r .t4))] ++
  digit .t0 rdx (lshr rax 32) ++
  [.set .rdx (sub (add (shl rdx 32) (lshr rax 32)) (.bin .mul (r .t0) (r .t5)))] ++
  digit .t3 rdx (z32 rax) ++
  [.set .rdx (.bin .lshr (sub (add (shl rdx 32) (z32 rax)) (.bin .mul (r .t3) (r .t5))) (r .t4)),
   .set .rax (add (shl (r .t0) 32) (r .t3))]

/-! ## Instructions -/

/-- One instruction. Bytes that are no instruction are `none`. -/
def liftI (cx : Cx) (_ : Option (At (Option Instr))) (i : At (Option Instr)) : Lcmd O Reg :=
  let o (ops : List O) : Lcmd O Reg := ops.map .Lopn
  let giveUpIf (op : String) (a : Reg) (b : LOperand Reg) : LinstrR O Reg := .Lcond (.cmp op (.reg a) b) cx.abort
  let rsp : E := r .rsp
  let push (v : E) : List O := [.set .rsp (sub rsp (num 8)), .store .b8 rsp v]
  -- one step of a string instruction, by `df`
  let step (sz : Size) : E := sub (num sz.bytes) (.bin .mul (r .df) (num (2 * sz.bytes)))
  let repeated (rep : Bool) (body : List O) : Lcmd O Reg :=
    if !rep then o body else
    match cx.label i.addr, cx.label i.next with
    | some here, some after =>
      [.Lcond (.cmp "eq" (.reg .rcx) (.imm 0)) after] ++ o (body ++ [.set .rcx (sub (r .rcx) (num 1))]) ++ [.Lgoto here]
    | _, _ => [.Labort]
  match i.instr with
  | none => [.Labort]
  | some ins =>
  match ins with
  | .mov sz dst src =>
    let (ld, v) := rdSrc sz .t5 src
    o (ld ++ wr sz dst v)
  | .movx signed dsz ssz dst src =>
    let (ld, v) := rdLoc ssz .t5 src
    o (ld ++ wr dsz (.reg dst) (if signed then low dsz (.un (.sext (width ssz)) v) else v))
  | .lea sz dst a => o (wr sz (.reg dst) (low sz (addr a)))
  | .alu op sz dst src =>
    -- a register with itself is how a compiler writes zero
    if op = .xor ∧ src = .loc dst ∧ (dst matches .reg _) then
      o ([.set .t0 (num 0), .set .cf (num 0), .set .ovf (num 0), .set .zf (num 1), .set .sf (num 0),
        .set .pf (num 0)] ++ wr sz dst (num 0)) else
    let (la, a) := rdLoc sz .t4 dst
    let (lb, b) := rdSrc sz .t5 src
    o (la ++ lb ++ aluOps op sz a b ++ (if op = .cmp then [] else wr sz dst (r .t0)))
  | .test sz a b =>
    let (la, a) := rdLoc sz .t4 a
    let (lb, b) := rdSrc sz .t5 b
    o (la ++ lb ++ aluOps .and sz a b)
  | .unary op sz dst =>
    let (la, a) := rdLoc sz .t4 dst
    o (la ++ (match op with
      | .not => [.set .t0 (low sz (bnot a))]
      | .neg => [.set .t0 (low sz (.un .neg a)), .set .cf (nonZero a), .set .ovf (same (r .t0) (top sz))] ++ setZS sz
      | .inc => [.set .t0 (low sz (add a (num 1))), .set .ovf (same (r .t0) (top sz))] ++ setZS sz
      | .dec => [.set .t0 (low sz (sub a (num 1))), .set .ovf (same a (top sz))] ++ setZS sz) ++
      wr sz dst (r .t0))
  | .shift op sz dst n =>
    let (la, a) := rdLoc sz .t4 dst
    let (lc, n, n1, known) := count sz n
    let (ops, cf, ovf) := shiftOps op sz a n n1
    if known = false ∧ lc = [] then o (la ++ wr sz dst a) else
    o (la ++ lc ++ ops ++ [setIf known .cf cf, setIf known .ovf ovf] ++
      (if op = .rol ∨ op = .ror then []
       else [setIf known .zf (isZero (r .t0)), setIf known .sf (msb sz (r .t0)), setIf known .pf (r .t0)]) ++
      wr sz dst (r .t0))
  | .shiftd left sz dst src n =>
    if sz = .b ∨ sz = .w then [.Labort] else
    let (la, a) := rdLoc sz .t4 dst
    let b := low sz (g src)
    let (lc, n, n1, known) := count sz n
    if known = false ∧ lc = [] then o (la ++ wr sz dst a) else
    -- the bits that come in from `src`: none when the count is zero
    let rest : E := band (sub (num (sz.bits - 1)) n) (num 63)
    let res : E := if left then bor (.bin .shl a n) (.bin .lshr (lshr b 1) rest)
      else bor (.bin .lshr a n) (.bin .shl (shl b 1) rest)
    let cf : E := if left then bit (.bin .lshr a (band (sub (num sz.bits) n) (num 63))) 0 else bit (.bin .lshr a n1) 0
    o (la ++ lc ++ [.set .t0 (low sz res), setIf known .cf cf, setIf known .ovf (msb sz (bxor a (r .t0))),
      setIf known .zf (isZero (r .t0)), setIf known .sf (msb sz (r .t0)), setIf known .pf (r .t0)] ++
      wr sz dst (r .t0))
  | .mul signed sz src =>
    let (ld, v) := rdLoc sz .t5 src
    let a := low sz (r .rax)
    let ext (e : E) : E := if signed then sext sz e else e
    let flags (e : E) : List O := [.set .cf (nonZero e), .set .ovf (r .cf)]
    o (ld ++ [.set .t5 v] ++ match sz with
      | .q =>
        [.set .t0 (.bin (if signed then .mulh else .mulhu) (r .rax) (r .t5)), .set .rax (.bin .mul (r .rax) (r .t5))] ++
        flags (if signed then bxor (r .t0) (.bin .ashr (r .rax) (num 63)) else r .t0) ++ [.set .rdx (r .t0)]
      | _ =>
        [.set .t0 (.bin .mul (ext a) (ext (r .t5)))] ++
        flags (if signed then bxor (r .t0) (sext sz (r .t0)) else lshr (r .t0) sz.bits) ++
        (if sz = .b then wr .w (.reg 0) (low .w (r .t0))
         else wr sz (.reg 0) (low sz (r .t0)) ++ wr sz (.reg 2) (low sz (lshr (r .t0) sz.bits))))
  | .div signed sz src =>
    let (ld, v) := rdLoc sz .t5 src
    let pre := o (ld ++ [.set .t5 (if signed then sext sz v else v)]) ++ [giveUpIf "eq" .t5 (.imm 0)]
    if sz = .q then
      if signed then
        -- the dividend is `rax` alone, its sign in `rdx`; and not the least number by -1
        pre ++ o [.set .t0 (bxor (r .rdx) (.bin .ashr (r .rax) (num 63)))] ++ [giveUpIf "ne" .t0 (.imm 0)] ++
          o [.set .t0 (band (same (r .rax) (top .q)) (isZero (add (r .t5) (num 1))))] ++ [giveUpIf "ne" .t0 (.imm 0)] ++
          o [.set .t0 (.bin .div (r .rax) (r .t5)), .set .rdx (.bin .rem (r .rax) (r .t5)), .set .rax (r .t0)]
      else pre ++ [giveUpIf "geu" .rdx (.reg .t5)] ++ o divWide
    else
      -- the dividend, of twice the size, fits a register
      let whole : E := if sz = .b then low .w (r .rax) else bor (shl (low sz (r .rdx)) sz.bits) (low sz (r .rax))
      let dividend : E := if !signed then whole else match sz with
        | .b => .un (.sext .b2) whole
        | .w => .un (.sext .b4) whole
        | _ => whole
      pre ++ o [.set .t0 dividend, .set .t1 (.bin (if signed then .div else .divu) (r .t0) (r .t5)),
        .set .t2 (if signed then bxor (r .t1) (sext sz (r .t1)) else lshr (r .t1) sz.bits)] ++
      [giveUpIf "ne" .t2 (.imm 0)] ++
      o ([.set .t2 (.bin (if signed then .rem else .remu) (r .t0) (r .t5))] ++
        (if sz = .b then wr .w (.reg 0) (bor (shl (low .b (r .t2)) 8) (low .b (r .t1)))
         else wr sz (.reg 0) (low sz (r .t1)) ++ wr sz (.reg 2) (low sz (r .t2))))
  | .imul sz dst a b =>
    let (la, a) := rdSrc sz .t4 a
    let (lb, b) := rdSrc sz .t5 b
    o (la ++ lb ++ (if sz = .q then
        [.set .t1 (.bin .mulh a b), .set .t0 (.bin .mul a b),
         .set .cf (nonZero (bxor (r .t1) (.bin .ashr (r .t0) (num 63))))]
      else
        [.set .t1 (.bin .mul (sext sz a) (sext sz b)), .set .t0 (low sz (r .t1)),
         .set .cf (nonZero (bxor (r .t1) (sext sz (r .t1))))]) ++
      [.set .ovf (r .cf)] ++ wr sz (.reg dst) (r .t0))
  | .push src =>
    let (ld, v) := rdSrc .q .t5 src
    o (ld ++ [.set .t0 v] ++ push (r .t0))
  | .pop dst => o ([.load .t0 .b8 false rsp, .set .rsp (add rsp (num 8))] ++ wr .q dst (r .t0))
  | .xchg sz a b =>
    let (la, v) := rdLoc sz .t4 a
    o (la ++ [.set .t0 v, .set .t1 (low sz (g b))] ++ wr sz a (r .t1) ++ wr sz (.reg b) (r .t0))
  | .jcc c t =>
    -- to another function it is a tail call if the condition holds: a branch past one, if not
    (match cx.label t, cx.entry t, cx.label i.next with
    | some l, _, _ => branch c l
    | none, some f, some after => branch c.not after ++ [.Ltail (.direct f)]
    | _, _, _ => [.Labort])
  | .jmp t =>
    (match cx.label t, cx.entry t with
    | some l, _ => [.Lgoto l]
    | none, some f => [.Ltail (.direct f)]
    | none, none => [.Labort])
  | .jmpTo l =>
    let (ld, v) := rdLoc .q .t2 l
    o ld ++ Linked.jump .t2 v [] cx.cands cx.all
  | .call t =>
    (match cx.entry t with
    | some f => o (push (.imm i.next)) ++ [.Lcall i.next (.direct f)] ++ o [.set .rsp (add rsp (num 8))]
    | none => [.Labort])
  | .callTo l =>
    let (ld, v) := rdLoc .q .t2 l
    o (ld ++ [.set .t2 v] ++ push (.imm i.next)) ++ [.Lcall i.next (.indirect (r .t2) cx.all)] ++
      o [.set .rsp (add rsp (num 8))]
  | .ret => [.Lopn (.load .ra .b8 false rsp), .Lret]
  | .setcc c dst => o (wr .b dst (cond c))
  | .cmov c sz dst src =>
    let (ld, v) := rdLoc sz .t5 src
    o (ld ++ wr sz (.reg dst) (choose (cond c) v (low sz (g dst))))
  | .widenA sz =>
    (match sz with
    | .w => o (wr .w (.reg 0) (low .w (.un (.sext .b1) (r .rax))))
    | .d => o [.set .rax (low .d (.un (.sext .b2) (r .rax)))]
    | _ => o [.set .rax (.un (.sext .b4) (r .rax))])
  | .widenD sz => o (wr sz (.reg 2) (low sz (.bin .ashr (sext sz (r .rax)) (num 63))))
  | .bswap sz x =>
    o ([.set .t0 (low sz (g x))] ++ reverseBytes .t0 (if sz = .q then 3 else 2) ++ wr sz (.reg x) (r .t0))
  | .scan op sz dst src =>
    let (ld, v) := rdLoc sz .t5 src
    let old := low sz (g dst)
    -- the number of leading zeros of `t0`, among 64 bits, into `t0`
    let clz (e : E) : List O := .set .t0 e :: countLeadingZeros .t0 .t1
    let lowest : E := band (r .t5) (.un .neg (r .t5))
    o (ld ++ [.set .t5 v] ++ match op with
      | .bsr => clz (r .t5) ++ [.set .zf (isZero (r .t5))] ++
          wr sz (.reg dst) (choose (nonZero (r .t5)) (sub (num 63) (r .t0)) old)
      | .bsf => clz lowest ++ [.set .zf (isZero (r .t5))] ++
          wr sz (.reg dst) (choose (nonZero (r .t5)) (sub (num 63) (r .t0)) old)
      | .tzcnt => clz lowest ++
          [.set .t0 (choose (nonZero (r .t5)) (sub (num 63) (r .t0)) (num sz.bits)),
           .set .cf (isZero (r .t5)), .set .zf (isZero (r .t0))] ++ wr sz (.reg dst) (r .t0)
      | .lzcnt => clz (r .t5) ++
          [.set .t0 (sub (r .t0) (num (64 - sz.bits))), .set .cf (isZero (r .t5)), .set .zf (isZero (r .t0))] ++
          wr sz (.reg dst) (r .t0))
  | .bit op sz dst ix =>
    if sz = .b then [.Labort] else
    let (la, a) := rdLoc sz .t4 dst
    let (lb, b) := rdSrc sz .t5 ix
    let one : E := .bin .shl (num 1) (r .t1)
    o (la ++ lb ++ [.set .t1 (band b (num (sz.bits - 1))), .set .cf (bit (.bin .lshr a (r .t1)) 0)] ++
      match op with
      | .bt => []
      | .bts => wr sz dst (bor a one)
      | .btr => wr sz dst (band a (bnot one))
      | .btc => wr sz dst (bxor a one))
  | .movs sz rep =>
    repeated rep [.load .t0 (width sz) false (r .rsi), .store (width sz) (r .rdi) (r .t0),
      .set .rsi (add (r .rsi) (step sz)), .set .rdi (add (r .rdi) (step sz))]
  | .stos sz rep =>
    repeated rep [.store (width sz) (r .rdi) (low sz (r .rax)), .set .rdi (add (r .rdi) (step sz))]
  | .cld => o [.set .df (num 0)]
  | .std => o [.set .df (num 1)]
  | .leave => o [.set .rsp (r .rbp), .load .rbp .b8 false rsp, .set .rsp (add rsp (num 8))]
  | .syscall => [.Lext 0]
  | .int3 | .ud2 => [.Labort]
  | .nop => []

/-- A function of an x86-64 program. -/
abbrev Fun := Linked.Fun (Option Instr)

/-- **An x86-64 program, lifted.** -/
def liftX86 (fns : List Fun) : Lprog O Reg := Linked.liftProgram liftI fns

end MachineChecked.X86.Lift
