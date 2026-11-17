/-
  Tools.Test.Text

  Tests of the text format of Lprog (`lprog/Lprog/Text.lean`) at the level the tool
  uses it: `toText` and `ofText` (`Tools/Decompile.lean` writes a program with `toText` and
  checks that `ofText` reads it back), over RISC-V's registers. `parse (print p) = some p` is
  proved on tokens; these tests are of the text: the lexer, numbers in decimal and
  hexadecimal, comments, names, and text that is not a program, which must read as nothing.
-/

import LprogRiscV.Instance

namespace Tools.Test.Text

open Lprog
open RiscvZkvm.Rv64 (Reg)

abbrev P := Lprog (Op Reg) Reg
abbrev I := LinstrR (Op Reg) Reg

/-- The program a text is. -/
def rd (s : String) : Option P := ofText s

/-- Does `p` read back from its text? -/
def rt (p : P) : Bool := rd (toText p) == some p

/-- A program of one function with `body`. -/
def one (body : List I) (name : String := "f") (addr : BitVec 64 := 0x201000) (depth : Nat := 0) :
    P :=
  [{ name, addr, body, depth }]

def all64 : BitVec 64 := -1

/-! ## Round trips: every instruction and operand form -/

/-- Every operation, label kind, jump, call and leaving, and every operand form. -/
def every : List I :=
  [.Llabel .internal 0,
    .Llabel .external 7,
    .Lopn (.set .x5 (.bin .add (.reg .x10) (.imm 8))),
    .Lopn (.set .x5 (.imm all64)),
    .Lopn (.set .x5 (.imm 0)),
    .Lopn (.set .x5 (.imm 4095)),
    .Lopn (.set .x5 (.imm 4096)),
    .Lopn (.set .x5 (.imm 0x8000000000000000)),
    .Lopn (.set .x31 (.un (.sext .b4) (.bin .lshr (.un (.zext .b4) (.reg .x1)) (.imm 31)))),
    .Lopn (.load .x6 .b1 true (.bin .add (.reg .x2) (.imm 0xfffffffffffffff8))),
    .Lopn (.load .x6 .b8 false (.reg .x2)),
    .Lopn (.store .b2 (.reg .x2) (.imm 0xffff)),
    .Lopn .skip,
    .Lgoto 0,
    .Lcond (.cmp "eq" (.reg .x5) (.imm 0)) 0,
    .Lcond (.cmp "lt" (.reg .x5) (.imm (-2048))) 7,
    .Lcond (.cmp "geu" (.imm (-1)) (.imm 18446744073709551615)) 0,
    .Lcond (.cmp "ne" (.cmp "eq" (.reg .x1) (.imm 1)) (.imm 0)) 0,
    .Lcond (.reg .x7) 0,
    .Lcond (.imm (-1)) 0,
    .Ligoto (.reg .x0) [],
    .Ligoto (.bin .and (.reg .x6) (.imm 0xfffffffffffffffe)) [(0x201000, 0), (all64, 7)],
    .Lcall 0x201008 (.direct 3),
    .Lcall 0 (.indirect (.reg .x11) [0, 1, 2]),
    .Lcall all64 (.indirect (.imm 0x201000) []),
    .Ltail (.direct 0),
    .Ltail (.indirect (.reg .x6) [5]),
    .Lret,
    .Lext 0,
    .Lext 4096,
    .Labort]

-- every instruction kind and operand form
#guard rt (one every)
-- each instruction alone
#guard every.all fun i => rt (one [i])
-- every unary operation
#guard [UnOp.sext .b1, .sext .b2, .sext .b4, .sext .b8, .zext .b1, .zext .b2, .zext .b4, .zext .b8,
    .not, .neg].all fun op => rt (one [.Lopn (.set .x1 (.un op (.reg .x2)))])
-- every binary operation
#guard [BinOp.add, .sub, .mul, .and, .or, .xor, .shl, .lshr, .ashr, .slt, .ult, .mulh, .mulhsu,
    .mulhu, .div, .divu, .rem, .remu].all fun op => rt (one [.Lopn (.set .x1 (.bin op (.reg .x2) (.imm 3)))])
-- loads of every width, signed and not; stores of every width
#guard [Width.b1, .b2, .b4, .b8].all fun w =>
  rt (one [.Lopn (.load .x1 w true (.reg .x2)), .Lopn (.load .x1 w false (.reg .x2)),
    .Lopn (.store w (.reg .x2) (.reg .x1))])
-- every register
#guard [Reg.x0, .x1, .x2, .x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15,
    .x16, .x17, .x18, .x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29, .x30,
    .x31].all fun r => rt (one [.Lopn (.set r (.reg r))])
-- every comparison a condition names
#guard ["eq", "ne", "lt", "ge", "ltu", "geu"].all fun c =>
  rt (one [.Lcond (.cmp c (.reg .x1) (.imm (-1))) 0])
-- a large negative operand and a large positive one, beyond 64 bits
#guard rt (one [.Lcond (.cmp "eq" (.imm (-(2 ^ 70))) (.imm (2 ^ 70))) 0])

/-! ## Round trips: programs, functions, addresses -/

-- no functions
#guard rt []
-- a function with no body
#guard rt (one [])
-- several functions
#guard rt (one every ++ one [.Lret] "g" 0x201100 ++ one [] "h" 0)
-- address 0, address all ones, a large depth
#guard rt (one [.Lret] "f" 0) && rt (one [.Lret] "f" all64) && rt (one [.Lret] "f" 0 1000000)
-- labels and functions numbered past 4096 (printed in hexadecimal)
#guard rt (one [.Llabel .internal 4096, .Lgoto 65536, .Lcall 0 (.direct 70000)])

/-! ## Names -/

-- names that need no care: Rust's mangling, paths, signs, other scripts
#guard ["_ZN4core3fmt5write17h0123456789abcdefE", "core::fmt::write", "a.b$c", "_start", "λ",
    "-", "x5", "ff", "1e5", "0x", "0xg", "fn", "lprog", "label", "set", "ret", "abort"].all
  fun n => rt (one [.Lret] n)
-- the documented limits: a name that is empty, has white space or `#`, or reads as a number or
-- a register does not read back (the tool checks, and refuses)
#guard ["", "a b", "a\tb", "a\nb", "a#b", "12", "0x1f", "%x5"].all fun n => !rt (one [.Lret] n)
-- and such a name reads as nothing, not as another program
#guard ["", "a b", "a#b", "12", "0x1f", "%x5"].all fun n => rd (toText (one [.Lret] n)) == none

/-! ## The text itself -/

-- the layout: a header, a paragraph for each function, numbers from 4096 in hexadecimal
#guard toText (one [.Llabel .internal 0, .Lopn (.set .x5 (.imm 4095)), .Lret] "f" 4096) ==
  "lprog 1\n\nfn f 0x1000 0 3\n  label 0\n    set %x5 4095\n    ret\n"
-- a program written by hand
#guard rd "lprog 1\nfn memcmp 0x201000 0 4\n  label 0\n    set %x5 add %x10 8\n    if cmp eq %x5 %x0 0\n    ret\n" ==
  some (one [.Llabel .internal 0, .Lopn (.set .x5 (.bin .add (.reg .x10) (.imm 8))),
    .Lcond (.cmp "eq" (.reg .x5) (.reg .x0)) 0, .Lret] "memcmp")
-- decimal and hexadecimal are the same number
#guard rd "lprog 1 fn f 16 0 1 set %x1 0x10" == rd "lprog 1 fn f 0x10 0 1 set %x1 16"
-- comments, blank lines and tabs are white space
#guard rd "# a header\n\nlprog 1 # one\n\tfn f 0 0 1 # f\n\n  ret # back\n#end" == some (one [.Lret] "f" 0)
-- a `#` ends a word
#guard rd "lprog 0#comment" == some []
-- a negative operand is `-` and its magnitude
#guard rd "lprog 1 fn f 0 0 1 if cmp lt %x1 - 5 3" ==
  some (one [.Lcond (.cmp "lt" (.reg .x1) (.imm (-5))) 3] "f" 0)
-- an expression's immediate is unsigned: all ones
#guard rd "lprog 1 fn f 0 0 1 set %x1 0xffffffffffffffff" == some (one [.Lopn (.set .x1 (.imm all64))] "f" 0)

/-! ## Text that is not a program reads as nothing -/

-- empty, or a header without a count, or with too many or too few functions
#guard rd "" == none
#guard rd "lprog" == none
#guard rd "lprog 1" == none
#guard rd "lprog 0 0" == none
#guard rd "lprog 0 ret" == none
-- no header
#guard rd "fn f 0 0 1 ret" == none
-- a body with fewer instructions than it says, or more
#guard rd "lprog 1 fn f 0 0 2 ret" == none
#guard rd "lprog 1 fn f 0 0 1 ret ret" == none
-- a register that does not exist, or by another name
#guard rd "lprog 1 fn f 0 0 1 set %x32 0" == none
#guard rd "lprog 1 fn f 0 0 1 set %sp 0" == none
#guard rd "lprog 1 fn f 0 0 1 set %X5 0" == none
-- an operation that does not exist, or with an operand missing
#guard rd "lprog 1 fn f 0 0 1 set %x5 frob %x1 %x2" == none
#guard rd "lprog 1 fn f 0 0 1 set %x5 add %x1" == none
-- a width or a signedness that does not exist
#guard rd "lprog 1 fn f 0 0 1 load %x5 b3 s %x1" == none
#guard rd "lprog 1 fn f 0 0 1 load %x5 b8 x %x1" == none
#guard rd "lprog 1 fn f 0 0 1 store b16 %x1 %x2" == none
-- an instruction that does not exist
#guard rd "lprog 1 fn f 0 0 1 jump 3" == none
-- a condition without its label
#guard rd "lprog 1 fn f 0 0 1 if cmp eq %x1 %x2" == none
-- `- 0` is no negative number, and `-5` is no number
#guard rd "lprog 1 fn f 0 0 1 if cmp eq %x1 - 0 3" == none
#guard rd "lprog 1 fn f 0 0 1 if cmp eq %x1 -5 3" == none
-- a negative label, or a negative immediate in an expression
#guard rd "lprog 1 fn f 0 0 1 goto - 1" == none
#guard rd "lprog 1 fn f 0 0 1 set %x1 - 1" == none
-- hexadecimal is lower case
#guard rd "lprog 1 fn f 0 0 1 set %x1 0xFF" == none
-- a call without its target, a target that is neither `fn` nor `via`
#guard rd "lprog 1 fn f 0 0 1 call 0" == none
#guard rd "lprog 1 fn f 0 0 1 tail jmp 0" == none
-- a computed jump with fewer candidates than it says
#guard rd "lprog 1 fn f 0 0 1 igoto %x1 2 16 0" == none
-- a function whose name is missing
#guard rd "lprog 1 fn 0 0 0" == none

/-! ## Numbers out of range -/

-- a number too large for its 64-bit field is refused, not read modulo 2^64
#guard rd "lprog 1 fn f 0 0 1 set %x1 0x10000000000000005" == none
-- a function's address
#guard rd "lprog 1 fn f 0x10000000000000000 0 0" == none
-- a call's return address
#guard rd "lprog 1 fn f 0 0 1 call 0x10000000000000000 fn 0" == none
-- a computed jump's candidate
#guard rd "lprog 1 fn f 0 0 1 igoto %x1 1 0x10000000000000010 0" == none
-- the largest that fits is read as it is
#guard (rd "lprog 1 fn f 0xffffffffffffffff 0 0").isSome

end Tools.Test.Text
