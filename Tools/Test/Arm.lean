/-
  Tools.Test.Arm

  Tests of the AArch64 lift, run when the module is built: each instruction from its word (as
  `llvm-mc --triple=aarch64 --show-encoding` gives its bytes, little-endian), decoded by
  arm64-semantics' `Arm64.decode`, lifted and run (`Tools.Test.Run`), against what the Arm
  Architecture Reference Manual says it does.
-/

import MachineChecked.ARM.Lift.Lift
import Tools.Test.Run

namespace Tools.Test.Arm

open Lprog MachineChecked.ARM.Lift Lprog.ARM
open Lprog.ARM.Reg
open Arm64 (CondCode)

/-- Where the instructions of the tests are: not at the start of a page, for `adrp`. -/
def at0 : BitVec 64 := 0x401234

/-- The instruction of word `w` at `at0`, decoded and lifted, run from `init` and `m`;
    `entries` are the addresses that are functions. -/
def exec (w : Nat) (init : List (Reg × BitVec 64)) (m : Mem := {})
    (entries : List (BitVec 64) := []) : End Reg :=
  match Arm64.decode (BitVec.ofNat 32 w) with
  | some i => run (liftI (cx at0 4 entries) none { addr := at0, size := 4, instr := some i }) init m
  | none => .wrong "does not decode"

/-- Do the registers `want` and the conditions `conds` (as `b.cond` and `csel` read them, 0 or
    1) hold after a run that reaches the next instruction? Flags are checked through the
    lift's `cond`, not through the registers that hold them. -/
def ok (e : End Reg) (want : List (Reg × BitVec 64)) (conds : List (CondCode × Nat) := []) : Bool :=
  match e with
  | .next regs _ =>
    want.all (fun (r, v) => regs r == v) && conds.all fun (c, v) => (cond c).eval regs == BitVec.ofNat 64 v
  | _ => false

/-- The flags N, Z, C, V as conditions: `MI`, `EQ`, `CS`, `VS`. -/
def nzcv (n z c v : Nat) : List (CondCode × Nat) := [(.MI, n), (.EQ, z), (.CS, c), (.VS, v)]

/-- Flags going in, each 0 or 1. -/
def fl (n z c v : Nat) : List (Reg × BitVec 64) :=
  [(nf, BitVec.ofNat 64 n), (zf, BitVec.ofNat 64 z), (cf, BitVec.ofNat 64 c), (vf, BitVec.ofNat 64 v)]

/-- Is the `w` bytes at `a` of the memory after a run that reaches the next instruction `v`? -/
def memIs (e : End Reg) (w : Width) (a v : BitVec 64) : Bool :=
  e.isNext && match e.mem? with
    | some m => m.read w a == v
    | none => false

/-- Does the run leave the function (a call, a return, a system call)? -/
def leaves : End Reg → Bool | .leaves .. => true | _ => false

def max64 : BitVec 64 := -1
def min64 : BitVec 64 := 0x8000000000000000
def maxS64 : BitVec 64 := 0x7fffffffffffffff

/-- Memory for the loads: `a0`..`a7` at `0xfff8`, then four double words from `0x10000`:
    `0x1122334455667788`, `0x8f9eadbccbdae9f8`, `0x0807060504030201`, `0x1817161514131211`. -/
def m0 : Mem := memAt 0xfff8
  [0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7,
   0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11,
   0xf8, 0xe9, 0xda, 0xcb, 0xbc, 0xad, 0x9e, 0x8f,
   0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08,
   0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18]

/-! ## add, sub, cmp, cmn: immediate -/

-- add x0, x1, #1: wraps to 0
#guard ok (exec 0x91000420 [(x1, max64)]) [(x0, 0)]
-- add w0, w1, #1: a W result clears the upper half
#guard ok (exec 0x11000420 [(x1, 0x1_7fffffff)]) [(x0, 0x80000000)]
-- add w0, w1, #1: wraps at 32 bits
#guard ok (exec 0x11000420 [(x1, max64)]) [(x0, 0)]
-- add x0, x1, #1, lsl #12
#guard ok (exec 0x91400420 [(x1, 5)]) [(x0, 0x1005)]
-- adds x0, x1, #1: carry out and zero
#guard ok (exec 0xb1000420 [(x1, max64)]) [(x0, 0)] (nzcv 0 1 1 0)
-- adds x0, x1, #1: signed overflow
#guard ok (exec 0xb1000420 [(x1, maxS64)]) [(x0, min64)] (nzcv 1 0 0 1)
-- adds w0, w1, #1: signed overflow at 32 bits
#guard ok (exec 0x31000420 [(x1, 0x7fffffff)]) [(x0, 0x80000000)] (nzcv 1 0 0 1)
-- adds w0, w1, #1: carry at 32 bits, the upper half of x1 ignored
#guard ok (exec 0x31000420 [(x1, 0x12345678_ffffffff)]) [(x0, 0)] (nzcv 0 1 1 0)
-- subs x0, x1, #1: 0 - 1 borrows (C clear)
#guard ok (exec 0xf1000420 [(x1, 0)]) [(x0, max64)] (nzcv 1 0 0 0)
-- subs x0, x1, #1: INT_MIN - 1 overflows
#guard ok (exec 0xf1000420 [(x1, min64)]) [(x0, maxS64)] (nzcv 0 0 1 1)
-- subs w0, w1, #1: 0 - 1 at 32 bits, zero-extended
#guard ok (exec 0x71000420 [(x1, 0xffffffff_00000000)]) [(x0, 0xffffffff)] (nzcv 1 0 0 0)
-- subs w0, w1, #1: INT32_MIN - 1 overflows
#guard ok (exec 0x71000420 [(x1, 0x80000000)]) [(x0, 0x7fffffff)] (nzcv 0 0 1 1)
-- cmp x1, #5: equal; register 31 as the destination of a flag-setting add is xzr, not sp
#guard ok (exec 0xf100143f [(x0, 77), (x1, 5), (sp, 0x8000)]) [(x0, 77), (x1, 5), (sp, 0x8000)]
  (nzcv 0 1 1 0)
-- cmp x1, #5: 3 < 5, lower and less
#guard ok (exec 0xf100143f [(x1, 3)]) [] (nzcv 1 0 0 0 ++ [(.LT, 1), (.HI, 0), (.LS, 1), (.CC, 1)])
-- cmn w1, #1: -1 + 1 at 32 bits
#guard ok (exec 0x3100043f [(x1, 0xffffffff)]) [] (nzcv 0 1 1 0)
-- add x0, sp, #16: sp as a source
#guard ok (exec 0x910043e0 [(sp, 0x8000)]) [(x0, 0x8010)]
-- mov sp, x1 (add sp, x1, #0)
#guard ok (exec 0x9100003f [(x1, 0x1230)]) [(sp, 0x1230)]
-- mov sp, x1 to a value that is not a multiple of 16: the function gives up
#guard !(exec 0x9100003f [(x1, 0x1234)]).isNext
-- sub sp, sp, #32
#guard ok (exec 0xd10083ff [(sp, 0x8000)]) [(sp, 0x7fe0)]

/-! ## add, sub, cmp: shifted and extended register -/

-- add x0, x1, x2, lsl #4: bits shifted out are lost
#guard ok (exec 0x8b021020 [(x1, 1), (x2, 0x1000000000000001)]) [(x0, 0x11)]
-- sub x0, x1, x2, lsr #4
#guard ok (exec 0xcb421020 [(x1, 0x100), (x2, 0xff0)]) [(x0, 1)]
-- sub w0, w1, w2, asr #4: the shift is arithmetic at 32 bits, on the low half of x2
#guard ok (exec 0x4b821020 [(x1, 0), (x2, 0x1_80000000)]) [(x0, 0x08000000)]
-- adds x0, x1, x2: INT_MIN + INT_MIN
#guard ok (exec 0xab020020 [(x1, min64), (x2, min64)]) [(x0, 0)] (nzcv 0 1 1 1)
-- adds w0, w1, w2: INT32_MIN + INT32_MIN
#guard ok (exec 0x2b020020 [(x1, 0x80000000), (x2, 0x80000000)]) [(x0, 0)] (nzcv 0 1 1 1)
-- adds w0, w1, w2: INT32_MAX + 1
#guard ok (exec 0x2b020020 [(x1, 0x7fffffff), (x2, 1)]) [(x0, 0x80000000)] (nzcv 1 0 0 1)
-- subs x0, x1, x2: 1 - 2
#guard ok (exec 0xeb020020 [(x1, 1), (x2, 2)]) [(x0, max64)] (nzcv 1 0 0 0)
-- subs x0, x1, x2: INT_MAX - (-1) overflows, and borrows
#guard ok (exec 0xeb020020 [(x1, maxS64), (x2, max64)]) [(x0, min64)] (nzcv 1 0 0 1)
-- subs w0, w1, w2: INT32_MIN - 1
#guard ok (exec 0x6b020020 [(x1, 0x80000000), (x2, 1)]) [(x0, 0x7fffffff)] (nzcv 0 0 1 1)
-- cmp x1, x2: equal
#guard ok (exec 0xeb02003f [(x1, 42), (x2, 42)]) [] (nzcv 0 1 1 0 ++ [(.GE, 1), (.GT, 0), (.LE, 1)])
-- cmp x1, x2: -1 against 1: signed less, unsigned higher
#guard ok (exec 0xeb02003f [(x1, max64), (x2, 1)]) []
  (nzcv 1 0 1 0 ++ [(.LT, 1), (.HI, 1), (.CC, 0), (.GT, 0)])
-- cmp w1, w2: only the low halves count
#guard ok (exec 0x6b02003f [(x1, 0x1_00000000), (x2, 0)]) [] (nzcv 0 1 1 0)
-- cmp w1, w2: 1 against 2 at 32 bits
#guard ok (exec 0x6b02003f [(x1, 1), (x2, 0xffffffff_00000002)]) [] (nzcv 1 0 0 0 ++ [(.LT, 1), (.CC, 1)])
-- add x0, sp, x1 (extended, uxtx): register 31 as the first operand is sp
#guard ok (exec 0x8b2163e0 [(sp, 0x8000), (x1, 0x10)]) [(x0, 0x8010)]
-- add x0, x1, w2, sxtw
#guard ok (exec 0x8b22c020 [(x1, 0x100), (x2, 0x12345678_fffffff0)]) [(x0, 0xf0)]
-- add x0, x1, w2, uxtw #2
#guard ok (exec 0x8b224820 [(x1, 0), (x2, 0xffffffff_80000000)]) [(x0, 0x200000000)]
-- add x0, x1, w2, sxtb
#guard ok (exec 0x8b228020 [(x1, 0x1000), (x2, 0x180)]) [(x0, 0xf80)]
-- add w0, w1, w2, uxth: wraps at 32 bits
#guard ok (exec 0x0b222020 [(x1, 0xffffffff), (x2, 0x12340001)]) [(x0, 0)]
-- add w0, w1, w2, uxth: upper half of x1 ignored
#guard ok (exec 0x0b222020 [(x1, 0xaaaaaaaa_00000001), (x2, 0x0002ffff)]) [(x0, 0x10000)]
-- sub x0, sp, x2, lsl #3 (uxtx #3)
#guard ok (exec 0xcb226fe0 [(sp, 0x8000), (x2, 2)]) [(x0, 0x7ff0)]
-- subs x0, x1, w2, sxth: 5 - (-32768)
#guard ok (exec 0xeb22a020 [(x1, 5), (x2, 0x8000)]) [(x0, 0x8005)] (nzcv 0 0 0 0)
-- cmp sp, x1 (extended form, sp the first operand)
#guard ok (exec 0xeb2163ff [(sp, 0x10), (x1, 0x10)]) [(sp, 0x10)] (nzcv 0 1 1 0)
-- neg x0, x1
#guard ok (exec 0xcb0103e0 [(x1, 1)]) [(x0, max64)]
-- negs w0, w1: -INT32_MIN overflows
#guard ok (exec 0x6b0103e0 [(x1, 0x80000000)]) [(x0, 0x80000000)] (nzcv 1 0 0 1)
-- negs w0, w1: -0 sets C (no borrow)
#guard ok (exec 0x6b0103e0 [(x1, 0)]) [(x0, 0)] (nzcv 0 1 1 0)

/-! ## adc, sbc, ngc -/

-- adc x0, x1, x2 with carry in
#guard ok (exec 0x9a020020 ([(x1, 1), (x2, 2)] ++ fl 0 0 1 0)) [(x0, 4)]
-- adc x0, x1, x2 without
#guard ok (exec 0x9a020020 ([(x1, 1), (x2, 2)] ++ fl 0 0 0 0)) [(x0, 3)]
-- adc w0, w1, w2: wraps at 32 bits
#guard ok (exec 0x1a020020 ([(x1, 0xffffffff), (x2, 0)] ++ fl 0 0 1 0)) [(x0, 0)]
-- adcs x0, x1, x2: max + 0 + 1
#guard ok (exec 0xba020020 ([(x1, max64), (x2, 0)] ++ fl 0 0 1 0)) [(x0, 0)] (nzcv 0 1 1 0)
-- adcs x0, x1, x2: INT_MAX + 0 + 1 overflows
#guard ok (exec 0xba020020 ([(x1, maxS64), (x2, 0)] ++ fl 0 0 1 0)) [(x0, min64)] (nzcv 1 0 0 1)
-- adcs x0, x1, x2: max + max + 1 carries
#guard ok (exec 0xba020020 ([(x1, max64), (x2, max64)] ++ fl 0 0 1 0)) [(x0, max64)] (nzcv 1 0 1 0)
-- adcs w0, w1, w2: max + max + 1 at 32 bits
#guard ok (exec 0x3a020020 ([(x1, 0xffffffff), (x2, 0xffffffff)] ++ fl 0 0 1 0)) [(x0, 0xffffffff)]
  (nzcv 1 0 1 0)
-- adcs w0, w1, w2: INT32_MAX + 0 + 1 overflows
#guard ok (exec 0x3a020020 ([(x1, 0x7fffffff), (x2, 0)] ++ fl 0 0 1 0)) [(x0, 0x80000000)]
  (nzcv 1 0 0 1)
-- sbc x0, x1, x2: 5 - 3 with C set
#guard ok (exec 0xda020020 ([(x1, 5), (x2, 3)] ++ fl 0 0 1 0)) [(x0, 2)]
-- sbc x0, x1, x2: 5 - 3 - 1 with C clear
#guard ok (exec 0xda020020 ([(x1, 5), (x2, 3)] ++ fl 0 0 0 0)) [(x0, 1)]
-- sbcs x0, x1, x2: 0 - 0 - 1 borrows
#guard ok (exec 0xfa020020 ([(x1, 0), (x2, 0)] ++ fl 0 0 0 0)) [(x0, max64)] (nzcv 1 0 0 0)
-- sbcs x0, x1, x2: 3 - 3 with C set
#guard ok (exec 0xfa020020 ([(x1, 3), (x2, 3)] ++ fl 0 0 1 0)) [(x0, 0)] (nzcv 0 1 1 0)
-- sbcs w0, w1, w2: 0 - 0 - 1 at 32 bits
#guard ok (exec 0x7a020020 ([(x1, 0), (x2, 0)] ++ fl 0 0 0 0)) [(x0, 0xffffffff)] (nzcv 1 0 0 0)
-- sbcs w0, w1, w2: INT32_MIN - 0 - 1 overflows
#guard ok (exec 0x7a020020 ([(x1, 0x80000000), (x2, 0)] ++ fl 0 0 0 0)) [(x0, 0x7fffffff)]
  (nzcv 0 0 1 1)
-- ngc x0, x2: -5 with C set
#guard ok (exec 0xda0203e0 ([(x2, 5)] ++ fl 0 0 1 0)) [(x0, -5)]
-- ngc x0, x2: -5 - 1 with C clear
#guard ok (exec 0xda0203e0 ([(x2, 5)] ++ fl 0 0 0 0)) [(x0, -6)]
-- ngcs w0, w2: 0 - 0 with C set
#guard ok (exec 0x7a0203e0 ([(x2, 0)] ++ fl 0 0 1 0)) [(x0, 0)] (nzcv 0 1 1 0)

/-! ## Logical immediates -/

-- and x0, x1, #0xff
#guard ok (exec 0x92401c20 [(x1, 0x1234)]) [(x0, 0x34)]
-- and w0, w1, #0xff
#guard ok (exec 0x12001c20 [(x1, max64)]) [(x0, 0xff)]
-- orr x0, x1, #0x5555555555555555 (element of 2)
#guard ok (exec 0xb200f020 [(x1, 0xaaaaaaaaaaaaaaaa)]) [(x0, max64)]
-- orr w0, w1, #0x55555555: the pattern is 32 bits, upper half clear
#guard ok (exec 0x3200f020 [(x1, 0xffffffff_00000000)]) [(x0, 0x55555555)]
-- eor x0, x1, #0x0f0f0f0f0f0f0f0f (element of 8)
#guard ok (exec 0xd200cc20 [(x1, max64)]) [(x0, 0xf0f0f0f0f0f0f0f0)]
-- eor w0, w1, #0xf0f0f0f0 (element of 8, rotated)
#guard ok (exec 0x5204cc20 [(x1, max64)]) [(x0, 0x0f0f0f0f)]
-- and x0, x1, #0xffff0000ffff0000 (element of 32, rotated)
#guard ok (exec 0x92103c20 [(x1, max64)]) [(x0, 0xffff0000ffff0000)]
-- orr w0, w1, #0x80000001 (element of 32, wrapping round)
#guard ok (exec 0x32010420 [(x1, 0)]) [(x0, 0x80000001)]
-- and x0, x1, #0x8000000000000001 (element of 64, wrapping round)
#guard ok (exec 0x92410420 [(x1, max64)]) [(x0, 0x8000000000000001)]
-- eor w0, w1, #0x3c3c3c3c
#guard ok (exec 0x5206cc20 [(x1, 0)]) [(x0, 0x3c3c3c3c)]
-- eor w0, w1, #0x7fff7fff (element of 16)
#guard ok (exec 0x5200b820 [(x1, 0xffffffff)]) [(x0, 0x80008000)]
-- mov x0, #0x00ff00ff00ff00ff (orr from xzr)
#guard ok (exec 0xb2009fe0 [(x0, 7)]) [(x0, 0x00ff00ff00ff00ff)]
-- and x0, x1, #0x7ffffffffffffffe
#guard ok (exec 0x927ff420 [(x1, max64)]) [(x0, 0x7ffffffffffffffe)]
-- and w0, w1, #0xfffffffe
#guard ok (exec 0x121f7820 [(x1, max64)]) [(x0, 0xfffffffe)]
-- mov w0, #0xaaaaaaaa (orr from wzr)
#guard ok (exec 0x3201f3e0 [(x0, max64)]) [(x0, 0xaaaaaaaa)]
-- and sp, x1, #-16: a logical immediate may write sp
#guard ok (exec 0x927cec3f [(x1, 0x1237)]) [(sp, 0x1230)]
-- ands x0, x1, #INT_MIN: N set, C and V cleared
#guard ok (exec 0xf2410020 ([(x1, max64)] ++ fl 0 1 1 1)) [(x0, min64)] (nzcv 1 0 0 0)
-- ands x0, x1, #INT_MIN: zero
#guard ok (exec 0xf2410020 ([(x1, maxS64)] ++ fl 1 0 1 1)) [(x0, 0)] (nzcv 0 1 0 0)
-- ands w0, w1, #0x80000000: N from bit 31
#guard ok (exec 0x72010020 ([(x1, 0xffffffff_80000000)] ++ fl 0 1 1 1)) [(x0, 0x80000000)]
  (nzcv 1 0 0 0)
-- ands w0, w1, #0x80000000: zero at 32 bits
#guard ok (exec 0x72010020 ([(x1, 0xffffffff_7fffffff)] ++ fl 1 0 1 1)) [(x0, 0)] (nzcv 0 1 0 0)
-- tst w1, #1: zero; x0 untouched, and the destination xzr is not sp
#guard ok (exec 0x7200003f [(x0, 9), (x1, 2), (sp, 0x8000)]) [(x0, 9), (sp, 0x8000)] (nzcv 0 1 0 0)
-- tst w1, #1: not zero
#guard ok (exec 0x7200003f [(x1, 1)]) [] (nzcv 0 0 0 0)
-- tst x1, #3: zero, though bit 63 is set
#guard ok (exec 0xf240043f [(x1, 0x8000000000000004)]) [] (nzcv 0 1 0 0)

/-! ## Logical, shifted register -/

-- and x0, x1, x2, lsl #8
#guard ok (exec 0x8a022020 [(x1, max64), (x2, 0xff000000000000ff)]) [(x0, 0xff00)]
-- orr w0, w1, w2, ror #8: rotation at 32 bits
#guard ok (exec 0x2ac22020 [(x1, 0), (x2, 0xff)]) [(x0, 0xff000000)]
-- orr w0, w1, w2, ror #8: the upper half of x2 does not rotate in
#guard ok (exec 0x2ac22020 [(x1, 0), (x2, 0xffffffff_00000012)]) [(x0, 0x12000000)]
-- eor x0, x1, x2, ror #60
#guard ok (exec 0xcac2f020 [(x1, 0), (x2, 0xf000000000000001)]) [(x0, 0x1f)]
-- bic x0, x1, x2
#guard ok (exec 0x8a220020 [(x1, 0xff), (x2, 0x0f)]) [(x0, 0xf0)]
-- bic w0, w1, w2, lsr #4
#guard ok (exec 0x0a621020 [(x1, max64), (x2, 0xf0)]) [(x0, 0xfffffff0)]
-- orn w0, w1, w2: the inversion is at 32 bits
#guard ok (exec 0x2a220020 [(x1, 0), (x2, 0)]) [(x0, 0xffffffff)]
-- mvn x0, x2
#guard ok (exec 0xaa2203e0 [(x2, 0)]) [(x0, max64)]
-- mvn w0, w2
#guard ok (exec 0x2a2203e0 [(x2, 0x12345678_0000ffff)]) [(x0, 0xffff0000)]
-- eon x0, x1, x2
#guard ok (exec 0xca220020 [(x1, 0xff), (x2, 0xff)]) [(x0, max64)]
-- ands w0, w1, w2: N from bit 31
#guard ok (exec 0x6a020020 [(x1, 0x80000000), (x2, 0xffffffff_80000000)]) [(x0, 0x80000000)]
  (nzcv 1 0 0 0)
-- bics x0, x1, x2: zero, C and V cleared
#guard ok (exec 0xea220020 ([(x1, 0xf), (x2, 0xf)] ++ fl 1 0 1 1)) [(x0, 0)] (nzcv 0 1 0 0)
-- tst x1, x2, asr #63
#guard ok (exec 0xea82fc3f [(x1, min64), (x2, min64)]) [] (nzcv 1 0 0 0)
-- mov x0, x1 (orr from xzr)
#guard ok (exec 0xaa0103e0 [(x1, 0xdeadbeefcafebabe)]) [(x0, 0xdeadbeefcafebabe)]
-- mov w0, w1
#guard ok (exec 0x2a0103e0 [(x1, 0xdeadbeefcafebabe)]) [(x0, 0xcafebabe)]

/-! ## movz, movn, movk -/

-- movz x0, #0x1234
#guard ok (exec 0xd2824680 [(x0, max64)]) [(x0, 0x1234)]
-- movz x0, #0x1234, lsl #16
#guard ok (exec 0xd2a24680 [(x0, max64)]) [(x0, 0x12340000)]
-- movz x0, #0x1234, lsl #32
#guard ok (exec 0xd2c24680 [(x0, max64)]) [(x0, 0x1234_00000000)]
-- movz x0, #0x1234, lsl #48
#guard ok (exec 0xd2e24680 [(x0, max64)]) [(x0, 0x1234_0000_0000_0000)]
-- movz w0, #0x1234, lsl #16
#guard ok (exec 0x52a24680 [(x0, max64)]) [(x0, 0x12340000)]
-- movn x0, #0x1234
#guard ok (exec 0x92824680 []) [(x0, 0xffffffffffffedcb)]
-- movn x0, #0x1234, lsl #48
#guard ok (exec 0x92e24680 []) [(x0, 0xedcbffffffffffff)]
-- movn w0, #0x1234: inverted at 32 bits
#guard ok (exec 0x12824680 []) [(x0, 0xffffedcb)]
-- movn w0, #0x1234, lsl #16
#guard ok (exec 0x12a24680 []) [(x0, 0xedcbffff)]
-- mov x0, #-1 (movn #0)
#guard ok (exec 0x92800000 []) [(x0, max64)]
-- movk x0, #0xbeef
#guard ok (exec 0xf297dde0 [(x0, 0x1111222233334444)]) [(x0, 0x111122223333beef)]
-- movk x0, #0xbeef, lsl #16
#guard ok (exec 0xf2b7dde0 [(x0, 0x1111222233334444)]) [(x0, 0x11112222beef4444)]
-- movk x0, #0xbeef, lsl #32
#guard ok (exec 0xf2d7dde0 [(x0, 0x1111222233334444)]) [(x0, 0x1111beef33334444)]
-- movk x0, #0xbeef, lsl #48
#guard ok (exec 0xf2f7dde0 [(x0, 0x1111222233334444)]) [(x0, 0xbeef222233334444)]
-- movk w0, #0xbeef, lsl #16: the upper half is cleared
#guard ok (exec 0x72b7dde0 [(x0, 0x1111222233334444)]) [(x0, 0xbeef4444)]
-- movk w0, #0xbeef
#guard ok (exec 0x7297dde0 [(x0, 0x1111222233334444)]) [(x0, 0x3333beef)]

/-! ## Bitfields: ubfm, sbfm, bfm and their aliases; extr -/

-- lsl x0, x1, #4
#guard ok (exec 0xd37cec20 [(x1, 0xf000000000000001)]) [(x0, 0x10)]
-- lsl w0, w1, #31
#guard ok (exec 0x53010020 [(x1, max64)]) [(x0, 0x80000000)]
-- lsr x0, x1, #4
#guard ok (exec 0xd344fc20 [(x1, min64)]) [(x0, 0x0800000000000000)]
-- lsr w0, w1, #31: bit 32 of x1 is not shifted in
#guard ok (exec 0x531f7c20 [(x1, 0x1_00000000)]) [(x0, 0)]
-- lsr w0, w1, #31
#guard ok (exec 0x531f7c20 [(x1, 0x1_80000000)]) [(x0, 1)]
-- asr x0, x1, #4
#guard ok (exec 0x9344fc20 [(x1, min64)]) [(x0, 0xf800000000000000)]
-- asr w0, w1, #4: the sign is bit 31
#guard ok (exec 0x13047c20 [(x1, 0x80000000)]) [(x0, 0xf8000000)]
-- asr w0, w1, #4: bit 31 clear, the upper half of x1 set
#guard ok (exec 0x13047c20 [(x1, 0xffffffff_7fffffff)]) [(x0, 0x07ffffff)]
-- asr x0, x1, #63
#guard ok (exec 0x937ffc20 [(x1, min64)]) [(x0, max64)]
-- ubfx x0, x1, #8, #8
#guard ok (exec 0xd3483c20 [(x1, 0x12345678)]) [(x0, 0x56)]
-- ubfx w0, w1, #28, #4
#guard ok (exec 0x531c7c20 [(x1, 0xffffffff_a0000000)]) [(x0, 0xa)]
-- sbfx x0, x1, #8, #8: negative field
#guard ok (exec 0x93483c20 [(x1, 0x8000)]) [(x0, 0xffffffffffffff80)]
-- sbfx x0, x1, #8, #8: positive field
#guard ok (exec 0x93483c20 [(x1, 0x7f00)]) [(x0, 0x7f)]
-- sbfx w0, w1, #4, #8: sign-extended to 32 bits only
#guard ok (exec 0x13042c20 [(x1, 0x800)]) [(x0, 0xffffff80)]
-- bfi x0, x1, #8, #8: the rest of x0 kept
#guard ok (exec 0xb3781c20 [(x0, max64), (x1, 0x12a5)]) [(x0, 0xffffffffffffa5ff)]
-- bfi w0, w1, #28, #4: the upper half of x0 cleared
#guard ok (exec 0x33040c20 [(x0, 0xaaaaaaaa_0fffffff), (x1, 5)]) [(x0, 0x5fffffff)]
-- bfxil x0, x1, #8, #8
#guard ok (exec 0xb3483c20 [(x0, 0x1111111111111111), (x1, 0xab00)]) [(x0, 0x11111111111111ab)]
-- bfxil w0, w1, #16, #16
#guard ok (exec 0x33107c20 [(x0, max64), (x1, 0x12340000)]) [(x0, 0xffff1234)]
-- sxtb x0, w1
#guard ok (exec 0x93401c20 [(x1, 0x180)]) [(x0, 0xffffffffffffff80)]
-- sxth w0, w1: to 32 bits
#guard ok (exec 0x13003c20 [(x1, 0x8000)]) [(x0, 0xffff8000)]
-- sxtw x0, w1
#guard ok (exec 0x93407c20 [(x1, 0x12345678_80000000)]) [(x0, 0xffffffff80000000)]
-- uxtb w0, w1
#guard ok (exec 0x53001c20 [(x1, max64)]) [(x0, 0xff)]
-- uxth w0, w1
#guard ok (exec 0x53003c20 [(x1, max64)]) [(x0, 0xffff)]
-- sbfiz x0, x1, #4, #8
#guard ok (exec 0x937c1c20 [(x1, 0x80)]) [(x0, 0xfffffffffffff800)]
-- ubfiz w0, w1, #4, #8
#guard ok (exec 0x531c1c20 [(x1, 0xfff)]) [(x0, 0xff0)]
-- extr x0, x1, x2, #8
#guard ok (exec 0x93c22020 [(x1, 0xab), (x2, 0x0123456789abcdef)]) [(x0, 0xab0123456789abcd)]
-- extr w0, w1, w2, #8: the upper half of x2 is not in the pair
#guard ok (exec 0x13822020 [(x1, 0xab), (x2, 0xffffffff_12345678)]) [(x0, 0xab123456)]
-- extr x0, x1, x2, #0 is x2
#guard ok (exec 0x93c20020 [(x1, 0xab), (x2, 0x0123456789abcdef)]) [(x0, 0x0123456789abcdef)]
-- ror x0, x1, #4
#guard ok (exec 0x93c11020 [(x1, 1)]) [(x0, 0x1000000000000000)]
-- ror w0, w1, #4
#guard ok (exec 0x13811020 [(x1, 0xffffffff_0000000f)]) [(x0, 0xf0000000)]

/-! ## Variable shifts: the amount is taken modulo the width -/

-- lsl x0, x1, x2: by 64 is by 0
#guard ok (exec 0x9ac22020 [(x1, 1), (x2, 64)]) [(x0, 1)]
-- lsl x0, x1, x2: by 65 is by 1
#guard ok (exec 0x9ac22020 [(x1, 1), (x2, 65)]) [(x0, 2)]
-- lsl x0, x1, x2: by 63
#guard ok (exec 0x9ac22020 [(x1, 1), (x2, 63)]) [(x0, min64)]
-- lsl w0, w1, w2: by 32 is by 0
#guard ok (exec 0x1ac22020 [(x1, 1), (x2, 32)]) [(x0, 1)]
-- lsl w0, w1, w2: by 4 at 32 bits
#guard ok (exec 0x1ac22020 [(x1, max64), (x2, 4)]) [(x0, 0xfffffff0)]
-- lsr x0, x1, x2: by 127 is by 63
#guard ok (exec 0x9ac22420 [(x1, min64), (x2, 127)]) [(x0, 1)]
-- lsr w0, w1, w2: by 31
#guard ok (exec 0x1ac22420 [(x1, 0xffffffff_80000000), (x2, 31)]) [(x0, 1)]
-- lsr w0, w1, w2: by 32 is by 0
#guard ok (exec 0x1ac22420 [(x1, 0xffffffff_80000000), (x2, 32)]) [(x0, 0x80000000)]
-- asr x0, x1, x2: by 68 is by 4
#guard ok (exec 0x9ac22820 [(x1, min64), (x2, 68)]) [(x0, 0xf800000000000000)]
-- asr w0, w1, w2: by 36 is by 4, sign from bit 31
#guard ok (exec 0x1ac22820 [(x1, 0x80000000), (x2, 36)]) [(x0, 0xf8000000)]
-- ror x0, x1, x2: by 1
#guard ok (exec 0x9ac22c20 [(x1, 1), (x2, 1)]) [(x0, min64)]
-- ror x0, x1, x2: by 64 is by 0
#guard ok (exec 0x9ac22c20 [(x1, 1), (x2, 64)]) [(x0, 1)]
-- ror w0, w1, w2: by 33 is by 1, at 32 bits
#guard ok (exec 0x1ac22c20 [(x1, 1), (x2, 33)]) [(x0, 0x80000000)]
-- ror w0, w1, w2: by 0 still clears the upper half
#guard ok (exec 0x1ac22c20 [(x1, 0xffffffff_00000001), (x2, 0)]) [(x0, 1)]

/-! ## Multiplication and division -/

-- madd x0, x1, x2, x3
#guard ok (exec 0x9b020c20 [(x1, 3), (x2, 4), (x3, 5)]) [(x0, 17)]
-- madd x0, x1, x2, x3: the product wraps
#guard ok (exec 0x9b020c20 [(x1, 0x1_00000000), (x2, 0x1_00000000), (x3, 7)]) [(x0, 7)]
-- msub x0, x1, x2, x3
#guard ok (exec 0x9b028c20 [(x1, 3), (x2, 4), (x3, 5)]) [(x0, -7)]
-- mul w0, w1, w2: the low 32 bits of the product
#guard ok (exec 0x1b027c20 [(x1, 0x10000), (x2, 0x10001)]) [(x0, 0x10000)]
-- madd w0, w1, w2, w3: -1 * 2 + 1
#guard ok (exec 0x1b020c20 [(x1, 0xffffffff), (x2, 2), (x3, 1)]) [(x0, 0xffffffff)]
-- msub w0, w1, w2, w3: 0 - 6
#guard ok (exec 0x1b028c20 [(x1, 2), (x2, 3), (x3, 0)]) [(x0, 0xfffffffa)]
-- mneg x0, x1, x2
#guard ok (exec 0x9b02fc20 [(x1, 3), (x2, 4)]) [(x0, -12)]
-- smull x0, w1, w2: -1 * 2
#guard ok (exec 0x9b227c20 [(x1, 0xffffffff), (x2, 2)]) [(x0, -2)]
-- smull x0, w1, w2: INT32_MIN squared
#guard ok (exec 0x9b227c20 [(x1, 0x80000000), (x2, 0x80000000)]) [(x0, 0x4000000000000000)]
-- umull x0, w1, w2
#guard ok (exec 0x9ba27c20 [(x1, 0xffffffff), (x2, 0xffffffff)]) [(x0, 0xfffffffe00000001)]
-- umull x0, w1, w2: the upper half of x1 ignored
#guard ok (exec 0x9ba27c20 [(x1, 0x12345678_ffffffff), (x2, 2)]) [(x0, 0x1fffffffe)]
-- smaddl x0, w1, w2, x3: 10 + (-1 * 5)
#guard ok (exec 0x9b220c20 [(x1, 0xffffffff), (x2, 5), (x3, 10)]) [(x0, 5)]
-- umsubl x0, w1, w2, x3: 0 - 0xffffffff
#guard ok (exec 0x9ba28c20 [(x1, 0xffffffff), (x2, 1), (x3, 0)]) [(x0, 0xffffffff00000001)]
-- smulh x0, x1, x2: -1 * -1
#guard ok (exec 0x9b427c20 [(x1, max64), (x2, max64)]) [(x0, 0)]
-- smulh x0, x1, x2: INT_MIN * 2 is -2^64
#guard ok (exec 0x9b427c20 [(x1, min64), (x2, 2)]) [(x0, max64)]
-- smulh x0, x1, x2: INT_MAX squared
#guard ok (exec 0x9b427c20 [(x1, maxS64), (x2, maxS64)]) [(x0, 0x3fffffffffffffff)]
-- umulh x0, x1, x2: max squared
#guard ok (exec 0x9bc27c20 [(x1, max64), (x2, max64)]) [(x0, 0xfffffffffffffffe)]
-- umulh x0, x1, x2: 2^32 squared
#guard ok (exec 0x9bc27c20 [(x1, 0x1_00000000), (x2, 0x1_00000000)]) [(x0, 1)]
-- udiv x0, x1, x2
#guard ok (exec 0x9ac20820 [(x1, 7), (x2, 2)]) [(x0, 3)]
-- udiv x0, x1, x2: unsigned
#guard ok (exec 0x9ac20820 [(x1, max64), (x2, 2)]) [(x0, maxS64)]
-- udiv x0, x1, x2: by zero is 0
#guard ok (exec 0x9ac20820 [(x0, 9), (x1, 7), (x2, 0)]) [(x0, 0)]
-- udiv w0, w1, w2: only the low half of x2
#guard ok (exec 0x1ac20820 [(x1, 0xffffffff), (x2, 0x1_00000002)]) [(x0, 0x7fffffff)]
-- udiv w0, w1, w2: by a zero low half is 0
#guard ok (exec 0x1ac20820 [(x0, 9), (x1, 0xffffffff), (x2, 0x1_00000000)]) [(x0, 0)]
-- sdiv x0, x1, x2: rounds toward zero
#guard ok (exec 0x9ac20c20 [(x1, -7), (x2, 2)]) [(x0, -3)]
-- sdiv x0, x1, x2: 7 / -2
#guard ok (exec 0x9ac20c20 [(x1, 7), (x2, -2)]) [(x0, -3)]
-- sdiv x0, x1, x2: INT_MIN / -1 is INT_MIN
#guard ok (exec 0x9ac20c20 [(x1, min64), (x2, max64)]) [(x0, min64)]
-- sdiv x0, x1, x2: by zero is 0
#guard ok (exec 0x9ac20c20 [(x0, 9), (x1, -7), (x2, 0)]) [(x0, 0)]
-- sdiv w0, w1, w2: INT32_MIN / -1, zero-extended
#guard ok (exec 0x1ac20c20 [(x1, 0x80000000), (x2, 0xffffffff)]) [(x0, 0x80000000)]
-- sdiv w0, w1, w2: -7 / 2 at 32 bits
#guard ok (exec 0x1ac20c20 [(x1, 0xfffffff9), (x2, 2)]) [(x0, 0xfffffffd)]
-- sdiv w0, w1, w2: by zero is 0
#guard ok (exec 0x1ac20c20 [(x0, 9), (x1, 0xfffffff9), (x2, 0)]) [(x0, 0)]

/-! ## clz, cls, rbit, rev -/

-- clz x0, x1: of 0
#guard ok (exec 0xdac01020 [(x1, 0)]) [(x0, 64)]
-- clz x0, x1: of 1
#guard ok (exec 0xdac01020 [(x1, 1)]) [(x0, 63)]
-- clz x0, x1: of INT_MIN
#guard ok (exec 0xdac01020 [(x1, min64)]) [(x0, 0)]
-- clz w0, w1: of 0
#guard ok (exec 0x5ac01020 [(x1, 0)]) [(x0, 32)]
-- clz w0, w1: the upper half of x1 ignored
#guard ok (exec 0x5ac01020 [(x1, 0xffffffff_00000001)]) [(x0, 31)]
-- clz w0, w1: of bit 31
#guard ok (exec 0x5ac01020 [(x1, 0x80000000)]) [(x0, 0)]
-- cls x0, x1: of 0
#guard ok (exec 0xdac01420 [(x1, 0)]) [(x0, 63)]
-- cls x0, x1: of -1
#guard ok (exec 0xdac01420 [(x1, max64)]) [(x0, 63)]
-- cls x0, x1: of 1
#guard ok (exec 0xdac01420 [(x1, 1)]) [(x0, 62)]
-- cls x0, x1: of 0xc000000000000000
#guard ok (exec 0xdac01420 [(x1, 0xc000000000000000)]) [(x0, 1)]
-- cls x0, x1: of INT_MIN
#guard ok (exec 0xdac01420 [(x1, min64)]) [(x0, 0)]
-- cls w0, w1: of -1 at 32 bits
#guard ok (exec 0x5ac01420 [(x1, 0xffffffff)]) [(x0, 31)]
-- cls w0, w1: of a zero low half
#guard ok (exec 0x5ac01420 [(x1, 0xffffffff_00000000)]) [(x0, 31)]
-- cls w0, w1: of 0x40000000
#guard ok (exec 0x5ac01420 [(x1, 0x40000000)]) [(x0, 0)]
-- cls w0, w1: of 0xffff
#guard ok (exec 0x5ac01420 [(x1, 0xffff)]) [(x0, 15)]
-- rbit x0, x1
#guard ok (exec 0xdac00020 [(x1, 0x0123456789abcdef)]) [(x0, 0xf7b3d591e6a2c480)]
-- rbit x0, x1: of 0
#guard ok (exec 0xdac00020 [(x0, 5), (x1, 0)]) [(x0, 0)]
-- rbit w0, w1
#guard ok (exec 0x5ac00020 [(x1, 0xffffffff_00000003)]) [(x0, 0xc0000000)]
-- rev x0, x1
#guard ok (exec 0xdac00c20 [(x1, 0x0123456789abcdef)]) [(x0, 0xefcdab8967452301)]
-- rev x0, x1: of 0
#guard ok (exec 0xdac00c20 [(x0, 5), (x1, 0)]) [(x0, 0)]
-- rev w0, w1
#guard ok (exec 0x5ac00820 [(x1, 0xaabbccdd_11223344)]) [(x0, 0x44332211)]
-- rev16 x0, x1
#guard ok (exec 0xdac00420 [(x1, 0x0123456789abcdef)]) [(x0, 0x23016745ab89efcd)]
-- rev16 w0, w1
#guard ok (exec 0x5ac00420 [(x1, 0xaabbccdd_11223344)]) [(x0, 0x22114433)]
-- rev32 x0, x1
#guard ok (exec 0xdac00820 [(x1, 0x0123456789abcdef)]) [(x0, 0x67452301efcdab89)]

/-! ## Conditional select -/

-- csel x0, x1, x2, eq: Z set
#guard ok (exec 0x9a820020 ([(x1, 1), (x2, 2)] ++ fl 0 1 0 0)) [(x0, 1)]
-- csel x0, x1, x2, eq: Z clear
#guard ok (exec 0x9a820020 ([(x1, 1), (x2, 2)] ++ fl 0 0 0 0)) [(x0, 2)]
-- csel w0, w1, w2, lt: N != V, at 32 bits
#guard ok (exec 0x1a82b020 ([(x1, 0xffffffff_00000001), (x2, 0xffffffff_00000002)] ++ fl 1 0 0 0))
  [(x0, 1)]
-- csel w0, w1, w2, lt: N = V
#guard ok (exec 0x1a82b020 ([(x1, 0xffffffff_00000001), (x2, 0xffffffff_00000002)] ++ fl 1 0 0 1))
  [(x0, 2)]
-- csel x0, x1, x2, gt: Z clear, N = V
#guard ok (exec 0x9a82c020 ([(x1, 1), (x2, 2)] ++ fl 1 0 0 1)) [(x0, 1)]
-- csel x0, x1, x2, gt: N != V
#guard ok (exec 0x9a82c020 ([(x1, 1), (x2, 2)] ++ fl 1 0 0 0)) [(x0, 2)]
-- csel x0, x1, x2, ls: C clear
#guard ok (exec 0x9a829020 ([(x1, 1), (x2, 2)] ++ fl 0 0 0 0)) [(x0, 1)]
-- csel x0, x1, x2, ls: C set, Z clear
#guard ok (exec 0x9a829020 ([(x1, 1), (x2, 2)] ++ fl 0 0 1 0)) [(x0, 2)]
-- csel x0, x1, x2, ls: C set, Z set
#guard ok (exec 0x9a829020 ([(x1, 1), (x2, 2)] ++ fl 0 1 1 0)) [(x0, 1)]
-- csel x0, x1, x2, vs
#guard ok (exec 0x9a826020 ([(x1, 1), (x2, 2)] ++ fl 0 0 0 1)) [(x0, 1)]
-- csinc x0, x1, x2, ne: Z set, x2 + 1 wraps
#guard ok (exec 0x9a821420 ([(x1, 1), (x2, max64)] ++ fl 0 1 0 0)) [(x0, 0)]
-- csinc x0, x1, x2, ne: Z clear
#guard ok (exec 0x9a821420 ([(x1, 1), (x2, max64)] ++ fl 0 0 0 0)) [(x0, 1)]
-- csinv w0, w1, w2, ge: N != V, inverted at 32 bits
#guard ok (exec 0x5a82a020 ([(x1, 1), (x2, 0)] ++ fl 1 0 0 0)) [(x0, 0xffffffff)]
-- csinv w0, w1, w2, ge: N = V
#guard ok (exec 0x5a82a020 ([(x1, 0xffffffff_00000001), (x2, 0)] ++ fl 0 0 0 0)) [(x0, 1)]
-- csneg x0, x1, x2, hi: C set, Z clear
#guard ok (exec 0xda828420 ([(x1, 1), (x2, 5)] ++ fl 0 0 1 0)) [(x0, 1)]
-- csneg x0, x1, x2, hi: C set, Z set
#guard ok (exec 0xda828420 ([(x1, 1), (x2, 5)] ++ fl 0 1 1 0)) [(x0, -5)]
-- csneg x0, x1, x2, hi: C clear
#guard ok (exec 0xda828420 ([(x1, 1), (x2, 5)] ++ fl 0 0 0 0)) [(x0, -5)]
-- cset w0, eq
#guard ok (exec 0x1a9f17e0 ([(x0, 7)] ++ fl 0 1 0 0)) [(x0, 1)]
-- cset w0, eq: Z clear
#guard ok (exec 0x1a9f17e0 ([(x0, 7)] ++ fl 0 0 0 0)) [(x0, 0)]
-- csetm x0, lt
#guard ok (exec 0xda9fa3e0 (fl 0 0 0 1)) [(x0, max64)]
-- csetm x0, lt: N = V
#guard ok (exec 0xda9fa3e0 ([(x0, 7)] ++ fl 1 0 0 1)) [(x0, 0)]
-- cinc x0, x1, le: Z set
#guard ok (exec 0x9a81c420 ([(x1, 5)] ++ fl 0 1 0 0)) [(x0, 6)]
-- cinc x0, x1, le: greater
#guard ok (exec 0x9a81c420 ([(x1, 5)] ++ fl 0 0 0 0)) [(x0, 5)]
-- cneg w0, w1, mi: N set, negated at 32 bits
#guard ok (exec 0x5a815420 ([(x1, 1)] ++ fl 1 0 0 0)) [(x0, 0xffffffff)]
-- cneg w0, w1, mi: N clear
#guard ok (exec 0x5a815420 ([(x1, 1)] ++ fl 0 0 0 0)) [(x0, 1)]
-- cinv x0, x1, hs: C set
#guard ok (exec 0xda813020 ([(x1, 0)] ++ fl 0 0 1 0)) [(x0, max64)]
-- cinv x0, x1, hs: C clear
#guard ok (exec 0xda813020 ([(x0, 7), (x1, 0)] ++ fl 0 0 0 0)) [(x0, 0)]

/-! ## Conditional compare -/

-- ccmp x1, x2, #0, eq: the condition holds, the flags of x1 - x2
#guard ok (exec 0xfa420020 ([(x1, 3), (x2, 3)] ++ fl 0 1 0 0)) [] (nzcv 0 1 1 0)
-- ccmp x1, x2, #0, eq: it fails, the flags are #0
#guard ok (exec 0xfa420020 ([(x1, 3), (x2, 3)] ++ fl 1 0 1 1)) [] (nzcv 0 0 0 0)
-- ccmp w1, #5, #15, ne: holds, 3 - 5 at 32 bits
#guard ok (exec 0x7a45182f ([(x1, 0xffffffff_00000003)] ++ fl 0 0 0 0)) [] (nzcv 1 0 0 0)
-- ccmp w1, #5, #15, ne: fails, the flags are #15
#guard ok (exec 0x7a45182f ([(x1, 5)] ++ fl 0 1 0 0)) [] (nzcv 1 1 1 1)
-- ccmn x1, x2, #0, ge: holds, the flags of max + 1
#guard ok (exec 0xba42a020 ([(x1, max64), (x2, 1)] ++ fl 0 0 0 0)) [] (nzcv 0 1 1 0)
-- ccmn x1, x2, #0, ge: fails
#guard ok (exec 0xba42a020 ([(x1, max64), (x2, 1)] ++ fl 1 0 0 0)) [] (nzcv 0 0 0 0)
-- ccmn w1, #1, #4, eq: holds, INT32_MAX + 1 overflows
#guard ok (exec 0x3a410824 ([(x1, 0x7fffffff)] ++ fl 0 1 0 0)) [] (nzcv 1 0 0 1)
-- ccmn w1, #1, #4, eq: fails, the flags are #4 (Z)
#guard ok (exec 0x3a410824 ([(x1, 0x7fffffff)] ++ fl 1 0 1 1)) [] (nzcv 0 1 0 0)

/-! ## Loads -/

-- ldr x0, [x1]
#guard ok (exec 0xf9400020 [(x1, 0x10000)] m0) [(x0, 0x1122334455667788), (x1, 0x10000)]
-- ldr x0, [x1, #8]
#guard ok (exec 0xf9400420 [(x1, 0x10000)] m0) [(x0, 0x8f9eadbccbdae9f8)]
-- ldr w0, [x1, #4]: zero-extended
#guard ok (exec 0xb9400420 [(x0, max64), (x1, 0x10000)] m0) [(x0, 0x11223344)]
-- ldrh w0, [x1, #2]
#guard ok (exec 0x79400420 [(x0, max64), (x1, 0x10000)] m0) [(x0, 0x5566)]
-- ldrb w0, [x1, #1]
#guard ok (exec 0x39400420 [(x0, max64), (x1, 0x10000)] m0) [(x0, 0x77)]
-- ldur x0, [x1, #-8]
#guard ok (exec 0xf85f8020 [(x1, 0x10000)] m0) [(x0, 0xa7a6a5a4a3a2a1a0)]
-- ldrsb w0, [x1]: sign-extended to 32 bits, zero above
#guard ok (exec 0x39c00020 [(x1, 0x10000)] m0) [(x0, 0xffffff88)]
-- ldrsb x0, [x1]: sign-extended to 64 bits
#guard ok (exec 0x39800020 [(x1, 0x10000)] m0) [(x0, 0xffffffffffffff88)]
-- ldrsh w0, [x1]
#guard ok (exec 0x79c00020 [(x1, 0x10008)] m0) [(x0, 0xffffe9f8)]
-- ldrsh x0, [x1]
#guard ok (exec 0x79800020 [(x1, 0x10008)] m0) [(x0, 0xffffffffffffe9f8)]
-- ldrsh x0, [x1]: positive
#guard ok (exec 0x79800020 [(x1, 0x10000)] m0) [(x0, 0x7788)]
-- ldrsw x0, [x1]
#guard ok (exec 0xb9800020 [(x1, 0x10008)] m0) [(x0, 0xffffffffcbdae9f8)]
-- ldrsw x0, [x1]: positive
#guard ok (exec 0xb9800020 [(x1, 0x10000)] m0) [(x0, 0x55667788)]
-- ldr x0, [x1, #16]!: pre-index writes back
#guard ok (exec 0xf8410c20 [(x1, 0x10000)] m0) [(x0, 0x0807060504030201), (x1, 0x10010)]
-- ldr x0, [x1], #16: post-index loads from the old base
#guard ok (exec 0xf8410420 [(x1, 0x10000)] m0) [(x0, 0x1122334455667788), (x1, 0x10010)]
-- ldr w0, [x1, #-4]!
#guard ok (exec 0xb85fcc20 [(x1, 0x10000)] m0) [(x0, 0xa7a6a5a4), (x1, 0xfffc)]
-- ldr x0, [x1, x2, lsl #3]
#guard ok (exec 0xf8627820 [(x1, 0x10000), (x2, 2)] m0) [(x0, 0x0807060504030201)]
-- ldr w0, [x1, w2, sxtw #2]: a negative index
#guard ok (exec 0xb862d820 [(x1, 0x10008), (x2, 0xfffffffe)] m0) [(x0, 0x55667788)]
-- ldrb w0, [x1, w2, uxtw]: the upper half of x2 ignored
#guard ok (exec 0x38624820 [(x1, 0x10000), (x2, 0xffffffff_00000003)] m0) [(x0, 0x55)]
-- ldr x0, [x1, w2, sxtw]
#guard ok (exec 0xf862c820 [(x1, 0x10010), (x2, 0xfffffff8)] m0) [(x0, 0x8f9eadbccbdae9f8)]
-- ldr x0, [sp, #8]
#guard ok (exec 0xf94007e0 [(sp, 0x10000)] m0) [(x0, 0x8f9eadbccbdae9f8)]
-- ldr xzr, [x1]: the load is dropped
#guard ok (exec 0xf940003f [(x0, 5), (x1, 0x10000)] m0) [(x0, 5), (x1, 0x10000)]
-- ldr w1, [x1]: the base is the destination
#guard ok (exec 0xb9400021 [(x1, 0x10000)] m0) [(x1, 0x55667788)]
-- ldp x0, x2, [x1]
#guard ok (exec 0xa9400820 [(x1, 0x10000)] m0) [(x0, 0x1122334455667788), (x2, 0x8f9eadbccbdae9f8)]
-- ldp w0, w2, [x1, #8]
#guard ok (exec 0x29410820 [(x0, max64), (x2, max64), (x1, 0x10000)] m0)
  [(x0, 0xcbdae9f8), (x2, 0x8f9eadbc)]
-- ldp x0, x2, [x1, #16]!
#guard ok (exec 0xa9c10820 [(x1, 0x10000)] m0)
  [(x0, 0x0807060504030201), (x2, 0x1817161514131211), (x1, 0x10010)]
-- ldp x0, x2, [x1], #16
#guard ok (exec 0xa8c10820 [(x1, 0x10000)] m0)
  [(x0, 0x1122334455667788), (x2, 0x8f9eadbccbdae9f8), (x1, 0x10010)]
-- ldpsw x0, x2, [x1]
#guard ok (exec 0x69400820 [(x1, 0x10008)] m0) [(x0, 0xffffffffcbdae9f8), (x2, 0xffffffff8f9eadbc)]
-- ldp x1, x2, [x1]: the base is the first destination
#guard ok (exec 0xa9400821 [(x1, 0x10000)] m0) [(x1, 0x1122334455667788), (x2, 0x8f9eadbccbdae9f8)]
-- ldr x0, #8 (literal)
#guard ok (exec 0x58000040 [] (memAt (at0 + 8) [1, 2, 3, 4, 5, 6, 7, 8])) [(x0, 0x0807060504030201)]
-- ldr w0, #-4 (literal): four bytes, zero-extended
#guard ok (exec 0x18ffffe0 [(x0, 5)] (memAt (at0 - 4) [0xff, 0xff, 0xff, 0xff, 0xee])) [(x0, 0xffffffff)]
-- ldrsw x0, #16 (literal)
#guard ok (exec 0x98000080 [] (memAt (at0 + 16) [0, 0, 0, 0x80, 0xee])) [(x0, 0xffffffff80000000)]

/-! ## Stores -/

-- str x0, [x1]
#guard memIs (exec 0xf9000020 [(x0, 0x1122334455667788), (x1, 0x2000)]) .b8 0x2000 0x1122334455667788
-- str w0, [x1, #4]: four bytes
#guard memIs (exec 0xb9000420 [(x0, 0xaabbccdd11223344), (x1, 0x2000)]) .b8 0x2000 0x11223344_00000000
-- str w0, [x1, #4]: nothing past them
#guard memIs (exec 0xb9000420 [(x0, 0xaabbccdd11223344), (x1, 0x2000)]) .b1 0x2008 0
-- strh w0, [x1]: two bytes, the rest kept
#guard memIs (exec 0x79000020 [(x0, 0x1234aaaa), (x1, 0x10000)] m0) .b8 0x10000 0x112233445566aaaa
-- strb w0, [x1]: one byte
#guard memIs (exec 0x39000020 [(x0, 0x1ff), (x1, 0x10000)] m0) .b8 0x10000 0x11223344556677ff
-- str x0, [x1, #-16]!: stored at the new base
#guard memIs (exec 0xf81f0c20 [(x0, 0x55), (x1, 0x2010)]) .b8 0x2000 0x55
-- str x0, [x1, #-16]!: writes back
#guard ok (exec 0xf81f0c20 [(x0, 0x55), (x1, 0x2010)]) [(x1, 0x2000)]
-- str x0, [x1], #8: stored at the old base
#guard memIs (exec 0xf8008420 [(x0, 0x55), (x1, 0x2000)]) .b8 0x2000 0x55
-- str x0, [x1], #8: writes back
#guard ok (exec 0xf8008420 [(x0, 0x55), (x1, 0x2000)]) [(x1, 0x2008)]
-- str x0, [x1, x2, lsl #3]
#guard memIs (exec 0xf8227820 [(x0, 0x55), (x1, 0x2000), (x2, 3)]) .b8 0x2018 0x55
-- stur w0, [x1, #-1]: unaligned
#guard memIs (exec 0xb81ff020 [(x0, 0x11223344), (x1, 0x2001)]) .b4 0x2000 0x11223344
-- str xzr, [x1]: stores zero
#guard memIs (exec 0xf900003f [(x1, 0x10000)] m0) .b8 0x10000 0
-- stp x0, x2, [x1]: first register
#guard memIs (exec 0xa9000820 [(x0, 0xaa), (x2, 0xbb), (x1, 0x2000)]) .b8 0x2000 0xaa
-- stp x0, x2, [x1]: second register
#guard memIs (exec 0xa9000820 [(x0, 0xaa), (x2, 0xbb), (x1, 0x2000)]) .b8 0x2008 0xbb
-- stp x0, x2, [x1, #-16]!: second register at the new base + 8
#guard memIs (exec 0xa9bf0820 [(x0, 0xaa), (x2, 0xbb), (x1, 0x2010)]) .b8 0x2008 0xbb
-- stp x0, x2, [x1, #-16]!: writes back
#guard ok (exec 0xa9bf0820 [(x0, 0xaa), (x2, 0xbb), (x1, 0x2010)]) [(x1, 0x2000)]
-- stp w0, w2, [x1], #8: two words
#guard memIs (exec 0x28810820 [(x0, 0xffffffff_11111111), (x2, 0xffffffff_22222222), (x1, 0x2000)])
  .b8 0x2000 0x2222222211111111
-- stp w0, w2, [x1], #8: writes back
#guard ok (exec 0x28810820 [(x0, 0xffffffff_11111111), (x2, 0xffffffff_22222222), (x1, 0x2000)])
  [(x1, 0x2008)]
-- stp x29, x30, [sp, #-16]!: the frame record
#guard memIs (exec 0xa9bf7bfd [(x29, 0x1d), (x30, 0x1e), (sp, 0x3000)]) .b8 0x2ff0 0x1d
-- stp x29, x30, [sp, #-16]!: the link register above it
#guard memIs (exec 0xa9bf7bfd [(x29, 0x1d), (x30, 0x1e), (sp, 0x3000)]) .b8 0x2ff8 0x1e
-- stp x29, x30, [sp, #-16]!: sp written back
#guard ok (exec 0xa9bf7bfd [(x29, 0x1d), (x30, 0x1e), (sp, 0x3000)]) [(sp, 0x2ff0)]

/-! ## adr, adrp -/

-- adr x0, #16
#guard ok (exec 0x10000080 []) [(x0, at0 + 16)]
-- adr x0, #-4
#guard ok (exec 0x10ffffe0 []) [(x0, at0 - 4)]
-- adrp x0, #4096: from the page of the instruction
#guard ok (exec 0xb0000000 []) [(x0, 0x402000)]
-- adrp x0, #-4096
#guard ok (exec 0xf0ffffe0 []) [(x0, 0x400000)]

/-! ## Branches -/

-- b #8
#guard (exec 0x14000002 []).isTaken
-- b #4: to the next instruction
#guard (exec 0x14000001 []).isNext
-- b.eq #8: Z set
#guard (exec 0x54000040 (fl 0 1 0 0)).isTaken
-- b.eq #8: Z clear
#guard (exec 0x54000040 (fl 0 0 0 0)).isNext
-- b.ne #8: Z clear
#guard (exec 0x54000041 (fl 0 0 0 0)).isTaken
-- b.cs #8: C set
#guard (exec 0x54000042 (fl 0 0 1 0)).isTaken
-- b.cs #8: C clear
#guard (exec 0x54000042 (fl 0 0 0 0)).isNext
-- b.lt #8: N != V
#guard (exec 0x5400004b (fl 1 0 0 0)).isTaken
-- b.lt #8: N = V
#guard (exec 0x5400004b (fl 1 0 0 1)).isNext
-- b.ge #8: N = V
#guard (exec 0x5400004a (fl 1 0 0 1)).isTaken
-- b.ge #8: N != V
#guard (exec 0x5400004a (fl 0 0 0 1)).isNext
-- b.hi #8: C set, Z clear
#guard (exec 0x54000048 (fl 0 0 1 0)).isTaken
-- b.hi #8: C set, Z set
#guard (exec 0x54000048 (fl 0 1 1 0)).isNext
-- b.hi #8: C clear
#guard (exec 0x54000048 (fl 0 0 0 0)).isNext
-- b.le #8: Z set
#guard (exec 0x5400004d (fl 0 1 0 0)).isTaken
-- b.le #8: Z clear, N = V
#guard (exec 0x5400004d (fl 0 0 0 0)).isNext
-- b.gt #8: Z clear, N = V
#guard (exec 0x5400004c (fl 1 0 0 1)).isTaken
-- b.gt #8: Z set
#guard (exec 0x5400004c (fl 0 1 0 0)).isNext
-- cbz w1: only the low half is tested
#guard (exec 0x34000041 [(x1, 0x1_00000000)]).isTaken
-- cbz x1: the whole register
#guard (exec 0xb4000041 [(x1, 0x1_00000000)]).isNext
-- cbz x1: zero
#guard (exec 0xb4000041 [(x1, 0)]).isTaken
-- cbnz w1: the low half is zero
#guard (exec 0x35000041 [(x1, 0x1_00000000)]).isNext
-- cbnz x1
#guard (exec 0xb5000041 [(x1, 0x1_00000000)]).isTaken
-- tbz x1, #0: bit clear
#guard (exec 0x36000041 [(x1, 2)]).isTaken
-- tbz x1, #0: bit set
#guard (exec 0x36000041 [(x1, 1)]).isNext
-- tbnz x1, #63: bit set
#guard (exec 0xb7f80041 [(x1, min64)]).isTaken
-- tbnz x1, #63: bit clear
#guard (exec 0xb7f80041 [(x1, maxS64)]).isNext
-- tbz w1, #31: bit 31 clear, bit 32 set
#guard (exec 0x36f80041 [(x1, 0x1_00000000)]).isTaken
-- tbz w1, #31: bit set
#guard (exec 0x36f80041 [(x1, 0x80000000)]).isNext
-- tbnz w1, #31: bit set
#guard (exec 0x37f80041 [(x1, 0x80000000)]).isTaken

/-! ## Calls, returns, system calls, and what is not lifted -/

-- bl #256 to a function: a call
#guard leaves (exec 0x94000040 [] {} [at0 + 256])
-- bl #256 to no function: gives up
#guard (exec 0x94000040 []).isAbort
-- blr x1: an indirect call
#guard leaves (exec 0xd63f0020 [(x1, 0x5000)])
-- ret: a return
#guard leaves (exec 0xd65f03c0 [])
-- ret x1: through another register than x30, not lifted (LIMITS.md)
#guard (exec 0xd65f0020 []).isAbort
-- svc #0: the external call
#guard leaves (exec 0xd4000001 [])
-- brk #0: not lifted
#guard (exec 0xd4200000 []).isAbort
-- nop: nothing changes
#guard ok (exec 0xd503201f [(x0, 5), (sp, 0x100)]) [(x0, 5), (sp, 0x100)]

end Tools.Test.Arm
