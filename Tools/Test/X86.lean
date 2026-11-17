/-
  Tools.Test.X86

  Tests of the x86-64 decoder and lift, run when the module is built: each instruction from its
  bytes (as `llvm-mc --show-encoding` gives them), decoded, lifted and run (`Tools.Test.Run`),
  against what Intel's manual says it does.
-/

import MachineChecked.X86.Lift.Lift
import Tools.Test.Run

namespace Tools.Test.X86

open Lprog MachineChecked.X86.Lift Lprog.X86
open Lprog.X86.Reg

/-- Where the instructions of the tests are. -/
def at0 : BitVec 64 := 0x401000

/-- The instruction of `bytes` at `at0`, decoded and lifted, run from `init` and `m`. -/
def exec (bytes : List Nat) (init : List (Reg × BitVec 64)) (m : Mem := {}) : End Reg :=
  match decode (ByteArray.mk (bytes.map UInt8.ofNat).toArray) 0 at0 with
  | some (i, n) =>
    if n ≠ bytes.length then .wrong s!"decoded {n} of {bytes.length} bytes"
    else run (liftI (cx at0 n) none { addr := at0, size := n, instr := some i }) init m
  | none => .wrong "does not decode"

/-- Do the registers `want` and the conditions `flags` (as `jcc`, `setcc` and `cmov` read
    them, 0 or 1) hold after a run that reaches the next instruction? Flags are checked through
    conditions, not registers: the lift keeps a result in `pf`, and takes its parity when a
    condition reads it. -/
def ok (e : End Reg) (want : List (Reg × BitVec 64)) (flags : List (Cc × Nat) := []) : Bool :=
  match e with
  | .next regs _ =>
    want.all (fun (r, v) => regs r == v) && flags.all fun (c, v) => (cond c).eval regs == BitVec.ofNat 64 v
  | _ => false

def max64 : BitVec 64 := -1
def min64 : BitVec 64 := 0x8000000000000000

/-- The instruction of `bytes` at `at0`, and its length. -/
def dec (bytes : List Nat) : Option (Instr × Nat) :=
  decode (ByteArray.mk (bytes.map UInt8.ofNat).toArray) 0 at0

/-- The length the decoder gives `bytes`. -/
def len (bytes : List Nat) : Option Nat := (dec bytes).map (·.2)

/-- `exec`, in a program whose functions start at `entries`. -/
def execF (bytes : List Nat) (init : List (Reg × BitVec 64)) (entries : List (BitVec 64))
    (m : Mem := {}) : End Reg :=
  match dec bytes with
  | some (i, n) => run (liftI (cx at0 n entries) none { addr := at0, size := n, instr := some i }) init m
  | none => .wrong "does not decode"

/-- `w` bytes of memory at `a` after a run, if it ends with a memory. -/
def rd (e : End Reg) (w : Width) (a : BitVec 64) : Option (BitVec 64) := e.mem?.map (·.read w a)

/-- A run that leaves the function, with the registers `want` where it leaves. -/
def leavesWith (e : End Reg) (want : List (Reg × BitVec 64)) : Bool :=
  match e with
  | .leaves _ regs _ => want.all fun (r, v) => regs r == v
  | _ => false

/-- A run that leaves by `ret`, `call`, a tail call, or the external call `n`. -/
def isRet (e : End Reg) : Bool := match e with | .leaves .Lret .. => true | _ => false
def isCall (e : End Reg) : Bool := match e with | .leaves (.Lcall ..) .. => true | _ => false
def isTail (e : End Reg) : Bool := match e with | .leaves (.Ltail _) .. => true | _ => false
def isExt (e : End Reg) (n : Nat) : Bool := match e with | .leaves (.Lext k) .. => k == n | _ => false

/-! ## add -/

-- add rax, rbx: 1 + 2
#guard ok (exec [0x48, 0x01, 0xd8] [(rax, 1), (rbx, 2)]) [(rax, 3)]
  [(.b, 0), (.e, 0), (.s, 0), (.o, 0), (.p, 1)]
-- add rax, rbx: carry out and zero
#guard ok (exec [0x48, 0x01, 0xd8] [(rax, max64), (rbx, 1)]) [(rax, 0)]
  [(.b, 1), (.e, 1), (.s, 0), (.o, 0), (.p, 1)]
-- add rax, rbx: signed overflow, no carry
#guard ok (exec [0x48, 0x01, 0xd8] [(rax, 0x7fffffffffffffff), (rbx, 1)]) [(rax, min64)]
  [(.b, 0), (.e, 0), (.s, 1), (.o, 1)]
-- add eax, ebx: a 32-bit write clears the upper half, flags at 32 bits
#guard ok (exec [0x01, 0xd8] [(rax, 0xffffffff_ffffffff), (rbx, 1)]) [(rax, 0)] [(.b, 1), (.e, 1)]

/-! ## idiv -/

-- idiv rcx: -7 / 2 (rdx:rax = -7 after cqo) is -3, remainder -1
#guard ok (exec [0x48, 0xf7, 0xf9] [(rax, -7), (rdx, -1), (rcx, 2)]) [(rax, -3), (rdx, -1)]
-- idiv rcx by zero faults, and the lift gives up
#guard (exec [0x48, 0xf7, 0xf9] [(rax, 7), (rcx, 0)]).isAbort
-- idiv rcx with rdx not the sign of rax: a 128-bit dividend the lift does not take
#guard (exec [0x48, 0xf7, 0xf9] [(rax, 7), (rdx, 1), (rcx, 2)]).isAbort

/-! ## Decoding: addresses -/

-- lea rax, [rip + 0x10]: from the end of the instruction, 0x401007
#guard ok (exec [0x48, 0x8d, 0x05, 0x10, 0x00, 0x00, 0x00] []) [(rax, 0x401017)]
-- lea rax, [rip - 8]: a negative disp32
#guard ok (exec [0x48, 0x8d, 0x05, 0xf8, 0xff, 0xff, 0xff] []) [(rax, 0x400fff)]
-- mov dword ptr [rip + 0x100], 0x11223344: the end is after the immediate, at 0x40100a
#guard rd (exec [0xc7, 0x05, 0x00, 0x01, 0x00, 0x00, 0x44, 0x33, 0x22, 0x11] []) .b4 0x40110a
  == some 0x11223344
-- cmp qword ptr [rip + 0x100], 0x12345678: 11 bytes, the end at 0x40100b
#guard ok (exec [0x48, 0x81, 0x3d, 0x00, 0x01, 0x00, 0x00, 0x78, 0x56, 0x34, 0x12] []
  (memAt 0x40110b [0x78, 0x56, 0x34, 0x12])) [] [(.e, 1)]
-- lea rax, [rbx + rcx*4 + 8]: SIB with disp8
#guard ok (exec [0x48, 0x8d, 0x44, 0x8b, 0x08] [(rbx, 0x1000), (rcx, 3)]) [(rax, 0x1014)]
-- lea rax, [rbx + rcx*8 + 0x12345]: SIB with disp32
#guard ok (exec [0x48, 0x8d, 0x84, 0xcb, 0x45, 0x23, 0x01, 0x00] [(rbx, 0x1000), (rcx, 2)])
  [(rax, 0x13355)]
-- lea rax, [rcx*2 + 0x100]: SIB with no base (base 101, mod 00); rbp is not added
#guard ok (exec [0x48, 0x8d, 0x04, 0x4d, 0x00, 0x01, 0x00, 0x00] [(rcx, 5), (rbp, 0x9999)])
  [(rax, 0x10a)]
-- lea rax, [rcx + 0x100] as 49 8d 04 0d: base 101 with REX.B and mod 00 is still no base
#guard ok (exec [0x49, 0x8d, 0x04, 0x0d, 0x00, 0x01, 0x00, 0x00] [(rcx, 5), (r13, 0x9999)])
  [(rax, 0x105)]
-- lea rax, [r12 + r13 - 1]: REX.X and REX.B, disp8 sign-extended
#guard ok (exec [0x4b, 0x8d, 0x44, 0x2c, 0xff] [(r12, 0x100), (r13, 0x20)]) [(rax, 0x11f)]
-- lea rax, [rbx + r12*2]: index 100 with REX.X is r12, not "no index"
#guard ok (exec [0x4a, 0x8d, 0x04, 0x63] [(rbx, 0x10), (r12, 3)]) [(rax, 0x16)]
-- lea rax, [r12*1 + 0x10]: r12 as index with no base
#guard ok (exec [0x4a, 0x8d, 0x04, 0x25, 0x10, 0x00, 0x00, 0x00] [(r12, 0x30), (rbp, 0x9999)])
  [(rax, 0x40)]
-- lea rax, [r13]: needs a disp8 of 0 (mod 00 would be RIP-relative)
#guard ok (exec [0x49, 0x8d, 0x45, 0x00] [(r13, 0x777)]) [(rax, 0x777)]
-- lea rax, [r12]: needs a SIB byte
#guard ok (exec [0x49, 0x8d, 0x04, 0x24] [(r12, 0x888)]) [(rax, 0x888)]
-- lea rax, [rsp + 0x10]: rsp as base, index 100 is none
#guard ok (exec [0x48, 0x8d, 0x44, 0x24, 0x10] [(rsp, 0x7000)]) [(rax, 0x7010)]
-- lea rax, [rbp]: mod 01 with disp8 0
#guard ok (exec [0x48, 0x8d, 0x45, 0x00] [(rbp, 0x5000)]) [(rax, 0x5000)]
-- lea rax, [r13 + r14*2]
#guard ok (exec [0x4b, 0x8d, 0x44, 0x75, 0x00] [(r13, 0x100), (r14, 3)]) [(rax, 0x106)]
-- lea r9, [r10 + r11*4]: REX.R, REX.X, REX.B
#guard ok (exec [0x4f, 0x8d, 0x0c, 0x9a] [(r10, 0x10), (r11, 3)]) [(r9, 0x1c)]
-- lea eax, [rbx + rcx]: the address truncated to 32 bits, upper half cleared
#guard ok (exec [0x8d, 0x04, 0x0b] [(rax, 0xdead00000000), (rbx, 0xffffffff), (rcx, 2)]) [(rax, 1)]
-- lea ax, [rbx + rcx]: 16 bits, the rest of rax kept
#guard ok (exec [0x66, 0x8d, 0x04, 0x0b] [(rax, 0x1111222233334444), (rbx, 0xffff), (rcx, 2)])
  [(rax, 0x1111222233330001)]

/-! ## Decoding: lengths, prefixes and what is not decoded -/

-- movabs rax, imm64 is 10 bytes
#guard len [0x48, 0xb8, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11] = some 10
-- lzcnt ax, bx: 66 F3 0F BD /r is 5 bytes
#guard len [0x66, 0xf3, 0x0f, 0xbd, 0xc3] = some 5
-- cs-prefixed add rax, rbx: the segment prefix is ignored, 4 bytes
#guard ok (exec [0x2e, 0x48, 0x01, 0xd8] [(rax, 1), (rbx, 2)]) [(rax, 3)]
-- je rel32 is 6 bytes, je rel8 2
#guard len [0x0f, 0x84, 0x10, 0x00, 0x00, 0x00] = some 6
#guard len [0x74, 0x10] = some 2
-- lock add: not decoded
#guard dec [0xf0, 0x48, 0x01, 0xd8] = none
-- 67 (32-bit address): not decoded
#guard dec [0x67, 0x8d, 0x04, 0x0b] = none
-- F2 (repne) add: not decoded
#guard dec [0xf2, 0x48, 0x01, 0xd8] = none
-- F3 on an add: not one of its meanings
#guard dec [0xf3, 0x48, 0x01, 0xd8] = none
-- fs-prefixed mov: not decoded
#guard dec [0x64, 0x48, 0x8b, 0x03] = none
-- movsxd eax, ebx (no REX.W): not decoded (LIMITS)
#guard dec [0x63, 0xc3] = none
-- push ax: not decoded (LIMITS)
#guard dec [0x66, 0x50] = none
-- bswap ax: undefined, not decoded
#guard dec [0x66, 0x0f, 0xc8] = none
-- xchg bl, cl: one byte, not decoded (LIMITS)
#guard dec [0x86, 0xd9] = none
-- rcl eax, 1: not decoded (LIMITS)
#guard dec [0xd1, 0xd0] = none
-- bt [rbx], rax: memory with a register index, not decoded (LIMITS)
#guard dec [0x48, 0x0f, 0xa3, 0x03] = none
-- lea rax, rbx (mod 11): no such instruction
#guard dec [0x48, 0x8d, 0xc3] = none
-- a lea cut short in its displacement
#guard dec [0x48, 0x8d, 0x05, 0x10, 0x00] = none
-- the long nops compilers pad with: 66 2e 0f 1f 84 00 .. is 10 bytes, with one more 66 is 11
#guard len [0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] = some 10
#guard len [0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0x00, 0x00, 0x00, 0x00, 0x00] = some 11
-- pause (f3 90) is a nop
#guard ok (exec [0xf3, 0x90] [(rax, 5)]) [(rax, 5)]
-- rep ret (f3 c3) is ret
#guard isRet (exec [0xf3, 0xc3] [(rsp, 0x8000)])
-- xchg eax, r8d (41 90): with REX.B, 90 is not nop, and 32 bits clear both upper halves
#guard ok (exec [0x41, 0x90] [(rax, 0x100000001), (r8, 0x200000002)]) [(rax, 2), (r8, 1)]
-- ud2 and int3 give up
#guard (exec [0x0f, 0x0b] []).isAbort
#guard (exec [0xcc] []).isAbort
-- nop and nop dword ptr [rax] do nothing
#guard ok (exec [0x90] [(rax, 5)]) [(rax, 5)]
#guard ok (exec [0x0f, 0x1f, 0x00] [(rax, 5)]) [(rax, 5)]

/-! ## mov: byte registers, immediates, memory -/

-- mov ah, 0x12: no REX, byte register 4 is ah
#guard ok (exec [0xb4, 0x12] [(rax, 0x1111222233334444)]) [(rax, 0x1111222233331244)]
-- mov spl, 0x12: with REX, byte register 4 is spl
#guard ok (exec [0x40, 0xb4, 0x12] [(rax, 0), (rsp, 0x1122334455667788)])
  [(rax, 0), (rsp, 0x1122334455667712)]
-- mov sil, bl: with REX, 6 is sil
#guard ok (exec [0x40, 0x88, 0xde] [(rsi, 0xaaaaaaaaaaaaaaaa), (rbx, 0x5a)]) [(rsi, 0xaaaaaaaaaaaaaa5a)]
-- mov dh, bl: without REX, 6 is dh
#guard ok (exec [0x88, 0xde] [(rdx, 0), (rsi, 0), (rbx, 0x34)]) [(rdx, 0x3400), (rsi, 0)]
-- mov bh, ch
#guard ok (exec [0x88, 0xef] [(rcx, 0x1200), (rbx, 0xff)]) [(rbx, 0x12ff)]
-- movabs rax, 0x1122334455667788
#guard ok (exec [0x48, 0xb8, 0x88, 0x77, 0x66, 0x55, 0x44, 0x33, 0x22, 0x11] [])
  [(rax, 0x1122334455667788)]
-- mov eax, 0xffffffff: not sign-extended, upper half cleared
#guard ok (exec [0xb8, 0xff, 0xff, 0xff, 0xff] [(rax, 0x1234567800000000)]) [(rax, 0xffffffff)]
-- mov rax, -1 (C7 /0 id): imm32 sign-extended to 64 bits
#guard ok (exec [0x48, 0xc7, 0xc0, 0xff, 0xff, 0xff, 0xff] []) [(rax, max64)]
-- mov ax, 0x1234: the rest kept
#guard ok (exec [0x66, 0xb8, 0x34, 0x12] [(rax, max64)]) [(rax, 0xffffffffffff1234)]
-- mov r8b, 0x55
#guard ok (exec [0x41, 0xb0, 0x55] [(r8, 0xff00)]) [(r8, 0xff55)]
-- mov r15d, 7: upper half cleared
#guard ok (exec [0x41, 0xbf, 0x07, 0x00, 0x00, 0x00] [(r15, max64)]) [(r15, 7)]
-- mov byte ptr [rbx], -1: one byte only
#guard rd (exec [0xc6, 0x03, 0xff] [(rbx, 0x2000)]) .b2 0x2000 == some 0xff
-- mov qword ptr [rbx], -2: imm32 sign-extended
#guard rd (exec [0x48, 0xc7, 0x03, 0xfe, 0xff, 0xff, 0xff] [(rbx, 0x2000)]) .b8 0x2000
  == some 0xfffffffffffffffe
-- mov [rbx + 8], rcx
#guard rd (exec [0x48, 0x89, 0x4b, 0x08] [(rbx, 0x2000), (rcx, 0x0102030405060708)]) .b8 0x2008
  == some 0x0102030405060708
-- mov rax, [rbx + 8]: little-endian
#guard ok (exec [0x48, 0x8b, 0x43, 0x08] [(rbx, 0x2000)] (memAt 0x2008 [1, 2, 3, 4, 5, 6, 7, 8]))
  [(rax, 0x0807060504030201)]
-- mov al, [rbx]: the rest kept
#guard ok (exec [0x8a, 0x03] [(rax, max64), (rbx, 0x2000)] (memAt 0x2000 [0x12, 0x34]))
  [(rax, 0xffffffffffffff12)]
-- mov ax, [rbx]
#guard ok (exec [0x66, 0x8b, 0x03] [(rax, max64), (rbx, 0x2000)] (memAt 0x2000 [0x12, 0x34, 0x56]))
  [(rax, 0xffffffffffff3412)]
-- mov eax, [rbx]: upper half cleared
#guard ok (exec [0x8b, 0x03] [(rax, max64), (rbx, 0x2000)] (memAt 0x2000 [0x12, 0x34, 0x56, 0x78, 0x9a]))
  [(rax, 0x78563412)]

/-! ## Operand sizes and memory operands -/

-- 66 with REX.W: REX.W wins, add rax, rbx at 64 bits
#guard ok (exec [0x66, 0x48, 0x01, 0xd8] [(rax, max64), (rbx, 1)]) [(rax, 0)] [(.b, 1), (.e, 1)]
-- add ax, 0x1234 (66 05 iw): a 2-byte immediate, 4 bytes in all
#guard len [0x66, 0x05, 0x34, 0x12] = some 4
#guard ok (exec [0x66, 0x05, 0x34, 0x12] [(rax, 0xffff0001)]) [(rax, 0xffff1235)]
-- imul ax, bx, 0x1234 (66 69 /r iw)
#guard ok (exec [0x66, 0x69, 0xc3, 0x34, 0x12] [(rbx, 2)]) [(rax, 0x2468)]
-- test ax, 0x1234 (66 a9 iw)
#guard ok (exec [0x66, 0xa9, 0x34, 0x12] [(rax, 0x10001)]) [] [(.e, 1)]
-- mov word ptr [rbx], 0x1234 (66 c7 /0 iw): two bytes written
#guard rd (exec [0x66, 0xc7, 0x03, 0x34, 0x12] [(rbx, 0x2000)] (memAt 0x2000 [9, 9, 9, 9])) .b4 0x2000
  == some 0x09091234
-- add ax, -1: imm8 sign-extended to 16 bits
#guard ok (exec [0x66, 0x83, 0xc0, 0xff] [(rax, 0x10001)]) [(rax, 0x10000)] [(.b, 1), (.e, 1)]
-- cmp eax, -1: imm8 sign-extended to 32 bits; the upper half of rax is not compared
#guard ok (exec [0x83, 0xf8, 0xff] [(rax, 0x1ffffffff)]) [] [(.e, 1), (.b, 0)]
-- xor ax, ax: only ax cleared
#guard ok (exec [0x66, 0x31, 0xc0] [(rax, 0x12345678)]) [(rax, 0x12340000)] [(.e, 1)]
-- mov word ptr [rbx], ax: two bytes written
#guard rd (exec [0x66, 0x89, 0x03] [(rax, 0x11223344), (rbx, 0x2000)] (memAt 0x2000 [0xaa, 0xaa, 0xaa, 0xaa]))
  .b4 0x2000 == some 0xaaaa3344
-- mov rax, [rip + 0x20]: from 0x401027
#guard ok (exec [0x48, 0x8b, 0x05, 0x20, 0x00, 0x00, 0x00] [] (memAt 0x401027 [0x99])) [(rax, 0x99)]
-- mov ah, byte ptr [rbx]
#guard ok (exec [0x8a, 0x23] [(rax, 0xffff), (rbx, 0x2000)] (memAt 0x2000 [0x5a])) [(rax, 0x5aff)]
-- movzx eax, byte ptr [rbx]: one byte loaded
#guard ok (exec [0x0f, 0xb6, 0x03] [(rax, max64), (rbx, 0x2000)] (memAt 0x2000 [0x80, 0xff])) [(rax, 0x80)]
-- inc dword ptr [rbx]: wraps within 4 bytes, CF kept
#guard rd (exec [0xff, 0x03] [(rbx, 0x2000), (cf, 1)] (memAt 0x2000 [0xff, 0xff, 0xff, 0xff, 0x77])) .b8 0x2000
  == some 0x7700000000
#guard ok (exec [0xff, 0x03] [(rbx, 0x2000), (cf, 1)] (memAt 0x2000 [0xff, 0xff, 0xff, 0xff, 0x77])) []
  [(.e, 1), (.b, 1)]
-- add byte ptr [rbx], al
#guard rd (exec [0x00, 0x03] [(rax, 0x20), (rbx, 0x2000)] (memAt 0x2000 [0xf0, 0x11])) .b2 0x2000 == some 0x1110
-- add byte ptr [rbx], 0x80: carries and overflows
#guard ok (exec [0x80, 0x03, 0x80] [(rbx, 0x2000)] (memAt 0x2000 [0x80])) [] [(.b, 1), (.o, 1), (.e, 1)]
-- bt qword ptr [rbx], 67: an immediate offset is taken mod 64, so bit 3
#guard ok (exec [0x48, 0x0f, 0xba, 0x23, 0x43] [(rbx, 0x2000)] (memAt 0x2000 [0x08])) [] [(.b, 1)]
-- sete byte ptr [rbx]: one byte written
#guard rd (exec [0x0f, 0x94, 0x03] [(rbx, 0x2000), (zf, 1)] (memAt 0x2000 [0xff, 0xff])) .b2 0x2000
  == some 0xff01
-- div dword ptr [rbx]
#guard ok (exec [0xf7, 0x33] [(rax, 100), (rdx, 0), (rbx, 0x2000)] (memAt 0x2000 [7, 0, 0, 0, 1]))
  [(rax, 14), (rdx, 2)]
-- cmovne rax, qword ptr [rbx]
#guard ok (exec [0x48, 0x0f, 0x45, 0x03] [(rbx, 0x2000), (zf, 0)] (memAt 0x2000 [0x42])) [(rax, 0x42)]
-- shl qword ptr [rbx], 4: CF is bit 60
#guard rd (exec [0x48, 0xc1, 0x23, 0x04] [(rbx, 0x2000)] (memAt 0x2000 [1, 0, 0, 0, 0, 0, 0, 0x10])) .b8 0x2000
  == some 0x10
#guard ok (exec [0x48, 0xc1, 0x23, 0x04] [(rbx, 0x2000)] (memAt 0x2000 [1, 0, 0, 0, 0, 0, 0, 0x10])) [] [(.b, 1)]

/-! ## add, adc: carry, overflow, parity, sizes -/

-- add rax, -1 (83 /0 ib): imm8 sign-extended, 1 + (2^64 - 1) carries to 0
#guard ok (exec [0x48, 0x83, 0xc0, 0xff] [(rax, 1)]) [(rax, 0)] [(.b, 1), (.e, 1), (.s, 0), (.o, 0)]
-- add eax, 0x7fffffff: signed overflow at 32 bits; low byte 0 has even parity
#guard ok (exec [0x05, 0xff, 0xff, 0xff, 0x7f] [(rax, 1)]) [(rax, 0x80000000)]
  [(.b, 0), (.e, 0), (.s, 1), (.o, 1), (.p, 1)]
-- add al, 0x80: 0x80 + 0x80 carries and overflows, the rest of rax kept
#guard ok (exec [0x04, 0x80] [(rax, 0x12345680)]) [(rax, 0x12345600)]
  [(.b, 1), (.e, 1), (.s, 0), (.o, 1)]
-- add ax, 1: 0xffff + 1 carries at 16 bits
#guard ok (exec [0x66, 0x83, 0xc0, 0x01] [(rax, 0xaaaaffff)]) [(rax, 0xaaaa0000)]
  [(.b, 1), (.e, 1), (.o, 0)]
-- add ah, bl: 0x01 + 0x0f = 0x10, one bit set: odd parity
#guard ok (exec [0x00, 0xdc] [(rax, 0x0170), (rbx, 0x0f)]) [(rax, 0x1070)] [(.b, 0), (.p, 0)]
-- add rax, rbx: 3 + 4 = 7, three bits: odd parity
#guard ok (exec [0x48, 0x01, 0xd8] [(rax, 3), (rbx, 4)]) [(rax, 7)] [(.p, 0)]
-- add rax, rbx: 0xff + 1 = 0x100: parity is of the low byte only
#guard ok (exec [0x48, 0x01, 0xd8] [(rax, 0xff), (rbx, 1)]) [(rax, 0x100)] [(.p, 1), (.e, 0)]
-- adc rax, rbx: max + 0 + CF carries only through the carry in
#guard ok (exec [0x48, 0x11, 0xd8] [(rax, max64), (rbx, 0), (cf, 1)]) [(rax, 0)] [(.b, 1), (.e, 1)]
-- adc rax, rbx: max + max + 1 = 2^65 - 1
#guard ok (exec [0x48, 0x11, 0xd8] [(rax, max64), (rbx, max64), (cf, 1)]) [(rax, max64)]
  [(.b, 1), (.o, 0), (.s, 1)]
-- adc rax, rbx: INT_MAX + 0 + 1 overflows
#guard ok (exec [0x48, 0x11, 0xd8] [(rax, 0x7fffffffffffffff), (rbx, 0), (cf, 1)]) [(rax, min64)]
  [(.b, 0), (.o, 1), (.s, 1)]
-- adc rax, rbx with CF clear is add
#guard ok (exec [0x48, 0x11, 0xd8] [(rax, 5), (rbx, 6), (cf, 0)]) [(rax, 11)] [(.b, 0), (.o, 0)]
-- adc eax, ebx: 0xffffffff + 0 + 1 carries at 32 bits, upper half cleared
#guard ok (exec [0x11, 0xd8] [(rax, max64), (rbx, 0), (cf, 1)]) [(rax, 0)] [(.b, 1), (.e, 1)]
-- adc al, bl: 0x7f + 0 + 1 overflows at 8 bits
#guard ok (exec [0x10, 0xd8] [(rax, 0xab7f), (rbx, 0), (cf, 1)]) [(rax, 0xab80)]
  [(.b, 0), (.o, 1), (.s, 1)]

/-! ## sub, sbb, cmp, neg -/

-- sub rax, rbx: 0 - 1 borrows
#guard ok (exec [0x48, 0x29, 0xd8] [(rax, 0), (rbx, 1)]) [(rax, max64)]
  [(.b, 1), (.e, 0), (.s, 1), (.o, 0), (.p, 1)]
-- sub rax, rbx: INT_MIN - 1 overflows
#guard ok (exec [0x48, 0x29, 0xd8] [(rax, min64), (rbx, 1)]) [(rax, 0x7fffffffffffffff)]
  [(.b, 0), (.s, 0), (.o, 1)]
-- sub eax, ebx: 5 - 5, upper half cleared
#guard ok (exec [0x29, 0xd8] [(rax, 0xffffffff00000005), (rbx, 5)]) [(rax, 0)] [(.e, 1), (.b, 0)]
-- sub ax, bx: 0x8000 - 1 overflows at 16 bits, the rest kept
#guard ok (exec [0x66, 0x29, 0xd8] [(rax, 0x123458000), (rbx, 1)]) [(rax, 0x123457fff)]
  [(.o, 1), (.b, 0), (.s, 0)]
-- sub al, bl: 1 - 2 borrows at 8 bits
#guard ok (exec [0x28, 0xd8] [(rax, 0x5501), (rbx, 2)]) [(rax, 0x55ff)] [(.b, 1), (.s, 1), (.o, 0)]
-- sbb rax, rbx: 0 - max - 1 = 0 with a borrow
#guard ok (exec [0x48, 0x19, 0xd8] [(rax, 0), (rbx, max64), (cf, 1)]) [(rax, 0)] [(.b, 1), (.e, 1)]
-- sbb rax, rbx: 5 - 5 - 1 borrows only through the carry in
#guard ok (exec [0x48, 0x19, 0xd8] [(rax, 5), (rbx, 5), (cf, 1)]) [(rax, max64)] [(.b, 1), (.s, 1)]
-- sbb rax, rbx with CF clear is sub
#guard ok (exec [0x48, 0x19, 0xd8] [(rax, 5), (rbx, 3), (cf, 0)]) [(rax, 2)] [(.b, 0)]
-- sbb eax, ebx: 0 - 0xffffffff - 1 = 0 with a borrow at 32 bits
#guard ok (exec [0x19, 0xd8] [(rax, 0), (rbx, 0xffffffff), (cf, 1)]) [(rax, 0)] [(.b, 1), (.e, 1)]
-- sbb al, bl: 0x80 - 0 - 1 overflows at 8 bits
#guard ok (exec [0x18, 0xd8] [(rax, 0x80), (rbx, 0), (cf, 1)]) [(rax, 0x7f)] [(.b, 0), (.o, 1)]
-- cmp rax, rbx: 1 < 2 both ways, rax unchanged
#guard ok (exec [0x48, 0x39, 0xd8] [(rax, 1), (rbx, 2)]) [(rax, 1)] [(.b, 1), (.l, 1), (.e, 0)]
-- cmp rax, rbx: -1 < 1 signed, above unsigned
#guard ok (exec [0x48, 0x39, 0xd8] [(rax, max64), (rbx, 1)]) [(rax, max64)]
  [(.b, 0), (.a, 1), (.l, 1), (.g, 0)]
-- cmp al, 0x7f: -128 < 127, by overflow
#guard ok (exec [0x3c, 0x7f] [(rax, 0x80)]) [(rax, 0x80)]
  [(.b, 0), (.s, 0), (.o, 1), (.l, 1), (.g, 0), (.a, 1)]
-- cmp qword ptr [rbx], 5: equal, memory unchanged
#guard ok (exec [0x48, 0x83, 0x3b, 0x05] [(rbx, 0x2000)] (memAt 0x2000 [5])) [] [(.e, 1), (.b, 0)]
-- neg rax: of 0 clears CF
#guard ok (exec [0x48, 0xf7, 0xd8] [(rax, 0), (cf, 1)]) [(rax, 0)] [(.b, 0), (.e, 1)]
-- neg rax: of 1
#guard ok (exec [0x48, 0xf7, 0xd8] [(rax, 1)]) [(rax, max64)] [(.b, 1), (.s, 1), (.o, 0)]
-- neg rax: of INT_MIN overflows
#guard ok (exec [0x48, 0xf7, 0xd8] [(rax, min64)]) [(rax, min64)] [(.b, 1), (.o, 1)]
-- neg eax: upper half cleared
#guard ok (exec [0xf7, 0xd8] [(rax, 0xffffffff00000001)]) [(rax, 0xffffffff)] [(.b, 1), (.s, 1)]
-- neg al: of 0x80 overflows, the rest kept
#guard ok (exec [0xf6, 0xd8] [(rax, 0x1180)]) [(rax, 0x1180)] [(.b, 1), (.o, 1)]
-- neg ax: of 1
#guard ok (exec [0x66, 0xf7, 0xd8] [(rax, 0x12340001)]) [(rax, 0x1234ffff)] [(.b, 1), (.s, 1)]

/-! ## and, or, xor, test: CF and OF cleared -/

-- and rax, rbx: zero, CF and OF cleared
#guard ok (exec [0x48, 0x21, 0xd8] [(rax, 0xf0), (rbx, 0x0f), (cf, 1), (ovf, 1)]) [(rax, 0)]
  [(.b, 0), (.o, 0), (.e, 1), (.p, 1)]
-- or eax, ebx: sign at 32 bits, upper half cleared
#guard ok (exec [0x09, 0xd8] [(rax, 0xffffffff00000000), (rbx, 0x80000000), (cf, 1), (ovf, 1)])
  [(rax, 0x80000000)] [(.b, 0), (.o, 0), (.s, 1)]
-- xor al, bl: 0xff ^ 0x0f = 0xf0, four bits: even parity
#guard ok (exec [0x30, 0xd8] [(rax, 0x12ff), (rbx, 0x0f), (cf, 1)]) [(rax, 0x12f0)]
  [(.b, 0), (.s, 1), (.p, 1)]
-- xor rax, rax: zero, every flag as for a zero result
#guard ok (exec [0x48, 0x31, 0xc0] [(rax, 5), (cf, 1), (ovf, 1), (sf, 1)]) [(rax, 0)]
  [(.b, 0), (.o, 0), (.e, 1), (.s, 0), (.p, 1)]
-- xor eax, eax: all 64 bits cleared
#guard ok (exec [0x31, 0xc0] [(rax, max64)]) [(rax, 0)] [(.e, 1)]
-- xor al, al: only al cleared
#guard ok (exec [0x30, 0xc0] [(rax, 0x1234)]) [(rax, 0x1200)] [(.e, 1)]
-- xor ah, ah: only ah cleared
#guard ok (exec [0x30, 0xe4] [(rax, 0x1234)]) [(rax, 0x0034)] [(.e, 1), (.b, 0)]
-- test rax, rbx: sign, rax unchanged
#guard ok (exec [0x48, 0x85, 0xd8] [(rax, min64), (rbx, max64), (cf, 1), (ovf, 1)]) [(rax, min64)]
  [(.s, 1), (.e, 0), (.b, 0), (.o, 0)]
-- test al, 0x80
#guard ok (exec [0xa8, 0x80] [(rax, 0x7f)]) [(rax, 0x7f)] [(.e, 1)]
-- test eax, 0x80000000: the sign at 32 bits
#guard ok (exec [0xa9, 0x00, 0x00, 0x00, 0x80] [(rax, 0xffffffff80000000)])
  [(rax, 0xffffffff80000000)] [(.s, 1), (.e, 0)]

/-! ## inc, dec, not: CF kept -/

-- inc rax: wraps to 0, CF stays clear
#guard ok (exec [0x48, 0xff, 0xc0] [(rax, max64), (cf, 0)]) [(rax, 0)] [(.e, 1), (.b, 0)]
-- inc rax: CF stays set
#guard ok (exec [0x48, 0xff, 0xc0] [(rax, 4), (cf, 1)]) [(rax, 5)] [(.e, 0), (.b, 1)]
-- inc rax: INT_MAX overflows
#guard ok (exec [0x48, 0xff, 0xc0] [(rax, 0x7fffffffffffffff)]) [(rax, min64)] [(.o, 1), (.s, 1)]
-- inc al: wraps at 8 bits, the rest kept
#guard ok (exec [0xfe, 0xc0] [(rax, 0x12ff)]) [(rax, 0x1200)] [(.e, 1), (.o, 0)]
-- inc ah: 0x7f overflows
#guard ok (exec [0xfe, 0xc4] [(rax, 0x7f00)]) [(rax, 0x8000)] [(.o, 1), (.s, 1)]
-- dec eax: 0 to 0xffffffff, upper half cleared, CF kept
#guard ok (exec [0xff, 0xc8] [(rax, 0xffffffff00000000), (cf, 1)]) [(rax, 0xffffffff)]
  [(.s, 1), (.b, 1), (.o, 0)]
-- dec ax: 0x8000 overflows, the rest kept
#guard ok (exec [0x66, 0xff, 0xc8] [(rax, 0xabcd00008000)]) [(rax, 0xabcd00007fff)] [(.o, 1), (.s, 0)]
-- not rax: no flags change
#guard ok (exec [0x48, 0xf7, 0xd0] [(rax, 0), (cf, 1), (zf, 1)]) [(rax, max64)] [(.b, 1), (.e, 1)]
-- not eax: upper half cleared
#guard ok (exec [0xf7, 0xd0] [(rax, 0xffffffff00000000)]) [(rax, 0xffffffff)]
-- not ah
#guard ok (exec [0xf6, 0xd4] [(rax, 0x12345)]) [(rax, 0x1dc45)]

/-! ## Shifts: count masking, count 0, CF and OF -/

-- shl eax, 33: the count is taken mod 32, so 1; CF = old bit 31, OF = MSB(result) ^ CF
#guard ok (exec [0xc1, 0xe0, 0x21] [(rax, 0x80000001)]) [(rax, 2)] [(.b, 1), (.o, 1)]
-- shl rax, 65: the count is taken mod 64, so 1
#guard ok (exec [0x48, 0xc1, 0xe0, 0x41] [(rax, 1), (cf, 1)]) [(rax, 2)] [(.b, 0), (.o, 0)]
-- shl al, 33: 8 bits also mask to 5 bits, so 1; the rest of rax kept
#guard ok (exec [0xc0, 0xe0, 0x21] [(rax, 0x5581)]) [(rax, 0x5502)] [(.b, 1)]
-- shl eax, 0: no flag changes; the 32-bit destination is still written (upper half cleared)
#guard ok (exec [0xc1, 0xe0, 0x00] [(rax, 0xffffffff00000005), (cf, 1), (zf, 1), (sf, 1), (ovf, 1)])
  [(rax, 5)] [(.b, 1), (.e, 1), (.s, 1), (.o, 1)]
-- shl rax, cl with cl = 64: count 0, nothing changes
#guard ok (exec [0x48, 0xd3, 0xe0] [(rax, 3), (rcx, 64), (cf, 1), (zf, 1)]) [(rax, 3)] [(.b, 1), (.e, 1)]
-- shl rax, cl with cl = 0x41: count 1
#guard ok (exec [0x48, 0xd3, 0xe0] [(rax, min64), (rcx, 0x41)]) [(rax, 0)]
  [(.b, 1), (.e, 1), (.o, 1)]
-- shl eax, cl with cl = 32: count 0, flags kept
#guard ok (exec [0xd3, 0xe0] [(rax, 7), (rcx, 32), (cf, 1), (sf, 1)]) [(rax, 7)] [(.b, 1), (.s, 1)]
-- shl al, cl with cl = 0x20: count 0
#guard ok (exec [0xd2, 0xe0] [(rax, 0x11), (rcx, 0x20), (zf, 1)]) [(rax, 0x11)] [(.e, 1)]
-- shl al, cl with cl = 4: CF is bit 4 of the old value
#guard ok (exec [0xd2, 0xe0] [(rax, 0x1f), (rcx, 4)]) [(rax, 0xf0)] [(.b, 1), (.s, 1)]
-- shl eax, 1: into the sign bit, OF set
#guard ok (exec [0xd1, 0xe0] [(rax, 0x40000000)]) [(rax, 0x80000000)] [(.b, 0), (.o, 1), (.s, 1)]
-- shl rax, 1: out of the top
#guard ok (exec [0x48, 0xd1, 0xe0] [(rax, min64)]) [(rax, 0)] [(.b, 1), (.e, 1), (.o, 1)]
-- shr rax, 1: OF is the old top bit
#guard ok (exec [0x48, 0xd1, 0xe8] [(rax, 0x8000000000000001)]) [(rax, 0x4000000000000000)]
  [(.b, 1), (.o, 1), (.s, 0)]
-- shr eax, 1: upper half cleared first
#guard ok (exec [0xd1, 0xe8] [(rax, 0xffffffff00000003)]) [(rax, 1)] [(.b, 1), (.o, 0)]
-- shr al, cl with cl = 3: CF is bit 2, the rest kept
#guard ok (exec [0xd2, 0xe8] [(rax, 0x7785), (rcx, 3)]) [(rax, 0x7710)] [(.b, 1)]
-- sar rax, 1: OF cleared, sign kept
#guard ok (exec [0x48, 0xd1, 0xf8] [(rax, 0x8000000000000001), (ovf, 1)]) [(rax, 0xc000000000000000)]
  [(.b, 1), (.o, 0), (.s, 1)]
-- sar al, cl with cl = 9: past the size, every bit is the sign, and so is CF
#guard ok (exec [0xd2, 0xf8] [(rax, 0x80), (rcx, 9)]) [(rax, 0xff)] [(.b, 1), (.s, 1)]
-- sar eax, 31: upper half cleared
#guard ok (exec [0xc1, 0xf8, 0x1f] [(rax, 0xffffffff80000000)]) [(rax, 0xffffffff)] [(.b, 0)]
-- sar ax, 4: the rest kept
#guard ok (exec [0x66, 0xc1, 0xf8, 0x04] [(rax, 0x123458010)]) [(rax, 0x12345f801)] [(.b, 0), (.s, 1)]

/-! ## Rotates -/

-- rol rax, 1: CF is the bit rotated in, OF = MSB ^ CF; ZF not touched
#guard ok (exec [0x48, 0xd1, 0xc0] [(rax, 0x8000000000000002), (zf, 1)]) [(rax, 5)]
  [(.b, 1), (.o, 1), (.e, 1)]
-- rol al, 1
#guard ok (exec [0xd0, 0xc0] [(rax, 0x140)]) [(rax, 0x180)] [(.b, 0), (.o, 1)]
-- rol eax, cl with cl = 36: masked to 4
#guard ok (exec [0xd3, 0xc0] [(rax, 0x12345678), (rcx, 36)]) [(rax, 0x23456781)] [(.b, 1)]
-- rol al, 8: a whole turn, but the count is not 0, so CF = LSB of the result
#guard ok (exec [0xc0, 0xc0, 0x08] [(rax, 0x81), (cf, 0)]) [(rax, 0x81)] [(.b, 1)]
-- ror rax, 1: CF is the new top bit, OF = top two bits differ
#guard ok (exec [0x48, 0xd1, 0xc8] [(rax, 1)]) [(rax, min64)] [(.b, 1), (.o, 1)]
-- ror al, 1
#guard ok (exec [0xd0, 0xc8] [(rax, 0x02), (cf, 1), (ovf, 1)]) [(rax, 0x01)] [(.b, 0), (.o, 0)]
-- ror eax, 4: upper half cleared
#guard ok (exec [0xc1, 0xc8, 0x04] [(rax, 0xffffffff12345678)]) [(rax, 0x81234567)] [(.b, 1)]

/-! ## shld, shrd -/

-- shld eax, ebx, 4: CF is bit 28 of the old eax
#guard ok (exec [0x0f, 0xa4, 0xd8, 0x04] [(rax, 0xffffffff12345678), (rbx, 0x9abcdef0)])
  [(rax, 0x23456789)] [(.b, 1)]
-- shld rax, rbx, 8: CF is bit 56 of the old rax
#guard ok (exec [0x48, 0x0f, 0xa4, 0xd8, 0x08] [(rax, 0x0123456789abcdef), (rbx, 0xfedcba9876543210)])
  [(rax, 0x23456789abcdeffe)] [(.b, 1)]
-- shld rax, rbx, cl with cl = 0x41: count 1, the sign changes so OF
#guard ok (exec [0x48, 0x0f, 0xa5, 0xd8] [(rax, min64), (rbx, min64), (rcx, 0x41)]) [(rax, 1)]
  [(.b, 1), (.o, 1)]
-- shrd eax, ebx, 4: CF is bit 3 of the old eax
#guard ok (exec [0x0f, 0xac, 0xd8, 0x04] [(rax, 0x12345678), (rbx, 0x9abcdef0)]) [(rax, 0x01234567)]
  [(.b, 1)]
-- shrd rax, rbx, cl with cl = 4
#guard ok (exec [0x48, 0x0f, 0xad, 0xd8] [(rax, 0x10), (rbx, 0xf), (rcx, 4)])
  [(rax, 0xf000000000000001)] [(.b, 0), (.s, 1)]
-- shrd rax, rbx, cl with cl = 1: the sign changes, OF
#guard ok (exec [0x48, 0x0f, 0xad, 0xd8] [(rax, 2), (rbx, 1), (rcx, 1)]) [(rax, 0x8000000000000001)]
  [(.b, 0), (.o, 1)]
-- shrd rax, rbx, cl with cl = 64: count 0, nothing changes
#guard ok (exec [0x48, 0x0f, 0xad, 0xd8] [(rax, 2), (rbx, 1), (rcx, 64), (cf, 1), (zf, 1)])
  [(rax, 2)] [(.b, 1), (.e, 1)]
-- shld ax, bx, 4 and shrd ax, bx, 4: not lifted (LIMITS), they give up
#guard (exec [0x66, 0x0f, 0xa4, 0xd8, 0x04] [(rax, 1)]).isAbort
#guard (exec [0x66, 0x0f, 0xac, 0xd8, 0x04] [(rax, 1)]).isAbort

/-! ## mul, imul: CF = OF -/

-- mul rbx: (2^64 - 1)^2 = 0xfffffffffffffffe_0000000000000001
#guard ok (exec [0x48, 0xf7, 0xe3] [(rax, max64), (rbx, max64)]) [(rax, 1), (rdx, 0xfffffffffffffffe)]
  [(.b, 1), (.o, 1)]
-- mul rbx: no high half
#guard ok (exec [0x48, 0xf7, 0xe3] [(rax, 3), (rbx, 4), (rdx, 9)]) [(rax, 12), (rdx, 0)]
  [(.b, 0), (.o, 0)]
-- mul ebx: 0x80000000 * 4 = 2^33, both halves zero-extended
#guard ok (exec [0xf7, 0xe3] [(rax, 0xffffffff80000000), (rbx, 4), (rdx, max64)]) [(rax, 0), (rdx, 2)]
  [(.b, 1), (.o, 1)]
-- mul bx: 0xffff^2 = 0xfffe0001 into dx:ax, the rest kept
#guard ok (exec [0x66, 0xf7, 0xe3] [(rax, 0x123400000000ffff), (rbx, 0xffff), (rdx, 0x5555000000000000)])
  [(rax, 0x1234000000000001), (rdx, 0x555500000000fffe)] [(.b, 1)]
-- mul bl: 0x10 * 0x10 = 0x100 into ax, rdx untouched
#guard ok (exec [0xf6, 0xe3] [(rax, 0xabcd0010), (rbx, 0x10), (rdx, 7)]) [(rax, 0xabcd0100), (rdx, 7)]
  [(.b, 1), (.o, 1)]
-- mul bl: 2 * 3 fits in al
#guard ok (exec [0xf6, 0xe3] [(rax, 2), (rbx, 3)]) [(rax, 6)] [(.b, 0), (.o, 0)]
-- imul rbx: -1 * -1
#guard ok (exec [0x48, 0xf7, 0xeb] [(rax, max64), (rbx, max64)]) [(rax, 1), (rdx, 0)] [(.b, 0), (.o, 0)]
-- imul rbx: INT_MIN * -1 = 2^63 does not fit in 64 signed bits
#guard ok (exec [0x48, 0xf7, 0xeb] [(rax, min64), (rbx, max64)]) [(rax, min64), (rdx, 0)]
  [(.b, 1), (.o, 1)]
-- imul rbx: -2 * 3 = -6, rdx all ones
#guard ok (exec [0x48, 0xf7, 0xeb] [(rax, -2), (rbx, 3)]) [(rax, -6), (rdx, max64)] [(.b, 0)]
-- imul ebx: -1 * 2 = -2 in edx:eax, zero-extended
#guard ok (exec [0xf7, 0xeb] [(rax, 0xffffffffffffffff), (rbx, 2)]) [(rax, 0xfffffffe), (rdx, 0xffffffff)]
  [(.b, 0), (.o, 0)]
-- imul ebx: 2^16 * 2^16 = 2^32
#guard ok (exec [0xf7, 0xeb] [(rax, 0x10000), (rbx, 0x10000)]) [(rax, 0), (rdx, 1)] [(.b, 1), (.o, 1)]
-- imul bl: -128 * -1 = 128 does not fit in al
#guard ok (exec [0xf6, 0xeb] [(rax, 0x80), (rbx, 0xff)]) [(rax, 0x0080)] [(.b, 1), (.o, 1)]
-- imul bl: -2 * 3 = -6, ax = 0xfffa
#guard ok (exec [0xf6, 0xeb] [(rax, 0xfe), (rbx, 3)]) [(rax, 0xfffa)] [(.b, 0), (.o, 0)]
-- imul bx: 0x7fff * 2 = 0xfffe does not fit in 16 signed bits
#guard ok (exec [0x66, 0xf7, 0xeb] [(rax, 0x7fff), (rbx, 2), (rdx, 0x10000)]) [(rax, 0xfffe), (rdx, 0x10000)]
  [(.b, 1), (.o, 1)]
-- imul rax, rbx: 2^32 * 2^32 overflows to 0
#guard ok (exec [0x48, 0x0f, 0xaf, 0xc3] [(rax, 0x100000000), (rbx, 0x100000000), (rdx, 5)])
  [(rax, 0), (rdx, 5)] [(.b, 1), (.o, 1)]
-- imul rax, rbx: -3 * 4
#guard ok (exec [0x48, 0x0f, 0xaf, 0xc3] [(rax, -3), (rbx, 4)]) [(rax, -12)] [(.b, 0), (.o, 0)]
-- imul eax, ebx: 0x7fffffff * 2 overflows, upper half cleared
#guard ok (exec [0x0f, 0xaf, 0xc3] [(rax, 0x7fffffff), (rbx, 2)]) [(rax, 0xfffffffe)] [(.b, 1), (.o, 1)]
-- imul ax, bx: -1 * -1, the rest kept
#guard ok (exec [0x66, 0x0f, 0xaf, 0xc3] [(rax, 0x1234ffff), (rbx, 0xffff)]) [(rax, 0x12340001)]
  [(.b, 0)]
-- imul rax, rbx, -3: imm8 sign-extended
#guard ok (exec [0x48, 0x6b, 0xc3, 0xfd] [(rbx, 5)]) [(rax, -15)] [(.b, 0)]
-- imul eax, ebx, 1000: imm32
#guard ok (exec [0x69, 0xc3, 0xe8, 0x03, 0x00, 0x00] [(rax, max64), (rbx, 3)]) [(rax, 3000)]
-- imul ax, bx, -1: -(-32768) does not fit in 16 bits
#guard ok (exec [0x66, 0x6b, 0xc3, 0xff] [(rax, 0), (rbx, 0x8000)]) [(rax, 0x8000)] [(.b, 1), (.o, 1)]

/-! ## div, idiv -/

-- div rbx: 100 / 7
#guard ok (exec [0x48, 0xf7, 0xf3] [(rax, 100), (rdx, 0), (rbx, 7)]) [(rax, 14), (rdx, 2)]
-- div rbx: 2^64 / 2, through rdx:rax
#guard ok (exec [0x48, 0xf7, 0xf3] [(rax, 0), (rdx, 1), (rbx, 2)]) [(rax, min64), (rdx, 0)]
-- div rbx: (2^64 + 5) / 16
#guard ok (exec [0x48, 0xf7, 0xf3] [(rax, 5), (rdx, 1), (rbx, 16)]) [(rax, 0x1000000000000000), (rdx, 5)]
-- div rbx: a 128-bit dividend with every digit used
#guard ok (exec [0x48, 0xf7, 0xf3]
  [(rax, 0x0fedcba987654321), (rdx, 0x123456789abcdef0), (rbx, 0xfedcba9876543210)])
  [(rax, 0x1249249249249237), (rdx, 0xfb494e2e7c8161b1)]
-- div rbx: (2^128 - 1) >> 1 by 2^63, the largest quotient
#guard ok (exec [0x48, 0xf7, 0xf3] [(rax, max64), (rdx, 0x7fffffffffffffff), (rbx, min64)])
  [(rax, max64), (rdx, 0x7fffffffffffffff)]
-- div rbx: (2^64 - 1)^2 / (2^64 - 1)
#guard ok (exec [0x48, 0xf7, 0xf3] [(rax, 1), (rdx, 0xfffffffffffffffe), (rbx, max64)])
  [(rax, max64), (rdx, 0)]
-- div rbx: 2^64 / (2^32 + 1), a divisor with a small top digit
#guard ok (exec [0x48, 0xf7, 0xf3] [(rax, 0), (rdx, 1), (rbx, 0x100000001)]) [(rax, 0xffffffff), (rdx, 1)]
-- div rbx: by zero faults
#guard (exec [0x48, 0xf7, 0xf3] [(rax, 1), (rdx, 0), (rbx, 0)]).isAbort
-- div rbx: rdx = rbx, the quotient does not fit
#guard (exec [0x48, 0xf7, 0xf3] [(rax, 0), (rdx, 5), (rbx, 5)]).isAbort
-- div ebx: 2^32 / 2 through edx:eax, upper halves ignored and cleared
#guard ok (exec [0xf7, 0xf3] [(rax, 0xffffffff00000000), (rdx, 0xffffffff00000001), (rbx, 2)])
  [(rax, 0x80000000), (rdx, 0)]
-- div ebx: 2^33 / 2 does not fit
#guard (exec [0xf7, 0xf3] [(rax, 0), (rdx, 2), (rbx, 2)]).isAbort
-- div bx: 1000 / 7, the rest of rax and rdx kept
#guard ok (exec [0x66, 0xf7, 0xf3] [(rax, 0xaaaa0000000003e8), (rdx, 0xbbbb000000000000), (rbx, 7)])
  [(rax, 0xaaaa00000000008e), (rdx, 0xbbbb000000000006)]
-- div bl: ax = 1000 / 10, quotient in al, remainder in ah
#guard ok (exec [0xf6, 0xf3] [(rax, 0x550003e8), (rbx, 10), (rdx, 9)]) [(rax, 0x55000064), (rdx, 9)]
-- div bl: 1003 / 10 = 100 r 3
#guard ok (exec [0xf6, 0xf3] [(rax, 0x3eb), (rbx, 10)]) [(rax, 0x0364)]
-- div bl: 256 / 1 does not fit
#guard (exec [0xf6, 0xf3] [(rax, 0x100), (rbx, 1)]).isAbort
-- div bl: by zero
#guard (exec [0xf6, 0xf3] [(rax, 5), (rbx, 0x100)]).isAbort
-- idiv rbx: INT_MIN / -1 faults
#guard (exec [0x48, 0xf7, 0xfb] [(rax, min64), (rdx, max64), (rbx, max64)]).isAbort
-- idiv rbx: 100 / -7 = -14 r 2 (truncation)
#guard ok (exec [0x48, 0xf7, 0xfb] [(rax, 100), (rdx, 0), (rbx, -7)]) [(rax, -14), (rdx, 2)]
-- idiv rbx: -100 / 7 = -14 r -2: the remainder has the sign of the dividend
#guard ok (exec [0x48, 0xf7, 0xfb] [(rax, -100), (rdx, max64), (rbx, 7)]) [(rax, -14), (rdx, -2)]
-- idiv ebx: -7 / 2 = -3 r -1, zero-extended
#guard ok (exec [0xf7, 0xfb] [(rax, 0xfffffff9), (rdx, 0xffffffff), (rbx, 2)])
  [(rax, 0xfffffffd), (rdx, 0xffffffff)]
-- idiv ebx: 2^32 / 4 = 2^30, a dividend wider than eax
#guard ok (exec [0xf7, 0xfb] [(rax, 0), (rdx, 1), (rbx, 4)]) [(rax, 0x40000000), (rdx, 0)]
-- idiv ebx: INT_MIN / -1 faults
#guard (exec [0xf7, 0xfb] [(rax, 0x80000000), (rdx, 0xffffffff), (rbx, 0xffffffff)]).isAbort
-- idiv ebx: by zero
#guard (exec [0xf7, 0xfb] [(rax, 1), (rdx, 0), (rbx, 0xffffffff00000000)]).isAbort
-- idiv bx: -1000 / 10 = -100, the rest kept
#guard ok (exec [0x66, 0xf7, 0xfb] [(rax, 0x123400000000fc18), (rdx, 0xffff), (rbx, 10)])
  [(rax, 0x123400000000ff9c), (rdx, 0)]
-- idiv bx: -1001 / 10 = -100 r -1
#guard ok (exec [0x66, 0xf7, 0xfb] [(rax, 0xfc17), (rdx, 0xffff), (rbx, 10)]) [(rax, 0xff9c), (rdx, 0xffff)]
-- idiv bl: 7 / -2 = -3 r 1: ax = 0x01fd
#guard ok (exec [0xf6, 0xfb] [(rax, 7), (rbx, 0xfe)]) [(rax, 0x01fd)]
-- idiv bx: -32768 / -1 faults
#guard (exec [0x66, 0xf7, 0xfb] [(rax, 0x8000), (rdx, 0xffff), (rbx, 0xffff)]).isAbort
-- idiv bl: -7 / 2 = -3 r -1: ax = 0xfffd
#guard ok (exec [0xf6, 0xfb] [(rax, 0xfff9), (rbx, 2)]) [(rax, 0xfffd)]
-- idiv bl: -128 / -1 faults
#guard (exec [0xf6, 0xfb] [(rax, 0xff80), (rbx, 0xff)]).isAbort
-- idiv bl: 256 / 2 = 128 does not fit in a signed byte
#guard (exec [0xf6, 0xfb] [(rax, 0x100), (rbx, 2)]).isAbort

/-! ## cbw, cwde, cdqe, cwd, cdq, cqo -/

-- cbw: al = 0x80 to ax = 0xff80, the rest kept
#guard ok (exec [0x66, 0x98] [(rax, 0x12345680)]) [(rax, 0x1234ff80)]
-- cwde: ax = 0x8000 to eax = 0xffff8000, upper half cleared
#guard ok (exec [0x98] [(rax, 0xffffffff12348000)]) [(rax, 0xffff8000)]
-- cdqe: eax = 0x80000000 to rax
#guard ok (exec [0x48, 0x98] [(rax, 0x80000000)]) [(rax, 0xffffffff80000000)]
-- cdqe: a positive eax drops the upper half
#guard ok (exec [0x48, 0x98] [(rax, 0xffffffff7fffffff)]) [(rax, 0x7fffffff)]
-- cwd: dx = the sign of ax, the rest of rdx kept
#guard ok (exec [0x66, 0x99] [(rax, 0x8000), (rdx, 0x1111000000000000)])
  [(rax, 0x8000), (rdx, 0x111100000000ffff)]
-- cdq: edx = the sign of eax, upper half cleared
#guard ok (exec [0x99] [(rax, 0x80000000), (rdx, 0x1234000000000000)]) [(rdx, 0xffffffff)]
#guard ok (exec [0x99] [(rax, 0xffffffff7fffffff), (rdx, max64)]) [(rdx, 0)]
-- cqo
#guard ok (exec [0x48, 0x99] [(rax, min64)]) [(rdx, max64)]
#guard ok (exec [0x48, 0x99] [(rax, 1), (rdx, 5)]) [(rdx, 0)]

/-! ## movzx, movsx, movsxd -/

-- movzx eax, bl
#guard ok (exec [0x0f, 0xb6, 0xc3] [(rax, max64), (rbx, 0xff80)]) [(rax, 0x80)]
-- movzx eax, bx
#guard ok (exec [0x0f, 0xb7, 0xc3] [(rax, max64), (rbx, 0x12348765)]) [(rax, 0x8765)]
-- movzx rax, bl
#guard ok (exec [0x48, 0x0f, 0xb6, 0xc3] [(rax, max64), (rbx, 0x80)]) [(rax, 0x80)]
-- movzx ax, bl: the rest of rax kept
#guard ok (exec [0x66, 0x0f, 0xb6, 0xc3] [(rax, 0x1111222233334444), (rbx, 0xff)])
  [(rax, 0x11112222333300ff)]
-- movzx eax, ah
#guard ok (exec [0x0f, 0xb6, 0xc4] [(rax, 0xffff1234)]) [(rax, 0x12)]
-- movzx eax, sil: with REX, 6 is sil
#guard ok (exec [0x40, 0x0f, 0xb6, 0xc6] [(rsi, 0xabcd), (rdx, 0x7700)]) [(rax, 0xcd)]
-- movsx eax, bl: to 32 bits, upper half clear
#guard ok (exec [0x0f, 0xbe, 0xc3] [(rax, max64), (rbx, 0x80)]) [(rax, 0xffffff80)]
-- movsx rax, bx
#guard ok (exec [0x48, 0x0f, 0xbf, 0xc3] [(rbx, 0x8000)]) [(rax, 0xffffffffffff8000)]
-- movsx ax, bl: the rest of rax kept
#guard ok (exec [0x66, 0x0f, 0xbe, 0xc3] [(rax, 0x12340000), (rbx, 0xff)]) [(rax, 0x1234ffff)]
-- movsxd rax, ebx
#guard ok (exec [0x48, 0x63, 0xc3] [(rbx, 0x1280000000)]) [(rax, 0xffffffff80000000)]
-- movsxd rax, dword ptr [rbx]
#guard ok (exec [0x48, 0x63, 0x03] [(rbx, 0x2000)] (memAt 0x2000 [0xfe, 0xff, 0xff, 0xff, 0x12]))
  [(rax, -2)]

/-! ## cmov -/

-- cmove eax, ebx, false: a 32-bit cmov still clears the upper half
#guard ok (exec [0x0f, 0x44, 0xc3] [(rax, 0xffffffff00000005), (rbx, 9), (zf, 0)]) [(rax, 5)]
-- cmove eax, ebx, true
#guard ok (exec [0x0f, 0x44, 0xc3] [(rax, max64), (rbx, 0x1100000009), (zf, 1)]) [(rax, 9)]
-- cmove rax, rbx, false: unchanged
#guard ok (exec [0x48, 0x0f, 0x44, 0xc3] [(rax, max64), (rbx, 9), (zf, 0)]) [(rax, max64)]
-- cmove ax, bx, true: the rest kept
#guard ok (exec [0x66, 0x0f, 0x44, 0xc3] [(rax, 0x1111222233334444), (rbx, 0x5555), (zf, 1)])
  [(rax, 0x1111222233335555)]
-- cmovl rax, rbx: SF != OF moves, SF = OF does not
#guard ok (exec [0x48, 0x0f, 0x4c, 0xc3] [(rax, 1), (rbx, 2), (sf, 1), (ovf, 0)]) [(rax, 2)]
#guard ok (exec [0x48, 0x0f, 0x4c, 0xc3] [(rax, 1), (rbx, 2), (sf, 1), (ovf, 1)]) [(rax, 1)]

/-! ## setcc: the sixteen conditions -/

-- seto: OF = 1, only al written
#guard ok (exec [0x0f, 0x90, 0xc0] [(rax, 0x12345600), (ovf, 1)]) [(rax, 0x12345601)]
-- setno: OF = 1 gives 0
#guard ok (exec [0x0f, 0x91, 0xc0] [(rax, 0xff), (ovf, 1)]) [(rax, 0)]
-- setb: CF = 1
#guard ok (exec [0x0f, 0x92, 0xc0] [(cf, 1)]) [(rax, 1)]
-- setae: CF = 1 gives 0
#guard ok (exec [0x0f, 0x93, 0xc0] [(rax, 0xff), (cf, 1)]) [(rax, 0)]
-- sete: ZF = 1
#guard ok (exec [0x0f, 0x94, 0xc0] [(zf, 1)]) [(rax, 1)]
-- setne: ZF = 1 gives 0
#guard ok (exec [0x0f, 0x95, 0xc0] [(rax, 0xff), (zf, 1)]) [(rax, 0)]
-- setbe: CF = 0 and ZF = 1 gives 1; both 0 gives 0
#guard ok (exec [0x0f, 0x96, 0xc0] [(cf, 0), (zf, 1)]) [(rax, 1)]
#guard ok (exec [0x0f, 0x96, 0xc0] [(rax, 0xff), (cf, 0), (zf, 0)]) [(rax, 0)]
-- seta: CF = ZF = 0 gives 1; CF = 1 gives 0
#guard ok (exec [0x0f, 0x97, 0xc0] [(cf, 0), (zf, 0)]) [(rax, 1)]
#guard ok (exec [0x0f, 0x97, 0xc0] [(rax, 0xff), (cf, 1), (zf, 0)]) [(rax, 0)]
-- sets: SF = 1
#guard ok (exec [0x0f, 0x98, 0xc0] [(sf, 1)]) [(rax, 1)]
-- setns: SF = 0
#guard ok (exec [0x0f, 0x99, 0xc0] [(sf, 0)]) [(rax, 1)]
-- setp: a result of 3 (two bits) has even parity; 0x100 has a low byte of 0; 1 does not
#guard ok (exec [0x0f, 0x9a, 0xc0] [(pf, 3)]) [(rax, 1)]
#guard ok (exec [0x0f, 0x9a, 0xc0] [(pf, 0x100)]) [(rax, 1)]
#guard ok (exec [0x0f, 0x9a, 0xc0] [(rax, 0xff), (pf, 1)]) [(rax, 0)]
-- setnp: a result of 0x80 (one bit) has odd parity
#guard ok (exec [0x0f, 0x9b, 0xc0] [(pf, 0x80)]) [(rax, 1)]
-- setl: SF != OF
#guard ok (exec [0x0f, 0x9c, 0xc0] [(sf, 1), (ovf, 0)]) [(rax, 1)]
#guard ok (exec [0x0f, 0x9c, 0xc0] [(rax, 0xff), (sf, 1), (ovf, 1)]) [(rax, 0)]
-- setge: SF = OF = 1
#guard ok (exec [0x0f, 0x9d, 0xc0] [(sf, 1), (ovf, 1)]) [(rax, 1)]
-- setle: ZF = 1; and ZF = 0 with SF = OF gives 0
#guard ok (exec [0x0f, 0x9e, 0xc0] [(zf, 1)]) [(rax, 1)]
#guard ok (exec [0x0f, 0x9e, 0xc0] [(rax, 0xff), (zf, 0), (sf, 0), (ovf, 0)]) [(rax, 0)]
-- setg: ZF = 0 and SF = OF = 1; and SF != OF gives 0
#guard ok (exec [0x0f, 0x9f, 0xc0] [(zf, 0), (sf, 1), (ovf, 1)]) [(rax, 1)]
#guard ok (exec [0x0f, 0x9f, 0xc0] [(rax, 0xff), (zf, 0), (sf, 0), (ovf, 1)]) [(rax, 0)]
-- sete ah: without REX, 4 is ah
#guard ok (exec [0x0f, 0x94, 0xc4] [(rax, 0xffff), (rsp, 0x8000), (zf, 1)]) [(rax, 0x01ff), (rsp, 0x8000)]
-- sete sil: with REX, 6 is sil
#guard ok (exec [0x40, 0x0f, 0x94, 0xc6] [(rsi, 0xffff), (rdx, 0xffff), (zf, 1)])
  [(rsi, 0xff01), (rdx, 0xffff)]

/-! ## bswap, bsf, bsr, tzcnt, lzcnt -/

-- bswap eax: upper half cleared
#guard ok (exec [0x0f, 0xc8] [(rax, 0xffffffff12345678)]) [(rax, 0x78563412)]
-- bswap rax
#guard ok (exec [0x48, 0x0f, 0xc8] [(rax, 0x0102030405060708)]) [(rax, 0x0807060504030201)]
-- bswap r9: REX.B
#guard ok (exec [0x49, 0x0f, 0xc9] [(r9, 0x1122334455667788), (rcx, 1)])
  [(r9, 0x8877665544332211), (rcx, 1)]
-- bsf rax, rbx: the lowest set bit
#guard ok (exec [0x48, 0x0f, 0xbc, 0xc3] [(rbx, 0x80 ||| 0x8000)]) [(rax, 7)] [(.e, 0)]
#guard ok (exec [0x48, 0x0f, 0xbc, 0xc3] [(rbx, min64)]) [(rax, 63)] [(.e, 0)]
-- bsf rax, rbx of 0: ZF set, rax as it was (LIMITS)
#guard ok (exec [0x48, 0x0f, 0xbc, 0xc3] [(rax, 0x1234), (rbx, 0)]) [(rax, 0x1234)] [(.e, 1)]
-- bsr rax, rbx: the highest set bit
#guard ok (exec [0x48, 0x0f, 0xbd, 0xc3] [(rbx, 0x81)]) [(rax, 7)] [(.e, 0)]
#guard ok (exec [0x48, 0x0f, 0xbd, 0xc3] [(rbx, 1)]) [(rax, 0)] [(.e, 0)]
#guard ok (exec [0x48, 0x0f, 0xbd, 0xc3] [(rbx, max64)]) [(rax, 63)]
-- bsr rax, rbx of 0: ZF set
#guard ok (exec [0x48, 0x0f, 0xbd, 0xc3] [(rax, 0x1234), (rbx, 0)]) [(rax, 0x1234)] [(.e, 1)]
-- bsr eax, ebx: only the low 32 bits of rbx
#guard ok (exec [0x0f, 0xbd, 0xc3] [(rbx, 0xffffffff00000010)]) [(rax, 4)]
-- bsf ax, bx: the rest of rax kept
#guard ok (exec [0x66, 0x0f, 0xbc, 0xc3] [(rax, 0x1234ffff), (rbx, 0x18000)]) [(rax, 0x1234000f)]
-- tzcnt rax, rbx of 0: the size, CF set
#guard ok (exec [0xf3, 0x48, 0x0f, 0xbc, 0xc3] [(rbx, 0)]) [(rax, 64)] [(.b, 1), (.e, 0)]
-- tzcnt rax, rbx of 8
#guard ok (exec [0xf3, 0x48, 0x0f, 0xbc, 0xc3] [(rbx, 8), (cf, 1)]) [(rax, 3)] [(.b, 0), (.e, 0)]
-- tzcnt rax, rbx of 1: a result of 0 sets ZF
#guard ok (exec [0xf3, 0x48, 0x0f, 0xbc, 0xc3] [(rbx, 1)]) [(rax, 0)] [(.b, 0), (.e, 1)]
-- tzcnt eax, ebx of 0 at 32 bits: 32, whatever the upper half of rbx
#guard ok (exec [0xf3, 0x0f, 0xbc, 0xc3] [(rax, max64), (rbx, 0x100000000)]) [(rax, 32)] [(.b, 1)]
-- lzcnt rax, rbx of 0
#guard ok (exec [0xf3, 0x48, 0x0f, 0xbd, 0xc3] [(rbx, 0)]) [(rax, 64)] [(.b, 1), (.e, 0)]
-- lzcnt rax, rbx of 1
#guard ok (exec [0xf3, 0x48, 0x0f, 0xbd, 0xc3] [(rbx, 1)]) [(rax, 63)] [(.b, 0)]
-- lzcnt rax, rbx of INT_MIN: 0 sets ZF
#guard ok (exec [0xf3, 0x48, 0x0f, 0xbd, 0xc3] [(rbx, min64)]) [(rax, 0)] [(.b, 0), (.e, 1)]
-- lzcnt eax, ebx of 1 at 32 bits
#guard ok (exec [0xf3, 0x0f, 0xbd, 0xc3] [(rax, max64), (rbx, 0xff00000000000001)]) [(rax, 31)]
-- lzcnt ax, bx of 0 at 16 bits: 16, the rest kept
#guard ok (exec [0x66, 0xf3, 0x0f, 0xbd, 0xc3] [(rax, 0x12340000), (rbx, 0x10000)]) [(rax, 0x12340010)]
  [(.b, 1)]

/-! ## bt, bts, btr, btc -/

-- bt rax, rbx: bit 4
#guard ok (exec [0x48, 0x0f, 0xa3, 0xd8] [(rax, 0x10), (rbx, 4)]) [(rax, 0x10)] [(.b, 1)]
-- bt rax, rbx: index 68 is 4 mod 64
#guard ok (exec [0x48, 0x0f, 0xa3, 0xd8] [(rax, 0x10), (rbx, 68)]) [] [(.b, 1)]
-- bt rax, rbx: bit 5 clear
#guard ok (exec [0x48, 0x0f, 0xa3, 0xd8] [(rax, 0x10), (rbx, 5), (cf, 1)]) [] [(.b, 0)]
-- bt eax, ebx: index 32 is 0 mod 32, not bit 32 of rax
#guard ok (exec [0x0f, 0xa3, 0xd8] [(rax, 0x100000000), (rbx, 32), (cf, 1)]) [] [(.b, 0)]
-- bt rax, 63
#guard ok (exec [0x48, 0x0f, 0xba, 0xe0, 0x3f] [(rax, min64)]) [(rax, min64)] [(.b, 1)]
-- bts rax, 5
#guard ok (exec [0x48, 0x0f, 0xba, 0xe8, 0x05] [(rax, 0), (cf, 1)]) [(rax, 0x20)] [(.b, 0)]
-- btr eax, 33: 1 mod 32, upper half cleared
#guard ok (exec [0x0f, 0xba, 0xf0, 0x21] [(rax, max64)]) [(rax, 0xfffffffd)] [(.b, 1)]
-- btc rax, rbx
#guard ok (exec [0x48, 0x0f, 0xbb, 0xd8] [(rax, 1), (rbx, 0)]) [(rax, 0)] [(.b, 1)]
-- bts ax, bx: index 17 is 1 mod 16, the rest kept
#guard ok (exec [0x66, 0x0f, 0xab, 0xd8] [(rax, 0x10000), (rbx, 17), (cf, 1)]) [(rax, 0x10002)] [(.b, 0)]
-- bt qword ptr [rbx], 3
#guard ok (exec [0x48, 0x0f, 0xba, 0x23, 0x03] [(rbx, 0x2000)] (memAt 0x2000 [0x08])) [] [(.b, 1)]

/-! ## xchg -/

-- xchg rax, rbx
#guard ok (exec [0x48, 0x93] [(rax, 1), (rbx, 2)]) [(rax, 2), (rbx, 1)]
-- xchg eax, ebx: both upper halves cleared
#guard ok (exec [0x93] [(rax, 0x1100000001), (rbx, 0x2200000002)]) [(rax, 2), (rbx, 1)]
-- xchg ax, bx: the rest of both kept
#guard ok (exec [0x66, 0x93] [(rax, 0x110001), (rbx, 0x220002)]) [(rax, 0x110002), (rbx, 0x220001)]
-- xchg rax, r8 (49 90): with REX.B, 90 is not nop
#guard ok (exec [0x49, 0x90] [(rax, 1), (r8, 2)]) [(rax, 2), (r8, 1)]
-- xchg [rbx], rcx
#guard ok (exec [0x48, 0x87, 0x0b] [(rbx, 0x2000), (rcx, 0x55)] (memAt 0x2000 [0x66])) [(rcx, 0x66)]
#guard rd (exec [0x48, 0x87, 0x0b] [(rbx, 0x2000), (rcx, 0x55)] (memAt 0x2000 [0x66])) .b8 0x2000
  == some 0x55
-- xchg eax, eax (87 c0) clears the upper half; nop (90) does not
#guard ok (exec [0x87, 0xc0] [(rax, 0xffffffff00000001)]) [(rax, 1)]
#guard ok (exec [0x90] [(rax, 0xffffffff00000001)]) [(rax, 0xffffffff00000001)]

/-! ## Stack -/

-- push rax
#guard ok (exec [0x50] [(rax, 0x1122), (rsp, 0x8000)]) [(rsp, 0x7ff8)]
#guard rd (exec [0x50] [(rax, 0x1122), (rsp, 0x8000)]) .b8 0x7ff8 == some 0x1122
-- push r12
#guard rd (exec [0x41, 0x54] [(r12, 0x3344), (rsp, 0x8000)]) .b8 0x7ff8 == some 0x3344
-- push -1: imm8 sign-extended to 8 bytes
#guard rd (exec [0x6a, 0xff] [(rsp, 0x8000)]) .b8 0x7ff8 == some max64
-- push 0x12345678
#guard rd (exec [0x68, 0x78, 0x56, 0x34, 0x12] [(rsp, 0x8000)]) .b8 0x7ff8 == some 0x12345678
-- push [rsp]: the address is computed before rsp moves
#guard rd (exec [0xff, 0x34, 0x24] [(rsp, 0x8000)] (memAt 0x8000 [0xef, 0xcd, 0xab])) .b8 0x7ff8
  == some 0xabcdef
-- push rsp: the old value
#guard rd (exec [0x54] [(rsp, 0x8000)]) .b8 0x7ff8 == some 0x8000
-- pop rax
#guard ok (exec [0x58] [(rsp, 0x8000)] (memAt 0x8000 [0x55])) [(rax, 0x55), (rsp, 0x8008)]
-- pop r8
#guard ok (exec [0x41, 0x58] [(rsp, 0x8000)] (memAt 0x8000 [0x55])) [(r8, 0x55), (rsp, 0x8008)]
-- pop [rsp + 8]: the address is computed after rsp moves, so 0x8010
#guard rd (exec [0x8f, 0x44, 0x24, 0x08] [(rsp, 0x8000)] (memAt 0x8000 [0x77])) .b8 0x8010 == some 0x77
#guard rd (exec [0x8f, 0x44, 0x24, 0x08] [(rsp, 0x8000)] (memAt 0x8000 [0x77])) .b8 0x8008 == some 0
-- pop [rbx]
#guard rd (exec [0x8f, 0x03] [(rsp, 0x8000), (rbx, 0x2000)] (memAt 0x8000 [0x77])) .b8 0x2000 == some 0x77
-- pop rsp: rsp is the value popped
#guard ok (exec [0x5c] [(rsp, 0x8000)] (memAt 0x8000 [0x34, 0x12])) [(rsp, 0x1234)]
-- leave: rsp = rbp, then pop rbp
#guard ok (exec [0xc9] [(rsp, 1), (rbp, 0x9000)] (memAt 0x9000 [0xaa, 0xaa])) [(rsp, 0x9008), (rbp, 0xaaaa)]

/-! ## Control -/

-- ret leaves, with the return address from [rsp] in `ra`
#guard isRet (exec [0xc3] [(rsp, 0x8000)] (memAt 0x8000 [0x10, 0x20, 0x40]))
#guard leavesWith (exec [0xc3] [(rsp, 0x8000)] (memAt 0x8000 [0x10, 0x20, 0x40])) [(ra, 0x402010)]
-- call 0x402000 (e8 rel32 from 0x401005) to a function: pushes 0x401005
#guard isCall (execF [0xe8, 0xfb, 0x0f, 0x00, 0x00] [(rsp, 0x8000)] [0x402000])
#guard leavesWith (execF [0xe8, 0xfb, 0x0f, 0x00, 0x00] [(rsp, 0x8000)] [0x402000]) [(rsp, 0x7ff8)]
#guard rd (execF [0xe8, 0xfb, 0x0f, 0x00, 0x00] [(rsp, 0x8000)] [0x402000]) .b8 0x7ff8 == some 0x401005
-- call to an address that is no function gives up
#guard (execF [0xe8, 0xfb, 0x0f, 0x00, 0x00] [(rsp, 0x8000)] [0x403000]).isAbort
-- call rax: pushes 0x401002
#guard isCall (execF [0xff, 0xd0] [(rax, 0x402000), (rsp, 0x8000)] [0x402000])
#guard rd (execF [0xff, 0xd0] [(rax, 0x402000), (rsp, 0x8000)] [0x402000]) .b8 0x7ff8 == some 0x401002
-- jmp 0x402000 (e9 rel32): a jump to the address, here labelled
#guard (exec [0xe9, 0xfb, 0x0f, 0x00, 0x00] []).isTaken
-- jmp 0x402000 to a function outside this one: a tail call
#guard isTail (run (liftI { cx at0 5 [0x402000] with label := fun a => if a == at0 then some here else none }
  none { addr := at0, size := 5, instr := some (.jmp 0x402000) }) [])
-- je 0x402000 to a function outside this one: a tail call when ZF = 1, the next one when not
#guard isTail (run (liftI { cx at0 6 [0x402000] with
    label := fun a => if a == at0 then some here else if a == at0 + 6 then some next else none }
  none { addr := at0, size := 6, instr := some (.jcc .e 0x402000) }) [(zf, 1)])
#guard (run (liftI { cx at0 6 [0x402000] with
    label := fun a => if a == at0 then some here else if a == at0 + 6 then some next else none }
  none { addr := at0, size := 6, instr := some (.jcc .e 0x402000) }) [(zf, 0)]).isNext
-- e9 rel32 decodes to its target
#guard dec [0xe9, 0xfb, 0x0f, 0x00, 0x00] = some (.jmp 0x402000, 5)
#guard dec [0x0f, 0x84, 0xfa, 0x0f, 0x00, 0x00] = some (.jcc .e 0x402000, 6)
-- je +0x10: taken when ZF = 1, falls through when not
#guard (exec [0x74, 0x10] [(zf, 1)]).isTaken
#guard (exec [0x74, 0x10] [(zf, 0)]).isNext
-- je rel32
#guard (exec [0x0f, 0x84, 0x10, 0x00, 0x00, 0x00] [(zf, 1)]).isTaken
#guard (exec [0x0f, 0x84, 0x10, 0x00, 0x00, 0x00] [(zf, 0)]).isNext
-- jl +0x10: SF != OF
#guard (exec [0x7c, 0x10] [(sf, 0), (ovf, 1)]).isTaken
#guard (exec [0x7c, 0x10] [(sf, 1), (ovf, 1)]).isNext
-- jp +0x10: parity of the result kept in pf
#guard (exec [0x7a, 0x10] [(pf, 0x0f)]).isTaken
#guard (exec [0x7a, 0x10] [(pf, 0x07)]).isNext
-- ja +0x10: CF = ZF = 0
#guard (exec [0x77, 0x10] [(cf, 0), (zf, 0)]).isTaken
#guard (exec [0x77, 0x10] [(cf, 1), (zf, 0)]).isNext
-- je +0 goes to the next instruction either way
#guard (exec [0x74, 0x00] [(zf, 1)]).isNext
-- jmp rax to an address of the function among the candidates
#guard (run (liftI (cx at0 2 [] [0x401100]) none { addr := at0, size := 2, instr := some (.jmpTo (.reg 0)) })
  [(rax, 0x401100)]).isTaken
-- syscall: the external call 0
#guard isExt (exec [0x0f, 0x05] [(rax, 1)]) 0

/-! ## String instructions -/

-- movsb, df = 0: forward
#guard ok (exec [0xa4] [(rsi, 0x1000), (rdi, 0x2000), (df, 0)] (memAt 0x1000 [0xab]))
  [(rsi, 0x1001), (rdi, 0x2001)]
#guard rd (exec [0xa4] [(rsi, 0x1000), (rdi, 0x2000), (df, 0)] (memAt 0x1000 [0xab, 0xcd])) .b2 0x2000
  == some 0xab
-- movsb, df = 1: backward
#guard ok (exec [0xa4] [(rsi, 0x1000), (rdi, 0x2000), (df, 1)] (memAt 0x1000 [0xab]))
  [(rsi, 0xfff), (rdi, 0x1fff)]
-- movsw, by 2 either way
#guard ok (exec [0x66, 0xa5] [(rsi, 0x1000), (rdi, 0x2000)]) [(rsi, 0x1002), (rdi, 0x2002)]
#guard ok (exec [0x66, 0xa5] [(rsi, 0x1000), (rdi, 0x2000), (df, 1)]) [(rsi, 0xffe), (rdi, 0x1ffe)]
-- movsd: 4 bytes
#guard rd (exec [0xa5] [(rsi, 0x1000), (rdi, 0x2000)] (memAt 0x1000 [1, 2, 3, 4, 5])) .b8 0x2000
  == some 0x04030201
-- movsq, df = 1: 8 bytes, back by 8
#guard ok (exec [0x48, 0xa5] [(rsi, 0x1000), (rdi, 0x2000), (df, 1)]) [(rsi, 0xff8), (rdi, 0x1ff8)]
#guard rd (exec [0x48, 0xa5] [(rsi, 0x1000), (rdi, 0x2000), (df, 1)] (memAt 0x1000 [1, 2, 3, 4, 5, 6, 7, 8]))
  .b8 0x2000 == some 0x0807060504030201
-- rep movsb, rcx = 3: three bytes and no more
#guard ok (exec [0xf3, 0xa4] [(rsi, 0x1000), (rdi, 0x2000), (rcx, 3)] (memAt 0x1000 [1, 2, 3, 4]))
  [(rsi, 0x1003), (rdi, 0x2003), (rcx, 0)]
#guard rd (exec [0xf3, 0xa4] [(rsi, 0x1000), (rdi, 0x2000), (rcx, 3)] (memAt 0x1000 [1, 2, 3, 4]))
  .b4 0x2000 == some 0x030201
-- rep movsb, rcx = 0: nothing
#guard ok (exec [0xf3, 0xa4] [(rsi, 0x1000), (rdi, 0x2000), (rcx, 0)] (memAt 0x1000 [1]))
  [(rsi, 0x1000), (rdi, 0x2000), (rcx, 0)]
#guard rd (exec [0xf3, 0xa4] [(rsi, 0x1000), (rdi, 0x2000), (rcx, 0)] (memAt 0x1000 [1])) .b1 0x2000
  == some 0
-- rep movsq, df = 1, rcx = 2: from 0x1008 then 0x1000
#guard ok (exec [0xf3, 0x48, 0xa5] [(rsi, 0x1008), (rdi, 0x2008), (rcx, 2), (df, 1)])
  [(rsi, 0xff8), (rdi, 0x1ff8), (rcx, 0)]
#guard rd (exec [0xf3, 0x48, 0xa5] [(rsi, 0x1008), (rdi, 0x2008), (rcx, 2), (df, 1)]
  (memAt 0x1000 [1, 0, 0, 0, 0, 0, 0, 0, 2])) .b8 0x2000 == some 1
#guard rd (exec [0xf3, 0x48, 0xa5] [(rsi, 0x1008), (rdi, 0x2008), (rcx, 2), (df, 1)]
  (memAt 0x1000 [1, 0, 0, 0, 0, 0, 0, 0, 2])) .b8 0x2008 == some 2
-- stosb: al only
#guard rd (exec [0xaa] [(rax, 0x125a), (rdi, 0x2000)]) .b2 0x2000 == some 0x5a
#guard ok (exec [0xaa] [(rax, 0x5a), (rdi, 0x2000)]) [(rdi, 0x2001)]
#guard ok (exec [0xaa] [(rax, 0x5a), (rdi, 0x2000), (df, 1)]) [(rdi, 0x1fff)]
-- stosw, stosd, stosq: 2, 4, 8 bytes
#guard rd (exec [0x66, 0xab] [(rax, max64), (rdi, 0x2000)]) .b8 0x2000 == some 0xffff
#guard rd (exec [0xab] [(rax, max64), (rdi, 0x2000)]) .b8 0x2000 == some 0xffffffff
#guard ok (exec [0xab] [(rax, max64), (rdi, 0x2000)]) [(rdi, 0x2004)]
#guard rd (exec [0x48, 0xab] [(rax, max64), (rdi, 0x2000)]) .b8 0x2000 == some max64
-- rep stosb, rcx = 4: four bytes, the fifth not written
#guard rd (exec [0xf3, 0xaa] [(rax, 0x11), (rdi, 0x2000), (rcx, 4)]) .b8 0x2000 == some 0x11111111
#guard ok (exec [0xf3, 0xaa] [(rax, 0x11), (rdi, 0x2000), (rcx, 4)]) [(rdi, 0x2004), (rcx, 0)]
-- rep stosq, rcx = 0: nothing written
#guard rd (exec [0xf3, 0x48, 0xab] [(rax, max64), (rdi, 0x2000), (rcx, 0)]) .b8 0x2000 == some 0
-- rep stosq, df = 1, rcx = 2: at 0x2008 then 0x2000
#guard ok (exec [0xf3, 0x48, 0xab] [(rax, 7), (rdi, 0x2008), (rcx, 2), (df, 1)]) [(rdi, 0x1ff8), (rcx, 0)]
#guard rd (exec [0xf3, 0x48, 0xab] [(rax, 7), (rdi, 0x2008), (rcx, 2), (df, 1)]) .b8 0x2000 == some 7
-- std, cld
#guard ok (exec [0xfd] [(df, 0)]) [(df, 1)]
#guard ok (exec [0xfc] [(df, 1)]) [(df, 0)]

end Tools.Test.X86
