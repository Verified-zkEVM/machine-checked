import Cases.Zip2005.Kit.ByteShiftAll
import Cases.Zip2005.Kit.ByteSimpPre
import Cases.Zip2005.Kit.Array32Model

/-!
# What the visitor's tail moves where

`tailByte Fr r9 … r27 p` is byte `p` of the 1392-byte struct the tail of `Zip2005Witness`'s
visitor writes on `Ok`: a byte of its frame `Fr` (334 words at its `sp`) or of one of the
callee-saved registers `s1` (`x9`), `s2`..`s4`, `s6`..`s11` (`x18`..`x20`, `x22`..`x27`) it
holds fields in. The table is read off the tail's code (a byte-provenance pass over its loads,
stores, shifts and `memcpy`s); `Cases.Zip2005.witness_tail_spec` checks it against the instructions.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- Byte `a` of the frame. -/
def frByte (Fr : List Word) (a : Nat) : BitVec 8 := extractByte Fr[a / 8]! (a % 8)

/-- Struct byte `p` on `Ok`. -/
def tailByte (Fr : List Word) (r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word) (p : Nat) : BitVec 8 :=
  if p < 0x6 then frByte Fr (0x9c0 + p)
  else if p < 0xe then frByte Fr (0x28 + (p - 0x6))
  else if p < 0x400 then frByte Fr (0x5b8 + (p - 0xe))
  else if p < 0x406 then frByte Fr (0xd8 + (p - 0x400))
  else if p < 0x40e then extractByte r23 (p - 0x406)
  else if p < 0x40f then extractByte r22 (p - 0x40e)
  else if p < 0x420 then frByte Fr (0xc0 + (p - 0x40f))
  else if p < 0x426 then frByte Fr (0xf8 + (p - 0x420))
  else if p < 0x42e then extractByte r25 (p - 0x426)
  else if p < 0x42f then extractByte r24 (p - 0x42e)
  else if p < 0x440 then frByte Fr (0xe0 + (p - 0x42f))
  else if p < 0x446 then frByte Fr (0x118 + (p - 0x440))
  else if p < 0x44e then frByte Fr (0x70 + (p - 0x446))
  else if p < 0x44f then extractByte r26 (p - 0x44e)
  else if p < 0x460 then frByte Fr (0x100 + (p - 0x44f))
  else if p < 0x466 then frByte Fr (0x138 + (p - 0x460))
  else if p < 0x46f then frByte Fr (0x78 + (p - 0x466))
  else if p < 0x480 then frByte Fr (0x120 + (p - 0x46f))
  else if p < 0x486 then frByte Fr (0x158 + (p - 0x480))
  else if p < 0x48f then frByte Fr (0x60 + (p - 0x486))
  else if p < 0x4a0 then frByte Fr (0x140 + (p - 0x48f))
  else if p < 0x4a6 then frByte Fr (0x160 + (p - 0x4a0))
  else if p < 0x4ae then frByte Fr (0x30 + (p - 0x4a6))
  else if p < 0x4af then frByte Fr (0x58 + (p - 0x4ae))
  else if p < 0x4c0 then frByte Fr (0x168 + (p - 0x4af))
  else if p < 0x4c6 then frByte Fr (0x180 + (p - 0x4c0))
  else if p < 0x4ce then frByte Fr (0x50 + (p - 0x4c6))
  else if p < 0x4cf then frByte Fr (0x48 + (p - 0x4ce))
  else if p < 0x4e0 then frByte Fr (0x188 + (p - 0x4cf))
  else if p < 0x4e6 then frByte Fr (0x1a0 + (p - 0x4e0))
  else if p < 0x4ee then frByte Fr (0x40 + (p - 0x4e6))
  else if p < 0x4ef then extractByte r9 (p - 0x4ee)
  else if p < 0x500 then frByte Fr (0x1a8 + (p - 0x4ef))
  else if p < 0x508 then extractByte r18 (p - 0x500)
  else if p < 0x50c then frByte Fr (0x38 + (p - 0x508))
  else if p < 0x50d then extractByte r20 (p - 0x50c)
  else if p < 0x513 then frByte Fr (0xb8 + (p - 0x50d))
  else if p < 0x51b then extractByte r19 (p - 0x513)
  else if p < 0x52d then frByte Fr (0xa0 + (p - 0x51b))
  else if p < 0x52e then extractByte r27 (p - 0x52d)
  else if p < 0x534 then frByte Fr (0x9c8 + (p - 0x52e))
  else if p < 0x53c then frByte Fr (0x20 + (p - 0x534))
  else if p < 0x54e then frByte Fr (0x9d0 + (p - 0x53c))
  else if p < 0x54f then frByte Fr (0x10 + (p - 0x54e))
  else if p < 0x555 then frByte Fr (0xa00 + (p - 0x54f))
  else if p < 0x55d then frByte Fr (0x18 + (p - 0x555))
  else if p < 0x56f then frByte Fr (0x1c0 + (p - 0x55d))
  else frByte Fr (0x9e9 + (p - 0x56f))

/-- The 174 words the tail writes on `Ok`. -/
def tailW (Fr : List Word) (r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word) : List Word :=
  (List.range 174).map fun i => word8 (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i))
    (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i + 1)) (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i + 2))
    (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i + 3)) (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i + 4))
    (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i + 5)) (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i + 6))
    (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i + 7))

@[simp] theorem tailW_length (Fr : List Word) (r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word) :
    (tailW Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27).length = 174 := by
  simp [tailW]

theorem tailW_getElem! (Fr : List Word) (r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word) (i : Nat) (h : i < 174) :
    (tailW Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27)[i]! = word8 (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i))
      (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i + 1)) (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i + 2))
      (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i + 3)) (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i + 4))
      (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i + 5)) (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i + 6))
      (tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 (8 * i + 7)) := by
  simp [tailW, h]

attribute [byte_simp] frByte tailByte tailW_getElem!
attribute [byte_pre ↓] frByte tailByte tailW_getElem!

end Cases.Zip2005
