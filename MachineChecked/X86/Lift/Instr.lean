/-
  MachineChecked.X86.Lift.Instr

  The instructions of x86-64 that the lift takes, and their decoding from bytes.

  Kraken's x64 model has instructions as assembly and no decoder, so the lift of a linked
  program reads the bytes itself. `Instr` is the integer instructions a compiler emits for a
  program without an operating system, in 64-bit mode, with their operands in one form
  (`Loc`, `Src`): what `Lift.lean` gives a meaning to. `decode` reads one from bytes.

  * **What is decoded** is the one-byte and `0F` two-byte opcodes of those instructions, with
    the prefixes `66` (16-bit operands), `F3` (on the string instructions, and where it
    makes another instruction: `tzcnt`, `lzcnt`, `pause`), REX, and the segment prefixes
    that 64-bit mode ignores (`2E`, `36`, `3E`, `26`).
  * **What is not** gives `none`, and the lift gives up there: every other prefix (`lock`,
    `F2`, `67`, `fs`, `gs`), VEX and EVEX, the x87, MMX and SSE opcodes, the instructions
    for the system, far control transfers, and the forms noted at their cases.
  * **An address relative to the instruction pointer** is decoded to the address it names:
    `decode` is given where the instruction is.

  The decoder is not proved against anything. It is checked on every instruction of the
  test programs against LLVM's disassembler, for the length and the name, and by running the
  programs (`scripts/decompile-check`).

  ## Main definitions

  * `Instr`, `decode`
-/

namespace MachineChecked.X86.Lift
/-- The size of an operand: 1, 2, 4 or 8 bytes. -/
inductive Size where
  | b
  | w
  | d
  | q
  deriving DecidableEq, Repr, Inhabited

def Size.bytes : Size → Nat
  | .b => 1
  | .w => 2
  | .d => 4
  | .q => 8

def Size.bits (s : Size) : Nat := 8 * s.bytes

/-- An address: a base register, an index register shifted by 0 to 3, and a constant. -/
structure Addr where
  base : Option (Fin 16)
  index : Option (Fin 16 × Nat)
  disp : BitVec 64
  deriving DecidableEq, Repr, Inhabited

/-- Where an operand is: a general register (the low bytes of it that the instruction's size
    says), the second byte of one of the first four (`ah`, `ch`, `dh`, `bh`), or memory. -/
inductive Loc where
  | reg (r : Fin 16)
  | high (r : Fin 4)
  | mem (a : Addr)
  deriving DecidableEq, Repr, Inhabited

/-- An operand that is read: a place, or a constant (sign-extended to 64 bits). -/
inductive Src where
  | loc (l : Loc)
  | imm (v : BitVec 64)
  deriving DecidableEq, Repr, Inhabited

/-- The eight operations of two operands, in the order of their encoding. -/
inductive Alu where
  | add | or | adc | sbb | and | sub | xor | cmp
  deriving DecidableEq, Repr, Inhabited

inductive Unary where
  | not | neg | inc | dec
  deriving DecidableEq, Repr, Inhabited

inductive Shift where
  | rol | ror | shl | shr | sar
  deriving DecidableEq, Repr, Inhabited

/-- The count of a shift: a constant, or the register `cl`. -/
inductive Count where
  | imm (n : Nat)
  | cl
  deriving DecidableEq, Repr, Inhabited

/-- The sixteen conditions, in the order of their encoding. -/
inductive Cc where
  | o | no | b | ae | e | ne | be | a | s | ns | p | np | l | ge | le | g
  deriving DecidableEq, Repr, Inhabited

inductive BitOp where
  | bt | bts | btr | btc
  deriving DecidableEq, Repr, Inhabited

inductive Scan where
  | bsf | bsr | tzcnt | lzcnt
  deriving DecidableEq, Repr, Inhabited

/-- **An instruction of x86-64**, of those the lift takes. A target is an address. -/
inductive Instr where
  | mov (sz : Size) (dst : Loc) (src : Src)
  /-- `movzx`, `movsx`, `movsxd`: `src` of size `ssz` extended into `dst` of size `dsz`. -/
  | movx (signed : Bool) (dsz ssz : Size) (dst : Fin 16) (src : Loc)
  | lea (sz : Size) (dst : Fin 16) (a : Addr)
  | alu (op : Alu) (sz : Size) (dst : Loc) (src : Src)
  | test (sz : Size) (a : Loc) (b : Src)
  | unary (op : Unary) (sz : Size) (dst : Loc)
  | shift (op : Shift) (sz : Size) (dst : Loc) (n : Count)
  /-- `shld` (`left`) and `shrd`. -/
  | shiftd (left : Bool) (sz : Size) (dst : Loc) (src : Fin 16) (n : Count)
  /-- `mul` and `imul` of one operand: `rdx:rax` is `rax` times `src`. -/
  | mul (signed : Bool) (sz : Size) (src : Loc)
  /-- `div` and `idiv`: `rdx:rax` divided by `src`. -/
  | div (signed : Bool) (sz : Size) (src : Loc)
  /-- `imul` of two or three operands: `dst` is `a` times `b`. -/
  | imul (sz : Size) (dst : Fin 16) (a b : Src)
  | push (src : Src)
  | pop (dst : Loc)
  | xchg (sz : Size) (a : Loc) (b : Fin 16)
  | jcc (c : Cc) (target : BitVec 64)
  | jmp (target : BitVec 64)
  | jmpTo (l : Loc)
  | call (target : BitVec 64)
  | callTo (l : Loc)
  | ret
  | setcc (c : Cc) (dst : Loc)
  | cmov (c : Cc) (sz : Size) (dst : Fin 16) (src : Loc)
  /-- `cbw`, `cwde`, `cdqe`: `rax` at half of `sz`, sign-extended to `sz`. -/
  | widenA (sz : Size)
  /-- `cwd`, `cdq`, `cqo`: the sign of `rax` at `sz` into `rdx`. -/
  | widenD (sz : Size)
  | bswap (sz : Size) (r : Fin 16)
  | scan (op : Scan) (sz : Size) (dst : Fin 16) (src : Loc)
  | bit (op : BitOp) (sz : Size) (dst : Loc) (i : Src)
  | movs (sz : Size) (rep : Bool)
  | stos (sz : Size) (rep : Bool)
  | cld
  | std
  | leave
  | syscall
  | int3
  | ud2
  | nop
  deriving DecidableEq, Repr, Inhabited

namespace Decode

/-- A decoder over the bytes: a position goes in and comes out. -/
abbrev D := ReaderT ByteArray (StateT Nat Option)

def byte : D Nat := fun bs p => if h : p < bs.size then some (bs[p].toNat, p + 1) else none

/-- The next byte, not taken. -/
def peek : D Nat := fun bs p => if h : p < bs.size then some (bs[p].toNat, p) else none

/-- `n` bytes, little-endian. -/
def le (n : Nat) : D Nat := do
  let mut v := 0
  for k in [0 : n] do
    v := v ||| ((← byte) <<< (8 * k))
  return v

/-- `n` bytes as a signed number, extended to 64 bits. -/
def simm (n : Nat) : D (BitVec 64) := do
  return (BitVec.ofNat (8 * n) (← le n)).signExtend 64

/-- The prefixes of an instruction. -/
structure Pre where
  /-- `66`: operands of 16 bits. -/
  small : Bool := false
  /-- `F3`. -/
  rep : Bool := false
  /-- The low four bits of a REX prefix: `W`, `R`, `X`, `B`. -/
  rex : Option Nat := none
  deriving Inhabited

def Pre.w (p : Pre) : Bool := (p.rex.getD 0) &&& 8 != 0
def Pre.r (p : Pre) : Nat := if (p.rex.getD 0) &&& 4 != 0 then 8 else 0
def Pre.x (p : Pre) : Nat := if (p.rex.getD 0) &&& 2 != 0 then 8 else 0
def Pre.b (p : Pre) : Nat := if (p.rex.getD 0) &&& 1 != 0 then 8 else 0

/-- The size of the operands where the opcode does not fix it. -/
def Pre.size (p : Pre) : Size := if p.w then .q else if p.small then .w else .d

/-- The prefixes: at most `fuel` of them, a REX prefix last. -/
def prefixes : Nat → Pre → D Pre
  | 0, _ => failure
  | fuel + 1, p => do
    let b ← peek
    if b == 0x66 then let _ ← byte; prefixes fuel { p with small := true }
    else if b == 0xF3 then let _ ← byte; prefixes fuel { p with rep := true }
    else if b == 0x2E || b == 0x36 || b == 0x3E || b == 0x26 then let _ ← byte; prefixes fuel p
    else if 0x40 ≤ b && b < 0x50 then let _ ← byte; return { p with rex := some (b &&& 15) }
    else return p

/-- A register as an operand of a size: of one byte and without a REX prefix, the numbers 4
    to 7 are the second bytes of the first four registers. -/
def regLoc (p : Pre) (sz : Size) (n : Nat) : Loc :=
  if sz = .b ∧ p.rex.isNone ∧ 4 ≤ n ∧ n < 8 then .high (Fin.ofNat 4 (n - 4)) else .reg (Fin.ofNat 16 n)

/-- A ModRM byte, with what follows it. -/
structure RM where
  /-- The middle field alone: the operation, in an opcode that is a group. -/
  ext : Nat
  /-- The middle field as a register. -/
  reg : Nat
  /-- The last field as a register, when it is one. -/
  rm : Nat
  /-- The address, when it is memory. -/
  mem : Option Addr

/-- A ModRM byte with its SIB byte and displacement. `next` is the address after the
    instruction, which an address relative to the instruction pointer counts from. -/
def modrm (p : Pre) (next : BitVec 64) : D RM := do
  let m ← byte
  let mode := m >>> 6
  let ext := (m >>> 3) &&& 7
  let rm := m &&& 7
  let out (mem : Option Addr) : RM := { ext, reg := ext + p.r, rm := rm + p.b, mem }
  let disp : D (BitVec 64) := if mode == 1 then simm 1 else if mode == 2 then simm 4 else pure 0
  if mode == 3 then return out none
  if rm == 4 then
    let s ← byte
    let i := ((s >>> 3) &&& 7) + p.x
    let index := if i == 4 then none else some (Fin.ofNat 16 i, s >>> 6)
    let base := s &&& 7
    if base == 5 && mode == 0 then
      return out (some { base := none, index, disp := ← simm 4 })
    return out (some { base := some (Fin.ofNat 16 (base + p.b)), index, disp := ← disp })
  if rm == 5 && mode == 0 then
    return out (some { base := none, index := none, disp := next + (← simm 4) })
  return out (some { base := some (Fin.ofNat 16 (rm + p.b)), index := none, disp := ← disp })

/-- The place a ModRM byte names with its last field. -/
def RM.loc (p : Pre) (sz : Size) (m : RM) : Loc :=
  match m.mem with
  | some a => .mem a
  | none => regLoc p sz m.rm

def aluOf : Nat → Alu
  | 0 => .add | 1 => .or | 2 => .adc | 3 => .sbb | 4 => .and | 5 => .sub | 6 => .xor | _ => .cmp

def ccOf : Nat → Cc
  | 0 => .o | 1 => .no | 2 => .b | 3 => .ae | 4 => .e | 5 => .ne | 6 => .be | 7 => .a
  | 8 => .s | 9 => .ns | 10 => .p | 11 => .np | 12 => .l | 13 => .ge | 14 => .le | _ => .g

/-- The shift of a group's field; `rcl` and `rcr` are not taken. -/
def shiftOf : Nat → Option Shift
  | 0 => some .rol | 1 => some .ror | 4 | 6 => some .shl | 5 => some .shr | 7 => some .sar | _ => none

/-- A constant of the operand size, as an instruction holds it: at most four bytes, signed. -/
def immz (sz : Size) : D (BitVec 64) := simm (if sz = .w then 2 else 4)

/-- An instruction after `0F`. -/
def two (p : Pre) (next : BitVec 64) : D Instr := do
  let sz := p.size
  let b ← byte
  let r (n : Nat) : Fin 16 := Fin.ofNat 16 n
  if b == 0x05 then return .syscall
  if b == 0x0B then return .ud2
  if b == 0x1F then let _ ← modrm p next; return .nop
  if 0x40 ≤ b && b < 0x50 then
    let m ← modrm p next
    return .cmov (ccOf (b - 0x40)) sz (r m.reg) (m.loc p sz)
  if 0x80 ≤ b && b < 0x90 then
    if p.small then failure
    return .jcc (ccOf (b - 0x80)) (next + (← simm 4))
  if 0x90 ≤ b && b < 0xA0 then
    let m ← modrm p next
    return .setcc (ccOf (b - 0x90)) (m.loc p .b)
  if b == 0xA3 || b == 0xAB || b == 0xB3 || b == 0xBB then
    let m ← modrm p next
    -- with a register for the index, memory is a string of bits: not taken
    if m.mem.isSome then failure
    let op : BitOp := if b == 0xA3 then .bt else if b == 0xAB then .bts else if b == 0xB3 then .btr else .btc
    return .bit op sz (m.loc p sz) (.loc (.reg (r m.reg)))
  if b == 0xBA then
    let m ← modrm p next
    let i ← le 1
    let op : BitOp ← match m.ext with
      | 4 => pure .bt | 5 => pure .bts | 6 => pure .btr | 7 => pure .btc | _ => failure
    return .bit op sz (m.loc p sz) (.imm (BitVec.ofNat 64 i))
  if b == 0xA4 || b == 0xAC then
    let m ← modrm p next
    return .shiftd (b == 0xA4) sz (m.loc p sz) (r m.reg) (.imm (← le 1))
  if b == 0xA5 || b == 0xAD then
    let m ← modrm p next
    return .shiftd (b == 0xA5) sz (m.loc p sz) (r m.reg) .cl
  if b == 0xAF then
    let m ← modrm p next
    return .imul sz (r m.reg) (.loc (.reg (r m.reg))) (.loc (m.loc p sz))
  if b == 0xB6 || b == 0xB7 || b == 0xBE || b == 0xBF then
    let m ← modrm p next
    let ssz : Size := if b == 0xB6 || b == 0xBE then .b else .w
    return .movx (b ≥ 0xBE) sz ssz (r m.reg) (m.loc p ssz)
  if b == 0xBC || b == 0xBD then
    let m ← modrm p next
    let op : Scan := match b == 0xBC, p.rep with
      | true, false => .bsf | true, true => .tzcnt | false, false => .bsr | false, true => .lzcnt
    return .scan op sz (r m.reg) (m.loc p sz)
  if 0xC8 ≤ b && b < 0xD0 then
    if p.small then failure
    return .bswap sz (r (b - 0xC8 + p.b))
  failure

/-- An instruction after its prefixes. -/
def one (p : Pre) (next : BitVec 64) : D Instr := do
  let sz := p.size
  let b ← byte
  let r (n : Nat) : Fin 16 := Fin.ofNat 16 n
  if b == 0x0F then two p next
  else if b < 0x40 && b &&& 7 < 6 then
    let op := aluOf (b >>> 3)
    match b &&& 7 with
    | 0 => let m ← modrm p next; return .alu op .b (m.loc p .b) (.loc (regLoc p .b m.reg))
    | 1 => let m ← modrm p next; return .alu op sz (m.loc p sz) (.loc (.reg (r m.reg)))
    | 2 => let m ← modrm p next; return .alu op .b (regLoc p .b m.reg) (.loc (m.loc p .b))
    | 3 => let m ← modrm p next; return .alu op sz (.reg (r m.reg)) (.loc (m.loc p sz))
    | 4 => return .alu op .b (.reg 0) (.imm (← simm 1))
    | _ => return .alu op sz (.reg 0) (.imm (← immz sz))
  else if 0x50 ≤ b && b < 0x58 then
    if p.small then failure
    return .push (.loc (.reg (r (b - 0x50 + p.b))))
  else if 0x58 ≤ b && b < 0x60 then
    if p.small then failure
    return .pop (.reg (r (b - 0x58 + p.b)))
  else if b == 0x63 then
    -- `movsxd` to a register of 32 bits is a `mov` no compiler writes: not taken
    if sz != .q then failure
    let m ← modrm p next
    return .movx true .q .d (r m.reg) (m.loc p .d)
  else if b == 0x68 || b == 0x6A then
    if p.small then failure
    return .push (.imm (← simm (if b == 0x68 then 4 else 1)))
  else if b == 0x69 || b == 0x6B then
    let m ← modrm p next
    let i ← if b == 0x69 then immz sz else simm 1
    return .imul sz (r m.reg) (.loc (m.loc p sz)) (.imm i)
  else if 0x70 ≤ b && b < 0x80 then
    return .jcc (ccOf (b - 0x70)) (next + (← simm 1))
  else if b == 0x80 || b == 0x81 || b == 0x83 then
    let s : Size := if b == 0x80 then .b else sz
    let m ← modrm p next
    let i ← if b == 0x81 then immz sz else simm 1
    return .alu (aluOf m.ext) s (m.loc p s) (.imm i)
  else if b == 0x84 || b == 0x85 then
    let s : Size := if b == 0x84 then .b else sz
    let m ← modrm p next
    return .test s (m.loc p s) (.loc (regLoc p s m.reg))
  else if b == 0x86 || b == 0x87 then
    -- of one byte it may name a second byte of a register: not taken
    if b == 0x86 then failure
    let m ← modrm p next
    return .xchg sz (m.loc p sz) (r m.reg)
  else if b == 0x88 || b == 0x89 then
    let s : Size := if b == 0x88 then .b else sz
    let m ← modrm p next
    return .mov s (m.loc p s) (.loc (regLoc p s m.reg))
  else if b == 0x8A || b == 0x8B then
    let s : Size := if b == 0x8A then .b else sz
    let m ← modrm p next
    return .mov s (regLoc p s m.reg) (.loc (m.loc p s))
  else if b == 0x8D then
    let m ← modrm p next
    let some a := m.mem | failure
    return .lea sz (r m.reg) a
  else if b == 0x8F then
    let m ← modrm p next
    if m.ext != 0 || p.small then failure
    return .pop (m.loc p .q)
  else if b == 0x90 then
    if p.b != 0 then return .xchg sz (.reg 0) 8
    return .nop
  else if 0x91 ≤ b && b < 0x98 then
    return .xchg sz (.reg 0) (r (b - 0x90 + p.b))
  else if b == 0x98 then return .widenA sz
  else if b == 0x99 then return .widenD sz
  else if b == 0xA4 || b == 0xA5 then return .movs (if b == 0xA4 then .b else sz) p.rep
  else if b == 0xAA || b == 0xAB then return .stos (if b == 0xAA then .b else sz) p.rep
  else if b == 0xA8 then return .test .b (.reg 0) (.imm (← simm 1))
  else if b == 0xA9 then return .test sz (.reg 0) (.imm (← immz sz))
  else if 0xB0 ≤ b && b < 0xB8 then
    return .mov .b (regLoc p .b (b - 0xB0 + p.b)) (.imm (BitVec.ofNat 64 (← le 1)))
  else if 0xB8 ≤ b && b < 0xC0 then
    return .mov sz (.reg (r (b - 0xB8 + p.b))) (.imm (BitVec.ofNat 64 (← le sz.bytes)))
  else if b == 0xC0 || b == 0xC1 || b == 0xD0 || b == 0xD1 || b == 0xD2 || b == 0xD3 then
    let s : Size := if b &&& 1 == 0 then .b else sz
    let m ← modrm p next
    let some op := shiftOf m.ext | failure
    let n : Count ← if b < 0xD0 then (.imm <$> le 1) else pure (if b < 0xD2 then .imm 1 else .cl)
    return .shift op s (m.loc p s) n
  else if b == 0xC3 then return .ret
  else if b == 0xC6 || b == 0xC7 then
    let s : Size := if b == 0xC6 then .b else sz
    let m ← modrm p next
    if m.ext != 0 then failure
    let i ← if b == 0xC6 then simm 1 else immz sz
    return .mov s (m.loc p s) (.imm i)
  else if b == 0xC9 then return .leave
  else if b == 0xCC then return .int3
  else if b == 0xE8 || b == 0xE9 then
    if p.small then failure
    let t := next + (← simm 4)
    return if b == 0xE8 then .call t else .jmp t
  else if b == 0xEB then return .jmp (next + (← simm 1))
  else if b == 0xF6 || b == 0xF7 then
    let s : Size := if b == 0xF6 then .b else sz
    let m ← modrm p next
    let l := m.loc p s
    match m.ext with
    | 0 | 1 => return .test s l (.imm (← if b == 0xF6 then simm 1 else immz sz))
    | 2 => return .unary .not s l
    | 3 => return .unary .neg s l
    | 4 => return .mul false s l
    | 5 => return .mul true s l
    | 6 => return .div false s l
    | _ => return .div true s l
  else if b == 0xFC then return .cld
  else if b == 0xFD then return .std
  else if b == 0xFE || b == 0xFF then
    let s : Size := if b == 0xFE then .b else sz
    let m ← modrm p next
    match m.ext with
    | 0 => return .unary .inc s (m.loc p s)
    | 1 => return .unary .dec s (m.loc p s)
    | 2 => if b == 0xFE || p.small then failure else return .callTo (m.loc p .q)
    | 4 => if b == 0xFE || p.small then failure else return .jmpTo (m.loc p .q)
    | 6 => if b == 0xFE || p.small then failure else return .push (.loc (m.loc p .q))
    | _ => failure
  else failure

/-- Whether `F3` before an instruction is one of its meanings here. -/
def repOk : Instr → Bool
  | .movs .. | .stos .. | .scan .tzcnt .. | .scan .lzcnt .. | .nop | .ret => true
  | _ => false

/-- An instruction with its prefixes. -/
def instr (next : BitVec 64) : D Instr := do
  let p ← prefixes 14 {}
  let i ← one p next
  if p.rep && !repOk i then failure
  return i

end Decode

/-- **The instruction at position `pos` of `bytes`, which is at address `addr`**, and its
    length: read once for the length, and again knowing where it ends. -/
def decode (bytes : ByteArray) (pos : Nat) (addr : BitVec 64) : Option (Instr × Nat) := do
  let (_, stop) ← Decode.instr 0 bytes pos
  let n := stop - pos
  if n > 15 then none
  let (i, _) ← Decode.instr (addr + BitVec.ofNat 64 n) bytes pos
  return (i, n)

end MachineChecked.X86.Lift
