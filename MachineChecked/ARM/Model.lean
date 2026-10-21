/-
  MachineChecked.ARM.Model

  **Trusted.** The AArch64 machine model, ported from catcrypt-compiler
  `CatCrypt/Crypto/SecureCompilation/ARMBackend/ArmModel.lean` at `69ffea9f` (MIT, Copyright
  (c) 2026 CatCrypt Contributors; see `MachineChecked/Ascent/LICENSE-catcrypt`). Changed: the
  namespace and the module-system markers; catcrypt-compiler's three nested machines (a
  32-bit `W` register file, a 64-bit register file with the carry flag, and that file with
  the zero flag, memory and the pc) are one machine here, whose `W` forms read and write the
  low halves of the `X` registers; the loop and branch-label alphabets of its code generator
  are not taken; the concrete `example`s are checked by `decide` instead of `native_decide`.

  It is hand-written and not proved against a canonical AArch64 specification: it sits on
  the trust ladder (`docs/ELF.md` §4) as a trusted ISA model, to be verified against
  sail-arm (`docs/ISA.md`) or replaced by a verified model. catcrypt-compiler's
  `SailArm64Refinement` (five ALU clauses) is not taken. Nothing in the RISC-V development
  imports it.
-/

import MachineChecked.ARM.Mem64

/-!
# An AArch64 machine model for a scalar general-purpose subset

The state is the `X` register file (`x0 … x30`, named by string; `xzr` and absent names read
zero), the carry and zero flags of NZCV, a byte-addressed data memory and the pc. One step
(`step`) runs one instruction:

* 64-bit arithmetic and logic, with the carry chain AArch64 exposes as a real flag:
  `ADD`/`SUB`, `ADDS`/`ADCS`/`ADC`, `SUBS`/`SBCS`/`SBC`, the widening `MUL`/`UMULH`,
  `AND`/`ORR`/`EOR`, `LSL`/`LSR`, `CSEL`, `MOVZ`/`MOVK`, `MOV`, and `ADD`/`SUB` with an
  immediate and `CMP`;
* the 32-bit `W` forms `ADD`/`SUB`/`AND`/`ORR`/`EOR`/`LSL`/`LSR`/`ROR`/`MOV`, which compute on
  the low 32 bits and zero-extend the result into the `X` register, as AArch64 does;
* doubleword loads and stores `LDR`/`STR Xt` at `[Xn, #8·pimm]` and `[Xn, Xm, LSL #3]`;
* the branches `CBNZ Xt` and `B.cond`, by a signed byte offset.

Each instruction's semantics is the integer operation the mnemonic names, auditable against
the Arm Architecture Reference Manual by eye; the flag-setting forms follow its
`AddWithCarry` pseudocode.
-/

set_option autoImplicit false

namespace MachineChecked.ARM

/-- A 64-bit `X` register value. -/
abbrev X64 : Type := BitVec 64

/-- The AArch64 machine state. -/
structure State where
  /-- The `X` register file, named by string. -/
  regs : String → X64
  /-- The NZCV carry flag `C`. -/
  cf : Bool
  /-- The NZCV zero flag `Z`. -/
  zf : Bool
  /-- The byte-addressed data memory. -/
  mem : Mem64
  /-- The program counter. -/
  pc : BitVec 64

namespace State

/-- Read an `X` register. The zero register `xzr` and any absent name read `0`. -/
@[simp] def get (s : State) (r : String) : X64 :=
  if r = "xzr" then 0 else s.regs r

/-- Read the `W` view (the low 32 bits) of a register. -/
def getW (s : State) (r : String) : BitVec 32 := (s.get r).truncate 32

/-- Write an `X` register. Writes to `xzr` are discarded. -/
def set (s : State) (r : String) (v : X64) : State :=
  if r = "xzr" then s else { s with regs := fun r' => if r' = r then v else s.regs r' }

/-- Write a `W` register: the value zero-extended into the `X` register. -/
def setW (s : State) (r : String) (v : BitVec 32) : State := s.set r (v.zeroExtend 64)

@[simp] theorem get_set_same (s : State) (r : String) (v : X64) (h : r ≠ "xzr") :
    (s.set r v).get r = v := by simp [set, get, h]

@[simp] theorem get_set_other (s : State) (r r' : String) (v : X64) (h : r' ≠ r) :
    (s.set r v).get r' = s.get r' := by
  by_cases hz : r' = "xzr"
  · simp [get, hz]
  · simp only [get, hz, if_false, set]
    by_cases hr : r = "xzr"
    · simp [hr]
    · simp [hr, h]

@[simp] theorem cf_set (s : State) (r : String) (v : X64) : (s.set r v).cf = s.cf := by
  unfold set; split <;> rfl

end State

/-! ## Operations -/

/-- `UMULH`: the high 64 bits of the unsigned product. -/
def umulh (a b : X64) : X64 := BitVec.ofNat 64 ((a.toNat * b.toNat) >>> 64)

/-- `AddWithCarry` for addition: the low 64 bits of `a + b + cin`, and the carry out. -/
def addWithCarry (a b : X64) (cin : Bool) : X64 × Bool :=
  let s : Nat := a.toNat + b.toNat + (if cin then 1 else 0)
  (BitVec.ofNat 64 s, s ≥ 2 ^ 64)

/-- `AddWithCarry(a, NOT b, cin)`, subtraction: `C` is set when there is no borrow. -/
def subWithBorrow (a b : X64) (cin : Bool) : X64 × Bool :=
  addWithCarry a (~~~ b) cin

/-- Insert `imm16` into the `hw`-th 16-bit lane of `old` (`MOVK`). -/
def movkInsert (old : X64) (imm16 hw : Nat) : X64 :=
  let lo := hw * 16
  let mask : X64 := BitVec.ofNat 64 (0xffff <<< lo)
  (old &&& ~~~ mask) ||| (BitVec.ofNat 64 ((imm16 % 0x10000) <<< lo))

/-- The condition codes the model uses. -/
inductive Cond where
  /-- `EQ`: `Z = 1`. -/
  | eq
  /-- `NE`: `Z = 0`. -/
  | ne
  /-- `CS`/`HS`: `C = 1`, unsigned `≥` after a `SUBS`. -/
  | cs
  /-- `CC`/`LO`: `C = 0`, unsigned `<` after a `SUBS`. -/
  | cc
  deriving Repr, DecidableEq

/-- The 4-bit condition-code number (Arm ARM C1.2.4). -/
def Cond.num : Cond → Nat
  | .eq => 0
  | .ne => 1
  | .cs => 2
  | .cc => 3

/-- Whether a condition holds for the zero flag `z` and the carry flag `c`. -/
def Cond.holds : Cond → Bool → Bool → Bool
  | .eq, z, _ => z
  | .ne, z, _ => !z
  | .cs, _, c => c
  | .cc, _, c => !c

/-! ## Instructions -/

/-- An instruction, over named registers. -/
inductive Inst where
  /-- `ADD Xd, Xn, Xm`. -/
  | add (d a b : String)
  /-- `SUB Xd, Xn, Xm`. -/
  | sub (d a b : String)
  /-- `ADDS Xd, Xn, Xm`: add, set `C`. -/
  | adds (d a b : String)
  /-- `ADCS Xd, Xn, Xm`: add with carry in, set `C`. -/
  | adcs (d a b : String)
  /-- `ADC Xd, Xn, Xm`: add with carry in. -/
  | adc (d a b : String)
  /-- `SUBS Xd, Xn, Xm`: subtract, set `C` (set when there is no borrow). -/
  | subs (d a b : String)
  /-- `SBCS Xd, Xn, Xm`: subtract with borrow, set `C`. -/
  | sbcs (d a b : String)
  /-- `SBC Xd, Xn, Xm`: subtract with borrow. -/
  | sbc (d a b : String)
  /-- `MUL Xd, Xn, Xm`: the low 64 bits of the product. -/
  | mul (d a b : String)
  /-- `UMULH Xd, Xn, Xm`: the high 64 bits of the unsigned product. -/
  | umulh (d a b : String)
  /-- `AND Xd, Xn, Xm`. -/
  | and (d a b : String)
  /-- `ORR Xd, Xn, Xm`. -/
  | orr (d a b : String)
  /-- `EOR Xd, Xn, Xm`. -/
  | eor (d a b : String)
  /-- `CSEL Xd, Xn, Xm, cond`. -/
  | csel (d a b : String) (c : Cond)
  /-- `MOVZ Xd, #imm16`. -/
  | movz (d : String) (imm16 : Nat)
  /-- `MOVK Xd, #imm16, LSL #(16·hw)`. -/
  | movk (d : String) (imm16 hw : Nat)
  /-- `MOV Xd, Xn`. -/
  | mov (d s : String)
  /-- `LSR Xd, Xn, #imm`. -/
  | lsr (d a : String) (imm : Fin 64)
  /-- `LSL Xd, Xn, #imm`. -/
  | lsl (d a : String) (imm : Fin 64)
  /-- `ADD Xd, Xn, #imm`, a 12-bit unsigned immediate. -/
  | addi (d a : String) (imm : Nat)
  /-- `SUB Xd, Xn, #imm`, a 12-bit unsigned immediate. -/
  | subi (d a : String) (imm : Nat)
  /-- `CMP Xn, Xm` (`SUBS XZR, Xn, Xm`): `Z` is `Xn = Xm`, `C` is `Xm ≤ Xn` unsigned. -/
  | cmp (a b : String)
  /-- `ADD Wd, Wn, Wm`. -/
  | addw (d a b : String)
  /-- `SUB Wd, Wn, Wm`. -/
  | subw (d a b : String)
  /-- `AND Wd, Wn, Wm`. -/
  | andw (d a b : String)
  /-- `ORR Wd, Wn, Wm`. -/
  | orrw (d a b : String)
  /-- `EOR Wd, Wn, Wm`. -/
  | eorw (d a b : String)
  /-- `LSL Wd, Wn, #imm`. -/
  | lslw (d a : String) (imm : Fin 32)
  /-- `LSR Wd, Wn, #imm`. -/
  | lsrw (d a : String) (imm : Fin 32)
  /-- `ROR Wd, Wn, #imm`. -/
  | rorw (d a : String) (imm : Fin 32)
  /-- `MOV Wd, Wn`. -/
  | movw (d s : String)
  /-- `LDR Xt, [Xn, #8·pimm]`. -/
  | ldr (t n : String) (pimm : Nat)
  /-- `STR Xt, [Xn, #8·pimm]`. -/
  | str (t n : String) (pimm : Nat)
  /-- `LDR Xt, [Xn, Xm, LSL #3]`. -/
  | ldrr (t n m : String)
  /-- `STR Xt, [Xn, Xm, LSL #3]`. -/
  | strr (t n m : String)
  /-- `CBNZ Xt, off`: branch by the byte offset `off` when `Xt ≠ 0`. -/
  | cbnz (t : String) (off : Int)
  /-- `B.cond off`: branch by the byte offset `off` when the condition holds. -/
  | bcond (c : Cond) (off : Int)
  deriving Repr, DecidableEq

/-- The effective address `Xn + 8·Xm` of the scaled register-offset form. -/
def addrR (s : State) (n m : String) : BitVec 64 := s.get n + (s.get m <<< 3)

/-- The effective address `Xn + 8·pimm` of the scaled immediate-offset form. -/
def addrI (s : State) (n : String) (pimm : Nat) : BitVec 64 :=
  s.get n + BitVec.ofNat 64 (8 * pimm)

/-- The register and flag effect of an instruction that falls through. -/
def exec (s : State) : Inst → State
  | .add d a b => s.set d (s.get a + s.get b)
  | .sub d a b => s.set d (s.get a - s.get b)
  | .adds d a b =>
      let (v, c) := addWithCarry (s.get a) (s.get b) false
      { s.set d v with cf := c }
  | .adcs d a b =>
      let (v, c) := addWithCarry (s.get a) (s.get b) s.cf
      { s.set d v with cf := c }
  | .adc d a b => s.set d (addWithCarry (s.get a) (s.get b) s.cf).1
  | .subs d a b =>
      let (v, c) := subWithBorrow (s.get a) (s.get b) true
      { s.set d v with cf := c }
  | .sbcs d a b =>
      let (v, c) := subWithBorrow (s.get a) (s.get b) s.cf
      { s.set d v with cf := c }
  | .sbc d a b => s.set d (subWithBorrow (s.get a) (s.get b) s.cf).1
  | .mul d a b => s.set d (s.get a * s.get b)
  | .umulh d a b => s.set d (umulh (s.get a) (s.get b))
  | .and d a b => s.set d (s.get a &&& s.get b)
  | .orr d a b => s.set d (s.get a ||| s.get b)
  | .eor d a b => s.set d (s.get a ^^^ s.get b)
  | .csel d a b c => s.set d (if c.holds s.zf s.cf then s.get a else s.get b)
  | .movz d imm16 => s.set d (BitVec.ofNat 64 (imm16 % 0x10000))
  | .movk d imm16 hw => s.set d (movkInsert (s.get d) imm16 hw)
  | .mov d a => s.set d (s.get a)
  | .lsr d a m => s.set d (s.get a >>> m.val)
  | .lsl d a m => s.set d (s.get a <<< m.val)
  | .addi d a imm => s.set d (s.get a + BitVec.ofNat 64 imm)
  | .subi d a imm => s.set d (s.get a - BitVec.ofNat 64 imm)
  | .cmp a b => { s with cf := !((s.get a).ult (s.get b)), zf := s.get a == s.get b }
  | .addw d a b => s.setW d (s.getW a + s.getW b)
  | .subw d a b => s.setW d (s.getW a - s.getW b)
  | .andw d a b => s.setW d (s.getW a &&& s.getW b)
  | .orrw d a b => s.setW d (s.getW a ||| s.getW b)
  | .eorw d a b => s.setW d (s.getW a ^^^ s.getW b)
  | .lslw d a m => s.setW d (s.getW a <<< m.val)
  | .lsrw d a m => s.setW d (s.getW a >>> m.val)
  | .rorw d a m => s.setW d (BitVec.rotateRight (s.getW a) m.val)
  | .movw d a => s.setW d (s.getW a)
  | .ldr t n pimm => s.set t (read64 s.mem (addrI s n pimm))
  | .str t n pimm => { s with mem := write64 s.mem (addrI s n pimm) (s.get t) }
  | .ldrr t n m => s.set t (read64 s.mem (addrR s n m))
  | .strr t n m => { s with mem := write64 s.mem (addrR s n m) (s.get t) }
  | .cbnz _ _ | .bcond _ _ => s

/-- **One step.** A branch adds its offset to the pc when taken; every other instruction runs
    `exec` and advances the pc by 4. -/
def step (s : State) : Inst → State
  | .cbnz t off => { s with pc := if s.get t ≠ 0 then s.pc + BitVec.ofInt 64 off else s.pc + 4 }
  | .bcond c off =>
      { s with pc := if c.holds s.zf s.cf then s.pc + BitVec.ofInt 64 off else s.pc + 4 }
  | i => { exec s i with pc := s.pc + 4 }

/-- A straight-line fold of `step`. -/
def runBlock (s : State) : List Inst → State
  | [] => s
  | i :: is => runBlock (step s i) is

@[simp] theorem runBlock_nil (s : State) : runBlock s [] = s := rfl

@[simp] theorem runBlock_cons (s : State) (i : Inst) (is : List Inst) :
    runBlock s (i :: is) = runBlock (step s i) is := rfl

theorem runBlock_append (xs ys : List Inst) (s : State) :
    runBlock s (xs ++ ys) = runBlock (runBlock s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih => simp only [List.cons_append, runBlock_cons]; exact ih _

/-- The scaled register offset is the byte offset `8·Xm` modulo `2⁶⁴`. -/
theorem shiftLeft_three_eq (x : BitVec 64) : x <<< 3 = BitVec.ofNat 64 (8 * x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mul_comm]

/-! ## Concrete checks -/

/-- `MUL`/`UMULH`: `(2⁶⁴-1)² = 0xfffffffffffffffe_0000000000000001`. -/
example : (BitVec.allOnes 64 * BitVec.allOnes 64 : X64) = 1
    ∧ umulh (BitVec.allOnes 64) (BitVec.allOnes 64) = BitVec.ofNat 64 0xfffffffffffffffe := by
  decide

/-- `ADDS` carry out: `(2⁶⁴-1) + 1` wraps to `0` and sets `C`. -/
example : addWithCarry (BitVec.allOnes 64) (1 : X64) false = (0, true) := by decide

/-- `SUBS` borrow: `0 - 1` gives all ones and clears `C`. -/
example : subWithBorrow (0 : X64) (1 : X64) true = (BitVec.allOnes 64, false) := by decide

/-- `MOVK`: `0xffff` into lane 3 of `1`. -/
example : movkInsert (BitVec.ofNat 64 1) 0xffff 3 = BitVec.ofNat 64 0xffff000000000001 := by
  decide

/-- `ROR Wd, Wn, #16` on `0x12345678` is `0x56781234`. -/
example : BitVec.rotateRight (BitVec.ofNat 32 0x12345678) 16 = BitVec.ofNat 32 0x56781234 := by
  decide

end MachineChecked.ARM
