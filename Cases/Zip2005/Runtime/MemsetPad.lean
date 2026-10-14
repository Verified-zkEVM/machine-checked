import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Image.F_7803f57c
import Cases.Zip2005.Image.Ro

/-!
# `memset(b + 1, 0, 63)`: the rest of a block after its pad byte

SHA-256's finalisation writes the `0x80` pad byte at the buffer position (here 0, the block's
first byte) and clears the 63 bytes after it: a pointer one byte into an aligned doubleword,
seven head bytes, seven doublewords, no tail. The spec leaves the block's contents unstated
(some eight words): its one caller, `syscall_halt`, hands the block to `compress256`, whose
contract (ledger S1) does not read them either.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- `negw` of a pointer one byte into an aligned doubleword: seven head bytes. -/
theorem negw_and7_one (a : Word) (h : (a - 1#64) &&& 7#64 = 0#64) :
    BitVec.signExtend 64 (BitVec.truncate 32 0#64 + -BitVec.truncate 32 a) &&& 7#64 = 7#64 := by
  have ha : (a - 1#64).toNat % 8 = 0 := by
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod] at this
    simpa using this
  rw [BitVec.toNat_sub] at ha
  simp only [BitVec.toNat_ofNat] at ha
  have hlt := a.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (7#64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    BitVec.toNat_signExtend]
  simp only [BitVec.truncate_eq_setWidth, BitVec.setWidth_zero, BitVec.zero_add, BitVec.toNat_neg,
    BitVec.toNat_setWidth]
  split <;> omega

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem memset63_pad_spec {P : Prop} (s : MachineState) (ra a0 : Word) (O : List Word)
    (hOl : O.length = 8)
    (hpc : s.pc = 0x7803f57c#64) (hcode : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = 0#64) (ha2 : s.getReg .x12 = 63#64)
    (hO : Region (a0 - 1#64) O s) (hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (a0 - 1#64) 8)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(a0 - 1#64, 8)] s t →
      (∃ W : List Word, W.length = 8 ∧ Region (a0 - 1#64) W t) → Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl [(a0 - 1#64, 8)] s
  have hm := negw_and7_one a0 hok0.and7
  sym_exec
  sym_close hk

end Cases.Zip2005
