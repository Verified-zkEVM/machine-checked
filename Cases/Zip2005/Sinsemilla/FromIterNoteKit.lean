import Cases.Zip2005.Sinsemilla.FromIterKit
import Cases.Zip2005.Sinsemilla.PadNextNoteSpec
import Cases.Zip2005.Image.Ro

/-!
# Lemmas for `from_iter`'s byte `Vec` (the note commitment's iterator)

`BitsUpToF bit V n`: bytes `0 … n - 1` of the words `V` are the bits `bit o`, as `byteAt`
reads them: `FromIterKit`'s `BitsUpTo` over any bit function. The frame of this `from_iter`
(`0x7801dfb4`) and its callees is `[sp - 0x180, sp + 0xe0)`, 76 words: `Pad::next`'s frame
(`0x180`) below the loop's `sp`, the loop's own frame (`0xe0`) above.
-/

namespace Cases.Zip2005

open Cases.Zip2005.Image

open RiscvZkvm.Rv64 MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- Bytes `o < n` of `V` hold the bits `bit o`. -/
def BitsUpToF (bit : Nat → Bool) (V : List Word) (n : Nat) : Prop :=
  ∀ o, o < n → byteAt V o = bw (bit o)

theorem BitsUpToF.mono {bit : Nat → Bool} {V : List Word} {n m : Nat} (h : BitsUpToF bit V n)
    (hm : m ≤ n) : BitsUpToF bit V m :=
  fun o ho => h o (by omega)

/-- Word `m` written with bytes `b < r` the bits `8m + b`: `8m + r` bits. -/
theorem BitsUpToF.set {bit : Nat → Bool} {V : List Word} {m : Nat} (w : Word) (r : Nat) (hr : r ≤ 8)
    (hm : m < V.length) (h : BitsUpToF bit V (8 * m))
    (hb : ∀ b, b < r → extractByte w b = BitVec.truncate 8 (bw (bit (8 * m + b)))) :
    BitsUpToF bit (V.set m w) (8 * m + r) := by
  intro o ho
  have ho8 : o / 8 ≤ m := by omega
  by_cases hom : o / 8 = m
  · apply byteAt_of_extract
    have hlen : o / 8 < (V.set m w).length := by rw [List.length_set]; omega
    rw [getBang hlen, List.getElem_set, if_pos hom.symm, hb (o % 8) (by omega),
      show 8 * m + o % 8 = o by omega]
  · have hlt : o / 8 < m := lt_of_le_of_ne ho8 hom
    have ho' : o < 8 * m := by omega
    unfold byteAt
    have hlen : o / 8 < (V.set m w).length := by rw [List.length_set]; omega
    rw [getBang hlen, List.getElem_set, if_neg (Ne.symm hom), ← getBang (by omega)]
    exact h o ho'

/-- Word `m` written with bytes `1 ≤ b < 8` the bits, byte 0 kept. -/
theorem BitsUpToF.set7 {bit : Nat → Bool} {V : List Word} {m : Nat} (w : Word)
    (hm : m < V.length) (h : BitsUpToF bit V (8 * m + 1))
    (hb0 : extractByte w 0 = extractByte V[m]! 0)
    (hb : ∀ b, 1 ≤ b → b < 8 → extractByte w b = BitVec.truncate 8 (bw (bit (8 * m + b)))) :
    BitsUpToF bit (V.set m w) (8 * m + 8) := by
  refine BitsUpToF.set w 8 (le_refl _) hm (h.mono (by omega)) ?_
  intro b hb8
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · rw [hb0]
    have := h (8 * m) (by omega)
    unfold byteAt at this
    rw [show 8 * m / 8 = m by omega, show 8 * m % 8 = 0 by omega] at this
    rw [Nat.add_zero, ← this, trunc8_zext]
  · exact hb b hb1 hb8

/-- The bits survive a copy of the words that hold them. -/
theorem BitsUpToF.prefix {bit : Nat → Bool} {V V' : List Word} {n k : Nat} (h : BitsUpToF bit V n)
    (hn : n ≤ 8 * k) (hp : ∀ i, i < k → V'[i]! = V[i]!) : BitsUpToF bit V' n := by
  intro o ho
  unfold byteAt
  rw [hp (o / 8) (by omega)]
  exact h o ho

theorem BitsUpToF.take {bit : Nat → Bool} {V : List Word} {n k : Nat} (h : BitsUpToF bit V n)
    (hn : n ≤ 8 * k) (hk : k ≤ V.length) : BitsUpToF bit (V.take k) n :=
  h.prefix hn fun i hi => by
    rw [getBang (by simp; omega), getBang (by omega), List.getElem_take]

/-- Byte 0 of word `k` the bit `8k`: one more bit. -/
theorem BitsUpToF.byte0 {bit : Nat → Bool} {V : List Word} {k : Nat} (h : BitsUpToF bit V (8 * k))
    (hb : extractByte V[k]! 0 = BitVec.truncate 8 (bw (bit (8 * k)))) :
    BitsUpToF bit V (8 * k + 1) := by
  intro o ho
  rcases Nat.lt_or_ge o (8 * k) with h1 | h1
  · exact h o h1
  · have : o = 8 * k := by omega
    subst this
    apply byteAt_of_extract
    rw [show 8 * k / 8 = k by omega, show 8 * k % 8 = 0 by omega, hb]

/-! The frame of this `from_iter` and its callees, `[sp - 0x180, sp + 0xe0)`, as one 76-word
block `F = sp - 0x180`; every stack region the loop touches is an offset into it. -/

theorem frn_m100 (sp : Word) : sp - 0x100#64 = sp - 0x180#64 + BitVec.ofNat 64 (8 * 16) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem frn_m30 (sp : Word) : sp - 0x30#64 = sp - 0x180#64 + BitVec.ofNat 64 (8 * 42) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem frn_0 (sp : Word) : sp = sp - 0x180#64 + BitVec.ofNat 64 (8 * 48) :=
  (BitVec.sub_add_cancel sp 0x180#64).symm
theorem frn_18 (sp : Word) : sp + 0x18#64 = sp - 0x180#64 + BitVec.ofNat 64 (8 * 51) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem frn_a8 (sp : Word) : sp + 0xa8#64 = sp - 0x180#64 + BitVec.ofNat 64 (8 * 69) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The frame does not wrap and lies below the heap. -/
theorem framen_toNat {sp : Word} (h : StackOk Ro.layout 0x180 sp) :
    (sp - 0x180#64).toNat = sp.toNat - 0x180 :=
  toNat_sub_lit sp 0x180 (by have := h.lo; omega)

theorem framen_nowrap {sp : Word} (h : StackOk Ro.layout 0x180 sp) : (sp - 0x180#64).toNat + 8 * 76 ≤ 2 ^ 64 := by
  rw [framen_toNat h]; have := (Nat.le_trans h.hi (Nat.le_of_eq Ro.layout_stackTop)); have := h.lo; omega

theorem _root_.MachineChecked.RiscV.Sym.Disjoint.heap_framen76 {sp : Word} (h : StackOk Ro.layout 0x180 sp) :
    MachineChecked.RiscV.Sym.Disjoint 0x78040620#64 14780694332 (sp - 0x180#64) 76 := by
  unfold MachineChecked.RiscV.Sym.Disjoint
  rw [framen_toNat h]
  have := (Nat.le_trans h.hi (Nat.le_of_eq Ro.layout_stackTop)); have := h.lo
  simp only [BitVec.toNat_ofNat]
  omega

/-! The message words at `NoteCommitment::derive`'s frame `sp0`: `g★_d` at `sp0 - 0xd0`, `pk★_d`
at `- 0xb0`, `v` at `- 0x90`, `ρ` at `- 0x88`, `ψ` at `- 0x68` — one 17-word block. -/

theorem msg_K (sp0 : Word) : sp0 + 18446744073709551440#64 = sp0 + 18446744073709551408#64 + BitVec.ofNat 64 (8 * 4) := by
  rw [BitVec.add_assoc]; rfl
theorem msg_V (sp0 : Word) : sp0 + 18446744073709551472#64 = sp0 + 18446744073709551408#64 + BitVec.ofNat 64 (8 * 8) := by
  rw [BitVec.add_assoc]; rfl
theorem msg_R (sp0 : Word) : sp0 + 18446744073709551480#64 = sp0 + 18446744073709551408#64 + BitVec.ofNat 64 (8 * 9) := by
  rw [BitVec.add_assoc]; rfl
theorem msg_Q (sp0 : Word) : sp0 + 18446744073709551512#64 = sp0 + 18446744073709551408#64 + BitVec.ofNat 64 (8 * 13) := by
  rw [BitVec.add_assoc]; rfl

end Cases.Zip2005
