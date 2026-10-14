import Cases.Zip2005.Sinsemilla.PadKit
import Cases.Zip2005.Sinsemilla.SinsemillaModel
import Cases.Zip2005.Orchard.CommitIvk
import Cases.Zip2005.Kit.RegionGlue
import Cases.Zip2005.Image.Ro

/-!
# Lemmas for `from_iter`'s byte `Vec`

`BitsUpTo A B V n`: bytes `0 … n - 1` of the words `V` are the message bits (`ivkBit`), as
`byteAt` reads them. The loop writes a word at a time (`List.set`), and the growth copies a
prefix.
-/

namespace Cases.Zip2005

open Cases.Zip2005.Image

open RiscvZkvm.Rv64 AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- Bytes `o < n` of `V` hold message bits `o`. -/
def BitsUpTo (A B V : List Word) (n : Nat) : Prop :=
  ∀ o, o < n → byteAt V o = bw (ivkBit A B o)

theorem BitsUpTo.mono {A B V : List Word} {n m : Nat} (h : BitsUpTo A B V n) (hm : m ≤ n) :
    BitsUpTo A B V m :=
  fun o ho => h o (by omega)

/-- A byte as the executor stores it, read back through `byteAt`. -/
theorem byteAt_of_extract {V : List Word} {o : Nat} {b : Bool}
    (h : extractByte V[o / 8]! (o % 8) = BitVec.truncate 8 (bw b)) : byteAt V o = bw b := by
  unfold byteAt; rw [h, bw_zext_trunc]

/-- Word `m` written with bytes `b < r` the bits `8m + b`: `8m + r` bits. -/
theorem BitsUpTo.set {A B V : List Word} {m : Nat} (w : Word) (r : Nat) (hr : r ≤ 8)
    (hm : m < V.length) (h : BitsUpTo A B V (8 * m))
    (hb : ∀ b, b < r → extractByte w b = BitVec.truncate 8 (bw (ivkBit A B (8 * m + b)))) :
    BitsUpTo A B (V.set m w) (8 * m + r) := by
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
theorem BitsUpTo.set7 {A B V : List Word} {m : Nat} (w : Word)
    (hm : m < V.length) (h : BitsUpTo A B V (8 * m + 1))
    (hb0 : extractByte w 0 = extractByte V[m]! 0)
    (hb : ∀ b, 1 ≤ b → b < 8 → extractByte w b = BitVec.truncate 8 (bw (ivkBit A B (8 * m + b)))) :
    BitsUpTo A B (V.set m w) (8 * m + 8) := by
  refine BitsUpTo.set w 8 (le_refl _) hm (h.mono (by omega)) ?_
  intro b hb8
  rcases Nat.eq_zero_or_pos b with rfl | hb1
  · rw [hb0]
    have := h (8 * m) (by omega)
    unfold byteAt at this
    rw [show 8 * m / 8 = m by omega, show 8 * m % 8 = 0 by omega] at this
    rw [Nat.add_zero, ← this, trunc8_zext]
  · exact hb b hb1 hb8

/-- The bits survive a copy of the words that hold them. -/
theorem BitsUpTo.prefix {A B V V' : List Word} {n k : Nat} (h : BitsUpTo A B V n) (hn : n ≤ 8 * k)
    (hp : ∀ i, i < k → V'[i]! = V[i]!) : BitsUpTo A B V' n := by
  intro o ho
  unfold byteAt
  rw [hp (o / 8) (by omega)]
  exact h o ho

theorem BitsUpTo.take {A B V : List Word} {n k : Nat} (h : BitsUpTo A B V n) (hn : n ≤ 8 * k)
    (hk : k ≤ V.length) : BitsUpTo A B (V.take k) n :=
  h.prefix hn fun i hi => by
    rw [getBang (by simp; omega), getBang (by omega), List.getElem_take]

/-- Byte 0 of word `k` the bit `8k`: one more bit. -/
theorem BitsUpTo.byte0 {A B V : List Word} {k : Nat} (h : BitsUpTo A B V (8 * k))
    (hb : extractByte V[k]! 0 = BitVec.truncate 8 (bw (ivkBit A B (8 * k)))) :
    BitsUpTo A B V (8 * k + 1) := by
  intro o ho
  rcases Nat.lt_or_ge o (8 * k) with h1 | h1
  · exact h o h1
  · have : o = 8 * k := by omega
    subst this
    apply byteAt_of_extract
    rw [show 8 * k / 8 = k by omega, show 8 * k % 8 = 0 by omega, hb]

/-! ## The `Vec`'s words as three regions: the words before `m`, word `m`, the rest -/

theorem Region.window {p : Word} {V : List Word} {s : MachineState} (h : Region p V s) (m : Nat)
    (hm : m < V.length) : Region (p + BitVec.ofNat 64 (8 * m)) [V[m]!] s := by
  have := (h.shift m).take 1
  rwa [List.drop_eq_getElem_cons hm, List.take_succ_cons, List.take_zero, ← getBang hm] at this

theorem Region.set_of_parts {p : Word} {V : List Word} {s : MachineState} (m : Nat) (w : Word)
    (hm : m < V.length) (h1 : Region p (V.take m) s) (h2 : Region (p + BitVec.ofNat 64 (8 * m)) [w] s)
    (h3 : Region (p + BitVec.ofNat 64 (8 * (m + 1))) (V.drop (m + 1)) s) :
    Region p (V.set m w) s := by
  rw [List.set_eq_take_append_cons_drop, if_pos hm]
  show Region p (V.take m ++ ([w] ++ V.drop (m + 1))) s
  refine Region.append' h1 (Region.append' h2 h3 ?_) ?_
  · rw [List.length_singleton, BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
  · rw [List.length_take, Nat.min_eq_left (by omega)]

/-- The word pointer of word `m + 1`. -/
theorem word_next (p : Word) (m : Nat) :
    p + BitVec.ofNat 64 (8 * m) + 8#64 = p + BitVec.ofNat 64 (8 * (m + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_succ]

/-! ## Word arithmetic for the loop glue -/

theorem ofNat_beq_false {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hne : a ≠ b) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  apply hne
  have := congrArg BitVec.toNat h
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem toNat_sub_lit (sp : Word) (k : Nat) (hk : k ≤ sp.toNat) :
    (sp - BitVec.ofNat 64 k).toNat = sp.toNat - k := by
  have := sp.isLt
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  omega

theorem toNat_add_lit (p : Word) (k : Nat) (h : p.toNat + k < 2 ^ 64) :
    (p + BitVec.ofNat 64 k).toNat = p.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt h]

/-- `sp - a + k` with `k ≤ a`. -/
theorem sub_add_eq_sub (sp : Word) (a k : Nat) (h : k ≤ a) :
    sp - BitVec.ofNat 64 a + BitVec.ofNat 64 k = sp - BitVec.ofNat 64 (a - k) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- `sp - a + k` with `a ≤ k`. -/
theorem sub_add_eq_add (sp : Word) (a k : Nat) (h : a ≤ k) :
    sp - BitVec.ofNat 64 a + BitVec.ofNat 64 k = sp + BitVec.ofNat 64 (k - a) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-! The frame of `from_iter` and its callees, `[sp - 0x1b0, sp + 0xb0)`, as one 76-word block
`F = sp - 0x1b0`; every stack region the loop touches is an offset into it. -/

theorem fr_m100 (sp : Word) : sp - 0x100#64 = sp - 0x1b0#64 + BitVec.ofNat 64 (8 * 22) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem fr_m30 (sp : Word) : sp - 0x30#64 = sp - 0x1b0#64 + BitVec.ofNat 64 (8 * 48) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem fr_m10 (sp : Word) : sp - 0x10#64 = sp - 0x1b0#64 + BitVec.ofNat 64 (8 * 52) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem fr_0 (sp : Word) : sp = sp - 0x1b0#64 + BitVec.ofNat 64 (8 * 54) :=
  (BitVec.sub_add_cancel sp 0x1b0#64).symm
theorem fr_18 (sp : Word) : sp + 0x18#64 = sp - 0x1b0#64 + BitVec.ofNat 64 (8 * 57) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega
theorem fr_78 (sp : Word) : sp + 0x78#64 = sp - 0x1b0#64 + BitVec.ofNat 64 (8 * 69) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- The frame does not wrap and lies below the heap. -/
theorem frame_toNat {sp : Word} (h : StackOk Ro.layout 0x1b0 sp) :
    (sp - 0x1b0#64).toNat = sp.toNat - 0x1b0 :=
  toNat_sub_lit sp 0x1b0 (by have := h.lo; omega)

theorem frame_nowrap {sp : Word} (h : StackOk Ro.layout 0x1b0 sp) : (sp - 0x1b0#64).toNat + 8 * 76 ≤ 2 ^ 64 := by
  rw [frame_toNat h]; have := (Nat.le_trans h.hi (Nat.le_of_eq Ro.layout_stackTop)); have := h.lo; omega

theorem _root_.Asm.Disjoint.heap_frame76 {sp : Word} (h : StackOk Ro.layout 0x1b0 sp) :
    AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 (sp - 0x1b0#64) 76 := by
  unfold AsmVerif.RiscV.Sym.Disjoint
  rw [frame_toNat h]
  have := (Nat.le_trans h.hi (Nat.le_of_eq Ro.layout_stackTop)); have := h.lo
  simp only [BitVec.toNat_ofNat]
  omega

/-- A block inside the heap range is disjoint from what the heap is disjoint from. -/
theorem _root_.Asm.Disjoint.of_heap {b : Word} {n : Nat} (h : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 b n)
    {p : Word} {L : Nat} (hlo : 0x78040620 ≤ p.toNat) (hhi : p.toNat + 8 * L ≤ 0x1c00000000) :
    AsmVerif.RiscV.Sym.Disjoint p L b n := by
  unfold AsmVerif.RiscV.Sym.Disjoint at *
  simp only [BitVec.toNat_ofNat] at h
  omega

/-- A sub-block of the left region. -/
theorem _root_.Asm.Disjoint.sub_left {b₁ : Word} {n₁ : Nat} {b₂ : Word} {n₂ : Nat} (h : AsmVerif.RiscV.Sym.Disjoint b₁ n₁ b₂ n₂)
    {a : Word} {i m : Nat} (ha : a = b₁ + BitVec.ofNat 64 (8 * i)) (him : i + m ≤ n₁) :
    AsmVerif.RiscV.Sym.Disjoint a m b₂ n₂ :=
  h.of_sub ha him (by rw [Nat.mul_zero, BitVec.add_zero]) (by omega)

theorem self_add_zero (p : Word) : p = p + BitVec.ofNat 64 (8 * 0) := by
  rw [Nat.mul_zero, BitVec.add_zero]

/-- A sub-block of the right region. -/
theorem _root_.Asm.Disjoint.sub_right {b₁ : Word} {n₁ : Nat} {b₂ : Word} {n₂ : Nat}
    (h : AsmVerif.RiscV.Sym.Disjoint b₁ n₁ b₂ n₂) {b : Word} {j n : Nat} (hb : b = b₂ + BitVec.ofNat 64 (8 * j))
    (hjn : j + n ≤ n₂) : AsmVerif.RiscV.Sym.Disjoint b₁ n₁ b n :=
  h.of_sub (self_add_zero b₁) (by omega) hb hjn

theorem covers_of_sub {b' : Word} {n' : Nat} (hnw : b'.toNat + 8 * n' ≤ 2 ^ 64) {b : Word} {i n : Nat}
    (hb : b = b' + BitVec.ofNat 64 (8 * i)) (hin : i + n ≤ n') (hn : 0 < n) : Covers b' n' b n := by
  subst hb
  unfold Covers
  rw [toNat_add_lit b' (8 * i) (by omega)]
  omega

theorem covers_heap {b : Word} {n : Nat} (hlo : 0x78040620 ≤ b.toNat) (hhi : b.toNat + 8 * n ≤ 0x1c00000000) :
    Covers 0x78040620#64 14780694332 b n := by
  unfold Covers
  simp only [BitVec.toNat_ofNat]
  omega

theorem list3_cells (O : List Word) (h : O.length = 3) : O = [O[0]!, O[1]!, O[2]!] := by
  match O, h with
  | [_, _, _], _ => rfl

end Cases.Zip2005
