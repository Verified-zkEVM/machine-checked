import Cases.Zip2005.Field.Coordinates
import Cases.Zip2005.Field.CtLimbs
import Cases.Zip2005.Kit.Bytes
import Cases.Zip2005.Image.Ro

/-!
# Glue for `main`'s cut segments

Reading the accepting path's branch facts back as the checks they encode: a flag byte tested
against `1`, and a `ct_eq` result (`bw (decide …)` masked to its low byte) tested against `1`.
-/

namespace Cases.Zip2005

open Cases.Zip2005.Image

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel MachineChecked.RiscV.Sym

/-- A flag byte whose zero-extension was found equal to `1`. -/
theorem flag_of_br (cf v : Word) (hv : BitVec.zeroExtend 64 (extractByte cf 0) = v)
    (h : ¬(v != 1#64) = true) : extractByte cf 0 = 1#8 := by
  have h1 : v = 1#64 := by simpa using h
  subst h1
  have h2 := congrArg BitVec.toNat hv
  have h3 := (extractByte cf 0).isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h2
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- A `ct_eq` result found equal to `1`: the four limb equalities hold. -/
theorem ct_of_br (c : Prop) [Decidable c] (v : Word) (hv : bw (decide c) &&& 255#64 = v)
    (h : ¬(v != 1#64) = true) : c := by
  by_contra hc
  simp only [hc, decide_false, bw, Bool.false_eq_true, if_false] at hv
  subst hv
  exact h (by decide)

/-- Four limbs equal cell by cell give equal `natToLeLimbs 4`. -/
theorem natToLeLimbs_four_eq (a b : Nat) (v0 v1 v2 v3 : Word)
    (h : BitVec.ofNat 64 (a >>> 0) = v0 ∧ BitVec.ofNat 64 (a >>> 64) = v1 ∧
      BitVec.ofNat 64 (a >>> 128) = v2 ∧ BitVec.ofNat 64 (a >>> 192) = v3)
    (h0 : BitVec.ofNat 64 b = v0) (h1 : BitVec.ofNat 64 (b >>> 64) = v1)
    (h2 : BitVec.ofNat 64 (b >>> 128) = v2) (h3 : BitVec.ofNat 64 (b >>> 192) = v3) :
    natToLeLimbs 4 a = natToLeLimbs 4 b := by
  obtain ⟨e0, e1, e2, e3⟩ := h
  rw [Nat.shiftRight_zero] at e0
  rw [natToLeLimbs_four, natToLeLimbs_four, e0, e1, e2, e3, h0, h1, h2, h3]


/-- A flag byte stored with `replaceByte` and found equal to `1`. -/
theorem flag_of_cell (cf o : Word) (f : BitVec 8) (he : cf = replaceByte o 0 f)
    (h : extractByte cf 0 = 1#8) : f = 1#8 := by
  rw [he, extractByte_replaceByte o 0 (by decide)] at h; exact h

/-- The same, with the cell already substituted. -/
theorem flag_of_replace (o : Word) (f : BitVec 8) (h : extractByte (replaceByte o 0 f) 0 = 1#8) :
    f = 1#8 := by
  rw [extractByte_replaceByte o 0 (by decide)] at h; exact h


/-- `ct_of_br` for a branch taken on equality (`beq`). -/
theorem ct_of_beq (c : Prop) [Decidable c] (v : Word) (hv : bw (decide c) &&& 255#64 = v)
    (h : (v == 1#64) = true) : c :=
  ct_of_br c v hv (by simp only [bne, h, Bool.not_true]; decide)

/-- A `ct_eq` result found equal to `0`: the limbs differ. -/
theorem ct_false_of_br (c : Prop) [Decidable c] (v : Word) (hv : bw (decide c) &&& 255#64 = v)
    (h : ¬(v != 0#64) = true) : ¬c := by
  intro hc
  simp only [hc, decide_true, bw, if_true] at hv
  subst hv
  exact h (by decide)


/-- A cell range of `main`'s frame is disjoint from the write set of the lazy `FP_TABLES` build:
the control block, the static itself and the arena. -/
theorem frame_disj_heap {sp : Word} (hspHi : sp.toNat + 0x10a0 ≤ 0x78000000) (o : Word) (n : Nat)
    (h : o.toNat + 8 * n ≤ 0x10a0) :
    ∀ r ∈ [((0x78040620#64 : Word), (4162 : Nat)), ((0x780488a8#64 : Word), (10 : Nat)),
      ((0x78048980#64 : Word), (14780690128 : Nat))], Disjoint (sp + o) n r.1 r.2 := by
  intro r hr
  have e : (sp + o).toNat = sp.toNat + o.toNat := by
    rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
  · refine ⟨Or.inl ?_, ?_, ?_⟩ <;> simp only [e, BitVec.toNat_ofNat] <;> omega

/-- That write set lies above the read-only segment. -/
theorem heap_above_ro : ∀ r ∈ [((0x78040620#64 : Word), (4162 : Nat)), ((0x780488a8#64 : Word), (10 : Nat)),
      ((0x78048980#64 : Word), (14780690128 : Nat))],
    r.1.toNat + 8 * r.2 ≤ Ro.layout.roBase ∨ Ro.layout.roBase + Ro.layout.roBytes ≤ r.1.toNat := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> right <;> decide

/-- Three branch facts that cannot hold together: `a ≠ b`, `a = 0` and `b = 0` (the `sk` / `qk`
dispatch's arm to segment B with `sk` absent). -/
theorem dead_arm (a b : Word) (h1 : ¬(a == b) = true) (h2 : ¬(a != 0#64) = true)
    (h3 : (b == 0#64) = true) : False := by
  have ha : a = 0#64 := by simpa [bne] using h2
  have hb : b = 0#64 := by simpa using h3
  exact h1 (by simp [ha, hb])


/-- `memcmp`'s result, sign-extended and found zero by the branch, is zero. -/
theorem memcmp_zero (x v : Word) (h5 : BitVec.signExtend 64 (BitVec.truncate 32 x) = x)
    (hv : BitVec.signExtend 64 (BitVec.truncate 32 x + BitVec.truncate 32 0#64) = v)
    (h : ¬(v != 0#64) = true) : x = 0#64 := by
  have hv0 : v = 0#64 := by simpa using h
  subst hv0
  rw [show BitVec.truncate 32 (0#64) = 0#32 from rfl, BitVec.add_zero, h5] at hv
  exact hv

/-- Four limb equalities as a list equality. -/
theorem list4_of_and {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h : a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3) : [a0, a1, a2, a3] = [b0, b1, b2, b3] := by
  obtain ⟨h0, h1, h2, h3⟩ := h; subst h0 h1 h2 h3; rfl

/-- The `sk` / `qk` dispatch's tag bytes on the `sk` arm: the two `qk` tags agree and are zero
(`qk` absent), the `sk` tag is not. -/
theorem tags_of_br (x y z : BitVec 8) (v12 v13 v15 : BitVec 64) (h12 : BitVec.zeroExtend 64 x = v12)
    (h13 : BitVec.zeroExtend 64 y = v13) (h15 : BitVec.zeroExtend 64 z = v15)
    (b14 : ¬(v12 != v13) = true) (b17 : ¬(v12 != 0#64) = true) (b18 : ¬(v15 == 0#64) = true) :
    x = 0#8 ∧ y = 0#8 ∧ z ≠ 0#8 := by
  have a : v12 = 0#64 := by simpa [bne] using b17
  have b : v12 = v13 := by simpa [bne] using b14
  have c : v15 ≠ 0#64 := by simpa using b18
  subst h12 h13 h15
  refine ⟨?_, ?_, ?_⟩ <;> bv_omega

end Cases.Zip2005
