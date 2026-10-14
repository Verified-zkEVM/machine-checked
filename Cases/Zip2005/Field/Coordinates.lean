/-
  Cases.Zip2005.Coordinates

  `EpAffine::coordinates`: `CtOption { value: (x, y), is_some: ¬(x = 0 ∧ y = 0) }`,
  the flag folded through `subtle::black_box` limb by limb.
-/

import Cases.Zip2005.Field.FpInvert
import Cases.Zip2005.Image.F_78023f64
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- A boolean as the word `0` or `1`. -/
def bw (b : Bool) : Word := if b then 1#64 else 0#64

theorem seqz_bw (x : Word) : (if x.ult 1#64 = true then 1#64 else 0#64) = bw (x == 0#64) := by
  rw [ult_one]; by_cases h : x = 0#64 <;> simp [h, bw]

theorem bb_bw (b : Bool) : BitVec.zeroExtend 64 (BitVec.truncate 8 (bw b)) = bw b := by
  cases b <;> decide

theorem and_bw (a b : Bool) : bw a &&& bw b = bw (a && b) := by
  cases a <;> cases b <;> decide

theorem and255_bw (a : Bool) : bw a &&& 255#64 = bw a := by
  cases a <;> decide

theorem not_bw (a : Bool) :
    BitVec.truncate 8 (BitVec.zeroExtend 64 (BitVec.truncate 8
      ((bw a ^^^ 18446744073709551615#64) &&& 1#64))) = if a then 0#8 else 1#8 := by
  cases a <;> decide

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 10000 in
theorem coordinates_spec {P : Prop} (s : MachineState) (ra a0 a1 sp : Word)
    (x0 x1 x2 x3 y0 y1 y2 y3 : Word) (O : List Word) (hOl : O.length = 9)
    (hpc : s.pc = 0x78023f64#64) (hcode : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x80 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hp : Region a1 [x0, x1, x2, x3, y0, y1, y2, y3] s) (hokp : RegionOk Ro.layout.roBase Ro.layout.textHi a1 8)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 9)
    (hd0 : Disjoint (sp - 0x80#64) 16 a0 9) (hd1 : Disjoint (sp - 0x80#64) 16 a1 8)
    (hd : Disjoint a0 9 a1 8)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x80#64, 16), (a0, 9)] s t →
      Region a0 [x0, x1, x2, x3, y0, y1, y2, y3, replaceByte O[8]! 0
        (if x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧ y0 = 0 ∧ y1 = 0 ∧ y2 = 0 ∧ y3 = 0
          then 0#8 else 1#8)] t →
      Safe P t) :
    Safe P s := by
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x70#64) 14 s
  obtain ⟨FB, hFB, hFBl⟩ := Region.exists_junk (sp - 0x80#64) 2 s
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x80#64) 16 := hstk.frame 16 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x70#64) 14 := hokA.sub' 2 14 (by decide) (by bv_omega)
  have hokFB : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x80#64) 2 := hokA.sub' 0 2 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x80#64, 16), (a0, 9)] s
  have hstkB : StackOk Ro.layout 0x10 (sp - 0x70#64) := by
    obtain ⟨h1, h2, h3⟩ := hstk
    rw [Ro.layout_stackTop] at h3
    have e : (sp - 0x70#64).toNat = sp.toNat - 0x70 := by
      rw [BitVec.toNat_sub, Bn.toNat_ofNat']; omega
    exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, Ro.layout_stackTop]; omega⟩
  sym_exec [black_box_spec]
  sym_close hk
  sym_subst
  simp only [seqz_bw, bb_bw, and255_bw, and_bw, not_bw]
  have e : ((y3 == 0#64 && (y2 == 0#64 && (y1 == 0#64 && y0 == 0#64))) &&
      (x3 == 0#64 && (x2 == 0#64 && (x1 == 0#64 && x0 == 0#64)))) = true ↔
      (x0 = 0 ∧ x1 = 0 ∧ x2 = 0 ∧ x3 = 0 ∧ y0 = 0 ∧ y1 = 0 ∧ y2 = 0 ∧ y3 = 0) := by
    simp only [Bool.and_eq_true, beq_iff_eq]; tauto
  simp only [e]

/-- `coordinates_spec` with the output cells ∀-bound: a caller whose point cells are large
expressions (`Nullifier::derive`: the affine form of a Jacobian sum) gets atoms in its
hypotheses, with one equation each (oriented expression = atom, so the executor's rewriting
folds the expressions into the atoms rather than expanding them), instead of the expressions
themselves inside the `is_some` condition. -/
theorem coordinates_spec' {P : Prop} (s : MachineState) (ra a0 a1 sp : Word)
    (x0 x1 x2 x3 y0 y1 y2 y3 : Word) (O : List Word) (hOl : O.length = 9)
    (hpc : s.pc = 0x78023f64#64) (hcode : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x80 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hp : Region a1 [x0, x1, x2, x3, y0, y1, y2, y3] s) (hokp : RegionOk Ro.layout.roBase Ro.layout.textHi a1 8)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 9)
    (hd0 : Disjoint (sp - 0x80#64) 16 a0 9) (hd1 : Disjoint (sp - 0x80#64) 16 a1 8)
    (hd : Disjoint a0 9 a1 8)
    (hk : ∀ (t : MachineState) (u0 u1 u2 u3 w0 w1 w2 w3 : Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x80#64, 16), (a0, 9)] s t →
      x0 = u0 → x1 = u1 → x2 = u2 → x3 = u3 → y0 = w0 → y1 = w1 → y2 = w2 → y3 = w3 →
      Region a0 [u0, u1, u2, u3, w0, w1, w2, w3, replaceByte O[8]! 0
        (if u0 = 0 ∧ u1 = 0 ∧ u2 = 0 ∧ u3 = 0 ∧ w0 = 0 ∧ w1 = 0 ∧ w2 = 0 ∧ w3 = 0
          then 0#8 else 1#8)] t →
      Safe P t) :
    Safe P s :=
  coordinates_spec s ra a0 a1 sp x0 x1 x2 x3 y0 y1 y2 y3 O hOl hpc hcode hcodeB hcw hra hra1 hsp hstk
    ha0 ha1 hp hokp hO hok0 hd0 hd1 hd
    (fun t h1 h2 h3 h4 hR => hk t x0 x1 x2 x3 y0 y1 y2 y3 h1 h2 h3 h4 rfl rfl rfl rfl rfl rfl rfl rfl hR)

end Cases.Zip2005
