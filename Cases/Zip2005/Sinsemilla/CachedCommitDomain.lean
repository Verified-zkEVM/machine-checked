import Cases.Zip2005.Sinsemilla.SinsemillaCommit
import Cases.Zip2005.Image.F_78020548
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `orchard::spec::cached_commit_domain`

`(out, qx, qy, rx, ry) ↦ out = [Q, R]`: for each of the two generators, `Fp::from_raw` of the
raw `x` and `y` (copied to the frame first), `EpAffine::from_xy` with its `is_some` asserted
(`assert_failed` otherwise, the `hpaf` arm), and `to_curve`. The model `domainPtW` is
`to_curve (from_xy (x·R2, y·R2))`; the continuation also learns `fromXyOk`, the on-curve
condition the assertion established, for both points.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

/-- `Fp::from_raw` of four raw limbs: the Montgomery form `x · R mod p`, as `x · R2` by mulmod. -/
def montW (x : List Word) : List Word := natToLeLimbs 4 (Fp.mul (leLimbsToNat x) Fp.R2)

/-- A domain generator as `cached_commit_domain` builds it: `from_raw` on both coordinates,
`from_xy`, `to_curve` (`Z = R` unless the affine identity). -/
def domainPtW (x y : List Word) : List Word := toCurveW (montW x ++ montW y)

/-- `from_xy`'s `is_some` on the Montgomery coordinates: `y² − x³ = 5·R2` as `from_xy`
computes it (`b` in Montgomery form), or the affine identity `(0, 0)`. -/
def fromXyOk (x y : List Word) : Prop :=
  Fp.sub (Fp.mul (Fp.mul (leLimbsToNat y) Fp.R2) (Fp.mul (leLimbsToNat y) Fp.R2))
      (Fp.mul (Fp.mul (Fp.mul (leLimbsToNat x) Fp.R2) (Fp.mul (leLimbsToNat x) Fp.R2))
        (Fp.mul (leLimbsToNat x) Fp.R2)) = Fp.mul 5 Fp.R2 ∨
    (Fp.mul (leLimbsToNat x) Fp.R2 = 0 ∧ Fp.mul (leLimbsToNat y) Fp.R2 = 0)

theorem montW_eq (x : List Word) : montW x = natToLeLimbs 4 (Fp.mul (leLimbsToNat x) Fp.R2) := rfl

theorem domainPtW_eq (x y : List Word) : domainPtW x y = toCurveW (montW x ++ montW y) := rfl

theorem domainPtW_length (x y : List Word) : (domainPtW x y).length = 12 := by
  simp only [domainPtW_eq, toCurveW_eq, montW_eq, natToLeLimbs_cells4, List.length_append,
    List.length_cons, List.length_nil]

/-- The `is_some` flag `from_xy` returns, read back as `1`, is the on-curve condition on the
Montgomery values (`X`, `Y` the executor's atoms for them). -/
theorem fromXyOk_of_flag {x y : List Word} {X Y : Nat} (hX : Fp.mul (leLimbsToNat x) Fp.R2 = X)
    (hY : Fp.mul (leLimbsToNat y) Fp.R2 = Y)
    (h : BitVec.zeroExtend 64 (if Fp.sub (Fp.mul
        (leLimbsToNat [BitVec.ofNat 64 (Y >>> 0), BitVec.ofNat 64 (Y >>> 64), BitVec.ofNat 64 (Y >>> 128), BitVec.ofNat 64 (Y >>> 192)])
        (leLimbsToNat [BitVec.ofNat 64 (Y >>> 0), BitVec.ofNat 64 (Y >>> 64), BitVec.ofNat 64 (Y >>> 128), BitVec.ofNat 64 (Y >>> 192)]))
        (Fp.mul (Fp.mul
          (leLimbsToNat [BitVec.ofNat 64 (X >>> 0), BitVec.ofNat 64 (X >>> 64), BitVec.ofNat 64 (X >>> 128), BitVec.ofNat 64 (X >>> 192)])
          (leLimbsToNat [BitVec.ofNat 64 (X >>> 0), BitVec.ofNat 64 (X >>> 64), BitVec.ofNat 64 (X >>> 128), BitVec.ofNat 64 (X >>> 192)]))
          (leLimbsToNat [BitVec.ofNat 64 (X >>> 0), BitVec.ofNat 64 (X >>> 64), BitVec.ofNat 64 (X >>> 128), BitVec.ofNat 64 (X >>> 192)])) =
        Fp.mul 5 Fp.R2 ∨
      BitVec.ofNat 64 (X >>> 0) = 0#64 ∧ BitVec.ofNat 64 (X >>> 64) = 0#64 ∧ BitVec.ofNat 64 (X >>> 128) = 0#64 ∧
        BitVec.ofNat 64 (X >>> 192) = 0#64 ∧ BitVec.ofNat 64 (Y >>> 0) = 0#64 ∧ BitVec.ofNat 64 (Y >>> 64) = 0#64 ∧
        BitVec.ofNat 64 (Y >>> 128) = 0#64 ∧ BitVec.ofNat 64 (Y >>> 192) = 0#64 then 1#8 else 0#8) = 1#64) :
    fromXyOk x y := by
  subst hX hY
  unfold fromXyOk
  have hXl := lt_trans (Fp.mul_lt (leLimbsToNat x) Fp.R2) Fp.p_lt
  have hYl := lt_trans (Fp.mul_lt (leLimbsToNat y) Fp.R2) Fp.p_lt
  rw [Nat.shiftRight_zero, Nat.shiftRight_zero, cells4_decode _ hYl, cells4_decode _ hXl] at h
  split at h
  · rename_i hc
    rcases hc with hc | ⟨a1, a2, a3, a4, b1, b2, b3, b4⟩
    · exact Or.inl hc
    · exact Or.inr ⟨(cells4_eq_zero_iff _ hXl).mp ⟨a1, a2, a3, a4⟩,
        (cells4_eq_zero_iff _ hYl).mp ⟨b1, b2, b3, b4⟩⟩
  · exact absurd h (by decide)

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 100000 in
set_option machineChecked.sym.foldBytes true in
theorem cached_commit_domain_spec {Gd : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out qx qy rx ry : Word)
    (x0 x1 x2 x3 y0 y1 y2 y3 u0 u1 u2 u3 w0 w1 w2 w3 : Word) (O : List Word) (hOl : O.length = 24)
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN Gd n P u)
    (hpc : s.pc = 0x78020548#64) (hcode : CodeAt F_78020548.base F_78020548.prog s)
    -- callees: from_raw, from_xy (+ is_on_curve, mulmod, black_box), to_curve
    (hcodeR : CodeAt F_78028298.base F_78028298.prog s) (hcodeXY : CodeAt F_78026878.base F_78026878.prog s)
    (hcodeOC : CodeAt F_78026258.base F_78026258.prog s) (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeBB : CodeAt F_7803a0fc.base F_7803a0fc.prog s) (hcodeTC : CodeAt F_78025854.base F_78025854.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x2a0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = qx) (ha2 : s.getReg .x12 = qy)
    (ha3 : s.getReg .x13 = rx) (ha4 : s.getReg .x14 = ry)
    (hX : Region qx [x0, x1, x2, x3] s) (hokX : RegionOk Ro.layout.textLo Ro.layout.textHi qx 4)
    (hY : Region qy [y0, y1, y2, y3] s) (hokY : RegionOk Ro.layout.textLo Ro.layout.textHi qy 4)
    (hU : Region rx [u0, u1, u2, u3] s) (hokU : RegionOk Ro.layout.textLo Ro.layout.textHi rx 4)
    (hW : Region ry [w0, w1, w2, w3] s) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi ry 4)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 24)
    (hout : out.toNat + 8 * 24 ≤ 0x78040620)
    (hd0 : Disjoint (sp - 0x2a0#64) 84 out 24) (hd1 : Disjoint (sp - 0x2a0#64) 84 qx 4)
    (hd2 : Disjoint (sp - 0x2a0#64) 84 qy 4) (hd3 : Disjoint (sp - 0x2a0#64) 84 rx 4)
    (hd4 : Disjoint (sp - 0x2a0#64) 84 ry 4)
    (he1 : Disjoint out 24 qx 4) (he2 : Disjoint out 24 qy 4) (he3 : Disjoint out 24 rx 4)
    (he4 : Disjoint out 24 ry 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x2a0#64, 84), (out, 24)] s t →
      Region out (domainPtW [x0, x1, x2, x3] [y0, y1, y2, y3]) t →
      Region (out + 0x60#64) (domainPtW [u0, u1, u2, u3] [w0, w1, w2, w3]) t →
      fromXyOk [x0, x1, x2, x3] [y0, y1, y2, y3] → fromXyOk [u0, u1, u2, u3] [w0, w1, w2, w3] →
      SafeN Gd n P t) :
    SafeN Gd n P s := by
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x2a0#64) 84 := hstk.frame 84 (by decide)
  -- the frame (below it 0x170 bytes for `from_xy`): the two raw copies, the affine point,
  -- `from_xy`'s output, `from_raw`'s first output, the flag byte's cell, the save area
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x2a0#64 + 0x170#64) 4 := hokF.sub' 46 4 (by decide) (by bv_omega)
  have hokB : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x2a0#64 + 0x190#64) 4 := hokF.sub' 50 4 (by decide) (by bv_omega)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x2a0#64 + 0x1b0#64) 8 := hokF.sub' 54 8 (by decide) (by bv_omega)
  have hokD : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x2a0#64 + 0x1f0#64) 9 := hokF.sub' 62 9 (by decide) (by bv_omega)
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x2a0#64 + 0x238#64) 4 := hokF.sub' 71 4 (by decide) (by bv_omega)
  have hokG : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x2a0#64 + 0x258#64) 1 := hokF.sub' 75 1 (by decide) (by bv_omega)
  have hokH : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x2a0#64 + 0x260#64) 8 := hokF.sub' 76 8 (by decide) (by bv_omega)
  obtain ⟨A, hA, hAl⟩ := Region.exists_junk (sp - 0x2a0#64 + 0x170#64) 4 s
  obtain ⟨B, hB, hBl⟩ := Region.exists_junk (sp - 0x2a0#64 + 0x190#64) 4 s
  obtain ⟨C, hC, hCl⟩ := Region.exists_junk (sp - 0x2a0#64 + 0x1b0#64) 8 s
  obtain ⟨D, hD, hDl⟩ := Region.exists_junk (sp - 0x2a0#64 + 0x1f0#64) 9 s
  obtain ⟨E, hE, hEl⟩ := Region.exists_junk (sp - 0x2a0#64 + 0x238#64) 4 s
  obtain ⟨G, hG, hGl⟩ := Region.exists_junk (sp - 0x2a0#64 + 0x258#64) 1 s
  obtain ⟨H, hH, hHl⟩ := Region.exists_junk (sp - 0x2a0#64 + 0x260#64) 8 s
  have hlo := hstk.lo
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hu := Unchanged.refl [(sp - 0x2a0#64, 84), (out, 24)] s
  sym_exec [fp_from_raw_spec, from_xy_spec, to_curve_spec, hpaf]
  -- the two assertions passed: both points are on the curve (or the identity)
  have hxyQ : fromXyOk [x0, x1, x2, x3] [y0, y1, y2, y3] :=
    fromXyOk_of_flag acc34_0_def acc39_0_def (v49_def.trans (by simpa using hbr54))
  have hxyR : fromXyOk [u0, u1, u2, u3] [w0, w1, w2, w3] :=
    fromXyOk_of_flag acc98_0_def acc103_0_def (v110_def.trans (by simpa using hbr114))
  -- the output in the model's shape
  have hRo : Region out (domainPtW [x0, x1, x2, x3] [y0, y1, y2, y3] ++
      domainPtW [u0, u1, u2, u3] [w0, w1, w2, w3]) s_146 := by
    rw [domainPtW_eq, domainPtW_eq, montW_eq, montW_eq, montW_eq, montW_eq, acc34_0_def, acc39_0_def,
      acc98_0_def, acc103_0_def, ← MachineChecked.RiscV.Sym.cells4', ← MachineChecked.RiscV.Sym.cells4', ← MachineChecked.RiscV.Sym.cells4', ← MachineChecked.RiscV.Sym.cells4']
    simp only [Nat.reduceMul, List.cons_append, List.nil_append]
    rw [v63_def, v64_def, v65_def, v66_def, v55_def, v56_def, v57_def, v58_def, v123_def, v124_def,
      v125_def, v126_def, v115_def, v116_def, v117_def, v118_def, toCurveW_eq, toCurveW_eq,
      ← MachineChecked.RiscV.Sym.cells4', ← MachineChecked.RiscV.Sym.cells4']
    simp only [list8_get_0, list8_get_1, list8_get_2, list8_get_3, list8_get_4, list8_get_5,
      list8_get_6, list8_get_7, List.cons_append, List.nil_append]
    exact hR4
  have hQl := domainPtW_length [x0, x1, x2, x3] [y0, y1, y2, y3]
  have hRl := domainPtW_length [u0, u1, u2, u3] [w0, w1, w2, w3]
  have hRoQ : Region out (domainPtW [x0, x1, x2, x3] [y0, y1, y2, y3]) s_146 :=
    hRo.sub 0 12 (by simp) (by rw [List.drop_zero, List.take_left' hQl])
  have hRoR : Region (out + 0x60#64) (domainPtW [u0, u1, u2, u3] [w0, w1, w2, w3]) s_146 :=
    hRo.sub 12 12 rfl (by rw [List.drop_left' hQl, List.take_of_length_le (le_of_eq hRl)])
  sym_close hk

end Cases.Zip2005
