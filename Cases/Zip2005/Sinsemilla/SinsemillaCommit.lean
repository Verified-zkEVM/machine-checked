import Cases.Zip2005.Orchard.NullifierDerive
import Cases.Zip2005.Sinsemilla.SinsemillaLoop
import Cases.Zip2005.Sinsemilla.SinsemillaPack
import Cases.Zip2005.Sinsemilla.SinsemillaUnpack
import Cases.Zip2005.Sinsemilla.IncompleteFrom
import Cases.Zip2005.Sinsemilla.IncompleteBottom
import Cases.Zip2005.Curve.CondSelect
import Cases.Zip2005.Sinsemilla.SinsemillaBlinding
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Runtime.MemsetSpec
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Sinsemilla.NoteBits
import Cases.Zip2005.Image.F_78020d50
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `sinsemilla::CommitDomain::commit` (`0x78020d50`)

`SinsemillaCommit_r(M) = SinsemillaHashToPoint(M) + [r] R`: the message iterator collected into
a `Vec<bool>` (`from_iter`, a contract hypothesis, discharged at the call sites by
`from_iter_nc_contract`: it yields the 1090 message bytes `Bv`), `Q` to affine and packed (`to_affine`, `coordinates` with its `is_some` assertion, `pack`),
the chunk loop (`Cases.Zip2005.sinsemilla_loop`), then `⊥` (`bottom`) or `unpack` / `from_xy` (asserted
`is_some`) / `to_curve` / `Ep::from`, the `Vec` freed (`__rust_dealloc`, a contract), the point
or the identity selected by the `is_some` flag (`conditional_select`), `[r] R` (`blinding`) and
the sum (`Ep::add`), the flag byte written last.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-! ## The model -/

/-- The affine `y` of a Jacobian triple (see `affineX`). -/
def affineY (A : Nat × Nat × Nat) : Nat := (Fp.toAffine A.1 A.2.1 A.2.2).2

theorem affineY_eq (A : Nat × Nat × Nat) : affineY A = (Fp.toAffine A.1 A.2.1 A.2.2).2 := rfl

theorem affineY_cells' (A : Nat × Nat × Nat) : (Fp.toAffine A.1 A.2.1 A.2.2).2 = affineY A := rfl

/-- `Q` packed: its affine coordinates taken out of Montgomery form (`pack`). -/
def commitAcc0 (Q : List Word) : List Word :=
  natToLeLimbs 4 (affineX (ptX Q, ptY Q, ptZ Q) * Fp.rInv % Fp.p) ++
    natToLeLimbs 4 (affineY (ptX Q, ptY Q, ptZ Q) * Fp.rInv % Fp.p)

/-- The chunk fold over the 109 chunks of the message bytes `Bv`. -/
def commitFold (Q Bv : List Word) : Option (List Word) :=
  sinFold sTable (some (commitAcc0 Q)) (chunks Bv 109)

/-- `to_curve` of an affine point held as Montgomery limbs: `Z = R`, or `0` for the identity. -/
def toCurveW (xy : List Word) : List Word :=
  xy ++ natToLeLimbs 4 (if xy[0]! = 0#64 ∧ xy[1]! = 0#64 ∧ xy[2]! = 0#64 ∧ xy[3]! = 0#64 ∧
    xy[4]! = 0#64 ∧ xy[5]! = 0#64 ∧ xy[6]! = 0#64 ∧ xy[7]! = 0#64 then 0 else Fp.R)

/-- `unpack` of the accumulator's canonical limbs: back into Montgomery form. -/
def unpackW (L : List Word) : List Word :=
  natToLeLimbs 4 (Fp.mul (leLimbsToNat [L[0]!, L[1]!, L[2]!, L[3]!]) Fp.R2) ++
    natToLeLimbs 4 (Fp.mul (leLimbsToNat [L[4]!, L[5]!, L[6]!, L[7]!]) Fp.R2)

/-- The hash point as the guest holds it: the identity for `⊥`, else the accumulator unpacked
and lifted to the curve. -/
def commitHash (Q Bv : List Word) : List Word :=
  (commitFold Q Bv).elim [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] (fun L => toCurveW (unpackW L))

/-- `is_some` of the hash. -/
def commitFlag (Q Bv : List Word) : BitVec 8 := if (commitFold Q Bv).isSome then 1#8 else 0#8

def jX (A : Nat × Nat × Nat) : Nat := A.1
def jY (A : Nat × Nat × Nat) : Nat := A.2.1
def jZ (A : Nat × Nat × Nat) : Nat := A.2.2

theorem jX_eq (A : Nat × Nat × Nat) : jX A = A.1 := rfl
theorem jY_eq (A : Nat × Nat × Nat) : jY A = A.2.1 := rfl
theorem jZ_eq (A : Nat × Nat × Nat) : jZ A = A.2.2 := rfl

/-- The commitment in Jacobian coordinates: the hash point plus `[r] R`. -/
def commitJ (Q R Bv k : List Word) : Nat × Nat × Nat :=
  Fp.addJ (ptX (commitHash Q Bv)) (ptY (commitHash Q Bv)) (ptZ (commitHash Q Bv))
    (ptX (mulW R k)) (ptY (mulW R k)) (ptZ (mulW R k))

theorem commitJ_eq (Q R Bv k : List Word) : commitJ Q R Bv k =
    Fp.addJ (ptX (commitHash Q Bv)) (ptY (commitHash Q Bv)) (ptZ (commitHash Q Bv))
      (ptX (mulW R k)) (ptY (mulW R k)) (ptZ (mulW R k)) := rfl

/-- The commitment's twelve limbs. -/
def commitW (Q R Bv k : List Word) : List Word :=
  natToLeLimbs 4 (jX (commitJ Q R Bv k)) ++ natToLeLimbs 4 (jY (commitJ Q R Bv k)) ++
    natToLeLimbs 4 (jZ (commitJ Q R Bv k))

theorem affineX_mk (x y z : Nat) : (Fp.toAffine x y z).1 = affineX (x, y, z) := rfl
theorem affineY_mk (x y z : Nat) : (Fp.toAffine x y z).2 = affineY (x, y, z) := rfl

theorem ptX_zero : ptX [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] = leLimbsToNat [0#64, 0#64, 0#64, 0#64] := rfl
theorem ptY_zero : ptY [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] = leLimbsToNat [0#64, 0#64, 0#64, 0#64] := rfl
theorem ptZ_zero : ptZ [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] = leLimbsToNat [0#64, 0#64, 0#64, 0#64] := rfl

theorem commitAcc0_eq (Q : List Word) : commitAcc0 Q =
    natToLeLimbs 4 (affineX (ptX Q, ptY Q, ptZ Q) * Fp.rInv % Fp.p) ++
      natToLeLimbs 4 (affineY (ptX Q, ptY Q, ptZ Q) * Fp.rInv % Fp.p) := rfl

theorem commitFold_eq (Q Bv : List Word) :
    commitFold Q Bv = sinFold sTable (some (commitAcc0 Q)) (chunks Bv 109) := rfl

theorem commitHash_none {Q Bv : List Word} (h : commitFold Q Bv = none) :
    commitHash Q Bv = [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] := by
  rw [commitHash, h]; rfl

theorem commitHash_some {Q Bv L : List Word} (h : commitFold Q Bv = some L) :
    commitHash Q Bv = toCurveW (unpackW L) := by
  rw [commitHash, h]; rfl

theorem commitFlag_none {Q Bv : List Word} (h : commitFold Q Bv = none) : commitFlag Q Bv = 0#8 := by
  rw [commitFlag, h]; rfl

theorem commitFlag_some {Q Bv L : List Word} (h : commitFold Q Bv = some L) : commitFlag Q Bv = 1#8 := by
  rw [commitFlag, h]; rfl

theorem commitW_eq (Q R Bv k : List Word) : commitW Q R Bv k =
    natToLeLimbs 4 (jX (commitJ Q R Bv k)) ++ natToLeLimbs 4 (jY (commitJ Q R Bv k)) ++
      natToLeLimbs 4 (jZ (commitJ Q R Bv k)) := rfl

theorem toCurveW_eq (xy : List Word) : toCurveW xy =
    xy ++ natToLeLimbs 4 (if xy[0]! = 0#64 ∧ xy[1]! = 0#64 ∧ xy[2]! = 0#64 ∧ xy[3]! = 0#64 ∧
      xy[4]! = 0#64 ∧ xy[5]! = 0#64 ∧ xy[6]! = 0#64 ∧ xy[7]! = 0#64 then 0 else Fp.R) := rfl

theorem unpackW_eq (L : List Word) : unpackW L =
    natToLeLimbs 4 (Fp.mul (leLimbsToNat [L[0]!, L[1]!, L[2]!, L[3]!]) Fp.R2) ++
      natToLeLimbs 4 (Fp.mul (leLimbsToNat [L[4]!, L[5]!, L[6]!, L[7]!]) Fp.R2) := rfl

@[simp] theorem commitW_length (Q R Bv k : List Word) : (commitW Q R Bv k).length = 12 := by
  simp only [commitW_eq, List.length_append, length_natToLeLimbs]

/-- The models depend on the message through its first 109 chunks only. -/
theorem commitFold_congr {Q A B : List Word} (h : chunks A 109 = chunks B 109) :
    commitFold Q A = commitFold Q B := by
  unfold commitFold; rw [h]

theorem commitHash_congr {Q A B : List Word} (h : chunks A 109 = chunks B 109) :
    commitHash Q A = commitHash Q B := by
  unfold commitHash; rw [commitFold_congr h]

theorem commitFlag_congr {Q A B : List Word} (h : chunks A 109 = chunks B 109) :
    commitFlag Q A = commitFlag Q B := by
  unfold commitFlag; rw [commitFold_congr h]

theorem commitW_congr {Q R A B k : List Word} (h : chunks A 109 = chunks B 109) :
    commitW Q R A k = commitW Q R B k := by
  unfold commitW commitJ; rw [commitHash_congr h]

theorem list8_get_0 (x0 x1 x2 x3 x4 x5 x6 x7 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7][0]! = x0 := rfl
theorem list8_get_1 (x0 x1 x2 x3 x4 x5 x6 x7 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7][1]! = x1 := rfl
theorem list8_get_2 (x0 x1 x2 x3 x4 x5 x6 x7 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7][2]! = x2 := rfl
theorem list8_get_3 (x0 x1 x2 x3 x4 x5 x6 x7 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7][3]! = x3 := rfl
theorem list8_get_4 (x0 x1 x2 x3 x4 x5 x6 x7 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7][4]! = x4 := rfl
theorem list8_get_5 (x0 x1 x2 x3 x4 x5 x6 x7 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7][5]! = x5 := rfl
theorem list8_get_6 (x0 x1 x2 x3 x4 x5 x6 x7 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7][6]! = x6 := rfl
theorem list8_get_7 (x0 x1 x2 x3 x4 x5 x6 x7 : Word) : [x0, x1, x2, x3, x4, x5, x6, x7][7]! = x7 := rfl

/-! ## The loop lemma as a specification at the loop head -/

/-- `Cases.Zip2005.sinsemilla_loop` for the whole message (109 chunks from the first) in the shape the
executor applies: the counter and pointer registers as values, the accumulator's nine cells
explicit, the table the read-only one. -/
theorem sinsemilla_loop_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (t : MachineState) (sp bp : Word) (Bv : List Word)
    (hBl : Bv.length = 137)
    (hbool : ∀ o, o < 1090 → byteAt Bv o = 0#64 ∨ byteAt Bv o = 1#64)
    (g3 g4 g8 g9 g18 a1 a2 a3 a4 a5 a6 a7 a8 : Word) (A C D E F : List Word)
    (hAl : A.length = 9) (hCl : C.length = 4) (hDl : D.length = 4) (hEl : E.length = 9)
    (hFl : F.length = 9)
    (hbounds : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = t.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n P u)
    (hunwrap : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dc7c#64 → u.code = t.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_dc7c_10 → u.getReg .x13 ∈ Run.vals_dc7c_13 → u.getReg .x14 ∈ Run.vals_dc7c_14 → SafeN G n P u)
    (hpc : t.pc = 0x78020e74#64)
    (hcodeC : CodeAt F_78020d50.base F_78020d50.prog t)
    (hcodeL : CodeAt F_780234cc.base F_780234cc.prog t)
    (hcodeP : CodeAt F_780237dc.base F_780237dc.prog t)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog t)
    (hcodeI : CodeAt F_780235e8.base F_780235e8.prog t)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog t)
    (hcodeAA : CodeAt F_78035f88.base F_78035f88.prog t)
    (hcodeLR : CodeAt F_780360e0.base F_780360e0.prog t)
    (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog t)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog t)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi t) (hro : RoImage Ro.layout t) (hheap : Run.HeapAt L t)
    (hsp : t.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x130 sp) (hhi : sp.toNat + 0x3c0 ≤ 0x78000000)
    (h3 : t.getReg .x3 = g3) (h4 : t.getReg .x4 = g4) (h8 : t.getReg .x8 = g8)
    (h9 : t.getReg .x9 = g9) (h18 : t.getReg .x18 = g18)
    (h19 : t.getReg .x19 = sp + 0x198#64) (h20 : t.getReg .x20 = sp + 0x2a0#64)
    (h21 : t.getReg .x21 = 1090#64) (h22 : t.getReg .x22 = bp)
    (h23 : t.getReg .x23 = 9#64) (h24 : t.getReg .x24 = 0x3ff#64)
    (h25 : t.getReg .x25 = 0x78001968#64) (h26 : t.getReg .x26 = 1#64)
    (hT : Region 0x78001968#64 sTable t) (hokT : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001968#64 8192)
    (hB : Region bp Bv t) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi bp 137)
    (hA : Region sp A t) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi sp 9)
    (hacc0 : Region (sp + 0x190#64) [1#64] t)
    (hacc1 : Region (sp + 0x198#64) [a1, a2, a3, a4, a5, a6, a7, a8] t)
    (hokacc : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x190#64) 9)
    (hC : Region (sp + 0x1d8#64) C t) (hokC : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x1d8#64) 4)
    (hD : Region (sp + 0x258#64) D t) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x258#64) 4)
    (hE : Region (sp + 0x298#64) E t) (hokE : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x298#64) 9)
    (hF : Region (sp + 0x2f8#64) F t) (hokF : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x2f8#64) 9)
    (hdB : Disjoint bp 137 (sp - 0x130#64) 142)
    (hk : ∀ (u : MachineState) (acc' : List Word), u.pc = 0x78020fbc#64 → u.code = t.code →
      u.getReg .x2 = sp → u.getReg .x3 = g3 → u.getReg .x4 = g4 → u.getReg .x8 = g8 →
      u.getReg .x9 = g9 → u.getReg .x18 = g18 → u.getReg .x19 = sp + 0x198#64 →
      Unchanged [(sp - 0x130#64, 38), (sp, 9), (sp + 0x190#64, 9), (sp + 0x1d8#64, 4),
        (sp + 0x258#64, 4), (sp + 0x298#64, 9), (sp + 0x2f8#64, 9)] t u →
      acc'.length = 9 → Region (sp + 0x190#64) acc' u →
      AccRep (sinFold sTable (some [a1, a2, a3, a4, a5, a6, a7, a8]) (chunks Bv 109)) acc' → Run.HeapAt L u →
      SafeN G n P u) :
    SafeN G n P t := by
  have hacc : Region (sp + 0x190#64) [1#64, a1, a2, a3, a4, a5, a6, a7, a8] t := by
    have h := Region.append hacc0 (by simpa [BitVec.add_assoc] using hacc1)
    simpa using h
  have hrep : AccRep (sinFold sTable (some [a1, a2, a3, a4, a5, a6, a7, a8]) (chunks Bv 0))
      [1#64, a1, a2, a3, a4, a5, a6, a7, a8] := by
    refine ⟨rfl, ?_, ?_⟩
    · simp only [chunks, List.range_zero, List.map_nil, sinFold, List.foldl_nil,
        List.getElem!_cons_zero, reduceCtorEq, iff_false]
      decide
    · intro L hL
      simp only [chunks, List.range_zero, List.map_nil, sinFold, List.foldl_nil,
        Option.some.injEq] at hL
      rw [hL]
  exact sinsemilla_loop sp bp sTable Bv 109 t.code g3 g4 g8 g9 g18 [a1, a2, a3, a4, a5, a6, a7, a8]
    hbounds hunwrap sTable_length hBl (by decide) hbool 109 0 t
    [1#64, a1, a2, a3, a4, a5, a6, a7, a8] 1090#64 bp (by omega) (by omega) hrep hpc rfl hcodeC hcodeL hcodeP
    hcodeT hcodeI hcodeCmp hcodeAA hcodeLR hcodeAdd hcodeM hcw hro hheap hsp hstk hhi h3 h4 h8 h9 h18
    h19 h20 h21 rfl h22 (by simp) h23 h24 h25 h26 hT hokT hB hokB ⟨A, hAl, hA⟩ hokA hacc hokacc
    ⟨C, hCl, hC⟩ hokC ⟨D, hDl, hD⟩ hokD ⟨E, hEl, hE⟩ hokE ⟨F, hFl, hF⟩ hokF hdB
    (fun u acc' hpc hc h2 h3 h4 h8 h9 h18 h19 hun hR hrep hH =>
      hk u acc' hpc hc h2 h3 h4 h8 h9 h18 h19 hun hrep.1 hR hrep hH)

/-! ## `conditional_select` with a literal choice -/

theorem conditional_select_spec_one {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 a2 : Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : Word)
    (O : List Word) (hOl : O.length = 12)
    (hpc : s.pc = 0x78023d7c#64) (hcode : CodeAt F_78023d7c.base F_78023d7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x20 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1) (ha2 : s.getReg .x12 = a2)
    (ha3 : s.getReg .x13 = 1#64)
    (hA : Region a1 [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11] s)
    (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hB : Region a2 [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11] s)
    (hok2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 12)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 12)
    (hd0 : Disjoint (sp - 0x20#64) 4 a0 12) (hd1 : Disjoint (sp - 0x20#64) 4 a1 12)
    (hd2 : Disjoint (sp - 0x20#64) 4 a2 12)
    (he1 : Disjoint a0 12 a1 12) (he2 : Disjoint a0 12 a2 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x20#64, 4), (a0, 12)] s t →
      Region a0 [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11] t → SafeN G n P t) :
    SafeN G n P s :=
  conditional_select_spec s ra sp a0 a1 a2 true p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11
    q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 O hOl hpc hcode hcw hra hra1 hsp hstk ha0 ha1 ha2 ha3
    hA hok1 hB hok2 hO hok0 hd0 hd1 hd2 he1 he2 hk

theorem conditional_select_spec_zero {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 a2 : Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : Word)
    (O : List Word) (hOl : O.length = 12)
    (hpc : s.pc = 0x78023d7c#64) (hcode : CodeAt F_78023d7c.base F_78023d7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x20 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1) (ha2 : s.getReg .x12 = a2)
    (ha3 : s.getReg .x13 = 0#64)
    (hA : Region a1 [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11] s)
    (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hB : Region a2 [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11] s)
    (hok2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 12)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 12)
    (hd0 : Disjoint (sp - 0x20#64) 4 a0 12) (hd1 : Disjoint (sp - 0x20#64) 4 a1 12)
    (hd2 : Disjoint (sp - 0x20#64) 4 a2 12)
    (he1 : Disjoint a0 12 a1 12) (he2 : Disjoint a0 12 a2 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x20#64, 4), (a0, 12)] s t →
      Region a0 [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11] t → SafeN G n P t) :
    SafeN G n P s :=
  conditional_select_spec s ra sp a0 a1 a2 false p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11
    q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 O hOl hpc hcode hcw hra hra1 hsp hstk ha0 ha1 ha2 ha3
    hA hok1 hB hok2 hO hok0 hd0 hd1 hd2 he1 he2 hk

/-! ## Cells of a canonical value -/

theorem mcells_lt (M : Nat) (h : M < Fp.p) :
    leLimbsToNat [BitVec.ofNat 64 (M >>> 0), BitVec.ofNat 64 (M >>> 64), BitVec.ofNat 64 (M >>> 128),
      BitVec.ofNat 64 (M >>> 192)] < Fp.p := by
  rw [Nat.shiftRight_zero, cells4_decode _ (lt_trans h Fp.p_lt)]; exact h

theorem ite_lt_p (c : Prop) [Decidable c] : (if c then 0 else Fp.R) < Fp.p := by
  split
  · exact Fp.p_pos
  · exact Fp.R_lt

theorem zcells_lt' (C : Nat) (h : C < Fp.p) :
    leLimbsToNat [BitVec.ofNat 64 (C >>> (64 * 0)), BitVec.ofNat 64 (C >>> (64 * 1)),
      BitVec.ofNat 64 (C >>> (64 * 2)), BitVec.ofNat 64 (C >>> (64 * 3))] < Fp.p := by
  rw [MachineChecked.RiscV.Sym.cells4', leLimbsToNat_natToLeLimbs 4 _ (lt_trans h Fp.p_lt)]; exact h

theorem zcells_lt (C : Nat) (h : C < Fp.p) :
    leLimbsToNat [BitVec.ofNat 64 C, BitVec.ofNat 64 (C >>> 64), BitVec.ofNat 64 (C >>> 128),
      BitVec.ofNat 64 (C >>> 192)] < Fp.p := by
  rw [cells4_decode _ (lt_trans h Fp.p_lt)]; exact h

/-! ## Callee outputs as literal lists -/

theorem memset96_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra a0 : Word) (O : List Word)
    (hOl : O.length = 12)
    (hpc : s.pc = 0x7803f57c#64) (hcode : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = 0#64) (ha2 : s.getReg .x12 = 96#64)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi a0 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(a0, 12)] s t →
      Region a0 [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] t →
      SafeN G n P t) :
    SafeN G n P s :=
  memset96_spec s ra a0 O hOl hpc hcode hcw hra hra1 ha0 ha1 ha2 hO hok0 hk

theorem incomplete_bottom_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 : Word)
    (o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 : Word)
    (hpc : s.pc = 0x78023544#64) (hcode : CodeAt F_78023544.base F_78023544.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeMS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x30 sp)
    (ha0 : s.getReg .x10 = a0)
    (hO : Region a0 [o0, o1, o2, o3, o4, o5, o6, o7, o8, o9, o10, o11, o12] s)
    (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 13)
    (hd0 : Disjoint (sp - 0x30#64) 6 a0 13)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x30#64, 6), (a0, 13)] s t →
      Region a0 [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64,
        replaceByte o12 0 0#8] t → SafeN G n P t) :
    SafeN G n P s :=
  incomplete_bottom_spec s ra sp a0 o0 o1 o2 o3 o4 o5 o6 o7 o8 o9 o10 o11 o12 hpc hcode hcodeB
    hcodeMS hcw hra hra1 hsp hstk ha0 hO hok0 hd0 hk

/-! ## The specification -/

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
set_option machineChecked.sym.foldBytes true in
/-- `CommitDomain::commit(out, domain, iter, r)`: `domain` holds `Q` and, at `+0x60`, `R`
(Jacobian Montgomery limbs); `iter` the 120-byte padded-bit iterator; `r` the blinding scalar
(`Fq`, Montgomery). `from_iter` is a contract (`hfrom`): it collects the iterator into the
1090 message bytes `Bv` (a `Vec<bool>`, a byte per bit), with `__rust_dealloc` (`hdealloc`)
freeing it. The result is `commitW` with the `is_some` flag byte. -/
theorem sinsemilla_commit_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out dom iter r : Word)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : Word)
    (k0 k1 k2 k3 : Word) (I : List Word) (hIl : I.length = 15)
    (bit : Nat → Bool) (M : Word) (Mw O : List Word) (hMl : Mw.length = 17) (hOl : O.length = 13)
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN G n P u)
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (hunwrap : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dc7c#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_dc7c_10 → u.getReg .x13 ∈ Run.vals_dc7c_13 → u.getReg .x14 ∈ Run.vals_dc7c_14 → SafeN G n P u)
    (hbounds : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n P u)
    (hpc : s.pc = 0x78020d50#64) (hcode : CodeAt F_78020d50.base F_78020d50.prog s)
    -- callees: memcpy, to_affine (+ invert, mulmod, black_box), coordinates, pack (+ to_repr),
    -- lebs2ip_k, incomplete_add and its callees, unpack (+ from_repr), from_xy (+ is_on_curve,
    -- from_raw), to_curve, from, bottom, memset, conditional_select, blinding and its callees,
    -- Ep::add (+ double)
    (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s) (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeBB : CodeAt F_7803a0fc.base F_7803a0fc.prog s) (hcodeCo : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeP : CodeAt F_780237dc.base F_780237dc.prog s) (hcodeRp : CodeAt F_78029468.base F_78029468.prog s)
    (hcodeL : CodeAt F_780234cc.base F_780234cc.prog s) (hcodeIA : CodeAt F_780235e8.base F_780235e8.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s) (hcodeAA : CodeAt F_78035f88.base F_78035f88.prog s)
    (hcodeLR : CodeAt F_780360e0.base F_780360e0.prog s) (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcodeU : CodeAt F_78023864.base F_78023864.prog s) (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeXY : CodeAt F_78026878.base F_78026878.prog s) (hcodeOC : CodeAt F_78026258.base F_78026258.prog s)
    (hcodeFR : CodeAt F_78028298.base F_78028298.prog s) (hcodeTC : CodeAt F_78025854.base F_78025854.prog s)
    (hcodeF : CodeAt F_780239bc.base F_780239bc.prog s) (hcodeBt : CodeAt F_78023544.base F_78023544.prog s)
    (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcodeCS : CodeAt F_78023d7c.base F_78023d7c.prog s)
    (hcodeB : CodeAt F_78023594.base F_78023594.prog s) (hcodeW : CodeAt F_7802827c.base F_7802827c.prog s)
    (hcodeMul : CodeAt F_78031be8.base F_78031be8.prog s) (hcodeRq : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    (hcodeA : CodeAt F_78035fe0.base F_78035fe0.prog s) (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcodeD : CodeAt F_780360c8.base F_780360c8.prog s) (hcodeAF : CodeAt F_7803a110.base F_7803a110.prog s)
    (hcodeAFI : CodeAt F_7803dd28.base F_7803dd28.prog s) (hcodeEA : CodeAt F_78026b44.base F_78026b44.prog s)
    (hcodeED : CodeAt F_7802413c.base F_7802413c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x8e0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = dom) (ha2 : s.getReg .x12 = iter)
    (ha3 : s.getReg .x13 = r)
    (hQ : Region dom [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] s)
    (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi dom 12)
    (hR : Region (dom + 0x60#64) [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] s)
    (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi (dom + 0x60#64) 12)
    (hI : Region iter I s)
    (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi iter 15)
    (hK : Region r [k0, k1, k2, k3] s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi r 4)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 13)
    (hd0 : Disjoint (sp - 0x8e0#64) 284 dom 12) (hd1 : Disjoint (sp - 0x8e0#64) 284 (dom + 0x60#64) 12)
    (hd2 : Disjoint (sp - 0x8e0#64) 284 iter 15) (hd3 : Disjoint (sp - 0x8e0#64) 284 r 4)
    (hd4 : Disjoint (sp - 0x8e0#64) 284 out 13)
    (he0 : Disjoint out 13 dom 12) (he1 : Disjoint out 13 (dom + 0x60#64) 12)
    (he2 : Disjoint out 13 iter 15) (he3 : Disjoint out 13 r 4)
    (hh0 : Disjoint 0x78040620#64 14780694332 dom 12)
    (hh1 : Disjoint 0x78040620#64 14780694332 (dom + 0x60#64) 12)
    (hh2 : Disjoint 0x78040620#64 14780694332 iter 15)
    (hh3 : Disjoint 0x78040620#64 14780694332 r 4)
    (hh4 : Disjoint 0x78040620#64 14780694332 out 13)
    -- the words the iterator points to (the caller's message), read by `from_iter` only
    (hM : Region M Mw s) (hokM : RegionOk Ro.layout.textLo Ro.layout.textHi M 17)
    -- what `from_iter` needs of the caller's frame, which holds `M` (`StackOk Ro.layout` of it at `derive`)
    (Mok : Prop) (hMok : Mok)
    (hdM : Disjoint (sp - 0x8e0#64) 284 M 17) (heM : Disjoint out 13 M 17)
    (hhM : Disjoint 0x78040620#64 14780694332 M 17)
    -- `from_iter` (ledger T2): the iterator (its state `[0, _, iter…, 0]`) collected into the
    -- 1090 message bytes, a `Vec` of some non-zero capacity on the heap
    (hfrom : ∀ (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word) (L' : List (Word × Nat)), O1.length = 3 →
      u.pc = 0x7801dfb4#64 → u.code = s.code → u.getReg .x1 = 0x78020dc4#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x260 sp' → u.getReg .x10 = a0' → u.getReg .x11 = a1' →
      Region a0' O1 u → Region a1' [0#64, j] u →
      Region (a1' + 0x10#64) I u →
      Region (a1' + 0x88#64) [0#64] u → Region M Mw u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 3 → RegionOk Ro.layout.roBase Ro.layout.textHi a1' 18 →
      Disjoint (sp' - 0x260#64) 76 a0' 3 → Disjoint (sp' - 0x260#64) 76 a1' 18 →
      Disjoint a0' 3 a1' 18 →
      Mok →
      Disjoint (sp' - 0x260#64) 76 M 17 → Disjoint a0' 3 M 17 → Disjoint a1' 18 M 17 →
      Disjoint 0x78040620#64 14780694332 a0' 3 → Disjoint 0x78040620#64 14780694332 a1' 18 →
      a0'.toNat + 8 * 3 ≤ 0x78040620 → a1'.toNat + 8 * 18 ≤ 0x78040620 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (cap ptr : Word) (J Bv : List Word), t.pc = 0x78020dc4#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x260#64, 76), (a0', 3), (a1', 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        J.length = 18 → Region a0' [cap, ptr, 1090#64] t → cap ≠ 0#64 → Region a1' J t →
        Bv.length = 137 → (∀ o, o < 1090 → byteAt Bv o = bw (bit o)) →
        Region ptr Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 137 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 137 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 256) :: L') t → SafeN G n P t) → SafeN G n P u)
    -- `__rust_dealloc` of that `Vec` (ledger T2)
    (hdealloc : ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word) (k : Nat) (L' : List (Word × Nat)), C.length = 137 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780210f0#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap →
      u.getReg .x12 = 1#64 → Region ptr C u → 0x78048980 ≤ ptr.toNat →
      ptr.toNat + 8 * 137 ≤ 0x1c00000000 →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = 0x780210f0#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x8e0#64, 284), (out, 13), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (commitW [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]
        [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] (boolBytesToWords bit 137) [k0, k1, k2, k3]) t →
      Region (out + 0x60#64) [replaceByte O[12]! 0 (commitFlag [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]
          (boolBytesToWords bit 137))] t →
      mulFacts [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] [k0, k1, k2, k3] → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64) 284 := hstk.frame 284 (by decide)
  -- the frame (below it 0x520 bytes for the callees' frames)
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64 + 0x520#64) 13 := hokW.sub' 164 13 (by decide) (by bv_omega)
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64 + 0x588#64) 3 := hokW.sub' 177 3 (by decide) (by bv_omega)
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64 + 0x5a0#64) 18 := hokW.sub' 180 18 (by decide) (by bv_omega)
  have hok5 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64 + 0x630#64) 8 := hokW.sub' 198 8 (by decide) (by bv_omega)
  have hok6 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64 + 0x670#64) 8 := hokW.sub' 206 8 (by decide) (by bv_omega)
  have hok7 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64 + 0x6b0#64) 1 := hokW.sub' 214 1 (by decide) (by bv_omega)
  have hok8 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64 + 0x6b8#64) 8 := hokW.sub' 215 8 (by decide) (by bv_omega)
  have hok9 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64 + 0x6f8#64) 8 := hokW.sub' 223 8 (by decide) (by bv_omega)
  have hok11 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64 + 0x738#64) 4 := hokW.sub' 231 4 (by decide) (by bv_omega)
  have hok12 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64 + 0x758#64) 4 := hokW.sub' 235 4 (by decide) (by bv_omega)
  have hok13 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64 + 0x778#64) 8 := hokW.sub' 239 8 (by decide) (by bv_omega)
  have hok14 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64 + 0x7b8#64) 12 := hokW.sub' 247 12 (by decide) (by bv_omega)
  have hok15 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64 + 0x818#64) 12 := hokW.sub' 259 12 (by decide) (by bv_omega)
  have hok16 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8e0#64 + 0x878#64) 13 := hokW.sub' 271 13 (by decide) (by bv_omega)
  obtain ⟨A0, hA0, hA0l⟩ := Region.exists_junk (sp - 0x8e0#64 + 0x520#64) 13 s
  obtain ⟨A1, hA1, hA1l⟩ := Region.exists_junk (sp - 0x8e0#64 + 0x588#64) 3 s
  obtain ⟨A2, hA2, hA2l⟩ := Region.exists_junk (sp - 0x8e0#64 + 0x5a0#64) 18 s
  obtain ⟨A5, hA5, hA5l⟩ := Region.exists_junk (sp - 0x8e0#64 + 0x630#64) 8 s
  obtain ⟨A6, hA6, hA6l⟩ := Region.exists_junk (sp - 0x8e0#64 + 0x670#64) 8 s
  obtain ⟨A7, hA7, hA7l⟩ := Region.exists_junk (sp - 0x8e0#64 + 0x6b0#64) 1 s
  obtain ⟨A8, hA8, hA8l⟩ := Region.exists_junk (sp - 0x8e0#64 + 0x6b8#64) 8 s
  obtain ⟨A9, hA9, hA9l⟩ := Region.exists_junk (sp - 0x8e0#64 + 0x6f8#64) 8 s
  obtain ⟨A11, hA11, hA11l⟩ := Region.exists_junk (sp - 0x8e0#64 + 0x738#64) 4 s
  obtain ⟨A12, hA12, hA12l⟩ := Region.exists_junk (sp - 0x8e0#64 + 0x758#64) 4 s
  obtain ⟨A13, hA13, hA13l⟩ := Region.exists_junk (sp - 0x8e0#64 + 0x778#64) 8 s
  obtain ⟨A14, hA14, hA14l⟩ := Region.exists_junk (sp - 0x8e0#64 + 0x7b8#64) 12 s
  obtain ⟨A15, hA15, hA15l⟩ := Region.exists_junk (sp - 0x8e0#64 + 0x818#64) 12 s
  obtain ⟨A16, hA16, hA16l⟩ := Region.exists_junk (sp - 0x8e0#64 + 0x878#64) 13 s
  have hT : Region 0x78001968#64 sTable s := RoImage.sTable hro
  have hTl : sTable.length = 8192 := sTable_length
  have hokT : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001968#64 8192 := sTable_ok
  -- the table is read-only: off `out` and off the heap
  have hdT0 : Disjoint 0x78001968#64 8192 out 13 := Disjoint.of_ro hokO (by decide) (by decide)
  have hdT1 : Disjoint 0x78001968#64 8192 0x78040620#64 14780694332 :=
    ⟨Or.inl (by decide), by decide, by decide⟩
  have hokH : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hlo := hstk.lo
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hu := Unchanged.refl [(sp - 0x8e0#64, 284), (out, 13), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  sym_exec [memcpy120_spec, hfrom, to_affine_spec, coordinates_spec', sinsemilla_pack_spec, hpaf]
    stop [0x78020e74]
  -- the chunk loop
  sym_reframe
  -- the message bytes `from_iter` produced (`post30_3`) are the bits, hence `0`/`1`, and agree
  -- with the canonical image on the 1090 bytes the chunks read
  have hbool : ∀ o, o < 1090 → byteAt post30_3 o = 0#64 ∨ byteAt post30_3 o = 1#64 :=
    fun o ho => by rw [post30_13 o ho]; cases bit o <;> simp [bw]
  have hch : chunks post30_3 109 = chunks (boolBytesToWords bit 137) 109 :=
    chunks_ext 109 (fun o ho => by rw [post30_13 o ho, byteAt_boolBytesToWords _ _ _ (by omega)])
  have hloop := fun (L' : List (Word × Nat)) => sinsemilla_loop_spec (L := L') (G := G) (n := n) (P := P) (Bv := post30_3) (hBl := post30_12) (hbool := hbool)
  sym_exec [hloop, sinsemilla_unpack_spec, from_xy_spec, to_curve_spec, incomplete_from_spec,
    incomplete_bottom_spec', hdealloc, memcpy104_spec, memset96_spec', conditional_select_spec_one,
    conditional_select_spec_zero, sinsemilla_blinding_spec, hpaf] stop [0x78021154]
  · -- `⊥`: the identity, then `[r] R`
    have hZ0 : leLimbsToNat [0#64, 0#64, 0#64, 0#64] < Fp.p := by decide +kernel
    have hW : leLimbsToNat [acc39_0[8]!, acc39_0[9]!, acc39_0[10]!, acc39_0[11]!] < Fp.p :=
      acc39_0_def ▸ mulW_Z_lt _ _
    sym_reframe
    sym_exec [ep_add_spec]
    -- `Q` packed is `commitAcc0 Q`
    have hqx : leLimbsToNat [post40_0, post40_1, post40_2, post40_3] =
        affineX (ptX [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], ptY [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], ptZ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]) := by
      rw [← post40_12, ← post40_13, ← post40_14, ← post40_15, MachineChecked.RiscV.Sym.cells4',
        leLimbsToNat_natToLeLimbs 4 _ (toAffine_lt (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)).1,
        ← ptX_eq, ← ptY_eq, ← ptZ_eq, affineX_mk]
    have hqy : leLimbsToNat [post40_4, post40_5, post40_6, post40_7] =
        affineY (ptX [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], ptY [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], ptZ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]) := by
      rw [← post40_16, ← post40_17, ← post40_18, ← post40_19, MachineChecked.RiscV.Sym.cells4',
        leLimbsToNat_natToLeLimbs 4 _ (toAffine_lt (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)).2,
        ← ptX_eq, ← ptY_eq, ← ptZ_eq, affineY_mk]
    have hacc0 : [BitVec.ofNat 64 ((leLimbsToNat [post40_0, post40_1, post40_2, post40_3] * Fp.rInv % Fp.p) >>> (64 * 0)),
        BitVec.ofNat 64 ((leLimbsToNat [post40_0, post40_1, post40_2, post40_3] * Fp.rInv % Fp.p) >>> (64 * 1)),
        BitVec.ofNat 64 ((leLimbsToNat [post40_0, post40_1, post40_2, post40_3] * Fp.rInv % Fp.p) >>> (64 * 2)),
        BitVec.ofNat 64 ((leLimbsToNat [post40_0, post40_1, post40_2, post40_3] * Fp.rInv % Fp.p) >>> (64 * 3)),
        BitVec.ofNat 64 ((leLimbsToNat [post40_4, post40_5, post40_6, post40_7] * Fp.rInv % Fp.p) >>> (64 * 0)),
        BitVec.ofNat 64 ((leLimbsToNat [post40_4, post40_5, post40_6, post40_7] * Fp.rInv % Fp.p) >>> (64 * 1)),
        BitVec.ofNat 64 ((leLimbsToNat [post40_4, post40_5, post40_6, post40_7] * Fp.rInv % Fp.p) >>> (64 * 2)),
        BitVec.ofNat 64 ((leLimbsToNat [post40_4, post40_5, post40_6, post40_7] * Fp.rInv % Fp.p) >>> (64 * 3))] = commitAcc0 [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] := by
      rw [commitAcc0_eq, hqx, hqy, natToLeLimbs_cells4, natToLeLimbs_cells4]
      simp only [Nat.reduceMul, Nat.shiftRight_zero, List.cons_append, List.nil_append]
    rw [hacc0, ← commitFold_eq] at post0_13
    have h0 : post0_0[0]! = 0#64 := by rw [v1_def]; exact beq_iff_eq.mp hbr2
    have hfold : commitFold [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] post30_3 = none := post0_13.2.1.mp h0
    have hv3 : v3 = replaceByte O[12]! 0 0#8 := by rw [← v3_def]; rfl
    have e : [BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [0#64, 0#64, 0#64, 0#64])
          (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [acc39_0[0]!, acc39_0[1]!, acc39_0[2]!, acc39_0[3]!])
          (leLimbsToNat [acc39_0[4]!, acc39_0[5]!, acc39_0[6]!, acc39_0[7]!])
          (leLimbsToNat [acc39_0[8]!, acc39_0[9]!, acc39_0[10]!, acc39_0[11]!])).1 >>> (64 * 0)),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [0#64, 0#64, 0#64, 0#64])
          (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [acc39_0[0]!, acc39_0[1]!, acc39_0[2]!, acc39_0[3]!])
          (leLimbsToNat [acc39_0[4]!, acc39_0[5]!, acc39_0[6]!, acc39_0[7]!])
          (leLimbsToNat [acc39_0[8]!, acc39_0[9]!, acc39_0[10]!, acc39_0[11]!])).1 >>> (64 * 1)),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [0#64, 0#64, 0#64, 0#64])
          (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [acc39_0[0]!, acc39_0[1]!, acc39_0[2]!, acc39_0[3]!])
          (leLimbsToNat [acc39_0[4]!, acc39_0[5]!, acc39_0[6]!, acc39_0[7]!])
          (leLimbsToNat [acc39_0[8]!, acc39_0[9]!, acc39_0[10]!, acc39_0[11]!])).1 >>> (64 * 2)),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [0#64, 0#64, 0#64, 0#64])
          (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [acc39_0[0]!, acc39_0[1]!, acc39_0[2]!, acc39_0[3]!])
          (leLimbsToNat [acc39_0[4]!, acc39_0[5]!, acc39_0[6]!, acc39_0[7]!])
          (leLimbsToNat [acc39_0[8]!, acc39_0[9]!, acc39_0[10]!, acc39_0[11]!])).1 >>> (64 * 3)),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [0#64, 0#64, 0#64, 0#64])
          (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [acc39_0[0]!, acc39_0[1]!, acc39_0[2]!, acc39_0[3]!])
          (leLimbsToNat [acc39_0[4]!, acc39_0[5]!, acc39_0[6]!, acc39_0[7]!])
          (leLimbsToNat [acc39_0[8]!, acc39_0[9]!, acc39_0[10]!, acc39_0[11]!])).2.1 >>> (64 * 0)),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [0#64, 0#64, 0#64, 0#64])
          (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [acc39_0[0]!, acc39_0[1]!, acc39_0[2]!, acc39_0[3]!])
          (leLimbsToNat [acc39_0[4]!, acc39_0[5]!, acc39_0[6]!, acc39_0[7]!])
          (leLimbsToNat [acc39_0[8]!, acc39_0[9]!, acc39_0[10]!, acc39_0[11]!])).2.1 >>> (64 * 1)),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [0#64, 0#64, 0#64, 0#64])
          (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [acc39_0[0]!, acc39_0[1]!, acc39_0[2]!, acc39_0[3]!])
          (leLimbsToNat [acc39_0[4]!, acc39_0[5]!, acc39_0[6]!, acc39_0[7]!])
          (leLimbsToNat [acc39_0[8]!, acc39_0[9]!, acc39_0[10]!, acc39_0[11]!])).2.1 >>> (64 * 2)),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [0#64, 0#64, 0#64, 0#64])
          (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [acc39_0[0]!, acc39_0[1]!, acc39_0[2]!, acc39_0[3]!])
          (leLimbsToNat [acc39_0[4]!, acc39_0[5]!, acc39_0[6]!, acc39_0[7]!])
          (leLimbsToNat [acc39_0[8]!, acc39_0[9]!, acc39_0[10]!, acc39_0[11]!])).2.1 >>> (64 * 3)),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [0#64, 0#64, 0#64, 0#64])
          (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [acc39_0[0]!, acc39_0[1]!, acc39_0[2]!, acc39_0[3]!])
          (leLimbsToNat [acc39_0[4]!, acc39_0[5]!, acc39_0[6]!, acc39_0[7]!])
          (leLimbsToNat [acc39_0[8]!, acc39_0[9]!, acc39_0[10]!, acc39_0[11]!])).2.2 >>> (64 * 0)),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [0#64, 0#64, 0#64, 0#64])
          (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [acc39_0[0]!, acc39_0[1]!, acc39_0[2]!, acc39_0[3]!])
          (leLimbsToNat [acc39_0[4]!, acc39_0[5]!, acc39_0[6]!, acc39_0[7]!])
          (leLimbsToNat [acc39_0[8]!, acc39_0[9]!, acc39_0[10]!, acc39_0[11]!])).2.2 >>> (64 * 1)),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [0#64, 0#64, 0#64, 0#64])
          (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [acc39_0[0]!, acc39_0[1]!, acc39_0[2]!, acc39_0[3]!])
          (leLimbsToNat [acc39_0[4]!, acc39_0[5]!, acc39_0[6]!, acc39_0[7]!])
          (leLimbsToNat [acc39_0[8]!, acc39_0[9]!, acc39_0[10]!, acc39_0[11]!])).2.2 >>> (64 * 2)),
        BitVec.ofNat 64 ((Fp.addJ (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [0#64, 0#64, 0#64, 0#64])
          (leLimbsToNat [0#64, 0#64, 0#64, 0#64]) (leLimbsToNat [acc39_0[0]!, acc39_0[1]!, acc39_0[2]!, acc39_0[3]!])
          (leLimbsToNat [acc39_0[4]!, acc39_0[5]!, acc39_0[6]!, acc39_0[7]!])
          (leLimbsToNat [acc39_0[8]!, acc39_0[9]!, acc39_0[10]!, acc39_0[11]!])).2.2 >>> (64 * 3)), v3] =
        commitW [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] post30_3 [k0, k1, k2, k3] ++ [replaceByte O[12]! 0 (commitFlag [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] post30_3)] := by
      rw [hv3, commitFlag_none hfold, commitW_eq, commitJ_eq, commitHash_none hfold, acc39_0_def, jX_eq,
        jY_eq, jZ_eq, ptX_zero, ptY_zero, ptZ_zero, ptX_eq acc39_0, ptY_eq acc39_0, ptZ_eq acc39_0,
        natToLeLimbs_cells4, natToLeLimbs_cells4, natToLeLimbs_cells4]
      simp only [Nat.reduceMul, Nat.shiftRight_zero, List.cons_append, List.nil_append]
    have hRo' := Eq.mp (congrArg (fun L => Region out L s_19) e) hR4
    have hRo := hRo'
    rw [commitW_congr hch, commitFlag_congr hch] at hRo
    have hRoP := hRo.sub 0 12 (a := out) (ws := commitW _ _ _ _) (by simp)
      (by rw [List.drop_zero, List.take_left' (commitW_length _ _ _ _)])
    have hRoF := hRo.sub 12 1 (a := out + 0x60#64) (ws := [replaceByte _ 0 (commitFlag _ _)]) rfl
      (by rw [List.drop_left' (commitW_length _ _ _ _)]; rfl)
    sym_close hk
  · -- `cap = 0` cannot happen (the executor does not decide this `bnez` from `cap ≠ 0`)
    exact absurd (by simpa using hbr8) post30_10
  · -- the hash point, then `[r] R`
    have hX : leLimbsToNat [v24, v25, v26, v27] < Fp.p := by
      rw [← v24_def, ← v25_def, ← v26_def, ← v27_def]; exact mcells_lt _ (Fp.mul_lt _ _)
    have hZ := zcells_lt' (if v24 = 0#64 ∧ v25 = 0#64 ∧ v26 = 0#64 ∧ v27 = 0#64 ∧ v32 = 0#64 ∧ v33 = 0#64 ∧ v34 = 0#64 ∧ v35 = 0#64 then 0 else Fp.R) (ite_lt_p _)
    have hW : leLimbsToNat [acc108_0[8]!, acc108_0[9]!, acc108_0[10]!, acc108_0[11]!] < Fp.p :=
      acc108_0_def ▸ mulW_Z_lt _ _
    -- the accumulator's cells, under names the next run does not shadow
    have c0_def := v1_def
    have c1_def := v11_def
    have c2_def := v12_def
    have c3_def := v13_def
    have c4_def := v14_def
    have c5_def := v3_def
    have c6_def := v4_def
    have c7_def := v5_def
    have c8_def := v6_def
    have hne := hbr2
    sym_reframe
    sym_exec [ep_add_spec]
    -- `Q` packed is `commitAcc0 Q`
    have hqx : leLimbsToNat [post40_0, post40_1, post40_2, post40_3] =
        affineX (ptX [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], ptY [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], ptZ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]) := by
      rw [← post40_12, ← post40_13, ← post40_14, ← post40_15, MachineChecked.RiscV.Sym.cells4',
        leLimbsToNat_natToLeLimbs 4 _ (toAffine_lt (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)).1,
        ← ptX_eq, ← ptY_eq, ← ptZ_eq, affineX_mk]
    have hqy : leLimbsToNat [post40_4, post40_5, post40_6, post40_7] =
        affineY (ptX [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], ptY [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], ptZ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]) := by
      rw [← post40_16, ← post40_17, ← post40_18, ← post40_19, MachineChecked.RiscV.Sym.cells4',
        leLimbsToNat_natToLeLimbs 4 _ (toAffine_lt (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)).2,
        ← ptX_eq, ← ptY_eq, ← ptZ_eq, affineY_mk]
    have hacc0 : [BitVec.ofNat 64 ((leLimbsToNat [post40_0, post40_1, post40_2, post40_3] * Fp.rInv % Fp.p) >>> (64 * 0)),
        BitVec.ofNat 64 ((leLimbsToNat [post40_0, post40_1, post40_2, post40_3] * Fp.rInv % Fp.p) >>> (64 * 1)),
        BitVec.ofNat 64 ((leLimbsToNat [post40_0, post40_1, post40_2, post40_3] * Fp.rInv % Fp.p) >>> (64 * 2)),
        BitVec.ofNat 64 ((leLimbsToNat [post40_0, post40_1, post40_2, post40_3] * Fp.rInv % Fp.p) >>> (64 * 3)),
        BitVec.ofNat 64 ((leLimbsToNat [post40_4, post40_5, post40_6, post40_7] * Fp.rInv % Fp.p) >>> (64 * 0)),
        BitVec.ofNat 64 ((leLimbsToNat [post40_4, post40_5, post40_6, post40_7] * Fp.rInv % Fp.p) >>> (64 * 1)),
        BitVec.ofNat 64 ((leLimbsToNat [post40_4, post40_5, post40_6, post40_7] * Fp.rInv % Fp.p) >>> (64 * 2)),
        BitVec.ofNat 64 ((leLimbsToNat [post40_4, post40_5, post40_6, post40_7] * Fp.rInv % Fp.p) >>> (64 * 3))] = commitAcc0 [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] := by
      rw [commitAcc0_eq, hqx, hqy, natToLeLimbs_cells4, natToLeLimbs_cells4]
      simp only [Nat.reduceMul, Nat.shiftRight_zero, List.cons_append, List.nil_append]
    rw [hacc0, ← commitFold_eq] at post0_13
    have h1 : post0_0[0]! ≠ 0#64 := by rw [c0_def]; exact fun h => hne (beq_iff_eq.mpr h)
    obtain ⟨L, hL, hw⟩ : ∃ L, commitFold [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] post30_3 = some L ∧ post0_0 = 1#64 :: L := by
      cases hm : commitFold [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] post30_3 with
      | none => exact absurd (post0_13.2.1.mpr hm) h1
      | some L => exact ⟨L, rfl, post0_13.2.2 L hm⟩
    rw [hw, List.getElem!_cons_succ] at c1_def c2_def c3_def c4_def c5_def c6_def c7_def c8_def
    have hu : unpackW L = [v24, v25, v26, v27, v32, v33, v34, v35] := by
      rw [unpackW_eq, c1_def, c2_def, c3_def, c4_def, c5_def, c6_def, c7_def, c8_def, ← v24_def,
        ← v25_def, ← v26_def, ← v27_def, ← v32_def, ← v33_def, ← v34_def, ← v35_def,
        natToLeLimbs_cells4, natToLeLimbs_cells4]
      simp only [Nat.shiftRight_zero, List.cons_append, List.nil_append]
    have htc : toCurveW (unpackW L) = [v24, v25, v26, v27, v32, v33, v34, v35,
        BitVec.ofNat 64 ((if v24 = 0#64 ∧ v25 = 0#64 ∧ v26 = 0#64 ∧ v27 = 0#64 ∧ v32 = 0#64 ∧ v33 = 0#64 ∧ v34 = 0#64 ∧ v35 = 0#64 then 0 else Fp.R) >>> (64 * 0)), BitVec.ofNat 64 ((if v24 = 0#64 ∧ v25 = 0#64 ∧ v26 = 0#64 ∧ v27 = 0#64 ∧ v32 = 0#64 ∧ v33 = 0#64 ∧ v34 = 0#64 ∧ v35 = 0#64 then 0 else Fp.R) >>> (64 * 1)),
        BitVec.ofNat 64 ((if v24 = 0#64 ∧ v25 = 0#64 ∧ v26 = 0#64 ∧ v27 = 0#64 ∧ v32 = 0#64 ∧ v33 = 0#64 ∧ v34 = 0#64 ∧ v35 = 0#64 then 0 else Fp.R) >>> (64 * 2)), BitVec.ofNat 64 ((if v24 = 0#64 ∧ v25 = 0#64 ∧ v26 = 0#64 ∧ v27 = 0#64 ∧ v32 = 0#64 ∧ v33 = 0#64 ∧ v34 = 0#64 ∧ v35 = 0#64 then 0 else Fp.R) >>> (64 * 3))] := by
      rw [toCurveW_eq, hu, natToLeLimbs_cells4]
      simp only [list8_get_0, list8_get_1, list8_get_2, list8_get_3, list8_get_4, list8_get_5,
        list8_get_6, list8_get_7, Nat.reduceMul, Nat.shiftRight_zero, List.cons_append, List.nil_append]
      rfl
    have hv3 : v3 = replaceByte O[12]! 0 1#8 := by rw [← v3_def]; rfl
    have hRo' : Region out (commitW [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] post30_3 [k0, k1, k2, k3] ++
        [replaceByte O[12]! 0 (commitFlag [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] post30_3)]) s_19 := by
      rw [commitFlag_some hL, ← hv3, commitW_eq, commitJ_eq, commitHash_some hL, htc, acc108_0_def,
        jX_eq, jY_eq, jZ_eq, ptX_eq, ptY_eq, ptZ_eq, ptX_eq acc108_0, ptY_eq acc108_0, ptZ_eq acc108_0,
        ← MachineChecked.RiscV.Sym.cells4', ← MachineChecked.RiscV.Sym.cells4', ← MachineChecked.RiscV.Sym.cells4']
      simp only [list12_get_0, list12_get_1, list12_get_2, list12_get_3, list12_get_4, list12_get_5,
        list12_get_6, list12_get_7, list12_get_8, list12_get_9, list12_get_10, list12_get_11,
        List.cons_append, List.nil_append]
      exact hR4
    have hRo := hRo'
    rw [commitW_congr hch, commitFlag_congr hch] at hRo
    have hRoP := hRo.sub 0 12 (a := out) (ws := commitW _ _ _ _) (by simp)
      (by rw [List.drop_zero, List.take_left' (commitW_length _ _ _ _)])
    have hRoF := hRo.sub 12 1 (a := out + 0x60#64) (ws := [replaceByte _ 0 (commitFlag _ _)]) rfl
      (by rw [List.drop_left' (commitW_length _ _ _ _)]; rfl)
    sym_close hk

end Cases.Zip2005
