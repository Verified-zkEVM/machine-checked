import Cases.Zip2005.Sinsemilla.SinsemillaCommit
import Cases.Zip2005.Sinsemilla.SinsemillaLoopIvk
import Cases.Zip2005.Kit.CellsGlue
import Cases.Zip2005.Image.F_78021238
import Cases.Zip2005.Image.Ro

/-!
# `sinsemilla::CommitDomain::commit`, the `commit_ivk` instantiation (`0x78021238`)

The same function as `0x78020d50` (`Proof/Sinsemilla/SinsemillaCommit.lean`) compiled for the
`commit_ivk` message iterator: a 72-byte `Pad<Chain<…>>` over the 255 bits of `ak` and of
`nk`, 510 message bits (51 chunks), hence a `Vec<bool>` of 510 bytes (stated over 65 words, see `SinsemillaLoopIvk`). The frame
is 0x3a0 bytes with the blocks laid out differently; the instruction sequence is otherwise
identical. The models are the 51-chunk counterparts of `commitFold` … `commitW`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-! ## The model: 51 chunks -/

/-- The chunk fold over the 51 chunks of the message bytes `Bv`. -/
def ivkFold (Q Bv : List Word) : Option (List Word) :=
  sinFold sTable (some (commitAcc0 Q)) (chunks Bv 51)

/-- The hash point as the guest holds it: the identity for `⊥`, else the accumulator unpacked
and lifted to the curve. -/
def ivkHash (Q Bv : List Word) : List Word :=
  (ivkFold Q Bv).elim [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] (fun L => toCurveW (unpackW L))

/-- `is_some` of the hash. -/
def ivkFlag (Q Bv : List Word) : BitVec 8 := if (ivkFold Q Bv).isSome then 1#8 else 0#8

/-- The commitment in Jacobian coordinates: the hash point plus `[r] R`. -/
def ivkJ (Q R Bv k : List Word) : Nat × Nat × Nat :=
  Fp.addJ (ptX (ivkHash Q Bv)) (ptY (ivkHash Q Bv)) (ptZ (ivkHash Q Bv))
    (ptX (mulW R k)) (ptY (mulW R k)) (ptZ (mulW R k))

theorem ivkJ_eq (Q R Bv k : List Word) : ivkJ Q R Bv k =
    Fp.addJ (ptX (ivkHash Q Bv)) (ptY (ivkHash Q Bv)) (ptZ (ivkHash Q Bv))
      (ptX (mulW R k)) (ptY (mulW R k)) (ptZ (mulW R k)) := rfl

/-- The commitment's twelve limbs. -/
def ivkW (Q R Bv k : List Word) : List Word :=
  natToLeLimbs 4 (jX (ivkJ Q R Bv k)) ++ natToLeLimbs 4 (jY (ivkJ Q R Bv k)) ++
    natToLeLimbs 4 (jZ (ivkJ Q R Bv k))

theorem ivkFold_eq (Q Bv : List Word) :
    ivkFold Q Bv = sinFold sTable (some (commitAcc0 Q)) (chunks Bv 51) := rfl

theorem ivkHash_none {Q Bv : List Word} (h : ivkFold Q Bv = none) :
    ivkHash Q Bv = [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] := by
  rw [ivkHash, h]; rfl

theorem ivkHash_some {Q Bv L : List Word} (h : ivkFold Q Bv = some L) :
    ivkHash Q Bv = toCurveW (unpackW L) := by
  rw [ivkHash, h]; rfl

theorem ivkFlag_none {Q Bv : List Word} (h : ivkFold Q Bv = none) : ivkFlag Q Bv = 0#8 := by
  rw [ivkFlag, h]; rfl

theorem ivkFlag_some {Q Bv L : List Word} (h : ivkFold Q Bv = some L) : ivkFlag Q Bv = 1#8 := by
  rw [ivkFlag, h]; rfl

theorem ivkW_eq (Q R Bv k : List Word) : ivkW Q R Bv k =
    natToLeLimbs 4 (jX (ivkJ Q R Bv k)) ++ natToLeLimbs 4 (jY (ivkJ Q R Bv k)) ++
      natToLeLimbs 4 (jZ (ivkJ Q R Bv k)) := rfl

@[simp] theorem ivkW_length (Q R Bv k : List Word) : (ivkW Q R Bv k).length = 12 := by
  simp only [ivkW_eq, List.length_append, length_natToLeLimbs]

/-- The models depend on the message through its first 51 chunks only. -/
theorem ivkFold_congr {Q A B : List Word} (h : chunks A 51 = chunks B 51) :
    ivkFold Q A = ivkFold Q B := by
  unfold ivkFold; rw [h]

theorem ivkHash_congr {Q A B : List Word} (h : chunks A 51 = chunks B 51) :
    ivkHash Q A = ivkHash Q B := by
  unfold ivkHash; rw [ivkFold_congr h]

theorem ivkFlag_congr {Q A B : List Word} (h : chunks A 51 = chunks B 51) :
    ivkFlag Q A = ivkFlag Q B := by
  unfold ivkFlag; rw [ivkFold_congr h]

theorem ivkW_congr {Q R A B k : List Word} (h : chunks A 51 = chunks B 51) :
    ivkW Q R A k = ivkW Q R B k := by
  unfold ivkW ivkJ; rw [ivkHash_congr h]

/-! ## The loop lemma as a specification at the loop head -/

/-- `Cases.Zip2005.sinsemilla_loop_ivk` for the whole message (51 chunks from the first) in the shape the
executor applies: the counter and pointer registers as values, the accumulator's nine cells
explicit, the table the read-only one. -/
theorem sinsemilla_loop_ivk_spec {P : Prop} (t : MachineState) (sp bp : Word) (Bv : List Word)
    (hBl : Bv.length = 65)
    (hbool : ∀ o, o < 510 → byteAt Bv o = 0#64 ∨ byteAt Bv o = 1#64)
    (g3 g4 g8 g9 g18 a1 a2 a3 a4 a5 a6 a7 a8 : Word) (A C D E F : List Word)
    (hAl : A.length = 9) (hCl : C.length = 4) (hDl : D.length = 4) (hEl : E.length = 9)
    (hFl : F.length = 9)
    (hbounds : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = t.code → Safe P u)
    (hunwrap : ∀ u : MachineState, u.pc = 0x7803dc7c#64 → u.code = t.code → Safe P u)
    (hpc : t.pc = 0x7802135c#64)
    (hcodeC : CodeAt F_78021238.base F_78021238.prog t)
    (hcodeL : CodeAt F_780234cc.base F_780234cc.prog t)
    (hcodeP : CodeAt F_780237dc.base F_780237dc.prog t)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog t)
    (hcodeI : CodeAt F_780235e8.base F_780235e8.prog t)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog t)
    (hcodeAA : CodeAt F_78035f88.base F_78035f88.prog t)
    (hcodeLR : CodeAt F_780360e0.base F_780360e0.prog t)
    (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog t)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog t)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi t) (hro : RoImage Ro.layout t)
    (hsp : t.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x130 sp) (hhi : sp.toNat + 0x3a0 ≤ 0x78000000)
    (h3 : t.getReg .x3 = g3) (h4 : t.getReg .x4 = g4) (h8 : t.getReg .x8 = g8)
    (h9 : t.getReg .x9 = g9) (h18 : t.getReg .x18 = g18)
    (h19 : t.getReg .x19 = sp + 0x178#64) (h20 : t.getReg .x20 = sp + 0x280#64)
    (h21 : t.getReg .x21 = 510#64) (h22 : t.getReg .x22 = bp)
    (h23 : t.getReg .x23 = 9#64) (h24 : t.getReg .x24 = 0x3ff#64)
    (h25 : t.getReg .x25 = 0x78001968#64) (h26 : t.getReg .x26 = 1#64)
    (hT : Region 0x78001968#64 sTable t) (hokT : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001968#64 8192)
    (hB : Region bp Bv t) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi bp 65)
    (hA : Region (sp + 0x70#64) A t) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x70#64) 9)
    (hacc0 : Region (sp + 0x170#64) [1#64] t)
    (hacc1 : Region (sp + 0x178#64) [a1, a2, a3, a4, a5, a6, a7, a8] t)
    (hokacc : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x170#64) 9)
    (hC : Region (sp + 0x1b8#64) C t) (hokC : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x1b8#64) 4)
    (hD : Region (sp + 0x238#64) D t) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x238#64) 4)
    (hE : Region (sp + 0x278#64) E t) (hokE : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x278#64) 9)
    (hF : Region (sp + 0x8#64) F t) (hokF : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x8#64) 9)
    (hdB : Disjoint bp 65 (sp - 0x130#64) 126)
    (hk : ∀ (u : MachineState) (acc' : List Word), u.pc = 0x780214a4#64 → u.code = t.code →
      u.getReg .x2 = sp → u.getReg .x3 = g3 → u.getReg .x4 = g4 → u.getReg .x8 = g8 →
      u.getReg .x9 = g9 → u.getReg .x18 = g18 → u.getReg .x19 = sp + 0x178#64 →
      Unchanged [(sp - 0x130#64, 38), (sp + 0x70#64, 9), (sp + 0x170#64, 9), (sp + 0x1b8#64, 4),
        (sp + 0x238#64, 4), (sp + 0x278#64, 9), (sp + 0x8#64, 9)] t u →
      acc'.length = 9 → Region (sp + 0x170#64) acc' u →
      AccRep (sinFold sTable (some [a1, a2, a3, a4, a5, a6, a7, a8]) (chunks Bv 51)) acc' →
      Safe P u) :
    Safe P t := by
  have hacc : Region (sp + 0x170#64) [1#64, a1, a2, a3, a4, a5, a6, a7, a8] t := by
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
  exact sinsemilla_loop_ivk sp bp sTable Bv 51 t.code g3 g4 g8 g9 g18 [a1, a2, a3, a4, a5, a6, a7, a8]
    hbounds hunwrap sTable_length hBl (by decide) hbool 51 0 t
    [1#64, a1, a2, a3, a4, a5, a6, a7, a8] 510#64 bp (by omega) (by omega) hrep hpc rfl hcodeC hcodeL hcodeP
    hcodeT hcodeI hcodeCmp hcodeAA hcodeLR hcodeAdd hcodeM hcw hro hsp hstk hhi h3 h4 h8 h9 h18
    h19 h20 h21 rfl h22 (by simp) h23 h24 h25 h26 hT hokT hB hokB ⟨A, hAl, hA⟩ hokA hacc hokacc
    ⟨C, hCl, hC⟩ hokC ⟨D, hDl, hD⟩ hokD ⟨E, hEl, hE⟩ hokE ⟨F, hFl, hF⟩ hokF hdB
    (fun u acc' hpc hc h2 h3 h4 h8 h9 h18 h19 hun hR hrep =>
      hk u acc' hpc hc h2 h3 h4 h8 h9 h18 h19 hun hrep.1 hR hrep)

/-! ## `conditional_select` with a literal choice -/


/-! ## The function -/

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
set_option asmverif.sym.foldBytes true in
/-- `CommitDomain::commit(out, domain, iter, r)`: `domain` holds `Q` and, at `+0x60`, `R`
(Jacobian Montgomery limbs); `iter` the 72-byte padded-bit iterator; `r` the blinding scalar
(`Fq`, Montgomery). `from_iter` is a contract (`hfrom`): it collects the iterator into the
510 message bytes `Bv` (a `Vec<bool>`, a byte per bit), with `__rust_dealloc` (`hdealloc`)
freeing it. The result is `ivkW` with the `is_some` flag byte. -/
theorem sinsemilla_commit_ivk_spec {P : Prop} (s : MachineState) (ra sp out dom iter r : Word)
    (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 : Word)
    (k0 k1 k2 k3 : Word) (I : List Word) (hIl : I.length = 9)
    (bit : Nat → Bool) (M : Word) (Mw O : List Word) (hMl : Mw.length = 8) (hOl : O.length = 13)
    -- the sqrt/generator tables (`FP_TABLES`) in the heap, carried through: the allocator
    -- contracts below keep them (the allocator never writes a live block)
    (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word)
    (hIVl : IV.length = 138) (hG0l : G0.length = 1024) (hG1l : G1.length = 1024)
    (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hTB : Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] s)
    (hIVr : Region iptr IV s) (hG0 : Region tg0 G0 s) (hG1 : Region tg1 G1 s)
    (hG2 : Region tg2 G2 s) (hG3 : Region tg3 G3 s)
    (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024)
    (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024)
    (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516)
    (hlo_iptr : 0x78048980 ≤ iptr.toNat) (hlo_g0 : 0x78048980 ≤ tg0.toNat) (hlo_g1 : 0x78048980 ≤ tg1.toNat)
    (hlo_g2 : 0x78048980 ≤ tg2.toNat) (hlo_g3 : 0x78048980 ≤ tg3.toNat)
    (hhi_iptr : iptr.toNat + 8 * 138 ≤ 0x1c00000000)
    (hhi_g0 : tg0.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g1 : tg1.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g2 : tg2.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g3 : tg3.toNat + 8 * 516 ≤ 0x1c00000000)
    -- the caller's blocks lie below the heap (on its stack), so off the tables
    (hbelow_dom : dom.toNat + 8 * 12 ≤ 0x78040620)
    (hbelow_iter : iter.toNat + 8 * 9 ≤ 0x78040620)
    (hbelow_r : r.toNat + 8 * 4 ≤ 0x78040620)
    (hbelow_out : out.toNat + 8 * 13 ≤ 0x78040620)
    (hbelow_M : M.toNat + 8 * 8 ≤ 0x78040620)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → Safe P u)
    (hpanic : ∀ u : MachineState, u.pc = 0x7803de40#64 → u.code = s.code → Safe P u)
    (hunwrap : ∀ u : MachineState, u.pc = 0x7803dc7c#64 → u.code = s.code → Safe P u)
    (hbounds : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → Safe P u)
    (hpc : s.pc = 0x78021238#64) (hcode : CodeAt F_78021238.base F_78021238.prog s)
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
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x8c0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = dom) (ha2 : s.getReg .x12 = iter)
    (ha3 : s.getReg .x13 = r)
    (hQ : Region dom [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] s)
    (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi dom 12)
    (hR : Region (dom + 0x60#64) [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] s)
    (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi (dom + 0x60#64) 12)
    (hI : Region iter I s)
    (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi iter 9)
    (hK : Region r [k0, k1, k2, k3] s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi r 4)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 13)
    (hd0 : Disjoint (sp - 0x8c0#64) 280 dom 12) (hd1 : Disjoint (sp - 0x8c0#64) 280 (dom + 0x60#64) 12)
    (hd2 : Disjoint (sp - 0x8c0#64) 280 iter 9) (hd3 : Disjoint (sp - 0x8c0#64) 280 r 4)
    (hd4 : Disjoint (sp - 0x8c0#64) 280 out 13)
    (he0 : Disjoint out 13 dom 12) (he1 : Disjoint out 13 (dom + 0x60#64) 12)
    (he2 : Disjoint out 13 iter 9) (he3 : Disjoint out 13 r 4)
    (hh0 : Disjoint 0x78040620#64 14780694332 dom 12)
    (hh1 : Disjoint 0x78040620#64 14780694332 (dom + 0x60#64) 12)
    (hh2 : Disjoint 0x78040620#64 14780694332 iter 9)
    (hh3 : Disjoint 0x78040620#64 14780694332 r 4)
    (hh4 : Disjoint 0x78040620#64 14780694332 out 13)
    -- the words the iterator points to (the caller's message), read by `from_iter` only
    (hM : Region M Mw s) (hokM : RegionOk Ro.layout.textLo Ro.layout.textHi M 8)
    -- what `from_iter` needs of the caller's frame, which holds `M` (`StackOk Ro.layout` of it at `commit_ivk`)
    (Mok : Prop) (hMok : Mok)
    (hdM : Disjoint (sp - 0x8c0#64) 280 M 8) (heM : Disjoint out 13 M 8)
    (hhM : Disjoint 0x78040620#64 14780694332 M 8)
    -- `from_iter` (ledger T2): the iterator (its state `[0, _, iter…, 0]`) collected into the
    -- 510 message bytes, a `Vec` of some non-zero capacity on the heap
    (hfrom : ∀ (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word), O1.length = 3 →
      u.pc = 0x7801e110#64 → u.code = s.code → u.getReg .x1 = 0x780212ac#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x260 sp' → u.getReg .x10 = a0' → u.getReg .x11 = a1' →
      Region a0' O1 u → Region a1' [0#64, j] u →
      Region (a1' + 0x10#64) I u →
      Region (a1' + 0x58#64) [0#64] u → Region M Mw u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 3 → RegionOk Ro.layout.roBase Ro.layout.textHi a1' 12 →
      Disjoint (sp' - 0x260#64) 76 a0' 3 → Disjoint (sp' - 0x260#64) 76 a1' 12 →
      Disjoint a0' 3 a1' 12 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      IV.length = 138 → G0.length = 1024 → G1.length = 1024 → G2.length = 1024 → G3.length = 516 →
      0x78048980 ≤ iptr.toNat → iptr.toNat + 8 * 138 ≤ 0x1c00000000 →
      0x78048980 ≤ tg0.toNat → tg0.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg1.toNat → tg1.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg2.toNat → tg2.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg3.toNat → tg3.toNat + 8 * 516 ≤ 0x1c00000000 →
      RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 → RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 →
      Mok →
      Disjoint (sp' - 0x260#64) 76 M 8 → Disjoint a0' 3 M 8 → Disjoint a1' 12 M 8 →
      Disjoint 0x78040620#64 14780694332 a0' 3 → Disjoint 0x78040620#64 14780694332 a1' 12 →
      (∀ (t : MachineState) (cap ptr : Word) (J Bv : List Word), t.pc = 0x780212ac#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x260#64, 76), (a0', 3), (a1', 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        J.length = 12 → Region a0' [cap, ptr, 510#64] t → cap ≠ 0#64 → Region a1' J t →
        Bv.length = 65 → (∀ o, o < 510 → byteAt Bv o = bw (bit o)) →
        Region ptr Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 65 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → Safe P t) → Safe P u)
    -- `__rust_dealloc` of that `Vec` (ledger T2)
    (hdealloc : ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word), C.length = 65 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780215d8#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap →
      u.getReg .x12 = 1#64 → Region ptr C u → 0x78048980 ≤ ptr.toNat →
      ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      (∀ t, t.pc = 0x780215d8#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → Safe P t) → Safe P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x8c0#64, 280), (out, 13), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (ivkW [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]
        [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] (boolBytesToWords bit 65) [k0, k1, k2, k3]) t →
      Region (out + 0x60#64) [replaceByte O[12]! 0 (ivkFlag [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]
          (boolBytesToWords bit 65))] t →
      mulFacts [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] [k0, k1, k2, k3] →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
      Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64) 280 := hstk.frame 280 (by decide)
  -- the frame (below it 0x520 bytes for the callees' frames); the blocks are those of
  -- `CommitDomain::commit` at `0x78020d50`, laid out differently: the `from` output and the
  -- loop's `F` share the 13 cells at +0x8, `conditional_select` writes over the iterator block
  have hokZ : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x520#64) 1 := hokW.sub' 164 1 (by decide) (by bv_omega)
  obtain ⟨AZ, hAZ, hAZl⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x520#64) 1 s
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x590#64) 13 := hokW.sub' 178 13 (by decide) (by bv_omega)
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x5f8#64) 3 := hokW.sub' 191 3 (by decide) (by bv_omega)
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x7f8#64) 12 := hokW.sub' 255 12 (by decide) (by bv_omega)
  have hok5 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x610#64) 8 := hokW.sub' 194 8 (by decide) (by bv_omega)
  have hok6 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x650#64) 8 := hokW.sub' 202 8 (by decide) (by bv_omega)
  have hok7 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x690#64) 1 := hokW.sub' 210 1 (by decide) (by bv_omega)
  have hok8 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x698#64) 8 := hokW.sub' 211 8 (by decide) (by bv_omega)
  have hok9 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x6d8#64) 8 := hokW.sub' 219 8 (by decide) (by bv_omega)
  have hok11 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x718#64) 4 := hokW.sub' 227 4 (by decide) (by bv_omega)
  have hok12 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x738#64) 4 := hokW.sub' 231 4 (by decide) (by bv_omega)
  have hok13 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x758#64) 8 := hokW.sub' 235 8 (by decide) (by bv_omega)
  have hok14 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x798#64) 12 := hokW.sub' 243 12 (by decide) (by bv_omega)
  have hok15 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x528#64) 13 := hokW.sub' 165 13 (by decide) (by bv_omega)
  have hok16 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x8c0#64 + 0x858#64) 13 := hokW.sub' 267 13 (by decide) (by bv_omega)
  obtain ⟨A0, hA0, hA0l⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x590#64) 13 s
  obtain ⟨A1, hA1, hA1l⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x5f8#64) 3 s
  obtain ⟨A2, hA2, hA2l⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x7f8#64) 12 s
  obtain ⟨A5, hA5, hA5l⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x610#64) 8 s
  obtain ⟨A6, hA6, hA6l⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x650#64) 8 s
  obtain ⟨A7, hA7, hA7l⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x690#64) 1 s
  obtain ⟨A8, hA8, hA8l⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x698#64) 8 s
  obtain ⟨A9, hA9, hA9l⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x6d8#64) 8 s
  obtain ⟨A11, hA11, hA11l⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x718#64) 4 s
  obtain ⟨A12, hA12, hA12l⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x738#64) 4 s
  obtain ⟨A13, hA13, hA13l⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x758#64) 8 s
  obtain ⟨A14, hA14, hA14l⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x798#64) 12 s
  obtain ⟨A15, hA15, hA15l⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x528#64) 13 s
  obtain ⟨A16, hA16, hA16l⟩ := Region.exists_junk (sp - 0x8c0#64 + 0x858#64) 13 s
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
  have hu := Unchanged.refl [(sp - 0x8c0#64, 280), (out, 13), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  sym_exec [memcpy72_spec, hfrom, to_affine_spec, coordinates_spec', sinsemilla_pack_spec, hpaf]
    stop [0x7802135c]
  -- the chunk loop
  sym_reframe
  -- the message bytes `from_iter` produced (`post30_3`) are the bits, hence `0`/`1`, and agree
  -- with the canonical image on the 1090 bytes the chunks read
  have hbool : ∀ o, o < 510 → byteAt post30_3 o = 0#64 ∨ byteAt post30_3 o = 1#64 :=
    fun o ho => by rw [post30_13 o ho]; cases bit o <;> simp [bw]
  have hch : chunks post30_3 51 = chunks (boolBytesToWords bit 65) 51 :=
    chunks_ext 51 (fun o ho => by rw [post30_13 o ho, byteAt_boolBytesToWords _ _ _ (by omega)])
  have hloop := sinsemilla_loop_ivk_spec (P := P) (Bv := post30_3) (hBl := post30_12) (hbool := hbool)
  sym_exec [hloop, sinsemilla_unpack_spec, from_xy_spec, to_curve_spec, incomplete_from_spec,
    incomplete_bottom_spec', hdealloc, memcpy104_spec, memset96_spec', conditional_select_spec_one,
    conditional_select_spec_zero, sinsemilla_blinding_spec, hpaf] stop [0x7802163c]
  · -- `⊥`: the identity, then `[r] R`
    have hZ0 : leLimbsToNat [0#64, 0#64, 0#64, 0#64] < Fp.p := by decide +kernel
    have hW : leLimbsToNat [acc39_0[8]!, acc39_0[9]!, acc39_0[10]!, acc39_0[11]!] < Fp.p :=
      acc39_0_def ▸ mulW_Z_lt _ _
    sym_reframe
    sym_exec [ep_add_spec]
    -- `Q` packed is `commitAcc0 Q`
    have hqx : leLimbsToNat [post40_0, post40_1, post40_2, post40_3] =
        affineX (ptX [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], ptY [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], ptZ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]) := by
      rw [← post40_12, ← post40_13, ← post40_14, ← post40_15, AsmVerif.RiscV.Sym.cells4',
        leLimbsToNat_natToLeLimbs 4 _ (toAffine_lt (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)).1,
        ← ptX_eq, ← ptY_eq, ← ptZ_eq, affineX_mk]
    have hqy : leLimbsToNat [post40_4, post40_5, post40_6, post40_7] =
        affineY (ptX [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], ptY [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], ptZ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]) := by
      rw [← post40_16, ← post40_17, ← post40_18, ← post40_19, AsmVerif.RiscV.Sym.cells4',
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
    rw [hacc0, ← ivkFold_eq] at post0_13
    have h0 : post0_0[0]! = 0#64 := by rw [v1_def]; exact beq_iff_eq.mp hbr2
    have hfold : ivkFold [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] post30_3 = none := post0_13.2.1.mp h0
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
        ivkW [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] post30_3 [k0, k1, k2, k3] ++ [replaceByte O[12]! 0 (ivkFlag [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] post30_3)] := by
      rw [hv3, ivkFlag_none hfold, ivkW_eq, ivkJ_eq, ivkHash_none hfold, acc39_0_def, jX_eq,
        jY_eq, jZ_eq, ptX_zero, ptY_zero, ptZ_zero, ptX_eq acc39_0, ptY_eq acc39_0, ptZ_eq acc39_0,
        natToLeLimbs_cells4, natToLeLimbs_cells4, natToLeLimbs_cells4]
      simp only [Nat.reduceMul, Nat.shiftRight_zero, List.cons_append, List.nil_append]
    region_at out in s_19 as hRout
    have hRo' := Eq.mp (congrArg (fun L => Region out L s_19) e) hRout
    have hRo := hRo'
    rw [ivkW_congr hch, ivkFlag_congr hch] at hRo
    have hRoP := hRo.sub 0 12 (a := out) (ws := ivkW _ _ _ _) (by simp)
      (by rw [List.drop_zero, List.take_left' (ivkW_length _ _ _ _)])
    have hRoF := hRo.sub 12 1 (a := out + 0x60#64) (ws := [replaceByte _ 0 (ivkFlag _ _)]) rfl
      (by rw [List.drop_left' (ivkW_length _ _ _ _)]; rfl)
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
      rw [← post40_12, ← post40_13, ← post40_14, ← post40_15, AsmVerif.RiscV.Sym.cells4',
        leLimbsToNat_natToLeLimbs 4 _ (toAffine_lt (leLimbsToNat4_lt _ _ _ _) (leLimbsToNat4_lt _ _ _ _)).1,
        ← ptX_eq, ← ptY_eq, ← ptZ_eq, affineX_mk]
    have hqy : leLimbsToNat [post40_4, post40_5, post40_6, post40_7] =
        affineY (ptX [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], ptY [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11], ptZ [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]) := by
      rw [← post40_16, ← post40_17, ← post40_18, ← post40_19, AsmVerif.RiscV.Sym.cells4',
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
    rw [hacc0, ← ivkFold_eq] at post0_13
    have h1 : post0_0[0]! ≠ 0#64 := by rw [c0_def]; exact fun h => hne (beq_iff_eq.mpr h)
    obtain ⟨L, hL, hw⟩ : ∃ L, ivkFold [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] post30_3 = some L ∧ post0_0 = 1#64 :: L := by
      cases hm : ivkFold [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] post30_3 with
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
    have hRo' : Region out (ivkW [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11] post30_3 [k0, k1, k2, k3] ++
        [replaceByte O[12]! 0 (ivkFlag [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11] post30_3)]) s_19 := by
      rw [ivkFlag_some hL, ← hv3, ivkW_eq, ivkJ_eq, ivkHash_some hL, htc, acc108_0_def,
        jX_eq, jY_eq, jZ_eq, ptX_eq, ptY_eq, ptZ_eq, ptX_eq acc108_0, ptY_eq acc108_0, ptZ_eq acc108_0,
        ← AsmVerif.RiscV.Sym.cells4', ← AsmVerif.RiscV.Sym.cells4', ← AsmVerif.RiscV.Sym.cells4']
      simp only [list12_get_0, list12_get_1, list12_get_2, list12_get_3, list12_get_4, list12_get_5,
        list12_get_6, list12_get_7, list12_get_8, list12_get_9, list12_get_10, list12_get_11,
        List.cons_append, List.nil_append]
      region_at out in s_19 as hRout
      exact hRout
    have hRo := hRo'
    rw [ivkW_congr hch, ivkFlag_congr hch] at hRo
    have hRoP := hRo.sub 0 12 (a := out) (ws := ivkW _ _ _ _) (by simp)
      (by rw [List.drop_zero, List.take_left' (ivkW_length _ _ _ _)])
    have hRoF := hRo.sub 12 1 (a := out + 0x60#64) (ws := [replaceByte _ 0 (ivkFlag _ _)]) rfl
      (by rw [List.drop_left' (ivkW_length _ _ _ _)]; rfl)
    sym_close hk


end Cases.Zip2005
