import Cases.Zip2005.Runtime.Memcpy_d6s0_1010
import Cases.Zip2005.Runtime.Memcpy_d3s0_18
import Cases.Zip2005.Runtime.Memcpy_d7s0_17
import Cases.Zip2005.Runtime.Memcpy_d4s0_18
import Cases.Zip2005.Runtime.Memcpy_d5s0_18
import Cases.Zip2005.Witness.WitnessTailCells
import Cases.Zip2005.Image.F_7801823c
import Cases.Zip2005.Image.Ro

/-!
# The tail of `Zip2005Witness`'s visitor (from `0x78018cc0`)

After `negate` has been read `Ok`: the fields the visitor has collected in its frame and in
callee-saved registers are moved into `out` (byte and halfword stores, twelve `memcpy`s), and
the visitor returns.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
set_option asmverif.sym.foldBytes true in
theorem witness_tail_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (sp out r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word)
    (vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 vs9 vs10 vs11 vra : Word) (Fr O : List Word)
    (hFl : Fr.length = 321) (hOl : O.length = 174)
    (hpc : s.pc = 0x78018cc0#64) (hcode : CodeAt F_7801823c.base F_7801823c.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x1120 sp)
    (hs0 : s.getReg .x8 = out) (hs5 : s.getReg .x21 = sp + 0x9c4#64)
    (hr9 : s.getReg .x9 = r9) (hr18 : s.getReg .x18 = r18) (hr19 : s.getReg .x19 = r19) (hr20 : s.getReg .x20 = r20) (hr22 : s.getReg .x22 = r22) (hr23 : s.getReg .x23 = r23) (hr24 : s.getReg .x24 = r24) (hr25 : s.getReg .x25 = r25) (hr26 : s.getReg .x26 = r26) (hr27 : s.getReg .x27 = r27)
    (hF : Region sp Fr s) (hokF : RegionOk Ro.layout.textLo Ro.layout.textHi sp 334)
    (hS : Region (sp + 0xa08#64) [vs11, vs10, vs9, vs8, vs7, vs6, vs5, vs4, vs3, vs2, vs1, vs0, vra] s)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 174)
    (hdO : Disjoint (sp - 0x1120#64) 882 out 174) (hOlo : out.toNat + 1392 ≤ 0x78000000)
    (hFlo : sp.toNat + 2672 ≤ 0x78000000)
    (hkOk : ∀ t : MachineState, t.pc = vra &&& ~~~1#64 → t.code = s.code →
      t.getReg .x1 = vra → t.getReg .x2 = sp + 0xa70#64 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x8 = vs0 → t.getReg .x9 = vs1 → t.getReg .x18 = vs2 → t.getReg .x19 = vs3 → t.getReg .x20 = vs4 → t.getReg .x21 = vs5 → t.getReg .x22 = vs6 → t.getReg .x23 = vs7 → t.getReg .x24 = vs8 → t.getReg .x25 = vs9 → t.getReg .x26 = vs10 → t.getReg .x27 = vs11 →
      Unchanged [(sp - 0x1120#64, 548), (sp, 334), (out, 174)] s t →
      Region out (tailW Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x1120#64) 548 := hstk.frame 548 (by decide)
  have hmO : out &&& 7#64 = 0#64 := hokO.and7
  have hokOr : RegionOk Ro.layout.roBase Ro.layout.textHi out 174 :=
    ⟨hokO.aligned, hokO.inMem, Or.inl (by simp only [Ro.layout_roBase]; omega)⟩
  have hokF' : RegionOk Ro.layout.textLo Ro.layout.textHi sp 321 := hokF.sub' 0 321 (by decide) (by simp)
  have hokS' : RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0xa08#64) 13 := hokF.sub' 321 13 (by decide) rfl
  have hu := Unchanged.refl [(sp - 0x1120#64, 548), (sp, 334), (out, 174)] s
  rw [AsmVerif.RiscV.Sym.List.eq_map_range Fr hFl] at hF
  rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl] at hO
  sym_exec [memcpy_d6s0_1010_spec, memcpy_d3s0_18_spec, memcpy_d7s0_17_spec,
    memcpy_d4s0_18_spec, memcpy_d5s0_18_spec] 2000
  sym_close hkOk
  have c0 := wt_cell0 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v176 v180 v121_def v122_def v123_def v124_def v125_def v126_def v127_def v128_def v129_def v130_def v131_def v132_def v176_def v180_def
  have c1 := wt_cell1 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 v176 v177 v178 v179 v181 v182 v183 acc138_0_def v176_def v177_def v178_def v179_def v181_def v182_def v183_def
  have c2 := wt_cell2 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c3 := wt_cell3 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c4 := wt_cell4 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c5 := wt_cell5 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c6 := wt_cell6 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c7 := wt_cell7 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c8 := wt_cell8 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c9 := wt_cell9 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c10 := wt_cell10 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c11 := wt_cell11 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c12 := wt_cell12 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c13 := wt_cell13 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c14 := wt_cell14 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c15 := wt_cell15 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c16 := wt_cell16 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c17 := wt_cell17 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c18 := wt_cell18 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c19 := wt_cell19 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c20 := wt_cell20 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c21 := wt_cell21 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c22 := wt_cell22 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c23 := wt_cell23 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c24 := wt_cell24 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c25 := wt_cell25 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c26 := wt_cell26 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c27 := wt_cell27 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c28 := wt_cell28 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c29 := wt_cell29 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c30 := wt_cell30 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c31 := wt_cell31 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c32 := wt_cell32 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c33 := wt_cell33 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c34 := wt_cell34 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c35 := wt_cell35 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c36 := wt_cell36 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c37 := wt_cell37 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c38 := wt_cell38 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c39 := wt_cell39 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c40 := wt_cell40 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c41 := wt_cell41 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c42 := wt_cell42 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c43 := wt_cell43 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c44 := wt_cell44 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c45 := wt_cell45 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c46 := wt_cell46 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c47 := wt_cell47 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c48 := wt_cell48 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c49 := wt_cell49 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c50 := wt_cell50 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c51 := wt_cell51 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c52 := wt_cell52 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c53 := wt_cell53 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c54 := wt_cell54 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c55 := wt_cell55 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c56 := wt_cell56 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c57 := wt_cell57 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c58 := wt_cell58 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c59 := wt_cell59 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c60 := wt_cell60 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c61 := wt_cell61 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c62 := wt_cell62 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c63 := wt_cell63 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c64 := wt_cell64 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c65 := wt_cell65 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c66 := wt_cell66 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c67 := wt_cell67 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c68 := wt_cell68 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c69 := wt_cell69 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c70 := wt_cell70 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c71 := wt_cell71 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c72 := wt_cell72 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c73 := wt_cell73 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c74 := wt_cell74 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c75 := wt_cell75 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c76 := wt_cell76 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c77 := wt_cell77 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c78 := wt_cell78 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c79 := wt_cell79 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c80 := wt_cell80 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c81 := wt_cell81 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c82 := wt_cell82 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c83 := wt_cell83 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c84 := wt_cell84 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c85 := wt_cell85 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c86 := wt_cell86 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c87 := wt_cell87 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c88 := wt_cell88 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c89 := wt_cell89 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c90 := wt_cell90 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c91 := wt_cell91 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c92 := wt_cell92 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c93 := wt_cell93 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c94 := wt_cell94 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c95 := wt_cell95 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c96 := wt_cell96 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c97 := wt_cell97 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c98 := wt_cell98 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c99 := wt_cell99 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c100 := wt_cell100 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c101 := wt_cell101 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c102 := wt_cell102 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c103 := wt_cell103 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c104 := wt_cell104 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c105 := wt_cell105 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c106 := wt_cell106 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c107 := wt_cell107 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c108 := wt_cell108 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c109 := wt_cell109 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c110 := wt_cell110 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c111 := wt_cell111 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c112 := wt_cell112 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c113 := wt_cell113 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c114 := wt_cell114 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c115 := wt_cell115 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c116 := wt_cell116 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c117 := wt_cell117 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c118 := wt_cell118 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c119 := wt_cell119 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c120 := wt_cell120 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c121 := wt_cell121 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c122 := wt_cell122 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c123 := wt_cell123 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c124 := wt_cell124 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c125 := wt_cell125 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c126 := wt_cell126 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c127 := wt_cell127 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc138_0 acc138_0_def
  have c128 := wt_cell128 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v20 v21 v22 v23 v24 v25 v187 v20_def v21_def v22_def v23_def v24_def v25_def v187_def
  have c129 := wt_cell129 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc31_0 v184 v185 v186 v188 v189 v190 v194 acc31_0_def v184_def v185_def v186_def v188_def v189_def v190_def v194_def
  have c130 := wt_cell130 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc31_0 acc31_0_def
  have c131 := wt_cell131 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc31_0 acc31_0_def
  have c132 := wt_cell132 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v32 v33 v34 v35 v36 v37 v195 v32_def v33_def v34_def v35_def v36_def v37_def v195_def
  have c133 := wt_cell133 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc43_0 v191 v192 v193 v196 v197 v202 v203 acc43_0_def v191_def v192_def v193_def v196_def v197_def v202_def v203_def
  have c134 := wt_cell134 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc43_0 acc43_0_def
  have c135 := wt_cell135 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc43_0 acc43_0_def
  have c136 := wt_cell136 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v44 v45 v46 v47 v48 v49 v198 v204 v44_def v45_def v46_def v47_def v48_def v49_def v198_def v204_def
  have c137 := wt_cell137 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc55_0 v198 v199 v200 v201 v205 v210 v211 v212 acc55_0_def v198_def v199_def v200_def v201_def v205_def v210_def v211_def v212_def
  have c138 := wt_cell138 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc55_0 acc55_0_def
  have c139 := wt_cell139 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc55_0 acc55_0_def
  have c140 := wt_cell140 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v56 v57 v58 v59 v60 v61 v206 v213 v56_def v57_def v58_def v59_def v60_def v61_def v206_def v213_def
  have c141 := wt_cell141 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc67_0 v206 v207 v208 v209 v214 v215 v216 v217 v218 acc67_0_def v206_def v207_def v208_def v209_def v214_def v215_def v216_def v217_def v218_def
  have c142 := wt_cell142 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc67_0 acc67_0_def
  have c143 := wt_cell143 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc67_0 acc67_0_def
  have c144 := wt_cell144 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v68 v69 v70 v71 v72 v73 v219 v223 v68_def v69_def v70_def v71_def v72_def v73_def v219_def v223_def
  have c145 := wt_cell145 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc79_0 v219 v220 v221 v222 v224 v225 v226 v231 v232 acc79_0_def v219_def v220_def v221_def v222_def v224_def v225_def v226_def v231_def v232_def
  have c146 := wt_cell146 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc79_0 acc79_0_def
  have c147 := wt_cell147 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc79_0 acc79_0_def
  have c148 := wt_cell148 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v80 v81 v82 v83 v84 v85 v227 v233 v80_def v81_def v82_def v83_def v84_def v85_def v227_def v233_def
  have c149 := wt_cell149 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v86 v87 acc93_0 v227 v228 v229 v230 v234 v235 v240 v86_def v87_def acc93_0_def v227_def v228_def v229_def v230_def v234_def v235_def v240_def
  have c150 := wt_cell150 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v86 v87 acc93_0 v86_def v87_def acc93_0_def
  have c151 := wt_cell151 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v86 v87 acc93_0 v86_def v87_def acc93_0_def
  have c152 := wt_cell152 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v94 v95 v96 v97 v98 v99 v236 v241 v94_def v95_def v96_def v97_def v98_def v99_def v236_def v241_def
  have c153 := wt_cell153 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v100 v101 acc107_0 v236 v237 v238 v239 v242 v243 v248 v100_def v101_def acc107_0_def v236_def v237_def v238_def v239_def v242_def v243_def v248_def
  have c154 := wt_cell154 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v100 v101 acc107_0 v100_def v101_def acc107_0_def
  have c155 := wt_cell155 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v100 v101 acc107_0 v100_def v101_def acc107_0_def
  have c156 := wt_cell156 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v108 v109 v110 v111 v112 v113 v244 v249 v108_def v109_def v110_def v111_def v112_def v113_def v244_def v249_def
  have c157 := wt_cell157 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v114 acc120_0 v244 v245 v246 v247 v250 v251 v252 v114_def acc120_0_def v244_def v245_def v246_def v247_def v250_def v251_def v252_def
  have c158 := wt_cell158 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v114 acc120_0 v114_def acc120_0_def
  have c159 := wt_cell159 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v114 acc120_0 v114_def acc120_0_def
  have c160 := wt_cell160 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 
  have c161 := wt_cell161 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v6 v7 v8 v10 v11 v12 v254 v255 v256 v6_def v7_def v8_def v10_def v11_def v12_def v254_def v255_def v256_def
  have c162 := wt_cell162 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v0 v1 v4 v5 v9 v13 v260 v261 v265 v266 v267 v268 v269 v270 v271 v0_def v1_def v4_def v5_def v9_def v13_def v260_def v261_def v265_def v266_def v267_def v268_def v269_def v270_def v271_def
  have c163 := wt_cell163 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc19_0 v257 v258 v259 v262 v263 v264 acc19_0_def v257_def v258_def v259_def v262_def v263_def v264_def
  have c164 := wt_cell164 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc19_0 acc19_0_def
  have c165 := wt_cell165 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc19_0 v139 v140 v145 v146 v274 acc19_0_def v139_def v140_def v145_def v146_def v274_def
  have c166 := wt_cell166 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v141 v142 v143 v144 v147 v148 v149 v150 v272 v275 v141_def v142_def v143_def v144_def v147_def v148_def v149_def v150_def v272_def v275_def
  have c167 := wt_cell167 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc157_0 v272 v273 v276 acc157_0_def v272_def v273_def v276_def
  have c168 := wt_cell168 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc157_0 acc157_0_def
  have c169 := wt_cell169 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc157_0 v158 v164 v277 v278 acc157_0_def v158_def v164_def v277_def v278_def
  have c170 := wt_cell170 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v159 v160 v161 v162 v163 v165 v166 v167 v168 v169 v279 v289 v290 v291 v292 v293 v159_def v160_def v161_def v162_def v163_def v165_def v166_def v167_def v168_def v169_def v279_def v289_def v290_def v291_def v292_def v293_def
  have c171 := wt_cell171 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc175_0 v279 v280 v281 v282 v283 v284 v285 v286 v287 v288 v294 acc175_0_def v279_def v280_def v281_def v282_def v283_def v284_def v285_def v286_def v287_def v288_def v294_def
  have c172 := wt_cell172 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O acc175_0 acc175_0_def
  have c173 := wt_cell173 Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 O v2 acc175_0 v297 v2_def acc175_0_def v297_def
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < 174 := by simpa using h2
  interval_cases i
  · exact c0.trans (getElem!_pos _ _ _)
  · exact c1.trans (getElem!_pos _ _ _)
  · exact c2.trans (getElem!_pos _ _ _)
  · exact c3.trans (getElem!_pos _ _ _)
  · exact c4.trans (getElem!_pos _ _ _)
  · exact c5.trans (getElem!_pos _ _ _)
  · exact c6.trans (getElem!_pos _ _ _)
  · exact c7.trans (getElem!_pos _ _ _)
  · exact c8.trans (getElem!_pos _ _ _)
  · exact c9.trans (getElem!_pos _ _ _)
  · exact c10.trans (getElem!_pos _ _ _)
  · exact c11.trans (getElem!_pos _ _ _)
  · exact c12.trans (getElem!_pos _ _ _)
  · exact c13.trans (getElem!_pos _ _ _)
  · exact c14.trans (getElem!_pos _ _ _)
  · exact c15.trans (getElem!_pos _ _ _)
  · exact c16.trans (getElem!_pos _ _ _)
  · exact c17.trans (getElem!_pos _ _ _)
  · exact c18.trans (getElem!_pos _ _ _)
  · exact c19.trans (getElem!_pos _ _ _)
  · exact c20.trans (getElem!_pos _ _ _)
  · exact c21.trans (getElem!_pos _ _ _)
  · exact c22.trans (getElem!_pos _ _ _)
  · exact c23.trans (getElem!_pos _ _ _)
  · exact c24.trans (getElem!_pos _ _ _)
  · exact c25.trans (getElem!_pos _ _ _)
  · exact c26.trans (getElem!_pos _ _ _)
  · exact c27.trans (getElem!_pos _ _ _)
  · exact c28.trans (getElem!_pos _ _ _)
  · exact c29.trans (getElem!_pos _ _ _)
  · exact c30.trans (getElem!_pos _ _ _)
  · exact c31.trans (getElem!_pos _ _ _)
  · exact c32.trans (getElem!_pos _ _ _)
  · exact c33.trans (getElem!_pos _ _ _)
  · exact c34.trans (getElem!_pos _ _ _)
  · exact c35.trans (getElem!_pos _ _ _)
  · exact c36.trans (getElem!_pos _ _ _)
  · exact c37.trans (getElem!_pos _ _ _)
  · exact c38.trans (getElem!_pos _ _ _)
  · exact c39.trans (getElem!_pos _ _ _)
  · exact c40.trans (getElem!_pos _ _ _)
  · exact c41.trans (getElem!_pos _ _ _)
  · exact c42.trans (getElem!_pos _ _ _)
  · exact c43.trans (getElem!_pos _ _ _)
  · exact c44.trans (getElem!_pos _ _ _)
  · exact c45.trans (getElem!_pos _ _ _)
  · exact c46.trans (getElem!_pos _ _ _)
  · exact c47.trans (getElem!_pos _ _ _)
  · exact c48.trans (getElem!_pos _ _ _)
  · exact c49.trans (getElem!_pos _ _ _)
  · exact c50.trans (getElem!_pos _ _ _)
  · exact c51.trans (getElem!_pos _ _ _)
  · exact c52.trans (getElem!_pos _ _ _)
  · exact c53.trans (getElem!_pos _ _ _)
  · exact c54.trans (getElem!_pos _ _ _)
  · exact c55.trans (getElem!_pos _ _ _)
  · exact c56.trans (getElem!_pos _ _ _)
  · exact c57.trans (getElem!_pos _ _ _)
  · exact c58.trans (getElem!_pos _ _ _)
  · exact c59.trans (getElem!_pos _ _ _)
  · exact c60.trans (getElem!_pos _ _ _)
  · exact c61.trans (getElem!_pos _ _ _)
  · exact c62.trans (getElem!_pos _ _ _)
  · exact c63.trans (getElem!_pos _ _ _)
  · exact c64.trans (getElem!_pos _ _ _)
  · exact c65.trans (getElem!_pos _ _ _)
  · exact c66.trans (getElem!_pos _ _ _)
  · exact c67.trans (getElem!_pos _ _ _)
  · exact c68.trans (getElem!_pos _ _ _)
  · exact c69.trans (getElem!_pos _ _ _)
  · exact c70.trans (getElem!_pos _ _ _)
  · exact c71.trans (getElem!_pos _ _ _)
  · exact c72.trans (getElem!_pos _ _ _)
  · exact c73.trans (getElem!_pos _ _ _)
  · exact c74.trans (getElem!_pos _ _ _)
  · exact c75.trans (getElem!_pos _ _ _)
  · exact c76.trans (getElem!_pos _ _ _)
  · exact c77.trans (getElem!_pos _ _ _)
  · exact c78.trans (getElem!_pos _ _ _)
  · exact c79.trans (getElem!_pos _ _ _)
  · exact c80.trans (getElem!_pos _ _ _)
  · exact c81.trans (getElem!_pos _ _ _)
  · exact c82.trans (getElem!_pos _ _ _)
  · exact c83.trans (getElem!_pos _ _ _)
  · exact c84.trans (getElem!_pos _ _ _)
  · exact c85.trans (getElem!_pos _ _ _)
  · exact c86.trans (getElem!_pos _ _ _)
  · exact c87.trans (getElem!_pos _ _ _)
  · exact c88.trans (getElem!_pos _ _ _)
  · exact c89.trans (getElem!_pos _ _ _)
  · exact c90.trans (getElem!_pos _ _ _)
  · exact c91.trans (getElem!_pos _ _ _)
  · exact c92.trans (getElem!_pos _ _ _)
  · exact c93.trans (getElem!_pos _ _ _)
  · exact c94.trans (getElem!_pos _ _ _)
  · exact c95.trans (getElem!_pos _ _ _)
  · exact c96.trans (getElem!_pos _ _ _)
  · exact c97.trans (getElem!_pos _ _ _)
  · exact c98.trans (getElem!_pos _ _ _)
  · exact c99.trans (getElem!_pos _ _ _)
  · exact c100.trans (getElem!_pos _ _ _)
  · exact c101.trans (getElem!_pos _ _ _)
  · exact c102.trans (getElem!_pos _ _ _)
  · exact c103.trans (getElem!_pos _ _ _)
  · exact c104.trans (getElem!_pos _ _ _)
  · exact c105.trans (getElem!_pos _ _ _)
  · exact c106.trans (getElem!_pos _ _ _)
  · exact c107.trans (getElem!_pos _ _ _)
  · exact c108.trans (getElem!_pos _ _ _)
  · exact c109.trans (getElem!_pos _ _ _)
  · exact c110.trans (getElem!_pos _ _ _)
  · exact c111.trans (getElem!_pos _ _ _)
  · exact c112.trans (getElem!_pos _ _ _)
  · exact c113.trans (getElem!_pos _ _ _)
  · exact c114.trans (getElem!_pos _ _ _)
  · exact c115.trans (getElem!_pos _ _ _)
  · exact c116.trans (getElem!_pos _ _ _)
  · exact c117.trans (getElem!_pos _ _ _)
  · exact c118.trans (getElem!_pos _ _ _)
  · exact c119.trans (getElem!_pos _ _ _)
  · exact c120.trans (getElem!_pos _ _ _)
  · exact c121.trans (getElem!_pos _ _ _)
  · exact c122.trans (getElem!_pos _ _ _)
  · exact c123.trans (getElem!_pos _ _ _)
  · exact c124.trans (getElem!_pos _ _ _)
  · exact c125.trans (getElem!_pos _ _ _)
  · exact c126.trans (getElem!_pos _ _ _)
  · exact c127.trans (getElem!_pos _ _ _)
  · exact c128.trans (getElem!_pos _ _ _)
  · exact c129.trans (getElem!_pos _ _ _)
  · exact c130.trans (getElem!_pos _ _ _)
  · exact c131.trans (getElem!_pos _ _ _)
  · exact c132.trans (getElem!_pos _ _ _)
  · exact c133.trans (getElem!_pos _ _ _)
  · exact c134.trans (getElem!_pos _ _ _)
  · exact c135.trans (getElem!_pos _ _ _)
  · exact c136.trans (getElem!_pos _ _ _)
  · exact c137.trans (getElem!_pos _ _ _)
  · exact c138.trans (getElem!_pos _ _ _)
  · exact c139.trans (getElem!_pos _ _ _)
  · exact c140.trans (getElem!_pos _ _ _)
  · exact c141.trans (getElem!_pos _ _ _)
  · exact c142.trans (getElem!_pos _ _ _)
  · exact c143.trans (getElem!_pos _ _ _)
  · exact c144.trans (getElem!_pos _ _ _)
  · exact c145.trans (getElem!_pos _ _ _)
  · exact c146.trans (getElem!_pos _ _ _)
  · exact c147.trans (getElem!_pos _ _ _)
  · exact c148.trans (getElem!_pos _ _ _)
  · exact c149.trans (getElem!_pos _ _ _)
  · exact c150.trans (getElem!_pos _ _ _)
  · exact c151.trans (getElem!_pos _ _ _)
  · exact c152.trans (getElem!_pos _ _ _)
  · exact c153.trans (getElem!_pos _ _ _)
  · exact c154.trans (getElem!_pos _ _ _)
  · exact c155.trans (getElem!_pos _ _ _)
  · exact c156.trans (getElem!_pos _ _ _)
  · exact c157.trans (getElem!_pos _ _ _)
  · exact c158.trans (getElem!_pos _ _ _)
  · exact c159.trans (getElem!_pos _ _ _)
  · exact c160.trans (getElem!_pos _ _ _)
  · exact c161.trans (getElem!_pos _ _ _)
  · exact c162.trans (getElem!_pos _ _ _)
  · exact c163.trans (getElem!_pos _ _ _)
  · exact c164.trans (getElem!_pos _ _ _)
  · exact c165.trans (getElem!_pos _ _ _)
  · exact c166.trans (getElem!_pos _ _ _)
  · exact c167.trans (getElem!_pos _ _ _)
  · exact c168.trans (getElem!_pos _ _ _)
  · exact c169.trans (getElem!_pos _ _ _)
  · exact c170.trans (getElem!_pos _ _ _)
  · exact c171.trans (getElem!_pos _ _ _)
  · exact c172.trans (getElem!_pos _ _ _)
  · exact c173.trans (getElem!_pos _ _ _)

end Cases.Zip2005
