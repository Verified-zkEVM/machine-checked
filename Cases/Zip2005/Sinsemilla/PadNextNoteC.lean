import Cases.Zip2005.Sinsemilla.PadNoteDefs
import Cases.Zip2005.Sinsemilla.PadNoteKit
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Image.F_78021720
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
set_option asmverif.sym.foldBytes true in
theorem pad_next_note_c_spec {Gd : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra spn sp iter v : Word)
    (J G K R Q : List Word)
    (hGl : G.length = 4) (hKl : K.length = 4) (hRl : R.length = 4) (hQl : Q.length = 4) (j : Word)
    (m : Nat) (hm1 : 1 ≤ m) (hm63 : m ≤ 63) (hV : BitVec 8)
    (hhV : BitVec.ofNat 8 (m % 8) = hV)
    (hpc : s.pc = 0x78021720#64) (hcode : CodeAt F_78021720.base F_78021720.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x180 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter (noteBlkC sp J j (sp + (18446744073709551472#64 + BitVec.ofNat 64 (m / 8))) hV (BitVec.ofNat 64 (512 + m))) s)
    (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi iter 18)
    (hGr : Region (sp + 18446744073709551408#64) G s) (hokG : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551408#64) 4)
    (hKr : Region (sp + 18446744073709551440#64) K s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551440#64) 4)
    (hVr : Region (sp + 18446744073709551472#64) [v] s) (hokV : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551472#64) 1)
    (hRr : Region (sp + 18446744073709551480#64) R s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551480#64) 4)
    (hQr : Region (sp + 18446744073709551512#64) Q s) (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551512#64) 4)
    (hdjIG : Disjoint iter 18 (sp + 18446744073709551408#64) 4) (hdjIK : Disjoint iter 18 (sp + 18446744073709551440#64) 4)
    (hdjIV : Disjoint iter 18 (sp + 18446744073709551472#64) 1) (hdjIR : Disjoint iter 18 (sp + 18446744073709551480#64) 4)
    (hdjIQ : Disjoint iter 18 (sp + 18446744073709551512#64) 4)
    (hdjS : Disjoint (spn - 0x180#64) 48 iter 18)
    (hdjSG : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551408#64) 4) (hdjSK : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551440#64) 4)
    (hdjSV : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551472#64) 1) (hdjSR : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551480#64) 4)
    (hdjSQ : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551512#64) 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x180#64, 48), (iter, 18)] s t →
      Region iter (noteBlkC sp J j (sp + 18446744073709551472#64 + BitVec.ofNat 64 ((m + 1) / 8))
        (BitVec.ofNat 8 ((m + 1) % 8)) (BitVec.ofNat 64 (512 + m + 1))) t →
      t.getReg .x10 = bw (noteBit G K v R Q (512 + m)) → SafeN Gd n P t) :
    SafeN Gd n P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (spn - 0x180#64) 48 := hstk.frame 48 (by decide)
  have hu := Unchanged.refl [(spn - 0x180#64, 48), (iter, 18)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (spn - 0x180#64) 48 s
  unfold noteBlkC noteW6 noteW7 noteW8 noteW9 noteW10 noteW11 at hI
  have hG4 : [G[0]!, G[1]!, G[2]!, G[3]!] = G := by
    match G, hGl with
    | [_, _, _, _], _ => rfl
  have hK4 : [K[0]!, K[1]!, K[2]!, K[3]!] = K := by
    match K, hKl with
    | [_, _, _, _], _ => rfl
  have hR4 : [R[0]!, R[1]!, R[2]!, R[3]!] = R := by
    match R, hRl with
    | [_, _, _, _], _ => rfl
  have hQ4 : [Q[0]!, Q[1]!, Q[2]!, Q[3]!] = Q := by
    match Q, hQl with
    | [_, _, _, _], _ => rfl
  -- the chain state byte, the five heads and five end heads, as the executor reads them
  have hTag : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[4]! 0 3#8) 1 (BitVec.truncate 8 (sp + 18446744073709551440#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 48))) 0) = 3#64 := by
    simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte]
    rfl
  have hHdG : BitVec.zeroExtend 64 (extractByte (replaceHalfword (replaceHalfword (replaceHalfword (replaceByte (replaceByte J[5]! 0 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 56))) 1 0#8) 1 (BitVec.truncate 16 (sp + 18446744073709551440#64))) 2 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 16))) 3 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 32))) 1) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceHalfword_ne, extractByte_replaceByte]
    rfl
  have hEhG : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceHalfword J[6]! 0 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 48))) 2 0#8) 3 (BitVec.truncate 8 (sp + 18446744073709551472#64))) 4 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 8))) 5 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 16))) 6 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 24))) 7 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 32))) 2) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte]
    rfl
  have hHdK : BitVec.zeroExtend 64 (extractByte (replaceWord32 (replaceByte (replaceByte (replaceByte (replaceByte J[7]! 0 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 40))) 1 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 48))) 2 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 56))) 3 0#8) 1 (BitVec.truncate 32 (sp + 18446744073709551472#64))) 3) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceWord32_ne, extractByte_replaceByte]
    rfl
  have hEhK : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceWord32 J[8]! 0 (BitVec.truncate 32 ((sp + 18446744073709551472#64) >>> 32))) 4 0#8) 5 (BitVec.truncate 8 (sp + (18446744073709551472#64 + BitVec.ofNat 64 (m / 8))))) 6 (BitVec.truncate 8 ((sp + (18446744073709551472#64 + BitVec.ofNat 64 (m / 8))) >>> 8))) 7 (BitVec.truncate 8 ((sp + (18446744073709551472#64 + BitVec.ofNat 64 (m / 8))) >>> 16))) 4) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte]
    rfl
  have hHdV : BitVec.zeroExtend 64 (extractByte (replaceHalfword (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[9]! 0 (BitVec.truncate 8 ((sp + (18446744073709551472#64 + BitVec.ofNat 64 (m / 8))) >>> 24))) 1 (BitVec.truncate 8 ((sp + (18446744073709551472#64 + BitVec.ofNat 64 (m / 8))) >>> 32))) 2 (BitVec.truncate 8 ((sp + (18446744073709551472#64 + BitVec.ofNat 64 (m / 8))) >>> 40))) 3 (BitVec.truncate 8 ((sp + (18446744073709551472#64 + BitVec.ofNat 64 (m / 8))) >>> 48))) 4 (BitVec.truncate 8 ((sp + (18446744073709551472#64 + BitVec.ofNat 64 (m / 8))) >>> 56))) 5 hV) 3 (BitVec.truncate 16 (sp + 18446744073709551480#64))) 5) = BitVec.zeroExtend 64 hV := by
    simp (disch := decide) only [extractByte_replaceHalfword_ne, extractByte_replaceByte]
  have hEhV : BitVec.zeroExtend 64 (extractByte (replaceHalfword (replaceHalfword (replaceByte (replaceHalfword J[10]! 2 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 48))) 6 0#8) 0 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 16))) 1 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 32))) 6) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceHalfword_ne, extractByte_replaceByte]
    rfl
  have hHdR : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[2]! 3 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 40))) 0 0#8) 1 (BitVec.truncate 8 (sp + 18446744073709551512#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 48))) 0) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte]
    rfl
  have hEhR : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 56))) 1 0#8) 1) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceByte]
    rfl
  have hHdQ : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[13]! 4 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 48))) 0 0#8) 1 (BitVec.truncate 8 (sp + 18446744073709551544#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 16))) 0) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte]
    rfl
  have hEhQ : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte J[14]! 0 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 56))) 1 0#8) 1) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceByte]
    rfl
  have hpR0 : (sp + 18446744073709551480#64 == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  have hpQ0 : (sp + 18446744073709551512#64 == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add] at this
    simp only [BitVec.toNat_ofNat] at this
    omega
  sym_exec []
  -- `v`'s cursor: its start pointer from the block's bytes, not null
  all_goals (have hv91 : v91 = sp + (18446744073709551472#64 + BitVec.ofNat 64 (m / 8)) := by rw [← v91_def, ← v90_def, ← v89_def, ← v88_def, ← v87_def, ← v86_def, ← v85_def, ← v84_def, ← v83_def, ← v82_def, ← v81_def, ← v80_def, ← v79_def, ← v78_def, ← v56_def, ← v57_def, ← v58_def, ← v59_def, ← v60_def, ← v61_def, ← v62_def, ← v63_def]; exact bytes_word_trunc _)
  all_goals (first
    | (exfalso; rw [hv91] at hbr92; simp only [beq_iff_eq] at hbr92; have := congrArg BitVec.toNat hbr92; rw [BitVec.toNat_add, BitVec.toNat_add, Bn.toNat_ofNat' (m / 8)] at this; simp only [BitVec.toNat_ofNat] at this; omega)
    | skip)
  -- its end from the four halfwords; the range is not exhausted
  all_goals (have hv102 : v102 = sp + 18446744073709551480#64 := by rw [← v102_def, ← v101_def, ← v100_def, ← v98_def, ← v96_def, ← v94_def, ← v72_def, ← v70_def, ← v68_def, ← v66_def]; exact halfwords_word_trunc _)
  all_goals (have hpe : sp + (18446744073709551472#64 + BitVec.ofNat 64 (m / 8)) ≠ sp + 18446744073709551480#64 := by intro h; have := congrArg BitVec.toNat h; rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, Bn.toNat_ofNat' (m / 8)] at this; simp only [BitVec.toNat_ofNat] at this; omega)
  all_goals (have hv109 : v109 = 0#64 := by rw [← v109_def, ← v108_def, ← v103_def, hv91, hv102]; exact seqz_or_xor _ _ _ hpe)
  all_goals (first
    | (exfalso; rw [hv109] at hbr110; exact absurd (by decide) hbr110)
    | skip)
  -- the stepped pointer is not null either
  all_goals (have hv114 : v114 = sp + 18446744073709551472#64 + BitVec.ofNat 64 ((m + 1) / 8) := by rw [← v114_def, ← v113_def, ← v111_def, ← v64_def, extractByte_zext8 _ _ (by decide), if_pos rfl, ← hhV, ptr8Step' _ (Nat.mod_lt _ (by decide)), hv91, ptr8Next])
  all_goals (first
    | (exfalso; rw [hv114] at hbr115; simp only [beq_iff_eq] at hbr115; have := congrArg BitVec.toNat hbr115; rw [BitVec.toNat_add, BitVec.toNat_add, Bn.toNat_ofNat' ((m + 1) / 8)] at this; simp only [BitVec.toNat_ofNat] at this; omega)
    | skip)
  -- the live path: the byte load through the reassembled pointer, now the pointer itself
  replace v91_def : sp + (18446744073709551472#64 + BitVec.ofNat 64 (m / 8)) = v91 := hv91.symm
  rw [← v91_def] at hx27
  have hunch0 : True ∧ Unchanged [(spn - 0x180#64, 48), (iter, 18)] s s_134 := ⟨trivial, hunch⟩
  clear hunch
  have hcode134 : s_134.code = s.code := hcode
  have hu2 := Unchanged.refl [(spn - 0x180#64, 48), (iter, 18)] s_134
  sym_exec []
  -- the live path's result, as the executor left it
  have hk' : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s_134.code →
      Unchanged [(spn - 0x180#64, 48), (iter, 18)] s_134 t →
      Region iter [0#64, j, 255#64, sp + 18446744073709551480#64, replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[2]! 3 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 40))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551512#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 48)), replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 56))) 1 (BitVec.truncate 8 0#64), replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[4]! 0 3#8) 1 (BitVec.truncate 8 (sp + 18446744073709551440#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 48)), replaceHalfword (replaceHalfword (replaceHalfword (replaceByte (replaceByte J[5]! 0 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 56))) 1 0#8) 1 (BitVec.truncate 16 (sp + 18446744073709551440#64))) 2 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 16))) 3 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 32)), replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceHalfword J[6]! 0 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 48))) 2 0#8) 3 (BitVec.truncate 8 (sp + 18446744073709551472#64))) 4 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 8))) 5 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 16))) 6 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 24))) 7 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 32)), replaceWord32 (replaceByte (replaceByte (replaceByte (replaceByte J[7]! 0 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 40))) 1 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 48))) 2 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 56))) 3 0#8) 1 (BitVec.truncate 32 (sp + 18446744073709551472#64)), v130, v132, replaceHalfword (replaceHalfword (replaceByte (replaceHalfword J[10]! 2 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 48))) 6 (BitVec.truncate 8 0#64)) 0 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 16))) 1 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 32)), 255#64, sp + 18446744073709551512#64, replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[13]! 4 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 48))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551544#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 16)), replaceByte (replaceByte J[14]! 0 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 56))) 1 (BitVec.truncate 8 0#64), v30 + 1#64] t →
      t.getReg .x10 = v8 → SafeN Gd n P t := by
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 (h3.trans hcode134) (hunch0.2.trans h4) (Region.of_eq h5 ?_) ?_
    · simp only [noteBlkC, List.cons.injEq, and_true, true_and]
      refine ⟨?_, ?_, ?_⟩
      · rw [← v130_def, ← v129_def, ← v128_def, ← v126_def, ← v127_def, hv114]
        apply word_ext
        intro i hi
        interval_cases i
        all_goals simp (disch := decide) only [noteW10, extractByte_replaceByte, extractByte_replaceByte_ne,
          extractByte_replaceWord32_in]
      · rw [← v132_def, ← v131_def, ← v124_def, ← v123_def, ← v122_def, ← v121_def, ← v116_def,
          ← v111_def, ← v64_def, extractByte_zext8 _ _ (by decide), if_pos rfl, ← hhV,
          head8Next' _ (Nat.mod_lt _ (by decide)), Nat.mod_add_mod, ← v117_def, ← v118_def, ← v119_def,
          ← v120_def, ← v125_def, hv114]
        apply word_ext
        intro i hi
        interval_cases i
        all_goals simp (disch := decide) only [noteW11, extractByte_replaceByte, extractByte_replaceByte_ne,
          extractByte_replaceHalfword_ne, extractByte_replaceHalfword_in]
      · rw [← v30_def]; exact lenNext _
    · rw [h6, ← v8_def, ← v2_def, ← v0_def, ← v1_def, ← v111_def, ← v64_def, extractByte_zext8 _ _ (by decide),
        if_pos rfl, ← hhV, shift8Amt7' _ (Nat.mod_lt _ (by decide)), show m / 8 / 8 = 0 by omega,
        show ([v] : List Word)[0]! = v from rfl, noteBit, if_neg (by omega), if_neg (by omega),
        if_pos (by omega), Nat.add_sub_cancel_left, byteBit _ _ _ (Nat.mod_lt _ (by decide)),
        show 8 * (m / 8 % 8) + m % 8 = m by omega]
      exact bitVal _
  sym_close hk'

end Cases.Zip2005
