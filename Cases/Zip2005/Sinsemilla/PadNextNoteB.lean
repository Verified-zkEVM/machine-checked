import Cases.Zip2005.Sinsemilla.PadNoteDefs
import Cases.Zip2005.Sinsemilla.PadNoteKit
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Image.F_78021720
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
set_option machineChecked.sym.foldBytes true in
theorem pad_next_note_b_spec {Gd : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra spn sp iter v : Word)
    (J G K R Q : List Word)
    (hGl : G.length = 4) (hKl : K.length = 4) (hRl : R.length = 4) (hQl : Q.length = 4) (j : Word)
    (m : Nat) (hm1 : 1 ≤ m) (hm255 : m ≤ 255) (hK : BitVec 8)
    (hhK : BitVec.ofNat 8 (m % 8) = hK)
    (hpc : s.pc = 0x78021720#64) (hcode : CodeAt F_78021720.base F_78021720.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x180 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter (noteBlkB sp J j (sp + (18446744073709551440#64 + BitVec.ofNat 64 (m / 8))) hK (BitVec.ofNat 64 (256 + m))) s)
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
      Region iter (noteBlkB sp J j (sp + 18446744073709551440#64 + BitVec.ofNat 64 ((m + 1) / 8))
        (BitVec.ofNat 8 ((m + 1) % 8)) (BitVec.ofNat 64 (256 + m + 1))) t →
      t.getReg .x10 = bw (noteBit G K v R Q (256 + m)) → SafeN Gd n P t) :
    SafeN Gd n P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (spn - 0x180#64) 48 := hstk.frame 48 (by decide)
  have hu := Unchanged.refl [(spn - 0x180#64, 48), (iter, 18)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (spn - 0x180#64) 48 s
  unfold noteBlkB noteW6 noteW7 noteW8 noteW9 at hI
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
  -- the chain state byte (1: `Some(Empty)` not yet taken), the five heads and five end heads,
  -- as the executor reads them
  have hTag : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[4]! 0 2#8) 1 (BitVec.truncate 8 (sp + 18446744073709551440#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 48))) 0) = 2#64 := by
    simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte]
    rfl
  have hHdG : BitVec.zeroExtend 64 (extractByte (replaceHalfword (replaceHalfword (replaceHalfword (replaceByte (replaceByte J[5]! 0 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 56))) 1 0#8) 1 (BitVec.truncate 16 (sp + 18446744073709551440#64))) 2 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 16))) 3 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 32))) 1) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceHalfword_ne, extractByte_replaceByte]
    rfl
  have hHdK : BitVec.zeroExtend 64 (extractByte (replaceWord32 (replaceByte (replaceByte (replaceByte (replaceByte J[7]! 0 (BitVec.truncate 8 ((sp + (18446744073709551440#64 + BitVec.ofNat 64 (m / 8))) >>> 40))) 1 (BitVec.truncate 8 ((sp + (18446744073709551440#64 + BitVec.ofNat 64 (m / 8))) >>> 48))) 2 (BitVec.truncate 8 ((sp + (18446744073709551440#64 + BitVec.ofNat 64 (m / 8))) >>> 56))) 3 hK) 1 (BitVec.truncate 32 (sp + 18446744073709551472#64))) 3) = BitVec.zeroExtend 64 hK := by
    simp (disch := decide) only [extractByte_replaceWord32_ne, extractByte_replaceByte]
  have hHdV : BitVec.zeroExtend 64 (extractByte (replaceHalfword (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[9]! 1 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 32))) 2 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 40))) 3 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 48))) 4 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 56))) 0 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 24))) 5 0#8) 3 (BitVec.truncate 16 (sp + 18446744073709551480#64))) 5) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceHalfword_ne, extractByte_replaceByte]
    rfl
  have hHdR : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[2]! 3 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 40))) 0 0#8) 1 (BitVec.truncate 8 (sp + 18446744073709551512#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 48))) 0) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte]
    rfl
  have hHdQ : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[13]! 4 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 48))) 0 0#8) 1 (BitVec.truncate 8 (sp + 18446744073709551544#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 16))) 0) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte]
    rfl
  have hEhG : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceHalfword J[6]! 0 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 48))) 2 0#8) 3 (BitVec.truncate 8 (sp + (18446744073709551440#64 + BitVec.ofNat 64 (m / 8))))) 4 (BitVec.truncate 8 ((sp + (18446744073709551440#64 + BitVec.ofNat 64 (m / 8))) >>> 8))) 5 (BitVec.truncate 8 ((sp + (18446744073709551440#64 + BitVec.ofNat 64 (m / 8))) >>> 16))) 6 (BitVec.truncate 8 ((sp + (18446744073709551440#64 + BitVec.ofNat 64 (m / 8))) >>> 24))) 7 (BitVec.truncate 8 ((sp + (18446744073709551440#64 + BitVec.ofNat 64 (m / 8))) >>> 32))) 2) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte]
    rfl
  have hEhK : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceWord32 J[8]! 0 (BitVec.truncate 32 ((sp + 18446744073709551472#64) >>> 32))) 4 0#8) 5 (BitVec.truncate 8 (sp + 18446744073709551472#64))) 6 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 16))) 4) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte]
    rfl
  have hEhV : BitVec.zeroExtend 64 (extractByte (replaceHalfword (replaceHalfword (replaceByte (replaceHalfword J[10]! 2 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 48))) 6 0#8) 0 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 16))) 1 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 32))) 6) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceHalfword_ne, extractByte_replaceByte]
    rfl
  have hEhR : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 56))) 1 0#8) 1) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceByte]
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
  -- `pk★_d`'s cursor: its start pointer from the block's bytes, not null
  all_goals (have hv117 : v117 = sp + (18446744073709551440#64 + BitVec.ofNat 64 (m / 8)) := by rw [← v117_def, ← v116_def, ← v115_def, ← v114_def, ← v113_def, ← v112_def, ← v111_def, ← v110_def, ← v109_def, ← v108_def, ← v107_def, ← v106_def, ← v105_def, ← v104_def, ← v86_def, ← v87_def, ← v88_def, ← v89_def, ← v90_def, ← v91_def, ← v92_def, ← v93_def]; exact bytes_word_trunc _)
  all_goals (first
    | (exfalso; rw [hv117] at hbr118; simp only [beq_iff_eq] at hbr118; have := congrArg BitVec.toNat hbr118; rw [BitVec.toNat_add, BitVec.toNat_add, Bn.toNat_ofNat' (m / 8)] at this; simp only [BitVec.toNat_ofNat] at this; omega)
    | skip)
  -- its end from the two 32-bit words; the range is not exhausted
  all_goals (have hv122 : v122 = sp + 18446744073709551472#64 := by rw [← v122_def, ← v120_def, ← v98_def, ← v96_def]; exact words32_word_trunc _)
  all_goals (have hpe : sp + (18446744073709551440#64 + BitVec.ofNat 64 (m / 8)) ≠ sp + 18446744073709551472#64 := by intro h; have := congrArg BitVec.toNat h; rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, Bn.toNat_ofNat' (m / 8)] at this; simp only [BitVec.toNat_ofNat] at this; omega)
  all_goals (have hv129 : v129 = 0#64 := by rw [← v129_def, ← v128_def, ← v123_def, hv117, hv122]; exact seqz_or_xor _ _ _ hpe)
  all_goals (first
    | (exfalso; rw [hv129] at hbr130; exact absurd (by decide) hbr130)
    | skip)
  -- the stepped pointer is not null either
  all_goals (have hv134 : v134 = sp + 18446744073709551440#64 + BitVec.ofNat 64 ((m + 1) / 8) := by rw [← v134_def, ← v133_def, ← v131_def, ← v94_def, extractByte_zext8 _ _ (by decide), if_pos rfl, ← hhK, ptr8Step' _ (Nat.mod_lt _ (by decide)), hv117, ptr8Next])
  all_goals (first
    | (exfalso; rw [hv134] at hbr135; simp only [beq_iff_eq] at hbr135; have := congrArg BitVec.toNat hbr135; rw [BitVec.toNat_add, BitVec.toNat_add, Bn.toNat_ofNat' ((m + 1) / 8)] at this; simp only [BitVec.toNat_ofNat] at this; omega)
    | skip)
  -- the live path: the byte load through the reassembled pointer, now the pointer itself
  replace v117_def : sp + (18446744073709551440#64 + BitVec.ofNat 64 (m / 8)) = v117 := hv117.symm
  rw [← v117_def] at hx27
  have hunch0 : True ∧ Unchanged [(spn - 0x180#64, 48), (iter, 18)] s s_154 := ⟨trivial, hunch⟩
  clear hunch
  have hcode154 : s_154.code = s.code := hcode
  have hu2 := Unchanged.refl [(spn - 0x180#64, 48), (iter, 18)] s_154
  sym_exec []
  -- the live path's result, as the executor left it
  have hk' : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s_154.code →
      Unchanged [(spn - 0x180#64, 48), (iter, 18)] s_154 t →
      Region iter [0#64, j, 255#64, sp + 18446744073709551480#64, replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[2]! 3 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 40))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551512#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 48)), replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 56))) 1 (BitVec.truncate 8 0#64), replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[4]! 0 2#8) 1 (BitVec.truncate 8 (sp + 18446744073709551440#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 48)), replaceHalfword (replaceHalfword (replaceHalfword (replaceByte (replaceByte J[5]! 0 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 56))) 1 0#8) 1 (BitVec.truncate 16 (sp + 18446744073709551440#64))) 2 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 16))) 3 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 32)), v151, v152, replaceByte (replaceByte (replaceByte (replaceByte (replaceWord32 J[8]! 0 (BitVec.truncate 32 ((sp + 18446744073709551472#64) >>> 32))) 4 (BitVec.truncate 8 0#64)) 5 (BitVec.truncate 8 (sp + 18446744073709551472#64))) 6 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 16)), replaceHalfword (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[9]! 1 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 32))) 2 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 40))) 3 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 48))) 4 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 56))) 0 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 24))) 5 (BitVec.truncate 8 0#64)) 3 (BitVec.truncate 16 (sp + 18446744073709551480#64)), replaceHalfword (replaceHalfword (replaceByte (replaceHalfword J[10]! 2 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 48))) 6 (BitVec.truncate 8 0#64)) 0 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 16))) 1 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 32)), 255#64, sp + 18446744073709551512#64, replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[13]! 4 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 48))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551544#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 16)), replaceByte (replaceByte J[14]! 0 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 56))) 1 (BitVec.truncate 8 0#64), v30 + 1#64] t →
      t.getReg .x10 = v8 → SafeN Gd n P t := by
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 (h3.trans hcode154) (hunch0.2.trans h4) (Region.of_eq h5 ?_) ?_
    · simp only [noteBlkB, List.cons.injEq, and_true, true_and]
      refine ⟨?_, ?_, ?_⟩
      · rw [← v151_def, ← v150_def, ← v149_def, ← v148_def, ← v141_def, ← v145_def, ← v146_def,
          ← v147_def, ← v140_def, hv134]
        apply word_ext
        intro i hi
        interval_cases i
        all_goals simp (disch := decide) only [noteW8, extractByte_replaceByte, extractByte_replaceByte_ne]
      · rw [← v152_def, ← v144_def, ← v143_def, ← v142_def, ← v136_def, ← v131_def, ← v94_def,
          extractByte_zext8 _ _ (by decide), if_pos rfl, ← hhK, head8Next' _ (Nat.mod_lt _ (by decide)),
          Nat.mod_add_mod, ← v137_def, ← v138_def, ← v139_def, hv134]
        apply word_ext
        intro i hi
        interval_cases i
        all_goals simp (disch := decide) only [noteW9, extractByte_replaceByte, extractByte_replaceByte_ne,
          extractByte_replaceWord32_ne, extractByte_replaceWord32_in]
      · rw [← v30_def]; exact lenNext _
    · rw [h6, ← v8_def, ← v2_def, ← v0_def, ← v1_def, ← v131_def, ← v94_def, extractByte_zext8 _ _ (by decide),
        if_pos rfl, ← hhK, noteBit, if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
      exact bit8Next7' K m
  sym_close hk'

end Cases.Zip2005
