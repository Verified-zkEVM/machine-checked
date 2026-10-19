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
theorem pad_next_note_e_spec {Gd : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra spn sp iter v : Word)
    (J G K R Q : List Word)
    (hGl : G.length = 4) (hKl : K.length = 4) (hRl : R.length = 4) (hQl : Q.length = 4) (j : Word)
    (m : Nat) (hm1 : 1 ≤ m) (hm254 : m ≤ 254) (hQ : BitVec 8)
    (hhQ : BitVec.ofNat 8 (m % 64) = hQ)
    (hpc : s.pc = 0x78021720#64) (hcode : CodeAt F_78021720.base F_78021720.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x180 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter (noteBlkE sp J j (BitVec.ofNat 64 (255 - m)) (sp + (18446744073709551512#64 + BitVec.ofNat 64 (8 * (m / 64)))) hQ (BitVec.ofNat 64 (831 + m))) s)
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
      Region iter (noteBlkE sp J j (BitVec.ofNat 64 (255 - (m + 1)))
        (sp + 18446744073709551512#64 + BitVec.ofNat 64 (8 * ((m + 1) / 64))) (BitVec.ofNat 8 ((m + 1) % 64))
        (BitVec.ofNat 64 (831 + m + 1))) t →
      t.getReg .x10 = bw (noteBit G K v R Q (831 + m)) → SafeN Gd n P t) :
    SafeN Gd n P s := by
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (spn - 0x180#64) 48 := hstk.frame 48 (by decide)
  have hu := Unchanged.refl [(spn - 0x180#64, 48), (iter, 18)] s
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (spn - 0x180#64) 48 s
  unfold noteBlkE noteW6 noteW7 noteW8 noteW9 noteW10 noteW11 at hI
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
  have hTag : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[4]! 0 5#8) 1 (BitVec.truncate 8 (sp + 18446744073709551440#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 48))) 0) = 5#64 := by
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
  have hEhK : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceWord32 J[8]! 0 (BitVec.truncate 32 ((sp + 18446744073709551472#64) >>> 32))) 4 0#8) 5 (BitVec.truncate 8 (sp + 18446744073709551480#64))) 6 (BitVec.truncate 8 ((sp + 18446744073709551480#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551480#64) >>> 16))) 4) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceByte_ne, extractByte_replaceByte]
    rfl
  have hHdV : BitVec.zeroExtend 64 (extractByte (replaceHalfword (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[9]! 0 (BitVec.truncate 8 ((sp + 18446744073709551480#64) >>> 24))) 1 (BitVec.truncate 8 ((sp + 18446744073709551480#64) >>> 32))) 2 (BitVec.truncate 8 ((sp + 18446744073709551480#64) >>> 40))) 3 (BitVec.truncate 8 ((sp + 18446744073709551480#64) >>> 48))) 4 (BitVec.truncate 8 ((sp + 18446744073709551480#64) >>> 56))) 5 0#8) 3 (BitVec.truncate 16 (sp + 18446744073709551480#64))) 5) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceHalfword_ne, extractByte_replaceByte]
    rfl
  have hEhV : BitVec.zeroExtend 64 (extractByte (replaceHalfword (replaceHalfword (replaceByte (replaceHalfword J[10]! 2 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 48))) 6 0#8) 0 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 16))) 1 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 32))) 6) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceHalfword_ne, extractByte_replaceByte]
    rfl
  have hHdR : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[2]! 3 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 40))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551512#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 48))) 0 63#8) 0) = 63#64 := by
    simp (disch := decide) only [extractByte_replaceByte]
    rfl
  have hEhR : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 56))) 1 0#8) 1) = 0#64 := by
    simp (disch := decide) only [extractByte_replaceByte]
    rfl
  have hHdQ : BitVec.zeroExtend 64 (extractByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[13]! 4 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 48))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551544#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 16))) 0 hQ) 0) = BitVec.zeroExtend 64 hQ := by
    simp (disch := decide) only [extractByte_replaceByte]
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
  -- `ψ`'s cursor: its pointer not null, its count not zero
  all_goals (first
    | (exfalso; rw [← v19_def] at hbr33; simp only [beq_iff_eq] at hbr33; have := congrArg BitVec.toNat hbr33; rw [BitVec.toNat_add, BitVec.toNat_add, Bn.toNat_ofNat' (8 * (m / 64))] at this; simp only [BitVec.toNat_ofNat] at this; omega)
    | skip)
  all_goals (first
    | (exfalso; rw [← v18_def] at hbr34; simp only [beq_iff_eq] at hbr34; have := congrArg BitVec.toNat hbr34; rw [Bn.toNat_ofNat'] at this; simp only [BitVec.toNat_ofNat] at this; omega)
    | skip)
  -- its end from the block's bytes; the range is not exhausted
  all_goals (have hv48 : v48 = sp + 18446744073709551544#64 := by rw [← v48_def, ← v47_def, ← v46_def, ← v45_def, ← v44_def, ← v43_def, ← v42_def, ← v41_def, ← v40_def, ← v39_def, ← v38_def, ← v37_def, ← v36_def, ← v35_def, ← v21_def, ← v22_def, ← v23_def, ← v24_def, ← v25_def, ← v26_def, ← v27_def, ← v28_def]; exact bytes_word_trunc _)
  all_goals (have hpe : sp + (18446744073709551512#64 + BitVec.ofNat 64 (8 * (m / 64))) ≠ sp + 18446744073709551544#64 := by intro h; have := congrArg BitVec.toNat h; rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, Bn.toNat_ofNat' (8 * (m / 64))] at this; simp only [BitVec.toNat_ofNat] at this; omega)
  all_goals (have hv53 : v53 = 0#64 := by rw [← v53_def, ← v52_def, ← v49_def, ← v19_def, hv48]; exact seqz_or_xor _ _ _ hpe)
  all_goals (first
    | (exfalso; rw [hv53] at hbr56; exact absurd (by decide) hbr56)
    | skip)
  -- the stepped pointer is not null either
  all_goals (have hv61 : v61 = sp + 18446744073709551512#64 + BitVec.ofNat 64 (8 * ((m + 1) / 64)) := by rw [← v61_def, ← v60_def, ← v59_def, ← v57_def, ← v20_def, ← hhQ, ptrStep _ (Nat.mod_lt _ (by decide)), ← v19_def, ptrNext])
  all_goals (first
    | (exfalso; rw [hv61] at hbr62; simp only [beq_iff_eq] at hbr62; have := congrArg BitVec.toNat hbr62; rw [BitVec.toNat_add, BitVec.toNat_add, Bn.toNat_ofNat' (8 * ((m + 1) / 64))] at this; simp only [BitVec.toNat_ofNat] at this; omega)
    | skip)
  -- the live path's result, as the executor left it
  have hk' : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x180#64, 48), (iter, 18)] s t →
      Region iter [0#64, j, 0#64, sp + 18446744073709551504#64, replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[2]! 3 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 40))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551512#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 48))) 0 63#8, replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 56))) 1 (BitVec.truncate 8 0#64), replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[4]! 0 5#8) 1 (BitVec.truncate 8 (sp + 18446744073709551440#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 48)), replaceHalfword (replaceHalfword (replaceHalfword (replaceByte (replaceByte J[5]! 0 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 56))) 1 0#8) 1 (BitVec.truncate 16 (sp + 18446744073709551440#64))) 2 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 16))) 3 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 32)), replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceHalfword J[6]! 0 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 48))) 2 0#8) 3 (BitVec.truncate 8 (sp + 18446744073709551472#64))) 4 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 8))) 5 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 16))) 6 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 24))) 7 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 32)), replaceWord32 (replaceByte (replaceByte (replaceByte (replaceByte J[7]! 0 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 40))) 1 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 48))) 2 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 56))) 3 0#8) 1 (BitVec.truncate 32 (sp + 18446744073709551472#64)), replaceByte (replaceByte (replaceByte (replaceByte (replaceWord32 J[8]! 0 (BitVec.truncate 32 ((sp + 18446744073709551472#64) >>> 32))) 4 0#8) 5 (BitVec.truncate 8 (sp + 18446744073709551480#64))) 6 (BitVec.truncate 8 ((sp + 18446744073709551480#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551480#64) >>> 16)), replaceHalfword (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[9]! 0 (BitVec.truncate 8 ((sp + 18446744073709551480#64) >>> 24))) 1 (BitVec.truncate 8 ((sp + 18446744073709551480#64) >>> 32))) 2 (BitVec.truncate 8 ((sp + 18446744073709551480#64) >>> 40))) 3 (BitVec.truncate 8 ((sp + 18446744073709551480#64) >>> 48))) 4 (BitVec.truncate 8 ((sp + 18446744073709551480#64) >>> 56))) 5 0#8) 3 (BitVec.truncate 16 (sp + 18446744073709551480#64)), replaceHalfword (replaceHalfword (replaceByte (replaceHalfword J[10]! 2 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 48))) 6 (BitVec.truncate 8 0#64)) 0 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 16))) 1 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 32)), v18 + 18446744073709551615#64, v61, v66, replaceByte (replaceByte J[14]! 0 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 56))) 1 (BitVec.truncate 8 0#64), v30 + 1#64] t →
      t.getReg .x10 = v75 → SafeN Gd n P t := by
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 (Region.of_eq h5 ?_) ?_
    · simp only [noteBlkE, List.cons.injEq, and_true, true_and]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [← v18_def]; exact countNext m hm254
      · exact hv61
      · rw [← v66_def, ← v64_def, ← v57_def, ← v20_def, ← hhQ, replaceByte_replaceByte _ _ (by decide),
          headNext (m % 64) (Nat.mod_lt _ (by decide)), Nat.mod_add_mod]
      · rw [← v30_def]; exact lenNext _
    · rw [h6, ← v75_def, ← v69_def, ← v67_def, ← v63_def, ← v57_def, ← v20_def, ← hhQ,
        show 8 * (m / 64) / 8 = m / 64 by omega, noteBit, if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left, BitVec.and_assoc, show 255#64 &&& 1#64 = 1#64 from rfl]
      exact bitNext Q m
  sym_close hk'

end Cases.Zip2005
