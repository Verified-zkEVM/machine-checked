import Cases.Zip2005.Kit.ByteKit
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Image.F_78019bf0
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `SeqAccess::next_element::<u32>` (0x78019bf0), the witness's `u32` at residue 1

With `c ≠ 0` fields left the count is decremented and four bytes are read from the reader at
`q + 1` (little-endian): `Ok(Some(v))` (two `u32` tags 0 and 1, then `v`). Fewer than four bytes
left is the boxed `UnexpectedEof`; `c = 0` is `Ok(None)`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- The `u32` at input residue 1: bytes 1–4 of the word at `q`, little-endian. -/
def u32r1 (W : List Word) : BitVec 32 :=
  extractByte W[0]! 4 ++ extractByte W[0]! 3 ++ extractByte W[0]! 2 ++ extractByte W[0]! 1

/-- The guest's packing of the four bytes (`lbu`, `lbu`, `lbu`, `lb`, shifted and or-ed). -/
theorem pack32_r1 (w : Word) :
    BitVec.truncate 32 ((BitVec.signExtend 64 (extractByte w 4) <<< 24 |||
      BitVec.zeroExtend 64 (extractByte w 3) <<< 16) |||
      (BitVec.zeroExtend 64 (extractByte w 2) <<< 8 ||| BitVec.zeroExtend 64 (extractByte w 1))) =
    extractByte w 4 ++ extractByte w 3 ++ extractByte w 2 ++ extractByte w 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
set_option asmverif.sym.foldBytes true in
theorem next_u32_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 2) (hWl : W.length = 1)
    (hpc : s.pc = 0x78019bf0#64) (hcode : CodeAt F_78019bf0.base F_78019bf0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x50 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 2)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 1#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 1)
    (hdO : Disjoint (sp - 0x50#64) 10 out 2) (hdA : Disjoint (sp - 0x50#64) 10 acs 2)
    (hdD : Disjoint (sp - 0x50#64) 10 de 2)
    (heA : Disjoint out 2 acs 2) (heD : Disjoint out 2 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 16 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hkN : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceWord32 (replaceWord32 O[0]! 1 0#32) 0 0#32, O[1]!] t →
      Region acs [de, c] t → Region de [q + 1#64, l] t → c = 0#64 → Run.HeapAt L t → SafeN G n P t)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceWord32 (replaceWord32 O[0]! 1 1#32) 0 0#32, replaceWord32 O[1]! 0 (u32r1 W)] t →
      Region acs [de, c - 1#64] t → Region de [q + 5#64, l - 4#64] t → c ≠ 0#64 → 4 ≤ l.toNat →
      Run.HeapAt L t → SafeN G n P t)
    (hkE : ∀ (t : MachineState) (e : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceWord32 O[0]! 0 1#32, e] t → Region acs [de, c - 1#64] t →
      Region de [q + 1#64, l] t → c ≠ 0#64 → l.toNat < 4 → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x50#64) 10 := hstk.frame 10 (by decide)
  have hu := Unchanged.refl [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2),
    (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hmO : out &&& 7#64 = 0#64 := hokO.and7
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokS.sub' 8 2 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl] at hO
  rw [AsmVerif.RiscV.Sym.List.eq_map_range W hWl] at hW
  sym_exec [hio]
  · have hc : c = 0#64 := by simpa using hbr1
    rw [show BitVec.truncate 32 (0#64) = 0#32 from rfl] at v2_def v3_def
    have hRo : Region out [replaceWord32 (replaceWord32 O[0]! 1 0#32) 0 0#32, O[1]!] s_5 := by
      rw [v2_def, v3_def]; exact hR0
    clear hR0
    sym_close hkN
  · have hc : c ≠ 0#64 := by simpa using hbr1
    rw [show BitVec.truncate 32 (1#64) = 1#32 from rfl] at v26_def
    rw [← v26_def] at hR0
    have hc1 : c + 18446744073709551615#64 = c - 1#64 := by bv_omega
    rw [hc1] at hR1
    have hlt : l.toNat < 4 := by
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hbr7
      simp only [BitVec.toNat_ofNat] at hbr7
      omega
    sym_close (hkE _ post18_0)
  · have hc : c ≠ 0#64 := by simpa using hbr1
    rw [show BitVec.truncate 32 (1#64) = 1#32 from rfl] at v24_def
    rw [show BitVec.truncate 32 (0#64) = 0#32 from rfl] at v26_def
    have hv : BitVec.truncate 32 v20 = u32r1 W := by
      rw [← v20_def, ← v17_def, ← v14_def, ← v16_def, ← v15_def, ← v13_def, ← v12_def, ← v11_def,
        ← v10_def, ← v9_def, u32r1]
      exact pack32_r1 W[0]!
    have hRo : Region out [replaceWord32 (replaceWord32 O[0]! 1 1#32) 0 0#32,
        replaceWord32 O[1]! 0 (u32r1 W)] s_28 := by
      rw [← hv, v24_def, v26_def, v25_def]; exact hR0
    clear hR0
    have hc1 : c + 18446744073709551615#64 = c - 1#64 := by bv_omega
    have hl4 : l + 18446744073709551612#64 = l - 4#64 := by bv_omega
    rw [hc1] at hR1
    rw [hl4] at hR2
    have hge : 4 ≤ l.toNat := by
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hbr7
      simp only [BitVec.toNat_ofNat] at hbr7
      omega
    sym_close hk

/-- `Ok(Some(v))`: a field left and four bytes. -/
theorem next_u32_ok_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 2) (hWl : W.length = 1)
    (hpc : s.pc = 0x78019bf0#64) (hcode : CodeAt F_78019bf0.base F_78019bf0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x50 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 2)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 1#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 1)
    (hdO : Disjoint (sp - 0x50#64) 10 out 2) (hdA : Disjoint (sp - 0x50#64) 10 acs 2)
    (hdD : Disjoint (sp - 0x50#64) 10 de 2)
    (heA : Disjoint out 2 acs 2) (heD : Disjoint out 2 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 16 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (hl : 4 ≤ l.toNat)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceWord32 (replaceWord32 O[0]! 1 1#32) 0 0#32, replaceWord32 O[1]! 0 (u32r1 W)] t →
      Region acs [de, c - 1#64] t → Region de [q + 5#64, l - 4#64] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  next_u32_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hio
    (fun _ _ _ _ _ _ _ _ hc' _ => absurd hc' hc)
    (fun t h1 h2 h3 h4 h5 h6 h7 _ _ hH => hk t h1 h2 h3 h4 h5 h6 h7 hH)
    (fun _ _ _ _ _ _ _ _ _ _ hlt _ => absurd hl (by omega))

/-- `Err`: a field left, fewer than four bytes. -/
theorem next_u32_err_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 2) (hWl : W.length = 1)
    (hpc : s.pc = 0x78019bf0#64) (hcode : CodeAt F_78019bf0.base F_78019bf0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x50 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 2)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 1#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 1)
    (hdO : Disjoint (sp - 0x50#64) 10 out 2) (hdA : Disjoint (sp - 0x50#64) 10 acs 2)
    (hdD : Disjoint (sp - 0x50#64) 10 de 2)
    (heA : Disjoint out 2 acs 2) (heD : Disjoint out 2 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 16 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (hl : l.toNat < 4)
    (hkE : ∀ (t : MachineState) (e : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceWord32 O[0]! 0 1#32, e] t → Region acs [de, c - 1#64] t →
      Region de [q + 1#64, l] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  next_u32_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hio
    (fun _ _ _ _ _ _ _ _ hc' _ => absurd hc' hc)
    (fun _ _ _ _ _ _ _ _ _ hge _ => absurd hl (by omega))
    (fun t e h1 h2 h3 h4 h5 h6 h7 _ _ hH => hkE t e h1 h2 h3 h4 h5 h6 h7 hH)

end Cases.Zip2005
