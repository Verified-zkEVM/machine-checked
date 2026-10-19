import Cases.Zip2005.Witness.OptionBytes32R0
import Cases.Zip2005.Witness.NextOptR5
import Cases.Zip2005.Witness.NextOptR6
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `Option<Bytes32>` readers with `Nat` preconditions

The tag and length cases of `deserialize_option<Bytes32>` (residue 0) and of
`next_element<Option<Bytes32>>` (residues 5, 6) as separate specifications whose preconditions are
`Nat` comparisons on the tag byte and the reader's length, so that a caller's run splits on them
(`sym_exec`'s undecided-precondition split) instead of naming the cases itself.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

theorem bv8_eq0 {t : BitVec 8} (h : t.toNat < 1) : t = 0#8 := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
theorem bv8_eq1 {t : BitVec 8} (h1 : 1 ≤ t.toNat) (h2 : t.toNat < 2) : t = 1#8 := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
theorem bv8_ne0 {t : BitVec 8} (h : 1 ≤ t.toNat) : t ≠ 0#8 := by
  intro e; rw [e] at h; exact absurd h (by decide)
theorem bv8_ne1_lt {t : BitVec 8} (h : t.toNat < 1) : t ≠ 1#8 := by
  intro e; rw [e] at h; exact absurd h (by decide)
theorem bv8_ne1_ge {t : BitVec 8} (h : 2 ≤ t.toNat) : t ≠ 1#8 := by
  intro e; rw [e] at h; exact absurd h (by decide)
theorem bv8_ne0_ge {t : BitVec 8} (h : 2 ≤ t.toNat) : t ≠ 0#8 := by
  intro e; rw [e] at h; exact absurd h (by decide)

theorem opt0_none_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x7801806c#64) (hcode : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x380 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hD : Region de [q, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x380#64) 112 out 5) (hdD : Disjoint (sp - 0x380#64) 112 de 2)
    (heD : Disjoint out 5 de 2) (hOlo : out.toNat + 40 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (ht : (optTag0 W).toNat < 1) (hl : 1 ≤ l.toNat)
    (hkN : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceHalfword O[0]! 0 0#16 :: O.drop 1) t → Region de [q + 1#64, l - 1#64] t →
      Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  option_bytes32_r0_spec s ra sp out de q l O W hOl hWl hpc hcode hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hhandle halloc hio
    (fun t h1 h2 h3 h4 h5 h6 _ _ hH => hkN t h1 h2 h3 h4 h5 h6 hH)
    (fun _ _ _ _ _ _ _ h _ _ => (bv8_ne1_lt ht h).elim)
    (fun _ _ _ _ _ _ _ _ _ _ hx _ _ => (hx ⟨bv8_eq0 ht, hl⟩).elim)

theorem opt0_some_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x7801806c#64) (hcode : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x380 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hD : Region de [q, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x380#64) 112 out 5) (hdD : Disjoint (sp - 0x380#64) 112 de 2)
    (heD : Disjoint out 5 de 2) (hOlo : out.toNat + 40 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (ht1 : 1 ≤ (optTag0 W).toNat) (ht2 : (optTag0 W).toNat < 2) (hl : 33 ≤ l.toNat)
    (hkS : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (someW O W 1) t → Region de [q + 33#64, l - 33#64] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  option_bytes32_r0_spec s ra sp out de q l O W hOl hWl hpc hcode hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ h _ _ => (bv8_ne0 ht1 h).elim)
    (fun t h1 h2 h3 h4 h5 h6 _ _ hH => hkS t h1 h2 h3 h4 h5 h6 hH)
    (fun _ _ _ _ _ _ _ _ _ _ _ hx _ => (hx ⟨bv8_eq1 ht1 ht2, hl⟩).elim)

theorem opt0_errtag_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x7801806c#64) (hcode : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x380 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hD : Region de [q, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x380#64) 112 out 5) (hdD : Disjoint (sp - 0x380#64) 112 de 2)
    (heD : Disjoint out 5 de 2) (hOlo : out.toNat + 40 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (ht : 2 ≤ (optTag0 W).toNat)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region de [d0, d1] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  option_bytes32_r0_spec s ra sp out de q l O W hOl hWl hpc hcode hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ h _ _ => (bv8_ne0_ge ht h).elim)
    (fun _ _ _ _ _ _ _ h _ _ => (bv8_ne1_ge ht h).elim)
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 _ _ hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 hH)

theorem opt0_errnone_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x7801806c#64) (hcode : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x380 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hD : Region de [q, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x380#64) 112 out 5) (hdD : Disjoint (sp - 0x380#64) 112 de 2)
    (heD : Disjoint out 5 de 2) (hOlo : out.toNat + 40 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (ht : (optTag0 W).toNat < 1) (hl : l.toNat < 1)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region de [d0, d1] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  option_bytes32_r0_spec s ra sp out de q l O W hOl hWl hpc hcode hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ _ h _ => absurd h (by omega))
    (fun _ _ _ _ _ _ _ h _ _ => (bv8_ne1_lt ht h).elim)
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 _ _ hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 hH)

theorem opt0_errsome_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x7801806c#64) (hcode : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x380 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hD : Region de [q, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x380#64) 112 out 5) (hdD : Disjoint (sp - 0x380#64) 112 de 2)
    (heD : Disjoint out 5 de 2) (hOlo : out.toNat + 40 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (ht1 : 1 ≤ (optTag0 W).toNat) (hl : l.toNat < 33)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x380#64, 112), (out, 5), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region de [d0, d1] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  option_bytes32_r0_spec s ra sp out de q l O W hOl hWl hpc hcode hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ h _ _ => (bv8_ne0 ht1 h).elim)
    (fun _ _ _ _ _ _ _ _ h _ => absurd h (by omega))
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 _ _ hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 hH)

theorem nopt5_none_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x78019918#64) (hcode : CodeAt F_78019918.base F_78019918.prog s)
    (hcodeO : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x3d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 5#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x3d0#64) 122 out 5) (hdA : Disjoint (sp - 0x3d0#64) 122 acs 2)
    (hdD : Disjoint (sp - 0x3d0#64) 122 de 2)
    (heA : Disjoint out 5 acs 2) (heD : Disjoint out 5 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 40 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (ht : (optTag5 W).toNat < 1) (hl : 1 ≤ l.toNat)
    (hkN : ∀ (t : MachineState) (J : List Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      J.length = 5 → Region out J t → extractByte J[0]! 0 = 0#8 → extractByte J[0]! 1 = 0#8 →
      Region acs [de, c - 1#64] t → Region de [q + 6#64, l - 1#64] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  next_opt_r5_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ _ h _ => (hc h).elim)
    (fun t J h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ _ _ hH => hkN t J h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hH)
    (fun _ _ _ _ _ _ _ _ _ h _ _ => (bv8_ne1_lt ht h).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hx _ _ => (hx ⟨bv8_eq0 ht, hl⟩).elim)

theorem nopt5_some_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x78019918#64) (hcode : CodeAt F_78019918.base F_78019918.prog s)
    (hcodeO : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x3d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 5#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x3d0#64) 122 out 5) (hdA : Disjoint (sp - 0x3d0#64) 122 acs 2)
    (hdD : Disjoint (sp - 0x3d0#64) 122 de 2)
    (heA : Disjoint out 5 acs 2) (heD : Disjoint out 5 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 40 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (ht1 : 1 ≤ (optTag5 W).toNat) (ht2 : (optTag5 W).toNat < 2) (hl : 33 ≤ l.toNat)
    (hkS : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (someW O W 6) t → Region acs [de, c - 1#64] t →
      Region de [q + 38#64, l - 33#64] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  next_opt_r5_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ _ h _ => (hc h).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ => (bv8_ne0 ht1 h).elim)
    (fun t h1 h2 h3 h4 h5 h6 h7 _ _ _ hH => hkS t h1 h2 h3 h4 h5 h6 h7 hH)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hx _ => (hx ⟨bv8_eq1 ht1 ht2, hl⟩).elim)

theorem nopt5_errtag_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x78019918#64) (hcode : CodeAt F_78019918.base F_78019918.prog s)
    (hcodeO : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x3d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 5#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x3d0#64) 122 out 5) (hdA : Disjoint (sp - 0x3d0#64) 122 acs 2)
    (hdD : Disjoint (sp - 0x3d0#64) 122 de 2)
    (heA : Disjoint out 5 acs 2) (heD : Disjoint out 5 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 40 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (ht : 2 ≤ (optTag5 W).toNat)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region acs [de, c - 1#64] t →
      Region de [d0, d1] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  next_opt_r5_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ _ h _ => (hc h).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ => (bv8_ne0_ge ht h).elim)
    (fun _ _ _ _ _ _ _ _ _ h _ _ => (bv8_ne1_ge ht h).elim)
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 h7 _ _ _ hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 h7 hH)

theorem nopt5_errnone_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x78019918#64) (hcode : CodeAt F_78019918.base F_78019918.prog s)
    (hcodeO : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x3d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 5#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x3d0#64) 122 out 5) (hdA : Disjoint (sp - 0x3d0#64) 122 acs 2)
    (hdD : Disjoint (sp - 0x3d0#64) 122 de 2)
    (heA : Disjoint out 5 acs 2) (heD : Disjoint out 5 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 40 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (ht : (optTag5 W).toNat < 1) (hl : l.toNat < 1)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region acs [de, c - 1#64] t →
      Region de [d0, d1] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  next_opt_r5_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ _ h _ => (hc h).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => absurd h (by omega))
    (fun _ _ _ _ _ _ _ _ _ h _ _ => (bv8_ne1_lt ht h).elim)
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 h7 _ _ _ hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 h7 hH)

theorem nopt5_errsome_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x78019918#64) (hcode : CodeAt F_78019918.base F_78019918.prog s)
    (hcodeO : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x3d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 5#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x3d0#64) 122 out 5) (hdA : Disjoint (sp - 0x3d0#64) 122 acs 2)
    (hdD : Disjoint (sp - 0x3d0#64) 122 de 2)
    (heA : Disjoint out 5 acs 2) (heD : Disjoint out 5 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 40 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (ht1 : 1 ≤ (optTag5 W).toNat) (hl : l.toNat < 33)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region acs [de, c - 1#64] t →
      Region de [d0, d1] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  next_opt_r5_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ _ h _ => (hc h).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ => (bv8_ne0 ht1 h).elim)
    (fun _ _ _ _ _ _ _ _ _ _ h _ => absurd h (by omega))
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 h7 _ _ _ hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 h7 hH)

theorem nopt6_none_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x78019918#64) (hcode : CodeAt F_78019918.base F_78019918.prog s)
    (hcodeO : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x3d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 6#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x3d0#64) 122 out 5) (hdA : Disjoint (sp - 0x3d0#64) 122 acs 2)
    (hdD : Disjoint (sp - 0x3d0#64) 122 de 2)
    (heA : Disjoint out 5 acs 2) (heD : Disjoint out 5 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 40 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (ht : (optTag6 W).toNat < 1) (hl : 1 ≤ l.toNat)
    (hkN : ∀ (t : MachineState) (J : List Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      J.length = 5 → Region out J t → extractByte J[0]! 0 = 0#8 → extractByte J[0]! 1 = 0#8 →
      Region acs [de, c - 1#64] t → Region de [q + 7#64, l - 1#64] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  next_opt_r6_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ _ h _ => (hc h).elim)
    (fun t J h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ _ _ hH => hkN t J h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hH)
    (fun _ _ _ _ _ _ _ _ _ h _ _ => (bv8_ne1_lt ht h).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ hx _ _ => (hx ⟨bv8_eq0 ht, hl⟩).elim)

theorem nopt6_some_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x78019918#64) (hcode : CodeAt F_78019918.base F_78019918.prog s)
    (hcodeO : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x3d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 6#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x3d0#64) 122 out 5) (hdA : Disjoint (sp - 0x3d0#64) 122 acs 2)
    (hdD : Disjoint (sp - 0x3d0#64) 122 de 2)
    (heA : Disjoint out 5 acs 2) (heD : Disjoint out 5 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 40 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (ht1 : 1 ≤ (optTag6 W).toNat) (ht2 : (optTag6 W).toNat < 2) (hl : 33 ≤ l.toNat)
    (hkS : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (someW O W 7) t → Region acs [de, c - 1#64] t →
      Region de [q + 39#64, l - 33#64] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  next_opt_r6_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ _ h _ => (hc h).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ => (bv8_ne0 ht1 h).elim)
    (fun t h1 h2 h3 h4 h5 h6 h7 _ _ _ hH => hkS t h1 h2 h3 h4 h5 h6 h7 hH)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hx _ => (hx ⟨bv8_eq1 ht1 ht2, hl⟩).elim)

theorem nopt6_errtag_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x78019918#64) (hcode : CodeAt F_78019918.base F_78019918.prog s)
    (hcodeO : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x3d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 6#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x3d0#64) 122 out 5) (hdA : Disjoint (sp - 0x3d0#64) 122 acs 2)
    (hdD : Disjoint (sp - 0x3d0#64) 122 de 2)
    (heA : Disjoint out 5 acs 2) (heD : Disjoint out 5 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 40 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (ht : 2 ≤ (optTag6 W).toNat)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region acs [de, c - 1#64] t →
      Region de [d0, d1] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  next_opt_r6_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ _ h _ => (hc h).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ => (bv8_ne0_ge ht h).elim)
    (fun _ _ _ _ _ _ _ _ _ h _ _ => (bv8_ne1_ge ht h).elim)
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 h7 _ _ _ hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 h7 hH)

theorem nopt6_errnone_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x78019918#64) (hcode : CodeAt F_78019918.base F_78019918.prog s)
    (hcodeO : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x3d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 6#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x3d0#64) 122 out 5) (hdA : Disjoint (sp - 0x3d0#64) 122 acs 2)
    (hdD : Disjoint (sp - 0x3d0#64) 122 de 2)
    (heA : Disjoint out 5 acs 2) (heD : Disjoint out 5 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 40 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (ht : (optTag6 W).toNat < 1) (hl : l.toNat < 1)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region acs [de, c - 1#64] t →
      Region de [d0, d1] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  next_opt_r6_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ _ h _ => (hc h).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => absurd h (by omega))
    (fun _ _ _ _ _ _ _ _ _ h _ _ => (bv8_ne1_lt ht h).elim)
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 h7 _ _ _ hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 h7 hH)

theorem nopt6_errsome_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 5) (hWl : W.length = 5)
    (hpc : s.pc = 0x78019918#64) (hcode : CodeAt F_78019918.base F_78019918.prog s)
    (hcodeO : CodeAt F_7801806c.base F_7801806c.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x3d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 5)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 6#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 5)
    (hdO : Disjoint (sp - 0x3d0#64) 122 out 5) (hdA : Disjoint (sp - 0x3d0#64) 122 acs 2)
    (hdD : Disjoint (sp - 0x3d0#64) 122 de 2)
    (heA : Disjoint out 5 acs 2) (heD : Disjoint out 5 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 40 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78018130#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78018130#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (ht1 : 1 ≤ (optTag6 W).toNat) (hl : l.toNat < 33)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 5), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region acs [de, c - 1#64] t →
      Region de [d0, d1] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  next_opt_r6_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcodeO hcodeA hcodeN hcodeM hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ _ h _ => (hc h).elim)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ _ => (bv8_ne0 ht1 h).elim)
    (fun _ _ _ _ _ _ _ _ _ _ h _ => absurd h (by omega))
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 h7 _ _ _ hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 h7 hH)

end Cases.Zip2005
