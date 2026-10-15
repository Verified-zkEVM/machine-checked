import Cases.Zip2005.Kit.ByteKit
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Image.F_78019dd8
import Cases.Zip2005.Image.F_7801aed0
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `deserialize_bool` over the `SliceReader` (0x78019dd8)

The witness's `negate` flag: one byte from the reader at `q + 7` (input residue 7). Byte 0 or 1
is `Ok(false)` / `Ok(true)` (tag byte 0, the flag in byte 1); any other byte is
`Err(Box(InvalidBoolEncoding(b)))` (`__rust_alloc(0x18, 8)`, ledger T2); an empty reader is the
`io::Error` `UnexpectedEof` boxed by `From<io::Error>` (0x78036184).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- The flag byte: input byte 7 of the word at `q`. -/
def boolByte (W : List Word) : BitVec 8 := extractByte W[0]! 7

/-- The loaded flag byte, zero-extended, has the byte's value. -/
theorem boolByte_toNat (W : List Word) :
    (BitVec.zeroExtend 64 (extractByte W[0]! 7)).toNat = (boolByte W).toNat := by
  simp only [boolByte, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have := (extractByte W[0]! 7).isLt
  omega

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem bool_reader_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 2) (hWl : W.length = 1)
    (hpc : s.pc = 0x78019dd8#64) (hcode : CodeAt F_78019dd8.base F_78019dd8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x60 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 2)
    (hD : Region de [q + 7#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 1)
    (hdO : Disjoint (sp - 0x60#64) 12 out 2) (hdD : Disjoint (sp - 0x60#64) 12 de 2)
    (heD : Disjoint out 2 de 2) (hOlo : out.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78019e80#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78019e80#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x60#64, 12), (out, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceByte (replaceByte O[0]! 1 (boolByte W)) 0 0#8, O[1]!] t →
      Region de [q + 8#64, l - 1#64] t → (boolByte W).toNat < 2 → 1 ≤ l.toNat → Run.HeapAt L t → SafeN G n P t)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x60#64, 12), (out, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceByte O[0]! 0 1#8, e] t → Region de [d0, d1] t →
      ¬ ((boolByte W).toNat < 2 ∧ 1 ≤ l.toNat) → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 12 := hstk.frame 12 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hokS.sub' 8 4 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x60#64, 12), (out, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hlo := hstk.lo
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hmO : out &&& 7#64 = 0#64 := hokO.and7
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  rw [AsmVerif.RiscV.Sym.List.eq_map_range O hOl] at hO
  rw [AsmVerif.RiscV.Sym.List.eq_map_range W hWl] at hW
  sym_exec [halloc, hhandle, hio]
  · -- empty reader: the boxed `UnexpectedEof`
    rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v16_def
    rw [← v16_def] at hR0
    have hl0 : l = 0#64 := by simpa using hbr6
    have hn : ¬ ((boolByte W).toNat < 2 ∧ 1 ≤ l.toNat) := by
      rw [hl0]; simp
    sym_close (hkE _ post12_0 (q + 7#64) l)
  · -- byte 0: `Ok(false)`
    have hv : v8.toNat = 0 := by simp only [beq_iff_eq] at hbr13; simp [hbr13]
    have hb : boolByte W = 0#8 := by
      apply BitVec.eq_of_toNat_eq
      rw [← boolByte_toNat, v8_def, hv]; rfl
    rw [show BitVec.truncate 8 (0#64) = 0#8 from rfl] at v14_def v15_def
    have hRo : Region out [replaceByte (replaceByte O[0]! 1 (boolByte W)) 0 0#8, O[1]!] s_21 := by
      rw [hb, v14_def, v15_def]; exact hR0
    clear hR0
    have hl1 : l + 18446744073709551615#64 = l - 1#64 := by bv_omega
    rw [hl1] at hR1
    have hb2 : (boolByte W).toNat < 2 := by rw [hb]; decide
    have hl0 : 1 ≤ l.toNat := by
      simp only [beq_iff_eq] at hbr6
      bv_omega
    sym_close hk
  · -- any other byte: `Err(Box(InvalidBoolEncoding(b)))`
    rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v32_def
    rw [← v32_def] at hR0
    have h0 : v8 ≠ 0#64 := by simpa using hbr13
    have h1 : v8 ≠ 1#64 := by simpa using hbr15
    have hn : ¬ ((boolByte W).toNat < 2 ∧ 1 ≤ l.toNat) := by
      intro ⟨h, _⟩
      have e := boolByte_toNat W
      rw [v8_def] at e
      apply (show v8.toNat = 0 ∨ v8.toNat = 1 by omega).elim
      · intro h'; exact h0 (BitVec.eq_of_toNat_eq h')
      · intro h'; exact h1 (BitVec.eq_of_toNat_eq h')
    sym_close (hkE _ post23_0 (q + 8#64) (l + 18446744073709551615#64))
  · -- byte 1: `Ok(true)`
    have hv : v8.toNat = 1 := by
      have : v8 = 1#64 := by simpa using hbr15
      simp [this]
    have hb : boolByte W = 1#8 := by
      apply BitVec.eq_of_toNat_eq
      rw [← boolByte_toNat, v8_def, hv]; rfl
    rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v16_def
    rw [show BitVec.truncate 8 (0#64) = 0#8 from rfl] at v17_def
    have hRo : Region out [replaceByte (replaceByte O[0]! 1 (boolByte W)) 0 0#8, O[1]!] s_23 := by
      rw [hb, v16_def, v17_def]; exact hR0
    clear hR0
    have hl1 : l + 18446744073709551615#64 = l - 1#64 := by bv_omega
    rw [hl1] at hR1
    have hb2 : (boolByte W).toNat < 2 := by rw [hb]; decide
    have hl0 : 1 ≤ l.toNat := by
      simp only [beq_iff_eq] at hbr6
      bv_omega
    sym_close hk

/-- `Ok(b)`: a byte left, and it is 0 or 1. -/
theorem bool_reader_ok_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 2) (hWl : W.length = 1)
    (hpc : s.pc = 0x78019dd8#64) (hcode : CodeAt F_78019dd8.base F_78019dd8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x60 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 2)
    (hD : Region de [q + 7#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 1)
    (hdO : Disjoint (sp - 0x60#64) 12 out 2) (hdD : Disjoint (sp - 0x60#64) 12 de 2)
    (heD : Disjoint out 2 de 2) (hOlo : out.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78019e80#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78019e80#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hl : 1 ≤ l.toNat) (hb : (boolByte W).toNat < 2)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x60#64, 12), (out, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceByte (replaceByte O[0]! 1 (boolByte W)) 0 0#8, O[1]!] t →
      Region de [q + 8#64, l - 1#64] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  bool_reader_spec s ra sp out de q l O W hOl hWl hpc hcode hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hhandle halloc hio
    (fun t h1 h2 h3 h4 h5 h6 _ _ hH => hk t h1 h2 h3 h4 h5 h6 hH)
    (fun _ _ _ _ _ _ _ _ _ _ hn _ => absurd ⟨hb, hl⟩ hn)

/-- `Err`: the reader is empty. -/
theorem bool_reader_eof_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 2) (hWl : W.length = 1)
    (hpc : s.pc = 0x78019dd8#64) (hcode : CodeAt F_78019dd8.base F_78019dd8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x60 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 2)
    (hD : Region de [q + 7#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 1)
    (hdO : Disjoint (sp - 0x60#64) 12 out 2) (hdD : Disjoint (sp - 0x60#64) 12 de 2)
    (heD : Disjoint out 2 de 2) (hOlo : out.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78019e80#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78019e80#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hl : l.toNat < 1)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x60#64, 12), (out, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceByte O[0]! 0 1#8, e] t → Region de [d0, d1] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  bool_reader_spec s ra sp out de q l O W hOl hWl hpc hcode hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ _ hl' _ => absurd hl' (by omega))
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 _ hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 hH)

/-- `Err`: the byte is neither 0 nor 1. -/
theorem bool_reader_badbyte_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O W : List Word) (hOl : O.length = 2) (hWl : W.length = 1)
    (hpc : s.pc = 0x78019dd8#64) (hcode : CodeAt F_78019dd8.base F_78019dd8.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x60 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 2)
    (hD : Region de [q + 7#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 1)
    (hdO : Disjoint (sp - 0x60#64) 12 out 2) (hdD : Disjoint (sp - 0x60#64) 12 de 2)
    (heD : Disjoint out 2 de 2) (hOlo : out.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hhandle : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1a8#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (halloc : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78019e80#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x18#64 → u.getReg .x11 = 8#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78019e80#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 3 → Region ptr B t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 3 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 0x18 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 3) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hb : 2 ≤ (boolByte W).toNat)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x60#64, 12), (out, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceByte O[0]! 0 1#8, e] t → Region de [d0, d1] t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s :=
  bool_reader_spec s ra sp out de q l O W hOl hWl hpc hcode hcodeSh hcw hro hheap hra hra1 hsp hstk ha0 ha1 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hhandle halloc hio
    (fun _ _ _ _ _ _ _ hb' _ _ => absurd hb' (by omega))
    (fun t e d0 d1 h1 h2 h3 h4 h5 h6 _ hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 hH)

end Cases.Zip2005
