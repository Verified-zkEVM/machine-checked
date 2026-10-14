import Cases.Zip2005.Kit.ByteShift32
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Image.F_78019cb8
import Cases.Zip2005.Image.Ro

/-!
# `SeqAccess::next_element::<u64>` (0x78019cb8), the witness's `u64` at residue 1

With `c ≠ 0` fields left the count is decremented and eight bytes are read from the reader at
`q + 1` (little-endian): `Ok(Some(v))` is the pair `[1, v]`. Fewer than eight bytes left is the
boxed `UnexpectedEof`, `[2, e]`; `c = 0` is `Ok(None)`, `[0, _]`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- The `u64` at input residue 1: bytes 1–7 of the word at `q` and byte 0 of the next. -/
def u64r1 (W : List Word) : Word :=
  word8 (extractByte W[0]! 1) (extractByte W[0]! 2) (extractByte W[0]! 3) (extractByte W[0]! 4)
    (extractByte W[0]! 5) (extractByte W[0]! 6) (extractByte W[0]! 7) (extractByte W[1]! 0)

set_option maxHeartbeats 4000000 in
/-- The guest's packing of the eight bytes (two `u32` halves, the high one shifted up). -/
theorem pack64_r1 (a b : Word) :
    ((BitVec.zeroExtend 64 (extractByte b 0) <<< 24 ||| BitVec.zeroExtend 64 (extractByte a 7) <<< 16) |||
        (BitVec.zeroExtend 64 (extractByte a 6) <<< 8 ||| BitVec.zeroExtend 64 (extractByte a 5))) <<< 32 |||
      ((BitVec.zeroExtend 64 (extractByte a 4) <<< 24 ||| BitVec.zeroExtend 64 (extractByte a 3) <<< 16) |||
        (BitVec.zeroExtend 64 (extractByte a 2) <<< 8 ||| BitVec.zeroExtend 64 (extractByte a 1))) =
    word8 (extractByte a 1) (extractByte a 2) (extractByte a 3) (extractByte a 4)
      (extractByte a 5) (extractByte a 6) (extractByte a 7) (extractByte b 0) := by
  apply word_ext
  intro k hk
  interval_cases k <;> simp (disch := decide) only [byte_simp]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
set_option asmverif.sym.foldBytes true in
theorem next_u64_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 2) (hWl : W.length = 2)
    (hpc : s.pc = 0x78019cb8#64) (hcode : CodeAt F_78019cb8.base F_78019cb8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x50 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 2)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 1#64, l] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 2)
    (hdO : Disjoint (sp - 0x50#64) 10 out 2) (hdA : Disjoint (sp - 0x50#64) 10 acs 2)
    (hdD : Disjoint (sp - 0x50#64) 10 de 2)
    (heA : Disjoint out 2 acs 2) (heD : Disjoint out 2 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 16 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        SafeN G n P t) → SafeN G n P u)
    (hkN : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [0#64, O[1]!] t → Region acs [de, c] t → Region de [q + 1#64, l] t → c = 0#64 →
      SafeN G n P t)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [1#64, u64r1 W] t → Region acs [de, c - 1#64] t → Region de [q + 9#64, l - 8#64] t →
      c ≠ 0#64 → 8 ≤ l.toNat → SafeN G n P t)
    (hkE : ∀ (t : MachineState) (e : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [2#64, e] t → Region acs [de, c - 1#64] t → Region de [q + 1#64, l] t →
      c ≠ 0#64 → l.toNat < 8 → SafeN G n P t) :
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
    sym_close hkN
  · have hc : c ≠ 0#64 := by simpa using hbr1
    have hc1 : c + 18446744073709551615#64 = c - 1#64 := by bv_omega
    rw [hc1] at hR1
    have hlt : l.toNat < 8 := by
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hbr7
      simp only [BitVec.toNat_ofNat] at hbr7
      omega
    sym_close (hkE _ post18_0)
  · have hc : c ≠ 0#64 := by simpa using hbr1
    have hv : v32 = u64r1 W := by
      rw [← v32_def, ← v31_def, ← v30_def, ← v18_def, ← v29_def, ← v24_def, ← v17_def, ← v14_def,
        ← v28_def, ← v27_def, ← v23_def, ← v16_def, ← v15_def, ← v13_def, ← v22_def, ← v21_def,
        ← v20_def, ← v19_def, ← v12_def, ← v11_def, ← v10_def, ← v9_def, u64r1]
      exact pack64_r1 W[0]! W[1]!
    rw [hv] at hR0
    have hc1 : c + 18446744073709551615#64 = c - 1#64 := by bv_omega
    have hl8 : l + 18446744073709551608#64 = l - 8#64 := by bv_omega
    rw [hc1] at hR1
    rw [hl8] at hR2
    have hge : 8 ≤ l.toNat := by
      simp only [BitVec.ult, decide_eq_true_eq, Nat.not_lt] at hbr7
      simp only [BitVec.toNat_ofNat] at hbr7
      omega
    sym_close hk

/-- `Ok(Some(v))`: a field left and eight bytes. -/
theorem next_u64_ok_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 2) (hWl : W.length = 2)
    (hpc : s.pc = 0x78019cb8#64) (hcode : CodeAt F_78019cb8.base F_78019cb8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x50 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 2)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 1#64, l] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 2)
    (hdO : Disjoint (sp - 0x50#64) 10 out 2) (hdA : Disjoint (sp - 0x50#64) 10 acs 2)
    (hdD : Disjoint (sp - 0x50#64) 10 de 2)
    (heA : Disjoint out 2 acs 2) (heD : Disjoint out 2 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 16 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (hl : 8 ≤ l.toNat)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [1#64, u64r1 W] t → Region acs [de, c - 1#64] t → Region de [q + 9#64, l - 8#64] t →
      SafeN G n P t) :
    SafeN G n P s :=
  next_u64_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcw hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hio
    (fun _ _ _ _ _ _ _ _ hc' => absurd hc' hc)
    (fun t h1 h2 h3 h4 h5 h6 h7 _ _ => hk t h1 h2 h3 h4 h5 h6 h7)
    (fun _ _ _ _ _ _ _ _ _ _ hlt => absurd hl (by omega))

/-- `Err`: a field left, fewer than eight bytes. -/
theorem next_u64_err_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out acs de q l c : Word)
    (O W : List Word) (hOl : O.length = 2) (hWl : W.length = 2)
    (hpc : s.pc = 0x78019cb8#64) (hcode : CodeAt F_78019cb8.base F_78019cb8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x50 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 2)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + 1#64, l] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 2)
    (hdO : Disjoint (sp - 0x50#64) 10 out 2) (hdA : Disjoint (sp - 0x50#64) 10 acs 2)
    (hdD : Disjoint (sp - 0x50#64) 10 de 2)
    (heA : Disjoint out 2 acs 2) (heD : Disjoint out 2 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 16 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        SafeN G n P t) → SafeN G n P u)
    (hc : c ≠ 0#64) (hl : l.toNat < 8)
    (hkE : ∀ (t : MachineState) (e : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [2#64, e] t → Region acs [de, c - 1#64] t → Region de [q + 1#64, l] t → SafeN G n P t) :
    SafeN G n P s :=
  next_u64_spec s ra sp out acs de q l c O W hOl hWl hpc hcode hcw hra hra1 hsp hstk ha0 ha1 hO hokO hA hokA hD hokD hW hq hokW hdO hdA hdD heA heD hAD hOlo hAlo hDlo hio
    (fun _ _ _ _ _ _ _ _ hc' => absurd hc' hc)
    (fun _ _ _ _ _ _ _ _ _ hge => absurd hl (by omega))
    (fun t e h1 h2 h3 h4 h5 h6 h7 _ _ => hkE t e h1 h2 h3 h4 h5 h6 h7)

end Cases.Zip2005
