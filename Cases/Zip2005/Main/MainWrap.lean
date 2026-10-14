import Cases.Zip2005.Runtime.ReadVecRaw
import Cases.Zip2005.Witness.InstanceVisitor
import Cases.Zip2005.Orchard.SpendValidatingKey
import Cases.Zip2005.Witness.ParseMerklePath
import Cases.Zip2005.Orchard.ExtractedNoteCommitment
import Cases.Zip2005.Image.Ro

/-! # Single-continuation forms of `main`'s callees

The executor applies a specification through its last continuation-shaped argument; a
specification with two outcomes needs them joined into one continuation with a disjunction. -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- `read_vec_raw`: no input (the hint length `u64::MAX`), or the vector of `L` bytes. -/
theorem read_vec_raw_spec' {P : Prop} (s : MachineState) (ra dst b : Word) (I : List (BitVec 8))
    (D J : List Word) (hDl : D.length = 3) (hJl : J.length = 175)
    (hpc : s.pc = 0x7801beb0#64) (hcode : CodeAt F_7801beb0.base F_7801beb0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (hI : s.privateInput = I)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 3)
    (hB : Region 0x78040618#64 [b] s) (hb : 0x1c00000000 ≤ b.toNat)
    (hJ : Region b J s) (hokJ : RegionOk Ro.layout.textLo Ro.layout.textHi b 175)
    (hdD : dst.toNat + 24 ≤ 0x78040618)
    (hpanic : ∀ u : MachineState, u.pc = 0x7803de40#64 → u.code = s.code → Safe P u)
    (hk : ∀ (t : MachineState) (D' Bp : List Word) (bp : Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code →
      Unchanged [(dst, 3), (0x78040618#64, 1), (0x1c00000000#64, 0x80000000)] s t →
      Region dst D' t → Region b Bp t → Region 0x78040618#64 [bp] t →
      D'.length = 3 → Bp.length = 175 →
      ((t.privateInput = I ∧ hlenW I = -1#64 ∧ D' = [0#64, 0#64, 0#64] ∧ Bp = J ∧ bp = b) ∨
        (∃ (L : Word) (B : List Word), bytesToWordLE (I.take 8) = L ∧
          t.privateInput = I.drop (8 + L.toNat) ∧ 8 + L.toNat ≤ I.length ∧
          b.toNat + 8 * (L.toNat / 8 + 1) ≤ 0x2000000000 ∧
          hintWords ((I.drop 8).take L.toNat) = B ∧ B.length = L.toNat / 8 + 1 ∧
          Bp = overlay B J ∧ D' = [b, L, L + 7#64 &&& 18446744073709551608#64] ∧
          bp = b + (L + 7#64 &&& 18446744073709551608#64))) → Safe P t) :
    Safe P s :=
  read_vec_raw_spec s ra dst b I D J hDl hJl hpc hcode hcw hra hra1 ha0 hI hD hokD hB hb hJ hokJ hdD
    hpanic
    (fun t h1 h2 h3 h4 h5 h6 hD' hJ' hB' =>
      hk t _ _ _ h1 h2 h3 h4 hD' hJ' hB' rfl hJl (Or.inl ⟨h5, h6, rfl, rfl, rfl⟩))
    (fun t L B h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hJ' hD' hB' =>
      hk t _ _ _ h1 h2 h3 h4 hD' hJ' hB' rfl (by rw [overlay_length, hJl]) (Or.inr ⟨L, B, h5, h6, h7, h8, h9, h10, rfl, rfl, rfl⟩))

/-- `Zip2005Instance`'s visitor: the instance (128 bytes read), or the `Err` (fewer than 128). -/
theorem instance_visitor_spec' {P : Prop} (s : MachineState) (ra sp out de q l : Word)
    (O W0 W1 W2 W3 : List Word) (hOl : O.length = 17)
    (hW0l : W0.length = 4) (hW1l : W1.length = 4) (hW2l : W2.length = 4) (hW3l : W3.length = 4)
    (hpc : s.pc = 0x780191c4#64) (hcode : CodeAt F_780191c4.base F_780191c4.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x420 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de) (ha5 : s.getReg .x15 = 4#64)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 17)
    (hD : Region de [q, l] s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi de 2)
    (hW0 : Region q W0 s) (hW1 : Region (q + 32#64) W1 s) (hW2 : Region (q + 64#64) W2 s)
    (hW3 : Region (q + 96#64) W3 s)
    (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 16)
    (hdO : Disjoint (sp - 0x420#64) 132 out 17) (hdD : Disjoint (sp - 0x420#64) 132 de 2)
    (heD : Disjoint out 17 de 2) (hOlo : out.toNat + 136 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        t.privateInput = u.privateInput →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Safe P t) → Safe P u)
    (hk : ∀ (t : MachineState) (V : List Word) (d0 d1 : Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → t.privateInput = s.privateInput →
      Unchanged [(sp - 0x420#64, 132), (out, 17), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out V t → Region de [d0, d1] t → V.length = 17 →
      ((V = instW O (W0 ++ W1 ++ W2 ++ W3) ∧ d0 = q + 128#64 ∧ d1 = l - 128#64 ∧ 128 ≤ l.toNat) ∨
        (∃ e : Word, V = replaceByte O[0]! 0 1#8 :: e :: O.drop 2 ∧ l.toNat < 128)) → Safe P t) :
    Safe P s :=
  instance_visitor_spec s ra sp out de q l O W0 W1 W2 W3 hOl hW0l hW1l hW2l hW3l hpc hcode hcodeA
    hcodeN hcodeM hcw hra hra1 hsp hstk ha0 ha1 ha5 hO hokO hD hokD hW0 hW1 hW2 hW3 hq hokW hdO hdD
    heD hOlo hDlo hio
    (fun t h1 h2 h3 hp h4 hV hd hl =>
      hk t _ _ _ h1 h2 h3 hp h4 hV hd (by simp) (Or.inl ⟨rfl, rfl, rfl, hl⟩))
    (fun t e d0 d1 h1 h2 h3 hp h4 hV hd hl =>
      hk t _ _ _ h1 h2 h3 hp h4 hV hd (by simp [hOl]) (Or.inr ⟨e, rfl, hl⟩))

/-- `SpendValidatingKey::from_bytes` with the output's length (inside `SvkPost`) stated where the
executor reads post regions. -/
theorem spend_validating_key_from_bytes_spec' {P : Prop} (s : MachineState) (ra sp a0 a1 : Word)
    (b0 b1 b2 b3 cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (O IV G0 G1 G2 G3 : List Word)
    (hOl : O.length = 17) (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → Safe P u)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → Safe P u)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → Safe P u)
    (hprz : ∀ u : MachineState, u.pc = 0x7803de78#64 → u.code = s.code → Safe P u)
    (hpc : s.pc = 0x78022514#64) (hcode : CodeAt F_78022514.base F_78022514.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hcodeU : CodeAt F_78026928.base F_78026928.prog s)
    (hcodeF : CodeAt F_78025a1c.base F_78025a1c.prog s)
    (hcodeMC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeP : CodeAt F_78029d94.base F_78029d94.prog s)
    (hcodeC : CodeAt F_7802f358.base F_7802f358.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeA : CodeAt F_780315c0.base F_780315c0.prog s)
    (hcodeR : CodeAt F_78028298.base F_78028298.prog s)
    (hcodeT : CodeAt F_78029468.base F_78029468.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x960 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (ha2 : s.getReg .x12 = 32#64)
    (hB : Region a1 [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 17)
    -- `FP_TABLES`, initialised (`Once` state byte 2 at 0x780488f0, padding zero)
    (hTB : Region 0x780488a8#64 [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx, 2#64] s)
    (hIV : Region iptr IV s) (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hG0 : Region g0 G0 s) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024)
    (hG1 : Region g1 G1 s) (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024)
    (hG2 : Region g2 G2 s) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024)
    (hG3 : Region g3 G3 s) (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hd0 : Disjoint (sp - 0x960#64) 300 a0 13) (hd_a1 : Disjoint (sp - 0x960#64) 300 a1 4)
    (hd_tb : Disjoint (sp - 0x960#64) 300 0x780488a8#64 10)
    (hd_iptr : Disjoint (sp - 0x960#64) 300 iptr 138)
    (hd_g0 : Disjoint (sp - 0x960#64) 300 g0 1024) (hd_g1 : Disjoint (sp - 0x960#64) 300 g1 1024)
    (hd_g2 : Disjoint (sp - 0x960#64) 300 g2 1024) (hd_g3 : Disjoint (sp - 0x960#64) 300 g3 516)
    (he_a1 : Disjoint a0 17 a1 4) (he_tb : Disjoint a0 17 0x780488a8#64 10)
    (he_iptr : Disjoint a0 17 iptr 138)
    (he_g0 : Disjoint a0 17 g0 1024) (he_g1 : Disjoint a0 17 g1 1024)
    (he_g2 : Disjoint a0 17 g2 1024) (he_g3 : Disjoint a0 17 g3 516)
    (hk : ∀ (t : MachineState) (tag : Word) (L : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x960#64, 300), (a0, 17)] s t →
      L.length = 16 → SvkPost b0 b1 b2 b3 tag L → Region a0 (tag :: L) t → Safe P t) :
    Safe P s :=
  spend_validating_key_from_bytes_spec s ra sp a0 a1 b0 b1 b2 b3 cap iptr ilen g0 g1 g2 g3 hmod hx O IV G0 G1 G2 G3 hOl hIVl hG0l hG1l hG2l hG3l hpb hpaf hpp hprz hpc hcode hcodeCmp hcodeU hcodeF hcodeMC hcodeM hcodeP hcodeC hcodeL hcodeB hcodeA hcodeR hcodeT hcw hro hra hra1 hsp hstk ha0 ha1 ha2 hB hok_a1 hO hok0 hTB hIV hok_iptr hG0 hok_g0 hG1 hok_g1 hG2 hok_g2 hG3 hok_g3 hilen hd0 hd_a1 hd_tb hd_iptr hd_g0 hd_g1 hd_g2 hd_g3 he_a1 he_tb he_iptr he_g0 he_g1 he_g2 he_g3
    (fun t tag L h1 h2 h3 h4 hp hR => hk t tag L h1 h2 h3 h4 hp.1 hp hR)

/-- `merklePathW` keeps the 130 words of `Option<([Rho; 32], u32)>`. -/
theorem merklePathW_length (O H : List Word) (pw : Word) (hOl : O.length = 130) :
    (merklePathW O H pw).length = 130 := by
  unfold merklePathW; split <;> simp [hOl]

/-- `parse_merkle_path_spec` with the output as a 130-word list (its value is unused in `main`:
divergence 1 of `Zip2005.Divergences`). -/
theorem parse_merkle_path_spec' {P : Prop} (s : MachineState) (ra sp out w pw : Word)
    (H O : List Word) (hHl : H.length = 128) (hOl : O.length = 130)
    (hpc : s.pc = 0x7801d098#64) (hcode : CodeAt F_7801d098.base F_7801d098.prog s)
    (hcodeRho : CodeAt F_7801ddd8.base F_7801ddd8.prog s)
    (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcodeMC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x5c0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = w)
    (hH : Region w H s) (hokH : RegionOk Ro.layout.roBase Ro.layout.textHi w 128)
    (hP : Region (w + 0x508#64) [pw] s) (hokP : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 0x508#64) 1)
    (hO : Region out O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi out 130)
    (hd0 : Disjoint (sp - 0x5c0#64) 184 out 130) (hdH : Disjoint (sp - 0x5c0#64) 184 w 128)
    (hdP : Disjoint (sp - 0x5c0#64) 184 (w + 0x508#64) 1)
    (heH : Disjoint out 130 w 128) (heP : Disjoint out 130 (w + 0x508#64) 1)
    (hhO : Disjoint 0x78040620#64 14780694332 out 130) (hhH : Disjoint 0x78040620#64 14780694332 w 128)
    (hhP : Disjoint 0x78040620#64 14780694332 (w + 0x508#64) 1)
    -- `raw_vec::handle_error` diverges (an allocation failure)
    (hhandle : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → Safe P u)
    -- `__rust_alloc(0x80, 8)` (ledger T2): a fresh 8-aligned block in the arena
    (halloc : ∀ (u : MachineState) (sp' : Word), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801d114#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x80#64 → u.getReg .x11 = 8#64 →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x7801d114#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 16 → Region ptr B t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 16 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 0x80 ≤ 0x1c00000000 → Safe P t) → Safe P u)
    -- `RawVecInner::reserve::do_reserve_and_handle` on a full `Vec<Rho>` (ledger T2): capacity
    -- doubled (`max(2·cap, len + 1, 4)` with `len = cap ≥ 4`), the old contents moved to a fresh
    -- block, the old one freed
    (hreserve : ∀ (u : MachineState) (sp' hdr ptr : Word) (n : Nat) (B : List Word),
      u.pc = 0x7801cac0#64 → u.code = s.code → u.getReg .x1 = 0x7801d1e8#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x100 sp' → u.getReg .x10 = hdr →
      u.getReg .x11 = BitVec.ofNat 64 n →
      Region hdr [BitVec.ofNat 64 n, ptr, BitVec.ofNat 64 n] u → RegionOk Ro.layout.roBase Ro.layout.textHi hdr 3 →
      Disjoint (sp' - 0x100#64) 32 hdr 3 → Disjoint 0x78040620#64 14780694332 hdr 3 →
      4 ≤ n → n ≤ 16 → B.length = 4 * n → Region ptr B u →
      0x78048980 ≤ ptr.toNat → ptr.toNat + 32 * n ≤ 0x1c00000000 →
      (∀ (t : MachineState) (ptr' : Word) (B' : List Word), t.pc = 0x7801d1e8#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x100#64, 32), (hdr, 3), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region hdr [BitVec.ofNat 64 (2 * n), ptr', BitVec.ofNat 64 n] t → B'.length = 4 * n →
        Region ptr' (B ++ B') t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr' (8 * n) →
        0x78048980 ≤ ptr'.toNat → ptr'.toNat + 64 * n ≤ 0x1c00000000 → Safe P t) → Safe P u)
    -- `__rust_dealloc(ptr, 32·cap, 8)` (ledger T2)
    (hdealloc : ∀ (u : MachineState) (sp' r ptr sz : Word), u.pc = 0x7801bd08#64 →
      u.code = s.code → u.getReg .x1 = r → r &&& ~~~1#64 = r → u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' →
      u.getReg .x10 = ptr → u.getReg .x11 = sz → u.getReg .x12 = 8#64 →
      0x78048980 ≤ ptr.toNat →
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Safe P t) → Safe P u)
    (hk : ∀ t (M : List Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x5c0#64, 184), (out, 130), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      M.length = 130 → Region out M t → Safe P t) :
    Safe P s :=
  parse_merkle_path_spec s ra sp out w pw H O hHl hOl hpc hcode hcodeRho hcodeR hcodeM hcodeB hcodeSh hcodeMC hcw hro hra hra1 hsp hstk ha0 ha1 hH hokH hP hokP hO hok0 hd0 hdH hdP heH heP hhO hhH hhP hhandle halloc hreserve hdealloc (fun t h1 h2 h3 h4 hR => hk t _ h1 h2 h3 h4 (merklePathW_length O H pw hOl) hR)

/-- `enc_from_bytes_spec` on a canonical input: the limbs in Montgomery form and the flag byte `1`, with no `if` left in the output region. -/
theorem enc_from_bytes_ok_spec {P : Prop} (s : MachineState) (ra sp a0 a1 : Word) (b0 b1 b2 b3 : Word)
    (O : List Word) (hOl : O.length = 5)
    (hpc : s.pc = 0x7801f5a4#64) (hcode : CodeAt F_7801f5a4.base F_7801f5a4.prog s)
    (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x110 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hB : Region a1 [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5)
    (hd0 : Disjoint (sp - 0x110#64) 34 a0 5) (hd_a1 : Disjoint (sp - 0x110#64) 34 a1 4)
    (he_a1 : Disjoint a0 5 a1 4)
    (hc : Accel.leLimbsToNat [b0, b1, b2, b3] < Fp.p)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x110#64, 34), (a0, 5)] s t →
      Region a0 [BitVec.ofNat 64 (Fp.mul (Accel.leLimbsToNat [b0, b1, b2, b3]) Fp.R2), BitVec.ofNat 64 ((Fp.mul (Accel.leLimbsToNat [b0, b1, b2, b3]) Fp.R2) >>> 64),
        BitVec.ofNat 64 ((Fp.mul (Accel.leLimbsToNat [b0, b1, b2, b3]) Fp.R2) >>> 128), BitVec.ofNat 64 ((Fp.mul (Accel.leLimbsToNat [b0, b1, b2, b3]) Fp.R2) >>> 192),
        replaceByte O[4]! 0 1#8] t → Safe P t) :
    Safe P s :=
  enc_from_bytes_spec s ra sp a0 a1 b0 b1 b2 b3 O hOl hpc hcode hcodeR hcodeM hcodeB hcw hro hra hra1 hsp hstk ha0 ha1 hB hok_a1 hO hok0 hd0 hd_a1 he_a1 (fun t h1 h2 h3 h4 hR => hk t h1 h2 h3 h4 (by simpa only [natToLeLimbs_four, ctLimbs_four, if_pos hc] using hR))

/-- `enc_from_bytes_spec` on a non-canonical input: zero limbs and the flag byte `0`, with no `if` left in the output region. -/
theorem enc_from_bytes_bad_spec {P : Prop} (s : MachineState) (ra sp a0 a1 : Word) (b0 b1 b2 b3 : Word)
    (O : List Word) (hOl : O.length = 5)
    (hpc : s.pc = 0x7801f5a4#64) (hcode : CodeAt F_7801f5a4.base F_7801f5a4.prog s)
    (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x110 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hB : Region a1 [b0, b1, b2, b3] s) (hok_a1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5)
    (hd0 : Disjoint (sp - 0x110#64) 34 a0 5) (hd_a1 : Disjoint (sp - 0x110#64) 34 a1 4)
    (he_a1 : Disjoint a0 5 a1 4)
    (hc : ¬ Accel.leLimbsToNat [b0, b1, b2, b3] < Fp.p)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x110#64, 34), (a0, 5)] s t →
      Region a0 [0#64, 0#64, 0#64, 0#64, replaceByte O[4]! 0 0#8] t → Safe P t) :
    Safe P s :=
  enc_from_bytes_spec s ra sp a0 a1 b0 b1 b2 b3 O hOl hpc hcode hcodeR hcodeM hcodeB hcw hro hra hra1 hsp hstk ha0 ha1 hB hok_a1 hO hok0 hd0 hd_a1 he_a1 (fun t h1 h2 h3 h4 hR => hk t h1 h2 h3 h4 (by simpa only [natToLeLimbs_four, ctLimbs_four, if_neg hc] using hR))

end Cases.Zip2005
