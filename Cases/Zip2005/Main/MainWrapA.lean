import Cases.Zip2005.Runtime.Memcpy_d0s0_1383
import Cases.Zip2005.Kit.ByteKit
import Cases.Zip2005.Orchard.DeriveUnchecked
import Cases.Zip2005.Orchard.SpendingKeyFrom
import Cases.Zip2005.Witness.ParseKeys
import Cases.Zip2005.Main.MainWrapC
import Cases.Zip2005.Orchard.SpendValidatingKey
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# Wrappers for `main`'s segment A1

`memcpy(sp + 0x90, sp + 0xb00, 0x567)` moves `Ok(witness)` (bar its first and last bytes'
neighbours) into the frame. `memcpy_d0s0_1383_spec` states the copy byte by byte (`mcpyW`); here
the first 172 cells are the source's and the last is seven source bytes and one kept byte, so
the executor reads the cells off the source's literal.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

theorem word8_bytes (w : Word) :
    word8 (extractByte w 0) (extractByte w 1) (extractByte w 2) (extractByte w 3) (extractByte w 4)
      (extractByte w 5) (extractByte w 6) (extractByte w 7) = w := by
  apply word_ext
  intro k hk
  interval_cases k <;> simp (disch := decide) only [byte_simp]

/-- A doubleword assembled from eight loaded bytes the way `main` builds the `sk` words (`lbu`,
shifts by 8, 16, 24 and 32, `or`): the bytes' `word8`. -/
theorem asm_word8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((BitVec.zeroExtend 64 b7 <<< 24 ||| BitVec.zeroExtend 64 b6 <<< 16) |||
        (BitVec.zeroExtend 64 b5 <<< 8 ||| BitVec.zeroExtend 64 b4)) <<< 32 |||
      ((BitVec.zeroExtend 64 b3 <<< 24 ||| BitVec.zeroExtend 64 b2 <<< 16) |||
        (BitVec.zeroExtend 64 b1 <<< 8 ||| BitVec.zeroExtend 64 b0)) =
      word8 b0 b1 b2 b3 b4 b5 b6 b7 := by
  apply word_ext
  intro k hk
  interval_cases k <;> simp (disch := decide) only [byte_simp]

theorem mcByte_in (D S : List Word) (n i k : Nat) (hk : k < 8) (h : 8 * i + k < n) :
    mcByte D S 0 0 n i k = extractByte S[i]! k := by
  unfold mcByte
  rw [if_pos (by omega)]
  rw [show (8 * i + k - 0 + 0) / 8 = i by omega, show (8 * i + k - 0 + 0) % 8 = k by omega]

theorem mcByte_out (D S : List Word) (n i k : Nat) (h : n ≤ 8 * i + k) :
    mcByte D S 0 0 n i k = extractByte D[i]! k := by
  unfold mcByte
  rw [if_neg (by omega)]

/-- The 1383-byte copy: 172 whole source cells, then seven source bytes and the kept top byte. -/
theorem mcpyW_1383 (D S : List Word) (hSl : S.length = 173) :
    mcpyW D S 0 0 1383 173 = S.take 172 ++
      [word8 (extractByte S[172]! 0) (extractByte S[172]! 1) (extractByte S[172]! 2)
        (extractByte S[172]! 3) (extractByte S[172]! 4) (extractByte S[172]! 5)
        (extractByte S[172]! 6) (extractByte D[172]! 7)] := by
  apply List.ext_getElem
  · simp [hSl]
  · intro i h1 h2
    simp only [mcpyW_length] at h1
    rw [← getElem!_pos (mcpyW D S 0 0 1383 173) i (by simpa using h1),
      mcpyW_getElem! _ _ _ _ _ _ _ h1]
    by_cases hi : i < 172
    · rw [List.getElem_append_left (by simp [hSl]; omega), List.getElem_take,
        ← getElem!_pos S i (by omega)]
      rw [mcByte_in D S 1383 i 0 (by decide) (by omega), mcByte_in D S 1383 i 1 (by decide) (by omega),
        mcByte_in D S 1383 i 2 (by decide) (by omega), mcByte_in D S 1383 i 3 (by decide) (by omega),
        mcByte_in D S 1383 i 4 (by decide) (by omega), mcByte_in D S 1383 i 5 (by decide) (by omega),
        mcByte_in D S 1383 i 6 (by decide) (by omega), mcByte_in D S 1383 i 7 (by decide) (by omega)]
      exact word8_bytes _
    · have e : i = 172 := by omega
      subst e
      rw [List.getElem_append_right (by simp [hSl])]
      simp only [List.length_take, hSl, show min 172 173 = 172 from rfl, Nat.sub_self,
        List.getElem_cons_zero]
      rw [mcByte_in D S 1383 172 0 (by decide) (by decide), mcByte_in D S 1383 172 1 (by decide) (by decide),
        mcByte_in D S 1383 172 2 (by decide) (by decide), mcByte_in D S 1383 172 3 (by decide) (by decide),
        mcByte_in D S 1383 172 4 (by decide) (by decide), mcByte_in D S 1383 172 5 (by decide) (by decide),
        mcByte_in D S 1383 172 6 (by decide) (by decide), mcByte_out D S 1383 172 7 (by decide)]

/-- `memcpy_d0s0_1383_spec` with the cells read off the source. -/
theorem memcpy1383_take_spec {Gd : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 173) (hSl : S.length = 173)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 1383#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 173)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 173)
    (hdj : Disjoint dst 173 src 173)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 173)] s t →
      Region dst (S.take 172 ++
        [word8 (extractByte S[172]! 0) (extractByte S[172]! 1) (extractByte S[172]! 2)
          (extractByte S[172]! 3) (extractByte S[172]! 4) (extractByte S[172]! 5)
          (extractByte S[172]! 6) (extractByte D[172]! 7)]) t → SafeN Gd n P t) :
    SafeN Gd n P s :=
  memcpy_d0s0_1383_spec s ra dst src D S hDl hSl hpc hcode hcw hra hra1 ha0 ha1 ha2 hD hokD hS hokS
    hdj (fun t h1 h2 h3 h4 h5 => hk t h1 h2 h3 h4 (h5.of_eq (mcpyW_1383 D S hSl)))

/-- `derive_unchecked_spec` with the twenty output cells named: `askW` (the point `[ask] G`, its
bytes, the scalar) is a model the executor cannot read cell by cell. -/
theorem derive_unchecked_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out sk neg s0 s1 s2 s3 : Word)
    (cap iptr ilen g0 g1 g2 g3 hmod hx : Word) (O IV G0 G1 G2 G3 : List Word)
    (hOl : O.length = 20) (hIVl : IV.length = 138)
    (hG0l : G0.length = 1024) (hG1l : G1.length = 1024) (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hpb : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G n P u)
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN G n P u)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G n P u)
    (hprz : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de78#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de78 → SafeN G n P u)
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (hunwrap : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dc7c#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_dc7c_10 → u.getReg .x13 ∈ Run.vals_dc7c_13 → u.getReg .x14 ∈ Run.vals_dc7c_14 → SafeN G n P u)
    (hpc : s.pc = 0x7802233c#64) (hcode : CodeAt F_7802233c.base F_7802233c.prog s)
    -- `PrfExpand::with`
    (hcW : CodeAt F_78023308.base F_78023308.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    -- `Fq::from_uniform_bytes`, `to_repr`
    (hcodeFU : CodeAt F_7802f038.base F_7802f038.prog s) (hcodeU5 : CodeAt F_7802e5b4.base F_7802e5b4.prog s)
    -- `try_from` and its callees
    (hcodeTF : CodeAt F_78022f5c.base F_78022f5c.prog s)
    (hcodeFR : CodeAt F_7802ed10.base F_7802ed10.prog s)
    (hcodeBP : CodeAt F_78023278.base F_78023278.prog s)
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
    (hcodeW : CodeAt F_7802827c.base F_7802827c.prog s)
    (hcodeMul : CodeAt F_78031be8.base F_78031be8.prog s)
    (hcodeMS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s)
    (hcodeCo : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeRq : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    (hcodeAs : CodeAt F_78035fe0.base F_78035fe0.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcodeD : CodeAt F_780360c8.base F_780360c8.prog s)
    (hcodeLn : CodeAt F_780360e0.base F_780360e0.prog s)
    (hcodeAF : CodeAt F_7803a110.base F_7803a110.prog s)
    (hcodeAFI : CodeAt F_7803dd28.base F_7803dd28.prog s)
    (hcodeTB : CodeAt F_78025654.base F_78025654.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0xb50 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = sk) (ha2 : s.getReg .x12 = neg)
    (hRS : Region sk [s0, s1, s2, s3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi sk 4)
    (hO : Region out O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi out 20)
    (hbelow_out : out.toNat + 8 * 20 ≤ 0x78040620)
    -- `FP_TABLES`, initialised (`Once` state byte 2 at 0x780488f0, padding zero)
    (hTB : Region 0x780488a8#64 [cap, iptr, ilen, g0, g1, g2, g3, hmod, hx, 2#64] s)
    (hIV : Region iptr IV s) (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138)
    (hG0 : Region g0 G0 s) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi g0 1024)
    (hG1 : Region g1 G1 s) (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi g1 1024)
    (hG2 : Region g2 G2 s) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi g2 1024)
    (hG3 : Region g3 G3 s) (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi g3 516)
    (hilen : ilen.toNat ≤ 1104)
    (hd0 : Disjoint (sp - 0xb50#64) 362 out 20) (hdS : Disjoint (sp - 0xb50#64) 362 sk 4)
    (hd_tb : Disjoint (sp - 0xb50#64) 362 0x780488a8#64 10)
    (hd_iptr : Disjoint (sp - 0xb50#64) 362 iptr 138)
    (hd_g0 : Disjoint (sp - 0xb50#64) 362 g0 1024) (hd_g1 : Disjoint (sp - 0xb50#64) 362 g1 1024)
    (hd_g2 : Disjoint (sp - 0xb50#64) 362 g2 1024) (hd_g3 : Disjoint (sp - 0xb50#64) 362 g3 516)
    (heS : Disjoint out 20 sk 4)
    (he_tb : Disjoint out 20 0x780488a8#64 10) (he_iptr : Disjoint out 20 iptr 138)
    (he_g0 : Disjoint out 20 g0 1024) (he_g1 : Disjoint out 20 g1 1024)
    (he_g2 : Disjoint out 20 g2 1024) (he_g3 : Disjoint out 20 g3 516)
    (hk : ∀ (t : MachineState) (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 : Word),
      t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0xb50#64, 362), (out, 20)] s t →
      FromBytesPost 0x8d1a7284b875c963#64 0xc7f0ce37b70a10c#64 0x3b8d187c3e5f445f#64 0xb75523b328f1d606#64
          (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) 1#8 ∧
        leLimbsToNat [z0, z1, z2, z3] =
          (if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R) ∧
        mulFacts [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] (skW (askR neg s0 s1 s2 s3)) →
      [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19] = askW neg s0 s1 s2 s3 [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] →
      Region out [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19] t → SafeN G n P t) :
    SafeN G n P s :=
  derive_unchecked_spec s ra sp out sk neg s0 s1 s2 s3 cap iptr ilen g0 g1 g2 g3 hmod hx O IV G0 G1 G2 G3 hOl hIVl hG0l hG1l hG2l hG3l hpb hpaf hpp hprz hpanic hunwrap hpc hcode hcW hcT hcU hcF hcL hcodeFU hcodeU5 hcodeTF hcodeFR hcodeBP hcodeU hcodeF hcodeMC hcodeM hcodeP hcodeC hcodeL hcodeB hcodeA hcodeR hcodeT hcodeW hcodeMul hcodeMS hcodeTA hcodeI hcodeCo hcodeRq hcodeAs hcodeCmp hcodeAdd hcodeDbl hcodeD hcodeLn hcodeAF hcodeAFI hcodeTB hcw hro hheap hra hra1 hsp hstk ha0 ha1 ha2 hRS hokS hO hok0 hbelow_out hTB hIV hok_iptr hG0 hok_g0 hG1 hok_g1 hG2 hok_g2 hG3 hok_g3 hilen hd0 hdS hd_tb hd_iptr hd_g0 hd_g1 hd_g2 hd_g3 heS he_tb he_iptr he_g0 he_g1 he_g2 he_g3 (fun t x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 h1 h2 h3 h4 hf hR => by
    generalize hL : askW neg s0 s1 s2 s3 [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] = L at hR
    have hl : L.length = 20 := by rw [← hL]; exact askW_length _ _ _ _ _ _
    match L, hl, hL with
    | [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19], _, hL =>
      exact hk t x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 h1 h2 h3 h4 hf hL.symm hR)

/-- `nk_from_spending_key_spec` with its frame obtained inside and its four output cells named (`nkW` hides a BLAKE2b compression the executor must not unfold). -/
theorem nk_from_spending_key_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out sk s0 s1 s2 s3 : Word)
    (hpc : s.pc = 0x780231e8#64) (hcode : CodeAt F_780231e8.base F_780231e8.prog s)
    (hcW : CodeAt F_78023308.base F_78023308.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeFU : CodeAt F_7802e2b4.base F_7802e2b4.prog s)
    (hcodeU : CodeAt F_78028718.base F_78028718.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x4d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = sk)
    (hRS : Region sk [s0, s1, s2, s3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi sk 4)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd1 : Disjoint (sp - 0x4d0#64) 154 sk 4) (hd2 : Disjoint (sp - 0x4d0#64) 154 out 4)
    (hd3 : Disjoint out 4 sk 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x4d0#64, 154), (out, 4)] s t →
      ∀ c0 c1 c2 c3 : Word, [c0, c1, c2, c3] = nkW s0 s1 s2 s3 →
      Region out [c0, c1, c2, c3] t → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨F1, hRF1, hF1⟩ := Region.exists_junk (sp - 0x4d0#64) 74 s
  obtain ⟨F2, hRF2, hF2⟩ := Region.exists_junk (sp - 0x280#64) 70 s
  exact nk_from_spending_key_spec s ra sp out sk s0 s1 s2 s3 F1 F2 hF1 hF2 hpc hcode hcW hcT hcU hcF hcL hcM hcC hcodeFU hcodeU hcodeM hcw hro hra hra1 hsp hstk ha0 ha1 hRF1 hRF2 hRS hokS hokO hd1 hd2 hd3 (fun t h1 h2 h3 h4 _ hR => by
    generalize hL : nkW s0 s1 s2 s3 = L at hR
    have hl : L.length = 4 := by rw [← hL]; unfold nkW; exact length_natToLeLimbs _ _
    match L, hl, hL with
    | [c0, c1, c2, c3], _, hL => exact hk t h1 h2 h3 h4 c0 c1 c2 c3 hL.symm hR)

/-- `rivk_from_spending_key_spec` with its frame obtained inside and its four output cells named (`rivkW` hides a BLAKE2b compression the executor must not unfold). -/
theorem rivk_from_spending_key_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp out sk s0 s1 s2 s3 : Word)
    (hpc : s.pc = 0x78023230#64) (hcode : CodeAt F_78023230.base F_78023230.prog s)
    (hcW : CodeAt F_78023308.base F_78023308.prog s)
    (hcT : CodeAt F_78032c1c.base F_78032c1c.prog s) (hcU : CodeAt F_78032db4.base F_78032db4.prog s)
    (hcF : CodeAt F_78032fa4.base F_78032fa4.prog s) (hcL : CodeAt F_78033260.base F_78033260.prog s)
    (hcM : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeFU : CodeAt F_7802f038.base F_7802f038.prog s)
    (hcodeU : CodeAt F_7802e5b4.base F_7802e5b4.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x4d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = sk)
    (hRS : Region sk [s0, s1, s2, s3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi sk 4)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd1 : Disjoint (sp - 0x4d0#64) 154 sk 4) (hd2 : Disjoint (sp - 0x4d0#64) 154 out 4)
    (hd3 : Disjoint out 4 sk 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x4d0#64, 154), (out, 4)] s t →
      ∀ c0 c1 c2 c3 : Word, [c0, c1, c2, c3] = rivkW s0 s1 s2 s3 →
      Region out [c0, c1, c2, c3] t → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨F1, hRF1, hF1⟩ := Region.exists_junk (sp - 0x4d0#64) 74 s
  obtain ⟨F2, hRF2, hF2⟩ := Region.exists_junk (sp - 0x280#64) 70 s
  exact rivk_from_spending_key_spec s ra sp out sk s0 s1 s2 s3 F1 F2 hF1 hF2 hpc hcode hcW hcT hcU hcF hcL hcM hcC hcodeFU hcodeU hcodeM hcw hro hra hra1 hsp hstk ha0 ha1 hRF1 hRF2 hRS hokS hokO hd1 hd2 hd3 (fun t h1 h2 h3 h4 _ hR => by
    generalize hL : rivkW s0 s1 s2 s3 = L at hR
    have hl : L.length = 4 := by rw [← hL]; unfold rivkW; exact length_natToLeLimbs _ _
    match L, hl, hL with
    | [c0, c1, c2, c3], _, hL => exact hk t h1 h2 h3 h4 c0 c1 c2 c3 hL.symm hR)

/-- `parse_nk_spec` on canonical bytes: tag `1`, the limbs named, with their value and canonicity. -/
theorem parse_nk_ok_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp a0 w : Word) (b0 b1 b2 b3 : Word)
    (O : List Word) (hOl : O.length = 5)
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN G n P u)
    (hpc : s.pc = 0x7801d2c8#64) (hcode : CodeAt F_7801d2c8.base F_7801d2c8.prog s)
    (hcodeF : CodeAt F_78022848.base F_78022848.prog s) (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s) (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x120 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = w)
    (hB : Region (w + 0x440#64) [b0, b1, b2, b3] s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 0x440#64) 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5)
    (hd0 : Disjoint (sp - 0x120#64) 36 a0 5) (hdB : Disjoint (sp - 0x120#64) 36 (w + 0x440#64) 4)
    (heB : Disjoint a0 5 (w + 0x440#64) 4)
    (hc : leLimbsToNat [b0, b1, b2, b3] < Fp.p)
    (hk : ∀ (t : MachineState) (r0 r1 r2 r3 : Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x120#64, 36), (a0, 5)] s t →
      leLimbsToNat [r0, r1, r2, r3] = Fp.mul (leLimbsToNat [b0, b1, b2, b3]) Fp.R2 →
      leLimbsToNat [r0, r1, r2, r3] < Fp.p →
      Region a0 [1#64, r0, r1, r2, r3] t → SafeN G n P t) :
    SafeN G n P s :=
  parse_nk_spec s ra sp a0 w b0 b1 b2 b3 O hOl hpaf hpc hcode hcodeF hcodeR hcodeM hcodeB hcw hro hheap hra hra1 hsp hstk ha0 ha1 hB hokB hO hok0 hd0 hdB heB (fun t tag L h1 h2 h3 h4 htag _ hLeq hR => by
    rw [if_pos hc] at htag; subst htag
    have e := hLeq hc; subst e
    have hX := leLimbsToNat_natToLeLimbs 4 (Fp.mul (leLimbsToNat [b0, b1, b2, b3]) Fp.R2) (lt_trans (Fp.mul_lt _ _) Fp.p_lt)
    rw [natToLeLimbs_four] at hR hX
    exact hk t _ _ _ _ h1 h2 h3 h4 hX (by rw [hX]; exact Fp.mul_lt _ _) hR)

/-- `parse_nk_spec` on non-canonical bytes: tag `0` (`None`). -/
theorem parse_nk_bad_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp a0 w : Word) (b0 b1 b2 b3 : Word)
    (O : List Word) (hOl : O.length = 5)
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN G n P u)
    (hpc : s.pc = 0x7801d2c8#64) (hcode : CodeAt F_7801d2c8.base F_7801d2c8.prog s)
    (hcodeF : CodeAt F_78022848.base F_78022848.prog s) (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s) (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x120 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = w)
    (hB : Region (w + 0x440#64) [b0, b1, b2, b3] s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 0x440#64) 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 5)
    (hd0 : Disjoint (sp - 0x120#64) 36 a0 5) (hdB : Disjoint (sp - 0x120#64) 36 (w + 0x440#64) 4)
    (heB : Disjoint a0 5 (w + 0x440#64) 4)
    (hc : ¬ leLimbsToNat [b0, b1, b2, b3] < Fp.p)
    (hk : ∀ (t : MachineState) (L : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(sp - 0x120#64, 36), (a0, 5)] s t → L.length = 4 →
      Region a0 (0#64 :: L) t → SafeN G n P t) :
    SafeN G n P s :=
  parse_nk_spec s ra sp a0 w b0 b1 b2 b3 O hOl hpaf hpc hcode hcodeF hcodeR hcodeM hcodeB hcw hro hheap hra hra1 hsp hstk ha0 ha1 hB hokB hO hok0 hd0 hdB heB (fun t tag L h1 h2 h3 h4 htag hL _ hR => by
    rw [if_neg hc] at htag; subst htag; exact hk t L h1 h2 h3 h4 hL hR)

/-- `SpendValidatingKey::from_bytes` returned `Some` (its tag word found non-zero by `main`'s
branch): the point's twelve words, their decoding facts, and the canonicity of `x` and `z`. -/
theorem svk_some (b0 b1 b2 b3 tag : Word) (L : List Word) (h : SvkPost b0 b1 b2 b3 tag L)
    (htag : ¬(tag == 0#64) = true) :
    ∃ x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word,
      L = [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3, b0, b1, b2, b3] ∧
      FromBytesPost b0 b1 b2 b3 (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) 1#8 ∧
      leLimbsToNat [z0, z1, z2, z3] =
        (if leLimbsToNat [x0, x1, x2, x3] = 0 ∧ leLimbsToNat [y0, y1, y2, y3] = 0 then 0 else Fp.R) ∧
      leLimbsToNat [x0, x1, x2, x3] < Fp.p ∧ leLimbsToNat [z0, z1, z2, z3] < Fp.p ∧
      [b0, b1, b2, b3] ≠ [0#64, 0#64, 0#64, 0#64] ∧ b3.msb = false := by
  have ht : tag ≠ 0#64 := by simpa using htag
  rcases h with ⟨-, ⟨h0, -⟩ | ⟨hb, hm, x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3, f, hfb, hz, htf, hL⟩⟩
  · exact absurd h0 ht
  · have hf : f = 1#8 := by
      rcases hfb.2.2 with ⟨hf, -⟩ | ⟨hf, -⟩
      · exact hf
      · subst hf; subst htf; exact absurd rfl ht
    subst hf
    refine ⟨x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3, hL rfl, hfb, hz, hfb.1, ?_, hb, hm⟩
    rw [hz]; split
    · exact Fp.p_pos
    · exact Fp.R_lt

end Cases.Zip2005
