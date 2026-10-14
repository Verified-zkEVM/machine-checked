import Cases.Zip2005.Orchard.NoteCommitDerive
import Cases.Zip2005.Orchard.NullifierDerive
import Cases.Zip2005.Image.Ro

/-!
# The note commitment's `Z` is canonical

`Nullifier::derive` takes the commitment's `Z` limbs below `p` (`hcz`); `main` gets it from
`NoteCommitment::derive`'s output, the `conditional_select` of `commitW` and the identity.
Every outcome of `Fp.addJ` keeps `Z < p` when both inputs' `Z` are, and both inputs are: the
Sinsemilla hash point (`Z` is `0` or `R`) and `[rcm] R` (`mulW_Z_lt`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

theorem Fp.addJ_Z_lt {X1 Y1 Z1 X2 Y2 Z2 : Nat} (h1 : Z1 < Fp.p) (h2 : Z2 < Fp.p) :
    (Fp.addJ X1 Y1 Z1 X2 Y2 Z2).2.2 < Fp.p := by
  unfold Fp.addJ
  dsimp only
  split_ifs
  · exact h2
  · exact h1
  · dsimp only [Fp.dblJ]; split <;> first | exact Fp.p_pos | exact Fp.add_lt _ _
  · exact Fp.p_pos
  · dsimp only [Fp.addJ_main]; exact Fp.mul_lt _ _

theorem commitHash_Z_lt (Q Bv : List Word) : ptZ (commitHash Q Bv) < Fp.p := by
  unfold commitHash
  cases commitFold Q Bv with
  | none => unfold ptZ; decide
  | some L =>
    simp only [Option.elim, ptZ, toCurveW, unpackW, natToLeLimbs_four, List.cons_append,
      List.nil_append, List.getElem!_cons_succ, List.getElem!_cons_zero]
    split_ifs
    · decide
    · have h := leLimbsToNat_natToLeLimbs 4 Fp.R (lt_trans Fp.R_lt Fp.p_lt)
      rw [natToLeLimbs_four] at h
      rw [h]; exact Fp.R_lt

/-- The `Z` limbs of `NoteCommitment::derive`'s output are below `p`. -/
theorem cmSel_Z_lt (Q R B k : List Word) :
    leLimbsToNat [(cmSel Q R B k)[8]!, (cmSel Q R B k)[9]!, (cmSel Q R B k)[10]!,
      (cmSel Q R B k)[11]!] < Fp.p := by
  have hz : jZ (commitJ Q R B k) < Fp.p := by
    rw [jZ_eq, commitJ_eq]
    exact Fp.addJ_Z_lt (commitHash_Z_lt Q B) (by unfold ptZ; exact mulW_Z_lt R k)
  have h := leLimbsToNat_natToLeLimbs 4 (jZ (commitJ Q R B k)) (lt_trans hz Fp.p_lt)
  unfold cmSel
  cases (commitFold Q B).isSome
  · simp only [cond_false, List.getElem!_cons_succ, List.getElem!_cons_zero]
    exact lt_of_eq_of_lt (by decide) Fp.p_pos
  · simp only [cond_true, commitW, natToLeLimbs_four, List.cons_append, List.nil_append,
      List.getElem!_cons_succ, List.getElem!_cons_zero] at h ⊢
    rw [h]; exact hz

/-- `note_commitment_derive_spec` with the output's cells named: the model equation, the flag
cell and the `Z` limbs below `p` as separate facts, for a caller whose next callee needs them. -/
theorem note_commitment_derive_spec' {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState)
    (ra sp out gd pkd v rho psi rcm : Word)
    (g0 g1 g2 g3 p0 p1 p2 p3 r0 r1 r2 r3 q0 q1 q2 q3 k0 k1 k2 k3 : Word)
    (O J : List Word) (hOl : O.length = 13) (hJl : J.length = 15)
    (hpaf : ∀ u : MachineState, u.pc = 0x7803a110#64 → u.code = s.code → SafeN G n P u)
    (hpanic : ∀ u : MachineState, u.pc = 0x7803de40#64 → u.code = s.code → SafeN G n P u)
    (hunwrap : ∀ u : MachineState, u.pc = 0x7803dc7c#64 → u.code = s.code → SafeN G n P u)
    (hbounds : ∀ u : MachineState, u.pc = 0x7803dcdc#64 → u.code = s.code → SafeN G n P u)
    (hpc : s.pc = 0x7801fbcc#64) (hcode : CodeAt F_7801fbcc.base F_7801fbcc.prog s)
    -- callees: cached_commit_domain (+ from_raw, from_xy, is_on_curve, mulmod, black_box,
    -- to_curve), to_le_bits (+ to_repr), commit and its callees, memset, conditional_select
    (hcodeCD : CodeAt F_78020548.base F_78020548.prog s) (hcodeLB : CodeAt F_78029b18.base F_78029b18.prog s)
    (hcodeCm : CodeAt F_78020d50.base F_78020d50.prog s)
    (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s) (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeBB : CodeAt F_7803a0fc.base F_7803a0fc.prog s) (hcodeCo : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeP : CodeAt F_780237dc.base F_780237dc.prog s) (hcodeRp : CodeAt F_78029468.base F_78029468.prog s)
    (hcodeL : CodeAt F_780234cc.base F_780234cc.prog s) (hcodeIA : CodeAt F_780235e8.base F_780235e8.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s) (hcodeAA : CodeAt F_78035f88.base F_78035f88.prog s)
    (hcodeLR : CodeAt F_780360e0.base F_780360e0.prog s) (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcodeU : CodeAt F_78023864.base F_78023864.prog s) (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeXY : CodeAt F_78026878.base F_78026878.prog s) (hcodeOC : CodeAt F_78026258.base F_78026258.prog s)
    (hcodeFR : CodeAt F_78028298.base F_78028298.prog s) (hcodeTC : CodeAt F_78025854.base F_78025854.prog s)
    (hcodeF : CodeAt F_780239bc.base F_780239bc.prog s) (hcodeBt : CodeAt F_78023544.base F_78023544.prog s)
    (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcodeCS : CodeAt F_78023d7c.base F_78023d7c.prog s)
    (hcodeB : CodeAt F_78023594.base F_78023594.prog s) (hcodeW : CodeAt F_7802827c.base F_7802827c.prog s)
    (hcodeMul : CodeAt F_78031be8.base F_78031be8.prog s) (hcodeRq : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    (hcodeA : CodeAt F_78035fe0.base F_78035fe0.prog s) (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcodeD : CodeAt F_780360c8.base F_780360c8.prog s) (hcodeAF : CodeAt F_7803a110.base F_7803a110.prog s)
    (hcodeAFI : CodeAt F_7803dd28.base F_7803dd28.prog s) (hcodeEA : CodeAt F_78026b44.base F_78026b44.prog s)
    (hcodeED : CodeAt F_7802413c.base F_7802413c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0xb50 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = gd) (ha2 : s.getReg .x12 = pkd)
    (ha3 : s.getReg .x13 = v) (ha4 : s.getReg .x14 = rho) (ha5 : s.getReg .x15 = psi)
    (ha6 : s.getReg .x16 = rcm)
    (hG : Region gd [g0, g1, g2, g3] s) (hokG : RegionOk Ro.layout.textLo Ro.layout.textHi gd 4)
    (hP : Region pkd [p0, p1, p2, p3] s) (hokP : RegionOk Ro.layout.textLo Ro.layout.textHi pkd 4)
    (hR : Region rho [r0, r1, r2, r3] s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi rho 4)
    (hS : Region psi [q0, q1, q2, q3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi psi 4)
    (hK : Region rcm [k0, k1, k2, k3] s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi rcm 4)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 13)
    -- the frame's iterator block before the call: the struct's padding bytes keep these
    (hJ : Region (sp - 0xb50#64 + 0xa08#64) J s)
    (hd0 : Disjoint (sp - 0xb50#64) 362 out 13) (hd1 : Disjoint (sp - 0xb50#64) 362 gd 4)
    (hd2 : Disjoint (sp - 0xb50#64) 362 pkd 4) (hd3 : Disjoint (sp - 0xb50#64) 362 rho 4)
    (hd4 : Disjoint (sp - 0xb50#64) 362 psi 4) (hd5 : Disjoint (sp - 0xb50#64) 362 rcm 4)
    (he0 : Disjoint out 13 gd 4) (he1 : Disjoint out 13 pkd 4) (he2 : Disjoint out 13 rho 4)
    (he3 : Disjoint out 13 psi 4) (he4 : Disjoint out 13 rcm 4)
    (hh0 : Disjoint 0x78040620#64 14780694332 out 13) (hh1 : Disjoint 0x78040620#64 14780694332 rcm 4)
    -- `Vec<bool>::from_iter` of the padded bit iterator (ledger T2): the iterator block as
    -- `derive` builds it (ITER_CELLS: tags, lengths and pointers into this frame — `ρ`'s bits at
    -- `+0x1e8`, `ψ`'s at `+0x208`, `g★_d` at `+0x1a0`, `pk★_d` at `+0x1c0`, `v` at `+0x1e0` —
    -- with the struct's padding bytes `J` left as they were) over the message words at
    -- `+0x1a0` yields 1090 bytes, byte `o` the message bit `o`
    (hfrom : ∀ (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word), O1.length = 3 →
      u.pc = 0x7801dfb4#64 → u.code = s.code → u.getReg .x1 = 0x78020dc4#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x260 sp' → u.getReg .x10 = a0' → u.getReg .x11 = a1' →
      Region a0' O1 u → Region a1' [0#64, j] u →
      Region (a1' + 0x10#64) (iterW sp J) u →
      Region (a1' + 0x88#64) [0#64] u →
      Region (sp - 0xb50#64 + 0xa80#64) ([g0, g1, g2, g3, p0, p1, p2, p3, v] ++
        reprW [r0, r1, r2, r3] ++ reprW [q0, q1, q2, q3]) u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 3 → RegionOk Ro.layout.roBase Ro.layout.textHi a1' 18 →
      Disjoint (sp' - 0x260#64) 76 a0' 3 → Disjoint (sp' - 0x260#64) 76 a1' 18 →
      Disjoint a0' 3 a1' 18 →
      StackOk Ro.layout 0xb50 sp →
      Disjoint (sp' - 0x260#64) 76 (sp - 0xb50#64 + 0xa80#64) 17 → Disjoint a0' 3 (sp - 0xb50#64 + 0xa80#64) 17 → Disjoint a1' 18 (sp - 0xb50#64 + 0xa80#64) 17 →
      Disjoint 0x78040620#64 14780694332 a0' 3 → Disjoint 0x78040620#64 14780694332 a1' 18 →
      (∀ (t : MachineState) (cap ptr : Word) (J Bv : List Word), t.pc = 0x78020dc4#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x260#64, 76), (a0', 3), (a1', 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        J.length = 18 → Region a0' [cap, ptr, 1090#64] t → cap ≠ 0#64 → Region a1' J t →
        Bv.length = 137 →
        (∀ o, o < 1090 → byteAt Bv o = bw (noteBit [g0, g1, g2, g3] [p0, p1, p2, p3] v
          (reprW [r0, r1, r2, r3]) (reprW [q0, q1, q2, q3]) o)) →
        Region ptr Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 137 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 137 ≤ 0x1c00000000 → SafeN G n P t) → SafeN G n P u)
    -- `__rust_dealloc` of that `Vec` (ledger T2)
    (hdealloc : ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word), C.length = 137 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780210f0#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap →
      u.getReg .x12 = 1#64 → Region ptr C u → 0x78048980 ≤ ptr.toNat →
      ptr.toNat + 8 * 137 ≤ 0x1c00000000 →
      (∀ t, t.pc = 0x780210f0#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → SafeN G n P t) → SafeN G n P u)
    (hk : ∀ (t : MachineState) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 cf : Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code →
      Unchanged [(sp - 0xb50#64, 362), (out, 13), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] = cmSel qNoteW rNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3]) [k0, k1, k2, k3] →
      cf = replaceByte O[12]! 0 (commitFlag qNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3])) →
      leLimbsToNat [c8, c9, c10, c11] < Fp.p →
      Region out [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11] t → Region (out + 0x60#64) [cf] t →
      mulFacts rNoteW [k0, k1, k2, k3] → SafeN G n P t) :
    SafeN G n P s :=
  note_commitment_derive_spec s ra sp out gd pkd v rho psi rcm g0 g1 g2 g3 p0 p1 p2 p3 r0 r1 r2 r3 q0 q1 q2 q3 k0 k1 k2 k3 O J hOl hJl hpaf hpanic hunwrap hbounds hpc hcode hcodeCD hcodeLB hcodeCm hcodeC hcodeTA hcodeI hcodeM hcodeBB hcodeCo hcodeP hcodeRp hcodeL hcodeIA hcodeCmp hcodeAA hcodeLR hcodeAdd hcodeU hcodeR hcodeXY hcodeOC hcodeFR hcodeTC hcodeF hcodeBt hcodeS hcodeCS hcodeB hcodeW hcodeMul hcodeRq hcodeA hcodeDbl hcodeD hcodeAF hcodeAFI hcodeEA hcodeED hcw hro hra hra1 hsp hstk ha0 ha1 ha2 ha3 ha4 ha5 ha6 hG hokG hP hokP hR hokR hS hokS hK hokK hO hokO hJ hd0 hd1 hd2 hd3 hd4 hd5 he0 he1 he2 he3 he4 hh0 hh1 hfrom hdealloc (fun t h1 h2 h3 h4 hR hF hm => hk t (cmSel qNoteW rNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3]) [k0, k1, k2, k3])[0]! (cmSel qNoteW rNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3]) [k0, k1, k2, k3])[1]! (cmSel qNoteW rNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3]) [k0, k1, k2, k3])[2]! (cmSel qNoteW rNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3]) [k0, k1, k2, k3])[3]! (cmSel qNoteW rNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3]) [k0, k1, k2, k3])[4]! (cmSel qNoteW rNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3]) [k0, k1, k2, k3])[5]! (cmSel qNoteW rNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3]) [k0, k1, k2, k3])[6]! (cmSel qNoteW rNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3]) [k0, k1, k2, k3])[7]! (cmSel qNoteW rNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3]) [k0, k1, k2, k3])[8]! (cmSel qNoteW rNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3]) [k0, k1, k2, k3])[9]! (cmSel qNoteW rNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3]) [k0, k1, k2, k3])[10]! (cmSel qNoteW rNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3]) [k0, k1, k2, k3])[11]! _ h1 h2 h3 h4 (cells12_eq _ (cmSel_length _ _ _ _)) rfl (cmSel_Z_lt _ _ _ _) (by rw [cells12_eq _ (cmSel_length _ _ _ _)]; exact hR) hF hm)

end Cases.Zip2005
