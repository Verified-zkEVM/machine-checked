import Cases.Zip2005.Field.SqIterLoop
import Cases.Zip2005.Field.SqIterPro
import Cases.Zip2005.Field.SqIterTail
import Cases.Zip2005.Image.Ro

/-!
# `Vec<Fp>::from_iter` of `SqrtTables::new` (0x780326cc), as a function

`(0..256).map(|_| { let r = gp; gp *= g; r }).collect::<Vec<Fp>>()`: the entry
(`sq_iter_pro`), the loop (`sq_loop`, growing the buffer 4 → … → 256 through
`do_reserve_and_handle`), the exit (`sq_iter_tail`). The result is a `Vec` of 256 elements with
capacity 256 in a heap block of `0x2000` bytes. The elements' values are not tracked: the
tables `SqrtTables::new` builds from them are only read by `sqrt_alt`, which checks its own
result (ledger A3).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

theorem sq_ok_of_nat {b : Word} {n : Nat} (h1 : b.toNat % 8 = 0) (h2 : b.toNat + 8 * n ≤ 0x78000000) :
    RegionOk Ro.layout.roBase Ro.layout.textHi b n :=
  RegionOk.of_nat h1 (by unfold SP1_MAX_MEMORY; omega) (Or.inl (by simp only [Ro.layout_roBase]; omega))

set_option maxHeartbeats 4000000 in
theorem sq_from_iter_spec {P : Prop} (s : MachineState) (ra sp out it g w2 w3 w4 w5 : Word)
    (G O : List Word) (hGl : G.length = 4) (hOl : O.length = 3)
    (hpc : s.pc = 0x780326cc#64) (hcode : CodeAt F_780326cc.base F_780326cc.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x240 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = it)
    (hI : Region it [g, 0x10000000000#64, w2, w3, w4, w5] s) (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi it 6)
    (hG : Region g G s) (hokG : RegionOk Ro.layout.roBase Ro.layout.textHi g 4)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 3)
    (hIlo : sp.toNat ≤ it.toNat) (hIhi : it.toNat + 48 ≤ 0x78000000)
    (hglo : sp.toNat ≤ g.toNat) (hghi : g.toNat + 32 ≤ 0x78000000)
    (hOlo : sp.toNat ≤ out.toNat) (hOhi : out.toNat + 24 ≤ 0x78000000)
    (hdIG : Disjoint it 6 g 4) (hdOI : Disjoint out 3 it 6)
    (halloc : SqAlloc P s.code) (hres : SqReserve P s.code)
    (hhandle_rv : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → Safe P u)
    (hk : ∀ (t : MachineState) (ptr : Word) (T : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code →
      Unchanged [(sp - 0x240#64, 72), (out, 3), (it, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [256#64, ptr, 256#64] t → T.length = 1024 → Region ptr T t →
      RegionOk Ro.layout.roBase Ro.layout.textHi ptr 1024 →
      0x78048980 ≤ ptr.toNat → ptr.toNat + 0x2000 ≤ 0x1c00000000 → Safe P t) :
    Safe P s := by
  have hlo := hstk.lo
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hal := hstk.aligned
  have e140 : (sp - 0x140#64).toNat = sp.toNat - 0x140 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have e170 : (sp - 0x170#64).toNat = sp.toNat - 0x170 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have e240 : (sp - 0x240#64).toNat = sp.toNat - 0x240 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have e1 : (sp - 0x140#64 - 0x100#64) = sp - 0x240#64 := by
    rw [BitVec.sub_sub]; rfl
  have eadd : ∀ c : Nat, c ≤ 0x140 → (sp - 0x140#64 + BitVec.ofNat 64 c).toNat = sp.toNat - 0x140 + c := by
    intro c hc; rw [BitVec.toNat_add, e140, BitVec.toNat_ofNat]; omega
  refine sq_iter_pro s ra sp out it g w2 w3 w4 w5 G hGl hpc hcode hcodeM hcodeSh hcw hro hra hsp hstk
    ha0 ha1 hI hokI hG hokG hIlo hIhi hglo hghi hdIG halloc hhandle_rv ?_
  intro t1 p J hpc1 hc1 hun1 r2 r8 r9 r19 r20 r21 r22 r23 r24 r25 r26 r27 r3 r4 hH1 hJl hJ1 hS1 hG1 hokP
    hplo hphi
  have E : SqEnv (sp - 0x140#64) g :=
    { stk := ⟨by rw [e140]; omega, by rw [e140]; omega, by rw [e140, Ro.layout_stackTop]; omega⟩
      sphi := by rw [e140]; omega
      glo := by rw [e140]; omega
      ghi := hghi
      okF := sq_ok_of_nat (by rw [e140]; omega) (by rw [e140]; omega)
      okH := sq_ok_of_nat (by rw [eadd 8 (by decide)]; omega) (by rw [eadd 8 (by decide)]; omega)
      okJ := sq_ok_of_nat (by rw [eadd 0x38 (by decide)]; omega) (by rw [eadd 0x38 (by decide)]; omega)
      okG := hokG }
  have hS1l : [s.getReg .x27, s.getReg .x26, s.getReg .x25, s.getReg .x24, s.getReg .x23,
      s.getReg .x22, s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18, s.getReg .x9,
      s.getReg .x8, ra].length = 13 := rfl
  refine sq_loop (P := P) s t1 (sp - 0x140#64) out g (s.getReg .x3) (s.getReg .x4) G _ hGl hS1l E
    hcode hcodeM hcw hres ?_ 255 t1 J 1#64 4#64 p hc1 (hro.of_unchanged hun1 ?_) (Unchanged.refl _ t1)
    (SqHead.mk hpc1 r2 r3 r4 r8 r9 r19 r20 r21 r22 r23 r24 r25 (by rw [r26]; rfl) r27 hH1 hJl hJ1 hS1
      hG1 hokP hplo (by have : (4#64 : Word).toNat = 4 := rfl; omega) (by unfold SqCap; decide) (by decide) (Or.inr rfl) (by decide)
      (by decide)) rfl
  · -- the exit: the header out, the frame restored
    intro t2 J2 c p2 l hpc2 hc2 hun2 r2' r3' r4' hH2 _ _ hS2 hc256 hl256 hokP2 hplo2 hphi2 _
    have hO1 : Region out O t1 := by
      refine hO.of_unchanged' hun1 hOl ?_
      intro r hr
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · unfold AsmVerif.RiscV.Sym.Disjoint; dsimp only; rw [e170]; omega
      · exact hdOI
      · unfold AsmVerif.RiscV.Sym.Disjoint; dsimp only; simp only [BitVec.toNat_ofNat]; omega
      · unfold AsmVerif.RiscV.Sym.Disjoint; dsimp only; simp only [BitVec.toNat_ofNat]; omega
    have hO2 : Region out O t2 := by
      refine hO1.of_unchanged' hun2 hOl ?_
      intro r hr
      rcases mem4 hr with rfl | rfl | rfl | rfl
      · unfold AsmVerif.RiscV.Sym.Disjoint; dsimp only; rw [e1, e240]; omega
      · unfold AsmVerif.RiscV.Sym.Disjoint; dsimp only; rw [e140]; omega
      · unfold AsmVerif.RiscV.Sym.Disjoint; dsimp only; simp only [BitVec.toNat_ofNat]; omega
      · unfold AsmVerif.RiscV.Sym.Disjoint; dsimp only; simp only [BitVec.toNat_ofNat]; omega
    have hc2s := hc2
    refine sq_iter_tail t2 (sp - 0x140#64) out c p2 l O hOl (s.getReg .x8) (s.getReg .x9)
      (s.getReg .x18) (s.getReg .x19) (s.getReg .x20) (s.getReg .x21) (s.getReg .x22) (s.getReg .x23)
      (s.getReg .x24) (s.getReg .x25) (s.getReg .x26) (s.getReg .x27) ra hra1 hpc2
      (codeAt_of_code_eq hc2s hcode) (fun a ha => hcw a (hc2s ▸ ha)) r2' hH2 E.okH hS2
      (sq_ok_of_nat (by rw [eadd 0xd8 (by decide)]; omega) (by rw [eadd 0xd8 (by decide)]; omega))
      hO2 hokO (by unfold AsmVerif.RiscV.Sym.Disjoint; rw [eadd 8 (by decide)]; omega)
      (by unfold AsmVerif.RiscV.Sym.Disjoint; rw [eadd 0xd8 (by decide)]; omega) ?_
    intro t3 hpc3 hc3 hun3 x2' x8' x9' x18' x19' x20' x21' x22' x23' x24' x25' x26' x27' x3' x4' hO3
    have hc3s := hc3.trans hc2s
    have hcE : c = 256#64 := BitVec.eq_of_toNat_eq hc256
    have hlE : l = 256#64 := BitVec.eq_of_toNat_eq hl256
    subst hcE hlE
    obtain ⟨T, hT, hTl⟩ := Region.exists_junk p2 1024 t3
    refine hk t3 p2 T hpc3 ?_ hc3s ?_ hO3 hTl hT hokP2 hplo2
      (by have : (256#64 : Word).toNat = 256 := rfl; omega)
    · refine CalleeSaved.intro ?_ (x3'.trans r3') (x4'.trans r4') x8' x9' x18' x19' x20' x21' x22' x23'
        x24' x25' x26' x27'
      rw [x2', hsp, BitVec.sub_add_cancel]
    · have hc1 : ∀ r ∈ [(sp - 0x170#64, 46), (it, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)],
          ∃ r' ∈ [(sp - 0x240#64, 72), (out, 3), (it, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)],
            Covers r'.1 r'.2 r.1 r.2 := by
        intro r hr
        rcases mem4 hr with rfl | rfl | rfl | rfl
        · exact ⟨(sp - 0x240#64, 72), by simp, by unfold Covers; dsimp only; rw [e170, e240]; omega⟩
        · exact ⟨(it, 6), by simp, by unfold Covers; omega⟩
        · exact ⟨(0x78040620#64, 4162), by simp, by unfold Covers; omega⟩
        · exact ⟨(0x78048980#64, 14780690128), by simp, by unfold Covers; omega⟩
      have hc2' : ∀ r ∈ sqW (sp - 0x140#64),
          ∃ r' ∈ [(sp - 0x240#64, 72), (out, 3), (it, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)],
            Covers r'.1 r'.2 r.1 r.2 := by
        intro r hr
        rcases mem4 hr with rfl | rfl | rfl | rfl
        · exact ⟨(sp - 0x240#64, 72), by simp, by unfold Covers; dsimp only; rw [e1]; omega⟩
        · exact ⟨(sp - 0x240#64, 72), by simp, by unfold Covers; dsimp only; rw [e140, e240]; omega⟩
        · exact ⟨(0x78040620#64, 4162), by simp, by unfold Covers; omega⟩
        · exact ⟨(0x78048980#64, 14780690128), by simp, by unfold Covers; omega⟩
      have hc3' : ∀ r ∈ [(out, 3)],
          ∃ r' ∈ [(sp - 0x240#64, 72), (out, 3), (it, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)],
            Covers r'.1 r'.2 r.1 r.2 := by
        intro r hr
        rw [List.mem_singleton] at hr
        subst hr
        exact ⟨(out, 3), by simp, by unfold Covers; omega⟩
      exact (((Unchanged.refl _ s).trans_cover hun1 hc1).trans_cover hun2 hc2').trans_cover hun3 hc3'
  · intro r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · left; dsimp only; rw [e170]; simp only [Ro.layout_roBase]; omega
    · left; dsimp only; simp only [Ro.layout_roBase]; omega
    · right; dsimp only; simp only [Ro.layout_roBase, Ro.layout_roBytes, BitVec.toNat_ofNat]; omega
    · right; dsimp only; simp only [Ro.layout_roBase, Ro.layout_roBytes, BitVec.toNat_ofNat]; omega

end Cases.Zip2005
