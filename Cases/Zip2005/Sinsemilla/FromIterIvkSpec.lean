import Cases.Zip2005.Sinsemilla.FromIterIvkLoop
import Cases.Zip2005.Image.Ro

/-!
# `Vec<bool>::from_iter` of `commit_ivk`'s padded bit iterator (`0x7801e110`), as a function

The prologue (`ivk_pro_step`), seven phases of whole words (`ivk_phase`) separated by six
growths of the `Vec` (`ivk_grow_step`, capacities 8 → 16 → … → 512), the exit from byte 504
(`ivk_tail_step`). The result is the 510-byte `Vec` with byte `o` the message bit `o`
(`ivkBit A B o`), stored at `out` as `(512, ptr, 510)`, in a 65-word block.

The contract `hfrom` of `commit_ivk_spec` (ledger A8) is this theorem's shape; the allocator
calls inside (`__rust_alloc(8, 1)`, `do_reserve_and_handle` at the six capacities) are the A4
and A5 instances `halloc`, `hreserve`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- The call's write set, in the loop frame's terms: the 76-word frame `[sp - 0x1b0, sp + 0xb0)`,
the output header, the caller's block, the heap. -/
abbrev fromIterW (sp out a1 : Word) : List (Word × Nat) :=
  [(sp - 0x1b0#64, 76), (out, 3), (a1, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)]

theorem coverF {sp out a1 : Word} (hstk : StackOk Ro.layout 0x1b0 sp) {b : Word} {i n : Nat}
    (hb : b = sp - 0x1b0#64 + BitVec.ofNat 64 (8 * i)) (hin : i + n ≤ 76) (hn : 0 < n) :
    ∃ r' ∈ fromIterW sp out a1, Covers r'.1 r'.2 b n :=
  ⟨(sp - 0x1b0#64, 76), by simp, covers_of_sub (frame_nowrap hstk) hb hin hn⟩

theorem coverHF {sp out a1 : Word} {b : Word} {n : Nat} (hlo : 0x78048980 ≤ b.toNat)
    (hhi : b.toNat + 8 * n ≤ 0x1c00000000) :
    ∃ r' ∈ fromIterW sp out a1, Covers r'.1 r'.2 b n :=
  ⟨(0x78048980#64, 14780690128), by simp, covers_arena hlo hhi⟩

theorem unch_pro {sp out a1 : Word} {s t : MachineState} (hstk : StackOk Ro.layout 0x1b0 sp)
    (hu : Unchanged [(sp - 0x30#64, 6), (sp, 22), (a1, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t) :
    Unchanged (fromIterW sp out a1) s t := by
  refine Unchanged.trans_cover (Unchanged.refl _ s) hu ?_
  intro r hr
  rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
  · exact coverF hstk (fr_m30 sp) (by omega) (by omega)
  · exact coverF hstk (fr_0 sp) (by omega) (by omega)
  · exact ⟨(a1, 12), by simp, le_refl _, le_refl _⟩
  · exact ⟨(0x78040620#64, 4162), by simp, le_refl _, le_refl _⟩
  · exact ⟨(0x78048980#64, 14780690128), by simp, le_refl _, le_refl _⟩

theorem unch_loop {sp out a1 : Word} {s t : MachineState} (hstk : StackOk Ro.layout 0x1b0 sp)
    (hu : Unchanged (loopW sp) s t) : Unchanged (fromIterW sp out a1) s t := by
  refine Unchanged.trans_cover (Unchanged.refl _ s) hu ?_
  intro r hr
  simp only [loopW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact coverF hstk (fr_m100 sp) (by omega) (by omega)
  · exact coverF hstk (fr_0 sp) (by omega) (by omega)
  · exact ⟨(0x78040620#64, 4162), by simp, le_refl _, le_refl _⟩
  · exact ⟨(0x78048980#64, 14780690128), by simp, le_refl _, le_refl _⟩

theorem unch_tail {sp out a1 p : Word} {s t : MachineState} (hstk : StackOk Ro.layout 0x1b0 sp)
    (hlo : 0x78048980 ≤ p.toNat) (hhi : p.toNat + 8 * 65 ≤ 0x1c00000000)
    (hu : Unchanged [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (p + 504#64, 2), (out, 3)] s t) :
    Unchanged (fromIterW sp out a1) s t := by
  refine Unchanged.trans_cover (Unchanged.refl _ s) hu ?_
  intro r hr
  rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
  · exact coverF hstk (fr_m10 sp) (by omega) (by omega)
  · exact coverF hstk (fr_0 sp) (by omega) (by omega)
  · exact coverF hstk (fr_18 sp) (by omega) (by omega)
  · exact coverHF (by rw [toNat_add_lit p 504 (by omega)]; omega)
      (by rw [toNat_add_lit p 504 (by omega)]; omega)
  · exact ⟨(out, 3), by simp, le_refl _, le_refl _⟩

/-- The saved registers, the output header and the caller's block survive the loop. -/
theorem IvkEnv.keepSv {sp sp0 out a1 : Word} {A B : List Word} {T : HasherT} (E : IvkEnv sp sp0 out a1 A B T)
    {s t : MachineState} (hu : Unchanged (loopW sp) s t) {L : List Word} (hL : L.length = 7)
    (h : Region (sp + 0x78#64) L s) : Region (sp + 0x78#64) L t := by
  refine h.of_unchanged' hu hL ?_
  intro r hr
  simp only [loopW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact E.djSvF32
  · exact AsmVerif.RiscV.Sym.Disjoint.within (frame_nowrap E.stk) (fr_78 sp) (fr_0 sp) (by omega) (by omega) (by omega)
  · exact (Disjoint.ctl_of_heap E.djSvH.symm).symm
  · exact (Disjoint.arena_of_heap E.djSvH.symm).symm

theorem IvkEnv.keepO {sp sp0 out a1 : Word} {A B : List Word} {T : HasherT} (E : IvkEnv sp sp0 out a1 A B T)
    {s t : MachineState} (hu : Unchanged (loopW sp) s t) {O : List Word} (hO : O.length = 3)
    (h : Region out O s) : Region out O t := by
  refine h.of_unchanged' hu hO ?_
  intro r hr
  simp only [loopW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact E.djF32O.symm
  · exact (E.djSO.sub_left (fr_0 sp) (by omega)).symm
  · exact E.djHO.ctl_of_heap.symm
  · exact E.djHO.arena_of_heap.symm

theorem IvkEnv.keepC {sp sp0 out a1 : Word} {A B : List Word} {T : HasherT} (E : IvkEnv sp sp0 out a1 A B T)
    {s t : MachineState} (hu : Unchanged (loopW sp) s t) {I : List Word} (hI : I.length = 12)
    (h : Region a1 I s) : Region a1 I t := by
  refine h.of_unchanged' hu hI ?_
  intro r hr
  simp only [loopW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact E.djF32C.symm
  · exact (E.djSC.sub_left (fr_0 sp) (by omega)).symm
  · exact E.djHC.ctl_of_heap.symm
  · exact E.djHC.arena_of_heap.symm

theorem IvkEnv.keepC_tail {sp sp0 out a1 p : Word} {A B : List Word} {T : HasherT} (E : IvkEnv sp sp0 out a1 A B T)
    {s t : MachineState} (hlo : 0x78048980 ≤ p.toNat) (hhi : p.toNat + 8 * 65 ≤ 0x1c00000000)
    (hu : Unchanged [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (p + 504#64, 2), (out, 3)] s t)
    {I : List Word} (hI : I.length = 12) (h : Region a1 I s) : Region a1 I t := by
  refine h.of_unchanged' hu hI ?_
  intro r hr
  rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
  · exact E.djFC.symm
  · exact E.djVC.symm
  · exact E.djBC.symm
  · exact ((E.djHC.of_heap (p := p) (L := 65) (by omega) hhi).sub_left (i := 63) rfl (by omega)).symm
  · exact E.djOC.symm

set_option maxHeartbeats 4000000 in
/-- `Vec<bool>::from_iter` of the padded `commit_ivk` iterator: the 510 message bits as bytes.
`sp` is the loop's frame (the entry stack pointer is `sp + 0xb0`); `sp0` is `commit_ivk`'s
frame, where the message words `A` (`ak`'s bits, at `ptrA sp0`) and `B` (`nk`'s, at `ptrB sp0`)
live; `a1` holds the iterator block as `commit_ivk` built it (`ivkState sp0 J j 0`). -/
theorem from_iter_ivk_spec {P : Prop} (s : MachineState) (sp sp0 out a1 ra : Word)
    (J A B O : List Word) (j : Word) (hAl : A.length = 4) (hBl : B.length = 4) (hOl : O.length = 3)
    (hpc : s.pc = 0x7801e110#64) (hcode : CodeAt F_7801e110.base F_7801e110.prog s)
    (hcodeN : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeZ : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp + 0xb0#64) (hstk : StackOk Ro.layout 0x1b0 sp) (hokFr : RegionOk Ro.layout.roBase Ro.layout.textHi sp 22)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = a1)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 3)
    (hCb : Region a1 (ivkState sp0 J j 0) s) (hokC : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hAr : Region (ptrA sp0) A s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrA sp0) 4)
    (hBr : Region (ptrB sp0) B s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrB sp0) 4)
    (hsp0_lo : 0x10000 ≤ sp0.toNat) (hsp0_hi : sp0.toNat ≤ 0x78000000)
    (hdjSA : AsmVerif.RiscV.Sym.Disjoint (sp - 0x1b0#64) 76 (ptrA sp0) 4) (hdjSB : AsmVerif.RiscV.Sym.Disjoint (sp - 0x1b0#64) 76 (ptrB sp0) 4)
    (hdjSO : AsmVerif.RiscV.Sym.Disjoint (sp - 0x1b0#64) 76 out 3) (hdjSC : AsmVerif.RiscV.Sym.Disjoint (sp - 0x1b0#64) 76 a1 12)
    (hdjOA : AsmVerif.RiscV.Sym.Disjoint out 3 (ptrA sp0) 4) (hdjOB : AsmVerif.RiscV.Sym.Disjoint out 3 (ptrB sp0) 4)
    (hdjOC : AsmVerif.RiscV.Sym.Disjoint out 3 a1 12)
    (hdjCA : AsmVerif.RiscV.Sym.Disjoint a1 12 (ptrA sp0) 4) (hdjCB : AsmVerif.RiscV.Sym.Disjoint a1 12 (ptrB sp0) 4)
    (hdjAB : AsmVerif.RiscV.Sym.Disjoint (ptrA sp0) 4 (ptrB sp0) 4)
    (hdjHA : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 (ptrA sp0) 4)
    (hdjHB : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 (ptrB sp0) 4)
    (hdjHO : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 out 3)
    (hdjHC : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 a1 12)
    -- the hasher's six regions (`T`): in the arena, held, kept by the allocator
    (T : HasherT) (hT : Kept6 T s) (hTA : Arena6 T) (hTO : Ok6 T)
    -- `__rust_alloc(8, 1)` (A4, this call's instance): a fresh word in the arena
    (halloc : ∀ (u : MachineState), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801e184#64 → u.getReg .x2 = sp → StackOk Ro.layout 0x30 sp →
      u.getReg .x10 = 8#64 → u.getReg .x11 = 1#64 →
      Region T.b1 T.L1 u → Region T.b2 T.L2 u → Region T.b3 T.L3 u → Region T.b4 T.L4 u → Region T.b5 T.L5 u → Region T.b6 T.L6 u →
      (∀ (t : MachineState) (ptr : Word) (B0 : List Word), t.pc = 0x7801e184#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B0.length = 1 → Region ptr B0 t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 ≤ 0x1c00000000 →
        Region T.b1 T.L1 t → Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t → Region T.b5 T.L5 t → Region T.b6 T.L6 t →
        AsmVerif.RiscV.Sym.Disjoint T.b1 10 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b2 138 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b3 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b4 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b5 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b6 516 ptr 1 → Safe P t) → Safe P u)
    -- `do_reserve_and_handle(&vec, C, 1, 1, 1)` (A5, this call's six instances, `C` the full
    -- capacity): the block doubled, its contents copied, one word past it readable
    (hreserve : ∀ (u : MachineState) (C : Nat) (p : Word) (W : List Word),
      (C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256) → W.length = C / 8 →
      u.pc = 0x780221a4#64 → u.code = s.code → u.getReg .x1 = 0x7801e254#64 → u.getReg .x2 = sp →
      StackOk Ro.layout 0x100 sp → u.getReg .x10 = sp → u.getReg .x11 = BitVec.ofNat 64 C →
      u.getReg .x12 = 1#64 → u.getReg .x13 = 1#64 → u.getReg .x14 = 1#64 →
      Region sp [BitVec.ofNat 64 C, p, BitVec.ofNat 64 C] u → Region p W u →
      0x78048980 ≤ p.toNat → p.toNat + C ≤ 0x1c00000000 →
      Region T.b1 T.L1 u → Region T.b2 T.L2 u → Region T.b3 T.L3 u → Region T.b4 T.L4 u → Region T.b5 T.L5 u → Region T.b6 T.L6 u →
      (∀ (t : MachineState) (p' : Word) (W' : List Word), t.pc = 0x7801e254#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp - 0x100#64, 32), (sp, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region sp [BitVec.ofNat 64 (2 * C), p', BitVec.ofNat 64 C] t → W'.length = C / 8 + 1 →
        Region p' (W ++ W') t → RegionOk Ro.layout.roBase Ro.layout.textHi p' (C / 4 + 1) →
        0x78048980 ≤ p'.toNat → p'.toNat + 2 * C + 8 ≤ 0x1c00000000 →
        Region T.b1 T.L1 t → Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t → Region T.b5 T.L5 t → Region T.b6 T.L6 t →
        AsmVerif.RiscV.Sym.Disjoint T.b1 10 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b2 138 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b3 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b4 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b5 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b6 516 p' (C / 4 + 1) → Safe P t) → Safe P u)
    (hunwrap_opt : ∀ u : MachineState, u.pc = 0x7803f364#64 → u.code = s.code → Safe P u)
    (hhandle_rv : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → Safe P u)
    (hk : ∀ (t : MachineState) (ptr : Word) (Bv I1 : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code →
      Unchanged [(sp - 0x1b0#64, 76), (out, 3), (a1, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      I1.length = 12 → Region out [512#64, ptr, 510#64] t → Region a1 I1 t →
      Bv.length = 65 → (∀ o, o < 510 → byteAt Bv o = bw (ivkBit A B o)) → Region ptr Bv t →
      RegionOk Ro.layout.roBase Ro.layout.textHi ptr 65 → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
      Kept6 T t → Safe P t) :
    Safe P s := by
  have E : IvkEnv sp sp0 out a1 A B T :=
    ⟨hAl, hBl, hstk, hokFr, hokO, hokC, hokA, hokB, hsp0_lo, hsp0_hi, hdjSA, hdjSB, hdjSO, hdjSC,
     hdjOA, hdjOB, hdjOC, hdjCA, hdjCB, hdjAB, hdjHA, hdjHB, hdjHO, hdjHC, hTA, hTO⟩
  have C0 : IvkCtx P sp0 A B T s := ⟨hcode, hcodeN, hcw, hAr, hBr, hT, hunwrap_opt⟩
  -- the reserve contract at a loop state
  have hres : ∀ (t : MachineState), t.code = s.code → ∀ (C : Nat) (p : Word),
      (C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256) →
      ∀ (u : MachineState) (W : List Word), W.length = C / 8 →
      u.pc = 0x780221a4#64 → u.code = t.code → u.getReg .x1 = 0x7801e254#64 → u.getReg .x2 = sp →
      StackOk Ro.layout 0x100 sp → u.getReg .x10 = sp → u.getReg .x11 = BitVec.ofNat 64 C →
      u.getReg .x12 = 1#64 → u.getReg .x13 = 1#64 → u.getReg .x14 = 1#64 →
      Region sp [BitVec.ofNat 64 C, p, BitVec.ofNat 64 C] u → Region p W u →
      0x78048980 ≤ p.toNat → p.toNat + C ≤ 0x1c00000000 →
      Region T.b1 T.L1 u → Region T.b2 T.L2 u → Region T.b3 T.L3 u → Region T.b4 T.L4 u → Region T.b5 T.L5 u → Region T.b6 T.L6 u →
      (∀ (t : MachineState) (p' : Word) (W' : List Word), t.pc = 0x7801e254#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp - 0x100#64, 32), (sp, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region sp [BitVec.ofNat 64 (2 * C), p', BitVec.ofNat 64 C] t → W'.length = C / 8 + 1 →
        Region p' (W ++ W') t → RegionOk Ro.layout.roBase Ro.layout.textHi p' (C / 4 + 1) →
        0x78048980 ≤ p'.toNat → p'.toNat + 2 * C + 8 ≤ 0x1c00000000 →
        Region T.b1 T.L1 t → Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t → Region T.b5 T.L5 t → Region T.b6 T.L6 t →
        AsmVerif.RiscV.Sym.Disjoint T.b1 10 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b2 138 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b3 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b4 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b5 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b6 516 p' (C / 4 + 1) → Safe P t) → Safe P u :=
    fun t hts C p hC u W hW hpc hcode hra hsp hstk h10 h11 h12 h13 h14 hV hW' hlo hhi hr1 hr2 hr3 hr4 hr5 hr6 hk' =>
      hreserve u C p W hC hW hpc (hcode.trans hts) hra hsp hstk h10 h11 h12 h13 h14 hV hW' hlo hhi
        hr1 hr2 hr3 hr4 hr5 hr6 hk'
  -- the prologue: byte 1, capacity 8
  refine ivk_pro_step E hOl hpc C0 hcodeM hcodeZ hra hsp ha0 ha1 hO hCb halloc hhandle_rv ?_
  intro t1 ptr w hc1 hu1 hk1 C1 H1 hF1 hO1 ⟨I1, hI1l, hR1⟩
  have hu1' := unch_pro (out := out) hstk hu1
  -- phase 1: bytes 1 … 8
  refine ivk_phase E (cap := 8) (by omega) 0 0 t1 ptr [w] (by omega) (by omega) (by simp) H1 C1 ?_
  intro t2 V2 hc2 hu2 hk2 C2 hl2 H2
  refine ivk_grow_step E (C := 8) (by simp) (by simp at hl2; omega) H2 C2
    (hres t2 (hc2.trans hc1) 8 ptr (by simp)) ?_
  intro t3 p3 V3 hc3 hu3 hk3 C3 hl3 H3
  -- phase 2: bytes 9 … 16
  refine ivk_phase E (cap := 2 * 8) (by omega) 1 0 t3 p3 V3 (by omega) (by omega) (by omega) H3 C3 ?_
  intro t4 V4 hc4 hu4 hk4 C4 hl4 H4
  refine ivk_grow_step E (C := 16) (by simp) (by omega) H4 C4
    (hres t4 (hc4.trans (hc3.trans (hc2.trans hc1))) 16 p3 (by simp)) ?_
  intro t5 p5 V5 hc5 hu5 hk5 C5 hl5 H5
  -- phase 3: bytes 17 … 32
  refine ivk_phase E (cap := 2 * 16) (by omega) 2 1 t5 p5 V5 (by omega) (by omega) (by omega) H5 C5 ?_
  intro t6 V6 hc6 hu6 hk6 C6 hl6 H6
  have hcs6 : t6.code = s.code := hc6.trans (hc5.trans (hc4.trans (hc3.trans (hc2.trans hc1))))
  refine ivk_grow_step E (C := 32) (by simp) (by omega) H6 C6 (hres t6 hcs6 32 p5 (by simp)) ?_
  intro t7 p7 V7 hc7 hu7 hk7 C7 hl7 H7
  -- phase 4: bytes 33 … 64
  refine ivk_phase E (cap := 2 * 32) (by omega) 4 3 t7 p7 V7 (by omega) (by omega) (by omega) H7 C7 ?_
  intro t8 V8 hc8 hu8 hk8 C8 hl8 H8
  have hcs8 : t8.code = s.code := hc8.trans (hc7.trans hcs6)
  refine ivk_grow_step E (C := 64) (by simp) (by omega) H8 C8 (hres t8 hcs8 64 p7 (by simp)) ?_
  intro t9 p9 V9 hc9 hu9 hk9 C9 hl9 H9
  -- phase 5: bytes 65 … 128
  refine ivk_phase E (cap := 2 * 64) (by omega) 8 7 t9 p9 V9 (by omega) (by omega) (by omega) H9 C9 ?_
  intro t10 V10 hc10 hu10 hk10 C10 hl10 H10
  have hcs10 : t10.code = s.code := hc10.trans (hc9.trans hcs8)
  refine ivk_grow_step E (C := 128) (by simp) (by omega) H10 C10 (hres t10 hcs10 128 p9 (by simp)) ?_
  intro t11 p11 V11 hc11 hu11 hk11 C11 hl11 H11
  -- phase 6: bytes 129 … 256
  refine ivk_phase E (cap := 2 * 128) (by omega) 16 15 t11 p11 V11 (by omega) (by omega) (by omega)
    H11 C11 ?_
  intro t12 V12 hc12 hu12 hk12 C12 hl12 H12
  have hcs12 : t12.code = s.code := hc12.trans (hc11.trans hcs10)
  refine ivk_grow_step E (C := 256) (by simp) (by omega) H12 C12 (hres t12 hcs12 256 p11 (by simp)) ?_
  intro t13 p13 V13 hc13 hu13 hk13 C13 hl13 H13
  -- phase 7: bytes 257 … 504
  refine ivk_phase E (cap := 2 * 256) (by omega) 32 30 t13 p13 V13 (by omega) (by omega) (by omega)
    H13 C13 ?_
  intro t14 V14 hc14 hu14 hk14 C14 hl14 H14
  have hcs14 : t14.code = s.code := hc14.trans (hc13.trans hcs12)
  have hl14' : V14.length = 65 := by rw [hl14, hl13]
  -- the loop's frame condition from the state after the prologue
  have huL : Unchanged (loopW sp) t1 t14 :=
    hu2.trans (hu3.trans (hu4.trans (hu5.trans (hu6.trans (hu7.trans (hu8.trans (hu9.trans
      (hu10.trans (hu11.trans (hu12.trans (hu13.trans hu14)))))))))))
  have hkL : Kept t1 t14 :=
    hk2.trans (hk3.trans (hk4.trans (hk5.trans (hk6.trans (hk7.trans (hk8.trans (hk9.trans
      (hk10.trans (hk11.trans (hk12.trans (hk13.trans hk14)))))))))))
  have hF14 := E.keepSv huL rfl hF1
  have hO14 := E.keepO huL hOl hO1
  have hR14 := E.keepC huL hI1l hR1
  -- the exit
  refine ivk_tail_step E hOl hl14' hra1 H14 C14 hF14 hO14 ?_
  intro t Bv hpc' hcode' hun hkT hsp' hs0' hs1' hs2' hs3' hs4' hs5' hOut hBvl hbits hBv hok' hlo' hhi' hKt
  have hkA : Kept s t := hk1.trans (hkL.trans hkT)
  refine hk t p13 Bv I1 hpc' ?_ (hcode'.trans hcs14) ?_ hI1l hOut (E.keepC_tail hlo' hhi' hun hI1l hR14)
    hBvl hbits hBv hok' hlo' hhi' hKt
  · intro r hr
    simp only [calleeSavedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hsp', hsp]
    · exact hkA.1
    · exact hkA.2.1
    · exact hs0'
    · exact hs1'
    · exact hs2'
    · exact hs3'
    · exact hs4'
    · exact hs5'
    · exact hkA.2.2.1
    · exact hkA.2.2.2.1
    · exact hkA.2.2.2.2.1
    · exact hkA.2.2.2.2.2.1
    · exact hkA.2.2.2.2.2.2.1
    · exact hkA.2.2.2.2.2.2.2
  · exact hu1'.trans ((unch_loop (out := out) (a1 := a1) hstk huL).trans
      (unch_tail (a1 := a1) hstk hlo' hhi' hun))

end Cases.Zip2005
