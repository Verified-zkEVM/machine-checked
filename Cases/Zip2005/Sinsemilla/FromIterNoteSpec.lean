import Cases.Zip2005.Sinsemilla.FromIterNoteLoop
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `Vec<bool>::from_iter` of `NoteCommitment::derive`'s padded bit iterator (`0x7801dfb4`), as a function

The prologue (`note_pro_step`), nine phases of whole words (`note_phase`) separated by eight
growths of the `Vec` (`note_grow_step`, capacities 8 → 16 → … → 2048), the exit from byte 1088
(`note_tail_step`). The result is the 1090-byte `Vec` with byte `o` the message bit `o`
(`noteBit G K v R Q o`), stored at `out` as `(2048, ptr, 1090)`, in a 257-word block.

The contract `hfrom` of `NoteCommitment::derive_spec` (ledger A8) is this theorem's shape; the allocator
calls inside (`__rust_alloc(8, 1)`, `do_reserve_and_handle` at the eight capacities) are the A4
and A5 instances `halloc`, `hreserve`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- The call's write set, in the loop frame's terms: the 76-word frame `[sp - 0x180, sp + 0xe0)`,
the output header, the caller's block, the heap. -/
abbrev fromIterNW (sp out a1 : Word) : List (Word × Nat) :=
  [(sp - 0x180#64, 76), (out, 3), (a1, 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)]

theorem coverFN {sp out a1 : Word} (hstk : StackOk Ro.layout 0x180 sp) {b : Word} {i n : Nat}
    (hb : b = sp - 0x180#64 + BitVec.ofNat 64 (8 * i)) (hin : i + n ≤ 76) (hn : 0 < n) :
    ∃ r' ∈ fromIterNW sp out a1, Covers r'.1 r'.2 b n :=
  ⟨(sp - 0x180#64, 76), by simp, covers_of_sub (framen_nowrap hstk) hb hin hn⟩

theorem coverHFN {sp out a1 : Word} {b : Word} {n : Nat} (hlo : 0x78048980 ≤ b.toNat)
    (hhi : b.toNat + 8 * n ≤ 0x1c00000000) :
    ∃ r' ∈ fromIterNW sp out a1, Covers r'.1 r'.2 b n :=
  ⟨(0x78048980#64, 14780690128), by simp, covers_arena hlo hhi⟩

theorem unch_proN {sp out a1 : Word} {s t : MachineState} (hstk : StackOk Ro.layout 0x180 sp)
    (hu : Unchanged [(sp - 0x180#64, 48), (sp, 28), (a1, 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t) :
    Unchanged (fromIterNW sp out a1) s t := by
  refine Unchanged.trans_cover (Unchanged.refl _ s) hu ?_
  intro r hr
  rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
  · exact coverFN hstk (self_add_zero _) (by omega) (by omega)
  · exact coverFN hstk (frn_0 sp) (by omega) (by omega)
  · exact ⟨(a1, 18), by simp, le_refl _, le_refl _⟩
  · exact ⟨(0x78040620#64, 4162), by simp, le_refl _, le_refl _⟩
  · exact ⟨(0x78048980#64, 14780690128), by simp, le_refl _, le_refl _⟩

theorem unch_loopN {sp out a1 : Word} {s t : MachineState} (hstk : StackOk Ro.layout 0x180 sp)
    (hu : Unchanged (noteLoopW sp) s t) : Unchanged (fromIterNW sp out a1) s t := by
  refine Unchanged.trans_cover (Unchanged.refl _ s) hu ?_
  intro r hr
  simp only [noteLoopW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact coverFN hstk (self_add_zero _) (by omega) (by omega)
  · exact coverFN hstk (frn_0 sp) (by omega) (by omega)
  · exact ⟨(0x78040620#64, 4162), by simp, le_refl _, le_refl _⟩
  · exact ⟨(0x78048980#64, 14780690128), by simp, le_refl _, le_refl _⟩

theorem unch_tailN {sp out a1 p : Word} {s t : MachineState} (hstk : StackOk Ro.layout 0x180 sp)
    (hlo : 0x78048980 ≤ p.toNat) (hhi : p.toNat + 8 * 257 ≤ 0x1c00000000)
    (hu : Unchanged [(sp - 0x180#64, 48), (sp, 3), (sp + 0x18#64, 18), (p + 1088#64, 2), (out, 3)] s t) :
    Unchanged (fromIterNW sp out a1) s t := by
  refine Unchanged.trans_cover (Unchanged.refl _ s) hu ?_
  intro r hr
  rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
  · exact coverFN hstk (self_add_zero _) (by omega) (by omega)
  · exact coverFN hstk (frn_0 sp) (by omega) (by omega)
  · exact coverFN hstk (frn_18 sp) (by omega) (by omega)
  · exact coverHFN (by rw [toNat_add_lit p 1088 (by omega)]; omega)
      (by rw [toNat_add_lit p 1088 (by omega)]; omega)
  · exact ⟨(out, 3), by simp, le_refl _, le_refl _⟩

/-- The saved registers, the output header and the caller's block survive the loop. -/
theorem NoteEnv.keepSv {sp sp0 out a1 : Word} {G K R Q : List Word} (E : NoteEnv sp sp0 out a1 G K R Q)
    {s t : MachineState} (hu : Unchanged (noteLoopW sp) s t) {L : List Word} (hL : L.length = 7)
    (h : Region (sp + 0xa8#64) L s) : Region (sp + 0xa8#64) L t := by
  refine h.of_unchanged' hu hL ?_
  intro r hr
  simp only [noteLoopW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact E.djSvF
  · exact AsmVerif.RiscV.Sym.Disjoint.within (N := 76) (framen_nowrap E.stk) (frn_a8 sp) (frn_0 sp) (by omega) (by omega)
      (Or.inr (by omega))
  · exact (Disjoint.ctl_of_heap E.djSvH.symm).symm
  · exact (Disjoint.arena_of_heap E.djSvH.symm).symm

theorem NoteEnv.keepO {sp sp0 out a1 : Word} {G K R Q : List Word} (E : NoteEnv sp sp0 out a1 G K R Q)
    {s t : MachineState} (hu : Unchanged (noteLoopW sp) s t) {O : List Word} (hO : O.length = 3)
    (h : Region out O s) : Region out O t := by
  refine h.of_unchanged' hu hO ?_
  intro r hr
  simp only [noteLoopW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact E.djFO.symm
  · exact (E.djSO.sub_left (frn_0 sp) (by omega)).symm
  · exact E.djHO.ctl_of_heap.symm
  · exact E.djHO.arena_of_heap.symm

theorem NoteEnv.keepC {sp sp0 out a1 : Word} {G K R Q : List Word} (E : NoteEnv sp sp0 out a1 G K R Q)
    {s t : MachineState} (hu : Unchanged (noteLoopW sp) s t) {I : List Word} (hI : I.length = 18)
    (h : Region a1 I s) : Region a1 I t := by
  refine h.of_unchanged' hu hI ?_
  intro r hr
  simp only [noteLoopW, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact E.djFC.symm
  · exact (E.djSC.sub_left (frn_0 sp) (by omega)).symm
  · exact E.djHC.ctl_of_heap.symm
  · exact E.djHC.arena_of_heap.symm

theorem NoteEnv.keepC_tail {sp sp0 out a1 p : Word} {G K R Q : List Word} (E : NoteEnv sp sp0 out a1 G K R Q)
    {s t : MachineState} (hlo : 0x78048980 ≤ p.toNat) (hhi : p.toNat + 8 * 257 ≤ 0x1c00000000)
    (hu : Unchanged [(sp - 0x180#64, 48), (sp, 3), (sp + 0x18#64, 18), (p + 1088#64, 2), (out, 3)] s t)
    {I : List Word} (hI : I.length = 18) (h : Region a1 I s) : Region a1 I t := by
  refine h.of_unchanged' hu hI ?_
  intro r hr
  rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
  · exact E.djFC.symm
  · exact E.djVC.symm
  · exact E.djBC.symm
  · exact ((E.djHC.of_heap (p := p) (L := 257) (by omega) hhi).sub_left (i := 136) rfl (by omega)).symm
  · exact E.djOC.symm

set_option maxHeartbeats 4000000 in
/-- `Vec<bool>::from_iter` of the padded `NoteCommitment::derive` iterator: the 1090 message bits as
bytes. `sp` is the loop's frame (the entry stack pointer is `sp + 0xe0`); `sp0` is
`NoteCommitment::derive`'s frame, where the 17-word message block lives (`G`, `K`, `[v]`, `R`, `Q`
at `sp0 - 0xd0`, `- 0xb0`, `- 0x90`, `- 0x88`, `- 0x68`); `a1` holds the iterator block as
`NoteCommitment::derive` built it (`noteState sp0 J j 0`). -/
theorem from_iter_nc_spec {Gd : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (sp sp0 out a1 ra v : Word)
    (J G K R Q O : List Word) (j : Word) (hGl : G.length = 4) (hKl : K.length = 4) (hRl : R.length = 4)
    (hQl : Q.length = 4) (hOl : O.length = 3)
    (hpc : s.pc = 0x7801dfb4#64) (hcode : CodeAt F_7801dfb4.base F_7801dfb4.prog s)
    (hcodeN : CodeAt F_78021720.base F_78021720.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeZ : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp + 0xe0#64) (hstk : StackOk Ro.layout 0x180 sp) (hokFr : RegionOk Ro.layout.roBase Ro.layout.textHi sp 28)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = a1)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 3)
    (hCb : Region a1 (noteState sp0 J j 0) s) (hokC : RegionOk Ro.layout.roBase Ro.layout.textHi a1 18)
    (hGr : Region (sp0 + 18446744073709551408#64) G s)
    (hKr : Region (sp0 + 18446744073709551440#64) K s)
    (hVr : Region (sp0 + 18446744073709551472#64) [v] s)
    (hRr : Region (sp0 + 18446744073709551480#64) R s)
    (hQr : Region (sp0 + 18446744073709551512#64) Q s)
    (hokM : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551408#64) 17)
    (hsp0_lo : 0x10000 ≤ sp0.toNat) (hsp0_hi : sp0.toNat ≤ 0x78000000)
    (hdjSM : AsmVerif.RiscV.Sym.Disjoint (sp - 0x180#64) 76 (sp0 + 18446744073709551408#64) 17)
    (hdjSO : AsmVerif.RiscV.Sym.Disjoint (sp - 0x180#64) 76 out 3) (hdjSC : AsmVerif.RiscV.Sym.Disjoint (sp - 0x180#64) 76 a1 18)
    (hdjOM : AsmVerif.RiscV.Sym.Disjoint out 3 (sp0 + 18446744073709551408#64) 17)
    (hdjOC : AsmVerif.RiscV.Sym.Disjoint out 3 a1 18)
    (hdjCM : AsmVerif.RiscV.Sym.Disjoint a1 18 (sp0 + 18446744073709551408#64) 17)
    (hdjHM : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 (sp0 + 18446744073709551408#64) 17)
    (hdjHO : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 out 3)
    (hdjHC : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 a1 18)
    (hout : out.toNat + 8 * 3 ≤ 0x78040620) (ha1lo : a1.toNat + 8 * 18 ≤ 0x78040620)
    -- `__rust_alloc(8, 1)` (A4, this call's instance): a fresh word in the arena
    (halloc : ∀ (u : MachineState) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801e028#64 → u.getReg .x2 = sp → StackOk Ro.layout 0x30 sp →
      u.getReg .x10 = 8#64 → u.getReg .x11 = 1#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B0 : List Word), t.pc = 0x7801e028#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B0.length = 1 → Region ptr B0 t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 8 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 1) :: L') t → SafeN Gd n P t) → SafeN Gd n P u)
    -- `do_reserve_and_handle(&vec, C, 1, 1, 1)` (A5, this call's eight instances, `C` the full
    -- capacity): the block doubled, its contents copied, one word past it readable
    (hreserve : ∀ (u : MachineState) (C : Nat) (p : Word) (W : List Word) (L' : List (Word × Nat)),
      (C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256 ∨ C = 512 ∨ C = 1024) → W.length = C / 8 →
      u.pc = 0x780221a4#64 → u.code = s.code → u.getReg .x1 = 0x7801e0f8#64 → u.getReg .x2 = sp →
      StackOk Ro.layout 0x100 sp → u.getReg .x10 = sp → u.getReg .x11 = BitVec.ofNat 64 C →
      u.getReg .x12 = 1#64 → u.getReg .x13 = 1#64 → u.getReg .x14 = 1#64 →
      Region sp [BitVec.ofNat 64 C, p, BitVec.ofNat 64 C] u → Region p W u →
      0x78048980 ≤ p.toNat → p.toNat + C ≤ 0x1c00000000 →
      RoImage Ro.layout u → Run.HeapAt ((p, C / 8) :: L') u →
      (∀ (t : MachineState) (p' : Word) (W' : List Word), t.pc = 0x7801e0f8#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp - 0x100#64, 32), (sp, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region sp [BitVec.ofNat 64 (2 * C), p', BitVec.ofNat 64 C] t → W'.length = C / 8 + 1 →
        Region p' (W ++ W') t → RegionOk Ro.layout.roBase Ro.layout.textHi p' (C / 4 + 1) →
        0x78048980 ≤ p'.toNat → p'.toNat + 2 * C + 8 ≤ 0x1c00000000 →
        Run.HeapAt ((p', C / 4) :: L') t → SafeN Gd n P t) → SafeN Gd n P u)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN Gd n P u)
    (hk : ∀ (t : MachineState) (ptr : Word) (Bv I1 : List Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code →
      Unchanged [(sp - 0x180#64, 76), (out, 3), (a1, 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      I1.length = 18 → Region out [2048#64, ptr, 1090#64] t → Region a1 I1 t →
      Bv.length = 257 → (∀ o, o < 1090 → byteAt Bv o = bw (noteBit G K v R Q o)) → Region ptr Bv t →
      RegionOk Ro.layout.roBase Ro.layout.textHi ptr 257 → 0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 257 ≤ 0x1c00000000 →
      Run.HeapAt ((ptr, 256) :: L) t → SafeN Gd n P t) :
    SafeN Gd n P s := by
  have E : NoteEnv sp sp0 out a1 G K R Q :=
    ⟨hGl, hKl, hRl, hQl, hstk, hokFr, hokO, hokC, hokM, hsp0_lo, hsp0_hi, hdjSM, hdjSO, hdjSC,
     hdjOM, hdjOC, hdjCM, hdjHM, hdjHO, hdjHC, hout, ha1lo⟩
  have C0 : NoteCtx sp0 v G K R Q s := ⟨hcode, hcodeN, hcw, hGr, hKr, hVr, hRr, hQr⟩
  -- the reserve contract at a loop state
  have hres : ∀ (t : MachineState), t.code = s.code → ∀ (C : Nat) (p : Word),
      (C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256 ∨ C = 512 ∨ C = 1024) →
      ∀ (u : MachineState) (W : List Word) (L' : List (Word × Nat)), W.length = C / 8 →
      u.pc = 0x780221a4#64 → u.code = t.code → u.getReg .x1 = 0x7801e0f8#64 → u.getReg .x2 = sp →
      StackOk Ro.layout 0x100 sp → u.getReg .x10 = sp → u.getReg .x11 = BitVec.ofNat 64 C →
      u.getReg .x12 = 1#64 → u.getReg .x13 = 1#64 → u.getReg .x14 = 1#64 →
      Region sp [BitVec.ofNat 64 C, p, BitVec.ofNat 64 C] u → Region p W u →
      0x78048980 ≤ p.toNat → p.toNat + C ≤ 0x1c00000000 →
      RoImage Ro.layout u → Run.HeapAt ((p, C / 8) :: L') u →
      (∀ (t : MachineState) (p' : Word) (W' : List Word), t.pc = 0x7801e0f8#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp - 0x100#64, 32), (sp, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region sp [BitVec.ofNat 64 (2 * C), p', BitVec.ofNat 64 C] t → W'.length = C / 8 + 1 →
        Region p' (W ++ W') t → RegionOk Ro.layout.roBase Ro.layout.textHi p' (C / 4 + 1) →
        0x78048980 ≤ p'.toNat → p'.toNat + 2 * C + 8 ≤ 0x1c00000000 →
        Run.HeapAt ((p', C / 4) :: L') t → SafeN Gd n P t) → SafeN Gd n P u :=
    fun t hts C p hC u W L' hW hpc hcode hra hsp hstk h10 h11 h12 h13 h14 hV hW' hlo hhi hro' hheap' hk' =>
      hreserve u C p W L' hC hW hpc (hcode.trans hts) hra hsp hstk h10 h11 h12 h13 h14 hV hW' hlo hhi hro' hheap' hk'
  -- the prologue: byte 1, capacity 8
  refine note_pro_step E hOl hpc C0 hcodeM hcodeZ hra hsp ha0 ha1 hO hCb hro hheap halloc hhandle_rv ?_
  intro t1 ptr w hc1 hu1 hk1 C1 H1 hF1 hO1 ⟨I1, hI1l, hR1⟩
  have hu1' := unch_proN (out := out) hstk hu1
  -- phase 1: bytes 1 … 8
  refine note_phase E (cap := 8) (by omega) 0 0 t1 ptr [w] (by omega) (by omega) (by simp) H1 C1 ?_
  intro t2 V2 hc2 hu2 hk2 C2 hl2 H2
  refine note_grow_step E (C := 8) (by simp) (by simp at hl2; omega) H2 C2
    (hres t2 (hc2.trans hc1) 8 ptr (by simp)) ?_
  intro t3 p3 V3 hc3 hu3 hk3 C3 hl3 H3
  -- phase 2: bytes 9 … 16
  refine note_phase E (cap := 16) (by omega) 1 0 t3 p3 V3 (by omega) (by omega) (by omega) H3 C3 ?_
  intro t4 V4 hc4 hu4 hk4 C4 hl4 H4
  have hcs4 : t4.code = s.code := hc4.trans (hc3.trans (hc2.trans hc1))
  refine note_grow_step E (C := 16) (by simp) (by omega) H4 C4 (hres t4 hcs4 16 p3 (by simp)) ?_
  intro t5 p5 V5 hc5 hu5 hk5 C5 hl5 H5
  -- phase 3: bytes 17 … 32
  refine note_phase E (cap := 32) (by omega) 2 1 t5 p5 V5 (by omega) (by omega) (by omega) H5 C5 ?_
  intro t6 V6 hc6 hu6 hk6 C6 hl6 H6
  have hcs6 : t6.code = s.code := hc6.trans (hc5.trans hcs4)
  refine note_grow_step E (C := 32) (by simp) (by omega) H6 C6 (hres t6 hcs6 32 p5 (by simp)) ?_
  intro t7 p7 V7 hc7 hu7 hk7 C7 hl7 H7
  -- phase 4: bytes 33 … 64
  refine note_phase E (cap := 64) (by omega) 4 3 t7 p7 V7 (by omega) (by omega) (by omega) H7 C7 ?_
  intro t8 V8 hc8 hu8 hk8 C8 hl8 H8
  have hcs8 : t8.code = s.code := hc8.trans (hc7.trans hcs6)
  refine note_grow_step E (C := 64) (by simp) (by omega) H8 C8 (hres t8 hcs8 64 p7 (by simp)) ?_
  intro t9 p9 V9 hc9 hu9 hk9 C9 hl9 H9
  -- phase 5: bytes 65 … 128
  refine note_phase E (cap := 128) (by omega) 8 7 t9 p9 V9 (by omega) (by omega) (by omega) H9 C9 ?_
  intro t10 V10 hc10 hu10 hk10 C10 hl10 H10
  have hcs10 : t10.code = s.code := hc10.trans (hc9.trans hcs8)
  refine note_grow_step E (C := 128) (by simp) (by omega) H10 C10 (hres t10 hcs10 128 p9 (by simp)) ?_
  intro t11 p11 V11 hc11 hu11 hk11 C11 hl11 H11
  -- phase 6: bytes 129 … 256
  refine note_phase E (cap := 256) (by omega) 16 15 t11 p11 V11 (by omega) (by omega) (by omega) H11 C11 ?_
  intro t12 V12 hc12 hu12 hk12 C12 hl12 H12
  have hcs12 : t12.code = s.code := hc12.trans (hc11.trans hcs10)
  refine note_grow_step E (C := 256) (by simp) (by omega) H12 C12 (hres t12 hcs12 256 p11 (by simp)) ?_
  intro t13 p13 V13 hc13 hu13 hk13 C13 hl13 H13
  -- phase 7: bytes 257 … 512
  refine note_phase E (cap := 512) (by omega) 32 31 t13 p13 V13 (by omega) (by omega) (by omega) H13 C13 ?_
  intro t14 V14 hc14 hu14 hk14 C14 hl14 H14
  have hcs14 : t14.code = s.code := hc14.trans (hc13.trans hcs12)
  refine note_grow_step E (C := 512) (by simp) (by omega) H14 C14 (hres t14 hcs14 512 p13 (by simp)) ?_
  intro t15 p15 V15 hc15 hu15 hk15 C15 hl15 H15
  -- phase 8: bytes 513 … 1024
  refine note_phase E (cap := 1024) (by omega) 64 63 t15 p15 V15 (by omega) (by omega) (by omega) H15 C15 ?_
  intro t16 V16 hc16 hu16 hk16 C16 hl16 H16
  have hcs16 : t16.code = s.code := hc16.trans (hc15.trans hcs14)
  refine note_grow_step E (C := 1024) (by simp) (by omega) H16 C16 (hres t16 hcs16 1024 p15 (by simp)) ?_
  intro t17 p17 V17 hc17 hu17 hk17 C17 hl17 H17
  -- phase 9: bytes 1025 … 1088
  refine note_phase E (cap := 2048) (by omega) 128 7 t17 p17 V17 (by omega) (by omega) (by omega) H17 C17 ?_
  intro t18 V18 hc18 hu18 hk18 C18 hl18 H18
  have hcs18 : t18.code = s.code := hc18.trans (hc17.trans hcs16)
  have hl18' : V18.length = 257 := by rw [hl18, hl17]
  -- the loop's frame condition from the state after the prologue
  have huL : Unchanged (noteLoopW sp) t1 t18 :=
    hu2.trans (hu3.trans (hu4.trans (hu5.trans (hu6.trans (hu7.trans (hu8.trans (hu9.trans
      (hu10.trans (hu11.trans (hu12.trans (hu13.trans (hu14.trans (hu15.trans (hu16.trans
      (hu17.trans hu18)))))))))))))))
  have hkL : Kept t1 t18 :=
    hk2.trans (hk3.trans (hk4.trans (hk5.trans (hk6.trans (hk7.trans (hk8.trans (hk9.trans
      (hk10.trans (hk11.trans (hk12.trans (hk13.trans (hk14.trans (hk15.trans (hk16.trans
      (hk17.trans hk18)))))))))))))))
  have hF18 := E.keepSv huL rfl hF1
  have hO18 := E.keepO huL hOl hO1
  have hR18 := E.keepC huL hI1l hR1
  -- the exit
  refine note_tail_step E hOl hl18' hra1 H18 C18 hF18 hO18 ?_
  intro t Bv hpc' hcode' hun hkT hsp' hs0' hs1' hs2' hs3' hs4' hs5' hOut hBvl hbits hBv hok' hlo' hhi' _ hheapT
  have hkA : Kept s t := hk1.trans (hkL.trans hkT)
  refine hk t p17 Bv I1 hpc' ?_ (hcode'.trans hcs18) ?_ hI1l hOut (E.keepC_tail hlo' hhi' hun hI1l hR18)
    hBvl hbits hBv hok' hlo' hhi' hheapT
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
  · exact hu1'.trans ((unch_loopN (out := out) (a1 := a1) hstk huL).trans
      (unch_tailN (a1 := a1) hstk hlo' hhi' hun))

end Cases.Zip2005
