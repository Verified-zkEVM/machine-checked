import Cases.Zip2005.Sinsemilla.FromIterNote
import Cases.Zip2005.Sinsemilla.FromIterNoteGrow
import Cases.Zip2005.Sinsemilla.FromIterNoteTail
import Cases.Zip2005.Sinsemilla.FromIterNotePro
import Cases.Zip2005.Sinsemilla.LoopKit
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `from_iter`'s loop (0x7801dfb4): the invariant and the steps

`NoteHead` is the state at the loop head (byte `n`, capacity `cap`, the buffer `V`); the steps
are one word (`note_word8_step`, `note_word7_step`), `k` words (`note_words8`), a phase between
growths (`note_phase`), a growth (`note_grow_step`), the prologue and the exit. The message
words `g★_d`, `pk★_d`, `v`, `ρ`, `ψ` sit in `NoteCommitment::derive`'s frame `sp0` as one
17-word block at `sp0 - 0xd0`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-! The five message regions are offsets into one 17-word block at `sp0 - 0xd0`. -/

theorem dj_G {sp0 b : Word} {n : Nat} (h : MachineChecked.RiscV.Sym.Disjoint b n (sp0 + 18446744073709551408#64) 17) : MachineChecked.RiscV.Sym.Disjoint b n (sp0 + 18446744073709551408#64) 4 :=
  h.sub_right (self_add_zero _) (by omega)
theorem dj_K {sp0 b : Word} {n : Nat} (h : MachineChecked.RiscV.Sym.Disjoint b n (sp0 + 18446744073709551408#64) 17) : MachineChecked.RiscV.Sym.Disjoint b n (sp0 + 18446744073709551440#64) 4 :=
  h.sub_right (msg_K sp0) (by omega)
theorem dj_V {sp0 b : Word} {n : Nat} (h : MachineChecked.RiscV.Sym.Disjoint b n (sp0 + 18446744073709551408#64) 17) : MachineChecked.RiscV.Sym.Disjoint b n (sp0 + 18446744073709551472#64) 1 :=
  h.sub_right (msg_V sp0) (by omega)
theorem dj_R {sp0 b : Word} {n : Nat} (h : MachineChecked.RiscV.Sym.Disjoint b n (sp0 + 18446744073709551408#64) 17) : MachineChecked.RiscV.Sym.Disjoint b n (sp0 + 18446744073709551480#64) 4 :=
  h.sub_right (msg_R sp0) (by omega)
theorem dj_Q {sp0 b : Word} {n : Nat} (h : MachineChecked.RiscV.Sym.Disjoint b n (sp0 + 18446744073709551408#64) 17) : MachineChecked.RiscV.Sym.Disjoint b n (sp0 + 18446744073709551512#64) 4 :=
  h.sub_right (msg_Q sp0) (by omega)

/-- The call's fixed facts: the 76-word frame `[sp - 0x180, sp + 0xe0)` (`sp` the frame the
loop runs in, the entry `sp + 0xe0`), the message block at `derive`'s frame `sp0`, the output
`Vec` header `out`, the caller's iterator block `a1`. -/
structure NoteEnv (sp sp0 out a1 : Word) (G K R Q : List Word) : Prop where
  Gl : G.length = 4
  Kl : K.length = 4
  Rl : R.length = 4
  Ql : Q.length = 4
  stk : StackOk Ro.layout 0x180 sp
  okFr : RegionOk Ro.layout.roBase Ro.layout.textHi sp 28
  okO : RegionOk Ro.layout.roBase Ro.layout.textHi out 3
  okC : RegionOk Ro.layout.roBase Ro.layout.textHi a1 18
  okM : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551408#64) 17
  sp0_lo : 0x10000 ≤ sp0.toNat
  sp0_hi : sp0.toNat ≤ 0x78000000
  djSM : MachineChecked.RiscV.Sym.Disjoint (sp - 0x180#64) 76 (sp0 + 18446744073709551408#64) 17
  djSO : MachineChecked.RiscV.Sym.Disjoint (sp - 0x180#64) 76 out 3
  djSC : MachineChecked.RiscV.Sym.Disjoint (sp - 0x180#64) 76 a1 18
  djOM : MachineChecked.RiscV.Sym.Disjoint out 3 (sp0 + 18446744073709551408#64) 17
  djOC : MachineChecked.RiscV.Sym.Disjoint out 3 a1 18
  djCM : MachineChecked.RiscV.Sym.Disjoint a1 18 (sp0 + 18446744073709551408#64) 17
  djHM : MachineChecked.RiscV.Sym.Disjoint 0x78040620#64 14780694332 (sp0 + 18446744073709551408#64) 17
  djHO : MachineChecked.RiscV.Sym.Disjoint 0x78040620#64 14780694332 out 3
  djHC : MachineChecked.RiscV.Sym.Disjoint 0x78040620#64 14780694332 a1 18
  outlo : out.toNat + 8 * 3 ≤ 0x78040620
  a1lo : a1.toNat + 8 * 18 ≤ 0x78040620

namespace NoteEnv

variable {sp sp0 out a1 : Word} {G K R Q : List Word}

theorem stk100 (E : NoteEnv sp sp0 out a1 G K R Q) : StackOk Ro.layout 0x100 sp := ⟨E.stk.aligned, by have := E.stk.lo; omega, E.stk.hi⟩
theorem okV (E : NoteEnv sp sp0 out a1 G K R Q) : RegionOk Ro.layout.roBase Ro.layout.textHi sp 3 := E.okFr.sub' 0 3 (by omega) (self_add_zero sp)
theorem okBlk (E : NoteEnv sp sp0 out a1 G K R Q) : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x18#64) 18 := E.okFr.sub' 3 18 (by omega) rfl
theorem okSv (E : NoteEnv sp sp0 out a1 G K R Q) : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xa8#64) 7 := E.okFr.sub' 21 7 (by omega) rfl
theorem okG (E : NoteEnv sp sp0 out a1 G K R Q) : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551408#64) 4 := E.okM.sub' 0 4 (by omega) (self_add_zero _)
theorem okK (E : NoteEnv sp sp0 out a1 G K R Q) : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551440#64) 4 := E.okM.sub' 4 4 (by omega) (msg_K sp0)
theorem okVv (E : NoteEnv sp sp0 out a1 G K R Q) : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551472#64) 1 := E.okM.sub' 8 1 (by omega) (msg_V sp0)
theorem okR (E : NoteEnv sp sp0 out a1 G K R Q) : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551480#64) 4 := E.okM.sub' 9 4 (by omega) (msg_R sp0)
theorem okQ (E : NoteEnv sp sp0 out a1 G K R Q) : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551512#64) 4 := E.okM.sub' 13 4 (by omega) (msg_Q sp0)
theorem djHS (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint 0x78040620#64 14780694332 (sp - 0x180#64) 76 :=
  MachineChecked.RiscV.Sym.Disjoint.heap_framen76 E.stk
theorem djFM (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint (sp - 0x180#64) 48 (sp0 + 18446744073709551408#64) 17 := E.djSM.sub_left (self_add_zero _) (by omega)
theorem djFO (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint (sp - 0x180#64) 48 out 3 := E.djSO.sub_left (self_add_zero _) (by omega)
theorem djFC (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint (sp - 0x180#64) 48 a1 18 := E.djSC.sub_left (self_add_zero _) (by omega)
theorem djVM (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint sp 3 (sp0 + 18446744073709551408#64) 17 := E.djSM.sub_left (frn_0 sp) (by omega)
theorem djVO (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint sp 3 out 3 := E.djSO.sub_left (frn_0 sp) (by omega)
theorem djVC (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint sp 3 a1 18 := E.djSC.sub_left (frn_0 sp) (by omega)
theorem djS28M (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint sp 28 (sp0 + 18446744073709551408#64) 17 := E.djSM.sub_left (frn_0 sp) (by omega)
theorem djS28O (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint sp 28 out 3 := E.djSO.sub_left (frn_0 sp) (by omega)
theorem djS28C (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint sp 28 a1 18 := E.djSC.sub_left (frn_0 sp) (by omega)
theorem djBM (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint (sp + 0x18#64) 18 (sp0 + 18446744073709551408#64) 17 := E.djSM.sub_left (frn_18 sp) (by omega)
theorem djBO (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint (sp + 0x18#64) 18 out 3 := E.djSO.sub_left (frn_18 sp) (by omega)
theorem djBC (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint (sp + 0x18#64) 18 a1 18 := E.djSC.sub_left (frn_18 sp) (by omega)
theorem djFBlk (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint (sp - 0x180#64) 48 (sp + 0x18#64) 18 :=
  MachineChecked.RiscV.Sym.Disjoint.within (N := 76) (framen_nowrap E.stk) (self_add_zero _) (frn_18 sp) (by omega) (by omega) (Or.inl (by omega))
theorem djSvF (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint (sp + 0xa8#64) 7 (sp - 0x180#64) 48 :=
  MachineChecked.RiscV.Sym.Disjoint.within (N := 76) (framen_nowrap E.stk) (frn_a8 sp) (self_add_zero _) (by omega) (by omega) (Or.inr (by omega))
theorem djSvV (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint (sp + 0xa8#64) 7 sp 3 :=
  MachineChecked.RiscV.Sym.Disjoint.within (N := 76) (framen_nowrap E.stk) (frn_a8 sp) (frn_0 sp) (by omega) (by omega) (Or.inr (by omega))
theorem djSvBlk (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint (sp + 0xa8#64) 7 (sp + 0x18#64) 18 :=
  MachineChecked.RiscV.Sym.Disjoint.within (N := 76) (framen_nowrap E.stk) (frn_a8 sp) (frn_18 sp) (by omega) (by omega) (Or.inr (by omega))
theorem djSvH (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint (sp + 0xa8#64) 7 0x78040620#64 14780694332 :=
  (E.djHS.sub_right (frn_a8 sp) (by omega)).symm
theorem djSvO (E : NoteEnv sp sp0 out a1 G K R Q) : MachineChecked.RiscV.Sym.Disjoint (sp + 0xa8#64) 7 out 3 := E.djSO.sub_left (frn_a8 sp) (by omega)

end NoteEnv

/-- The state at the loop head, byte `n` with capacity `cap`, the buffer `V` at `p`. -/
structure NoteHead (sp sp0 out p v : Word) (J G K R Q : List Word) (L : List (Word × Nat)) (j : Word) (cap n : Nat) (V : List Word)
    (t : MachineState) : Prop where
  hpc : t.pc = 0x7801e0d4#64
  hsp : t.getReg .x2 = sp
  hout : t.getReg .x8 = out
  hp : t.getReg .x9 = p
  hn : t.getReg .x18 = BitVec.ofNat 64 n
  htwo : t.getReg .x19 = 2#64
  hbit : t.getReg .x20 = bw (noteBit G K v R Q n)
  hvec : Region sp [BitVec.ofNat 64 cap, p, BitVec.ofNat 64 n] t
  hblk : Region (sp + 0x18#64) (noteState sp0 J j (n + 1)) t
  hbuf : Region p V t
  hbits : BitsUpToF (noteBit G K v R Q) V n
  hok : RegionOk Ro.layout.roBase Ro.layout.textHi p V.length
  hlo : 0x78048980 ≤ p.toNat
  hhi : p.toNat + 8 * V.length ≤ 0x1c00000000
  ro : RoImage Ro.layout t
  heap : Run.HeapAt ((p, cap / 8) :: L) t

/-- What the loop needs of a state besides the head: the code and the message words. -/
structure NoteCtx (sp0 v : Word) (G K R Q : List Word) (t : MachineState) : Prop where
  code : CodeAt F_7801dfb4.base F_7801dfb4.prog t
  codeN : CodeAt F_78021720.base F_78021720.prog t
  cw : CodeWithin Ro.layout.textLo Ro.layout.textHi t
  Gr : Region (sp0 + 18446744073709551408#64) G t
  Kr : Region (sp0 + 18446744073709551440#64) K t
  Vr : Region (sp0 + 18446744073709551472#64) [v] t
  Rr : Region (sp0 + 18446744073709551480#64) R t
  Qr : Region (sp0 + 18446744073709551512#64) Q t

theorem NoteCtx.step {sp sp0 out a1 v : Word} {G K R Q : List Word} {s t : MachineState}
    (E : NoteEnv sp sp0 out a1 G K R Q)
    (C : NoteCtx sp0 v G K R Q s) (hc : t.code = s.code) {W : List (Word × Nat)} (hu : Unchanged W s t)
    (hM : ∀ r ∈ W, MachineChecked.RiscV.Sym.Disjoint r.1 r.2 (sp0 + 18446744073709551408#64) 17) : NoteCtx sp0 v G K R Q t :=
  ⟨codeAt_of_code_eq hc C.code, codeAt_of_code_eq hc C.codeN, codeWithin_of_code_eq hc C.cw,
   C.Gr.of_unchanged hu (fun r hr => by rw [E.Gl]; exact (dj_G (hM r hr)).symm),
   C.Kr.of_unchanged hu (fun r hr => by rw [E.Kl]; exact (dj_K (hM r hr)).symm),
   C.Vr.of_unchanged hu (fun r hr => (dj_V (hM r hr)).symm),
   C.Rr.of_unchanged hu (fun r hr => by rw [E.Rl]; exact (dj_R (hM r hr)).symm),
   C.Qr.of_unchanged hu (fun r hr => by rw [E.Ql]; exact (dj_Q (hM r hr)).symm)⟩

/-- The loop's write set: its callees' frames, the `Vec` header and the block copy, the heap.
The saved registers at `sp + 0xa8` and the output header lie outside it. -/
abbrev noteLoopW (sp : Word) : List (Word × Nat) :=
  [(sp - 0x180#64, 48), (sp, 21), (0x78040620#64, 4162), (0x78048980#64, 14780690128)]

theorem loop_nowrap48 {sp : Word} (h : StackOk Ro.layout 0x180 sp) : (sp - 0x180#64).toNat + 8 * 48 ≤ 2 ^ 64 := by
  rw [toNat_sub_lit sp 0x180 (by have := h.lo; omega)]; have := (Nat.le_trans h.hi (Nat.le_of_eq Ro.layout_stackTop)); omega

theorem loop_nowrap21 {sp : Word} (h : StackOk Ro.layout 0x180 sp) : sp.toNat + 8 * 21 ≤ 2 ^ 64 := by
  have := (Nat.le_trans h.hi (Nat.le_of_eq Ro.layout_stackTop)); omega

/-- The callees' frames cover an offset block. -/
theorem coverF48 {sp : Word} (hstk : StackOk Ro.layout 0x180 sp) {b : Word} {i n : Nat}
    (hb : b = sp - 0x180#64 + BitVec.ofNat 64 (8 * i)) (hin : i + n ≤ 48) (hn : 0 < n) :
    ∃ r' ∈ noteLoopW sp, Covers r'.1 r'.2 b n :=
  ⟨(sp - 0x180#64, 48), by simp, covers_of_sub (loop_nowrap48 hstk) hb hin hn⟩

theorem noteCoverV {sp : Word} (hstk : StackOk Ro.layout 0x180 sp) {b : Word} {i n : Nat}
    (hb : b = sp + BitVec.ofNat 64 (8 * i)) (hin : i + n ≤ 21) (hn : 0 < n) :
    ∃ r' ∈ noteLoopW sp, Covers r'.1 r'.2 b n :=
  ⟨(sp, 21), by simp, covers_of_sub (loop_nowrap21 hstk) hb hin hn⟩

theorem noteCoverH {sp : Word} {b : Word} {n : Nat} (hlo : 0x78048980 ≤ b.toNat)
    (hhi : b.toNat + 8 * n ≤ 0x1c00000000) :
    ∃ r' ∈ noteLoopW sp, Covers r'.1 r'.2 b n :=
  ⟨(0x78048980#64, 14780690128), by simp, covers_arena hlo hhi⟩

/-- One word of the loop from byte `8m`: eight `next` calls, eight byte stores. -/
theorem note_word8_step {L : List (Word × Nat)} {Gd : MachineState → Prop} {nb : Nat} {P : Prop} {s : MachineState} {sp sp0 out a1 p v : Word} {J G K R Q V : List Word}
    {j : Word} (E : NoteEnv sp sp0 out a1 G K R Q) {cap m : Nat} (hcap : cap ≤ 2048)
    (hm8 : 8 * (m + 1) ≤ cap) (hm : m ≤ 135) (hmV : m < V.length)
    (H : NoteHead sp sp0 out p v J G K R Q L j cap (8 * m) V s) (C : NoteCtx sp0 v G K R Q s)
    (hk : ∀ (t : MachineState) (w' : Word), t.code = s.code → Unchanged (noteLoopW sp) s t →
      Kept s t → NoteCtx sp0 v G K R Q t →
      NoteHead sp sp0 out p v J G K R Q L j cap (8 * (m + 1)) (V.set m w') t → SafeN Gd nb P t) :
    SafeN Gd nb P s := by
  have hlo := H.hlo
  have hhi := H.hhi
  have hnw : p.toNat + 8 * V.length < 2 ^ 64 := by omega
  have hq : ∀ r : Nat, p + (BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 r) =
      p + BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 r := fun r => (BitVec.add_assoc _ _ _).symm
  have hc : ∀ r : Nat, r < 8 →
      (BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 r == BitVec.ofNat 64 cap) = false := fun r hr => by
    rw [BitVec.ofNat_add_ofNat]; exact ofNat_beq_false (by omega) (by omega) (by omega)
  have hokq : RegionOk Ro.layout.roBase Ro.layout.textHi (p + BitVec.ofNat 64 (8 * m)) 1 := H.hok.sub' m 1 (by omega) rfl
  have djP : ∀ {b : Word} {n : Nat}, MachineChecked.RiscV.Sym.Disjoint 0x78040620#64 14780694332 b n →
      MachineChecked.RiscV.Sym.Disjoint p V.length b n := fun h => h.of_heap (by omega) hhi
  have hdjq : ∀ {b : Word} {n : Nat}, MachineChecked.RiscV.Sym.Disjoint p V.length b n →
      MachineChecked.RiscV.Sym.Disjoint (p + BitVec.ofNat 64 (8 * m)) 1 b n := fun h => h.sub_left rfl (by omega)
  have hdjqS := hdjq (djP E.djHS)
  refine from_iter_note_word8 s sp sp0 out v p (BitVec.ofNat 64 (8 * m)) (p + BitVec.ofNat 64 (8 * m))
    (BitVec.ofNat 64 cap) V[m]! (bw (noteBit G K v R Q (8 * m))) J G K R Q (noteState sp0 J j (8 * m + 1)) j E.Gl E.Kl E.Rl E.Ql
    m hm (by simp) rfl rfl (hq 1) (hq 2) (hq 3) (hq 4) (hq 5) (hq 6) (hq 7)
    (ofNat_beq_false (by omega) (by omega) (by omega))
    (hc 1 (by omega)) (hc 2 (by omega)) (hc 3 (by omega)) (hc 4 (by omega)) (hc 5 (by omega))
    (hc 6 (by omega)) (hc 7 (by omega))
    H.hpc C.code C.codeN C.cw H.ro H.heap
    (by rw [toNat_add_lit p (8 * m) (by omega)]; omega) (by rw [toNat_add_lit p (8 * m) (by omega)]; omega)
    H.hsp E.stk H.hout H.hp H.hn H.htwo rfl H.hbit H.hvec E.okV H.hblk
    E.okBlk (Region.window H.hbuf m hmV) hokq C.Gr E.okG C.Kr E.okK C.Vr E.okVv C.Rr E.okR C.Qr E.okQ E.sp0_lo E.sp0_hi
    (dj_G E.djBM) (dj_K E.djBM) (dj_V E.djBM) (dj_R E.djBM) (dj_Q E.djBM)
    (dj_G E.djFM) (dj_K E.djFM) (dj_V E.djFM) (dj_R E.djFM) (dj_Q E.djFM)
    (hdjqS.sub_right (self_add_zero _) (by omega)).symm
    (hdjqS.sub_right (frn_0 sp) (by omega)).symm (hdjqS.sub_right (frn_18 sp) (by omega)).symm
    E.djFBlk (hdjq (djP (dj_G E.djHM))) (hdjq (djP (dj_K E.djHM))) (hdjq (djP (dj_V E.djHM)))
    (hdjq (djP (dj_R E.djHM))) (hdjq (djP (dj_Q E.djHM))) ?_
  intro t I' w' bit' hpc' hcode' hun hsp' hs0' hs1' hs2' hs3' h3 h4 h22 h23 h24 h25 h26 h27 hbit' hs4'
    hV' _ hIv' hBlk' hW' hb hro' hheap'
  rw [show 8 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 8 * (m + 1) by omega] at hbit'
  rw [show 8 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 8 * (m + 1) + 1 by omega] at hIv'
  rw [BitVec.ofNat_add_ofNat, show 8 * m + 8 = 8 * (m + 1) by omega] at hV' hs2'
  -- the frame condition, covered
  have hunF : Unchanged (noteLoopW sp) s t := by
    refine Unchanged.trans_cover (Unchanged.refl _ s) hun ?_
    intro r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact coverF48 E.stk (self_add_zero _) (by omega) (by omega)
    · exact noteCoverV E.stk (self_add_zero sp) (by omega) (by omega)
    · exact noteCoverV E.stk (i := 3) rfl (by omega) (by omega)
    · exact noteCoverH (by rw [toNat_add_lit p (8 * m) (by omega)]; omega)
        (by rw [toNat_add_lit p (8 * m) (by omega)]; omega)
  have hdjM : ∀ r ∈ [(sp - 0x180#64, 48), (sp, 3), (sp + 0x18#64, 18), (p + BitVec.ofNat 64 (8 * m), 1)],
      MachineChecked.RiscV.Sym.Disjoint r.1 r.2 (sp0 + 18446744073709551408#64) 17 := by
    intro r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact E.djFM
    · exact E.djVM
    · exact E.djBM
    · exact hdjq (djP E.djHM)
  -- the buffer: the words before `m`, word `m`, the words after
  have hpre : Region p (V.take m) t := by
    refine (Region.take H.hbuf m).of_unchanged' hun (n := m) (by simp [List.length_take]; omega) ?_
    intro r hr
    have hd : ∀ {b : Word} {n : Nat}, MachineChecked.RiscV.Sym.Disjoint p V.length b n → MachineChecked.RiscV.Sym.Disjoint p m b n :=
      fun h => h.sub_left (self_add_zero p) (by omega)
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact hd (djP E.djHS) |>.sub_right (self_add_zero _) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (frn_0 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (frn_18 sp) (by omega)
    · exact MachineChecked.RiscV.Sym.Disjoint.within (N := V.length) (by omega) (self_add_zero p) rfl (by omega) (by omega) (Or.inl (by omega))
  have hpost : Region (p + BitVec.ofNat 64 (8 * (m + 1))) (V.drop (m + 1)) t := by
    refine (Region.shift H.hbuf (m + 1)).of_unchanged' hun (n := V.length - (m + 1))
      (by simp [List.length_drop]) ?_
    intro r hr
    have hd : ∀ {b : Word} {n : Nat}, MachineChecked.RiscV.Sym.Disjoint p V.length b n →
        MachineChecked.RiscV.Sym.Disjoint (p + BitVec.ofNat 64 (8 * (m + 1))) (V.length - (m + 1)) b n :=
      fun h => h.sub_left rfl (by omega)
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact hd (djP E.djHS) |>.sub_right (self_add_zero _) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (frn_0 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (frn_18 sp) (by omega)
    · exact MachineChecked.RiscV.Sym.Disjoint.within (N := V.length) (by omega) rfl rfl (by omega) (by omega) (Or.inr (by omega))
  refine hk t w' hcode' hunF ⟨h3, h4, h22, h23, h24, h25, h26, h27⟩ (C.step E hcode' hun hdjM) ?_
  refine ⟨hpc', hsp', hs0', hs1', hs2', hs3', by rw [hs4', ← hbit'], hV', ?_, ?_, ?_, ?_, H.hlo, ?_, hro', hheap'⟩
  · rw [hIv']; exact hBlk'
  · exact Region.set_of_parts m w' hmV hpre hW' hpost
  · exact BitsUpToF.set w' 8 (le_refl _) hmV H.hbits hb
  · rw [List.length_set]; exact H.hok
  · rw [List.length_set]; exact H.hhi

/-- The rest of a word from byte `8m + 1`: seven `next` calls, seven byte stores, byte 0 kept. -/
theorem note_word7_step {L : List (Word × Nat)} {Gd : MachineState → Prop} {nb : Nat} {P : Prop} {s : MachineState} {sp sp0 out a1 p v : Word} {J G K R Q V : List Word}
    {j : Word} (E : NoteEnv sp sp0 out a1 G K R Q) {cap m : Nat} (hcap : cap ≤ 2048)
    (hm8 : 8 * (m + 1) ≤ cap) (hm : m ≤ 135) (hmV : m < V.length)
    (H : NoteHead sp sp0 out p v J G K R Q L j cap (8 * m + 1) V s) (C : NoteCtx sp0 v G K R Q s)
    (hk : ∀ (t : MachineState) (w' : Word), t.code = s.code → Unchanged (noteLoopW sp) s t →
      Kept s t → NoteCtx sp0 v G K R Q t →
      NoteHead sp sp0 out p v J G K R Q L j cap (8 * (m + 1)) (V.set m w') t → SafeN Gd nb P t) :
    SafeN Gd nb P s := by
  have hlo := H.hlo
  have hhi := H.hhi
  have hnw : p.toNat + 8 * V.length < 2 ^ 64 := by omega
  have hq : ∀ r : Nat, p + (BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 r) =
      p + BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 r := fun r => (BitVec.add_assoc _ _ _).symm
  have hc : ∀ r : Nat, r < 8 →
      (BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 r == BitVec.ofNat 64 cap) = false := fun r hr => by
    rw [BitVec.ofNat_add_ofNat]; exact ofNat_beq_false (by omega) (by omega) (by omega)
  have hokq : RegionOk Ro.layout.roBase Ro.layout.textHi (p + BitVec.ofNat 64 (8 * m)) 1 := H.hok.sub' m 1 (by omega) rfl
  have djP : ∀ {b : Word} {n : Nat}, MachineChecked.RiscV.Sym.Disjoint 0x78040620#64 14780694332 b n →
      MachineChecked.RiscV.Sym.Disjoint p V.length b n := fun h => h.of_heap (by omega) hhi
  have hdjq : ∀ {b : Word} {n : Nat}, MachineChecked.RiscV.Sym.Disjoint p V.length b n →
      MachineChecked.RiscV.Sym.Disjoint (p + BitVec.ofNat 64 (8 * m)) 1 b n := fun h => h.sub_left rfl (by omega)
  have hdjqS := hdjq (djP E.djHS)
  have hn1 : s.getReg .x18 = BitVec.ofNat 64 (8 * m) + 1#64 := by rw [H.hn, BitVec.ofNat_add]
  have hvec1 : Region sp [BitVec.ofNat 64 cap, p, BitVec.ofNat 64 (8 * m) + 1#64] s := by
    rw [← BitVec.ofNat_add]; exact H.hvec
  refine from_iter_note_word s sp sp0 out v p (BitVec.ofNat 64 (8 * m)) (p + BitVec.ofNat 64 (8 * m))
    (BitVec.ofNat 64 cap) V[m]! (bw (noteBit G K v R Q (8 * m + 1))) J G K R Q (noteState sp0 J j (8 * m + 2)) j
    E.Gl E.Kl E.Rl E.Ql m hm (by simp) rfl (hq 1) (hq 2) (hq 3) (hq 4) (hq 5) (hq 6) (hq 7)
    (hc 1 (by omega)) (hc 2 (by omega)) (hc 3 (by omega)) (hc 4 (by omega)) (hc 5 (by omega))
    (hc 6 (by omega)) (hc 7 (by omega))
    H.hpc C.code C.codeN C.cw H.ro H.heap
    (by rw [toNat_add_lit p (8 * m) (by omega)]; omega) (by rw [toNat_add_lit p (8 * m) (by omega)]; omega)
    H.hsp E.stk H.hout H.hp hn1 H.htwo rfl H.hbit hvec1 E.okV
    (by have := H.hblk; rwa [show 8 * m + 1 + 1 = 8 * m + 2 by omega] at this)
    E.okBlk (Region.window H.hbuf m hmV) hokq C.Gr E.okG C.Kr E.okK C.Vr E.okVv C.Rr E.okR C.Qr E.okQ E.sp0_lo E.sp0_hi
    (dj_G E.djBM) (dj_K E.djBM) (dj_V E.djBM) (dj_R E.djBM) (dj_Q E.djBM)
    (dj_G E.djFM) (dj_K E.djFM) (dj_V E.djFM) (dj_R E.djFM) (dj_Q E.djFM)
    (hdjqS.sub_right (self_add_zero _) (by omega)).symm
    (hdjqS.sub_right (frn_0 sp) (by omega)).symm (hdjqS.sub_right (frn_18 sp) (by omega)).symm
    E.djFBlk (hdjq (djP (dj_G E.djHM))) (hdjq (djP (dj_K E.djHM))) (hdjq (djP (dj_V E.djHM)))
    (hdjq (djP (dj_R E.djHM))) (hdjq (djP (dj_Q E.djHM))) ?_
  intro t I' w' bit' hpc' hcode' hun hsp' hs0' hs1' hs2' hs3' h3 h4 h22 h23 h24 h25 h26 h27 hbit' hs4'
    hV' _ hIv' hBlk' hW' hb0 hb hro' hheap'
  rw [show 8 * m + 2 + 1 + 1 + 1 + 1 + 1 + 1 = 8 * (m + 1) by omega] at hbit'
  rw [show 8 * m + 2 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 8 * (m + 1) + 1 by omega] at hIv'
  rw [BitVec.ofNat_add_ofNat, show 8 * m + 8 = 8 * (m + 1) by omega] at hV' hs2'
  have hunF : Unchanged (noteLoopW sp) s t := by
    refine Unchanged.trans_cover (Unchanged.refl _ s) hun ?_
    intro r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact coverF48 E.stk (self_add_zero _) (by omega) (by omega)
    · exact noteCoverV E.stk (self_add_zero sp) (by omega) (by omega)
    · exact noteCoverV E.stk (i := 3) rfl (by omega) (by omega)
    · exact noteCoverH (by rw [toNat_add_lit p (8 * m) (by omega)]; omega)
        (by rw [toNat_add_lit p (8 * m) (by omega)]; omega)
  have hdjM : ∀ r ∈ [(sp - 0x180#64, 48), (sp, 3), (sp + 0x18#64, 18), (p + BitVec.ofNat 64 (8 * m), 1)],
      MachineChecked.RiscV.Sym.Disjoint r.1 r.2 (sp0 + 18446744073709551408#64) 17 := by
    intro r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact E.djFM
    · exact E.djVM
    · exact E.djBM
    · exact hdjq (djP E.djHM)
  have hpre : Region p (V.take m) t := by
    refine (Region.take H.hbuf m).of_unchanged' hun (n := m) (by simp [List.length_take]; omega) ?_
    intro r hr
    have hd : ∀ {b : Word} {n : Nat}, MachineChecked.RiscV.Sym.Disjoint p V.length b n → MachineChecked.RiscV.Sym.Disjoint p m b n :=
      fun h => h.sub_left (self_add_zero p) (by omega)
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact hd (djP E.djHS) |>.sub_right (self_add_zero _) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (frn_0 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (frn_18 sp) (by omega)
    · exact MachineChecked.RiscV.Sym.Disjoint.within (N := V.length) (by omega) (self_add_zero p) rfl (by omega) (by omega) (Or.inl (by omega))
  have hpost : Region (p + BitVec.ofNat 64 (8 * (m + 1))) (V.drop (m + 1)) t := by
    refine (Region.shift H.hbuf (m + 1)).of_unchanged' hun (n := V.length - (m + 1))
      (by simp [List.length_drop]) ?_
    intro r hr
    have hd : ∀ {b : Word} {n : Nat}, MachineChecked.RiscV.Sym.Disjoint p V.length b n →
        MachineChecked.RiscV.Sym.Disjoint (p + BitVec.ofNat 64 (8 * (m + 1))) (V.length - (m + 1)) b n :=
      fun h => h.sub_left rfl (by omega)
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact hd (djP E.djHS) |>.sub_right (self_add_zero _) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (frn_0 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (frn_18 sp) (by omega)
    · exact MachineChecked.RiscV.Sym.Disjoint.within (N := V.length) (by omega) rfl rfl (by omega) (by omega) (Or.inr (by omega))
  refine hk t w' hcode' hunF ⟨h3, h4, h22, h23, h24, h25, h26, h27⟩ (C.step E hcode' hun hdjM) ?_
  refine ⟨hpc', hsp', hs0', hs1', hs2', hs3', by rw [hs4', ← hbit'], hV', ?_, ?_, ?_, ?_, H.hlo, ?_, hro', hheap'⟩
  · rw [hIv']; exact hBlk'
  · exact Region.set_of_parts m w' hmV hpre hW' hpost
  · exact BitsUpToF.set7 w' hmV H.hbits hb0 hb
  · rw [List.length_set]; exact H.hok
  · rw [List.length_set]; exact H.hhi

/-- `k` whole words from byte `8m`. -/
theorem note_words8 {L : List (Word × Nat)} {Gd : MachineState → Prop} {n : Nat} {P : Prop} {sp sp0 out a1 v : Word} {J G K R Q : List Word} {j : Word}
    (E : NoteEnv sp sp0 out a1 G K R Q) {cap : Nat} (hcap : cap ≤ 2048) (k : Nat) :
    ∀ (m : Nat) (s : MachineState) (p : Word) (V : List Word), 8 * (m + k) ≤ cap → m + k ≤ 136 →
      m + k ≤ V.length →
      NoteHead sp sp0 out p v J G K R Q L j cap (8 * m) V s → NoteCtx sp0 v G K R Q s →
      (∀ (t : MachineState) (V' : List Word), t.code = s.code → Unchanged (noteLoopW sp) s t →
        Kept s t → NoteCtx sp0 v G K R Q t → V'.length = V.length →
        NoteHead sp sp0 out p v J G K R Q L j cap (8 * (m + k)) V' t → SafeN Gd n P t) → SafeN Gd n P s := by
  induction k with
  | zero =>
    intro m s p V _ _ _ H C hk
    exact hk s V rfl (Unchanged.refl _ s) (Kept.refl s) C rfl H
  | succ k ih =>
    intro m s p V h8 h63 hV H C hk
    refine note_word8_step E hcap (by omega) (by omega) (by omega) H C ?_
    intro t w' hc1 hu1 hk1 C1 H1
    refine ih (m + 1) t p (V.set m w') (by omega) (by omega) (by rw [List.length_set]; omega) H1 C1 ?_
    intro t' V' hc2 hu2 hk2 C2 hl H2
    rw [show m + 1 + k = m + (k + 1) by omega] at H2
    rw [List.length_set] at hl
    exact hk t' V' (hc2.trans hc1) (hu1.trans hu2) (hk1.trans hk2) C2 hl H2

/-- A phase: from byte `8m + 1` (the byte after a growth, or the first) to byte `8(m + 1 + k)`. -/
theorem note_phase {L : List (Word × Nat)} {Gd : MachineState → Prop} {n : Nat} {P : Prop} {sp sp0 out a1 v : Word} {J G K R Q : List Word} {j : Word}
    (E : NoteEnv sp sp0 out a1 G K R Q) {cap : Nat} (hcap : cap ≤ 2048) (m k : Nat) (s : MachineState)
    (p : Word) (V : List Word) (h8 : 8 * (m + 1 + k) ≤ cap) (h63 : m + 1 + k ≤ 136)
    (hV : m + 1 + k ≤ V.length)
    (H : NoteHead sp sp0 out p v J G K R Q L j cap (8 * m + 1) V s) (C : NoteCtx sp0 v G K R Q s)
    (hk : ∀ (t : MachineState) (V' : List Word), t.code = s.code → Unchanged (noteLoopW sp) s t →
      Kept s t → NoteCtx sp0 v G K R Q t → V'.length = V.length →
      NoteHead sp sp0 out p v J G K R Q L j cap (8 * (m + 1 + k)) V' t → SafeN Gd n P t) : SafeN Gd n P s := by
  refine note_word7_step E hcap (by omega) (by omega) (by omega) H C ?_
  intro t w' hc1 hu1 hk1 C1 H1
  refine note_words8 E hcap k (m + 1) t p (V.set m w') h8 h63 (by rw [List.length_set]; omega) H1 C1 ?_
  intro t' V' hc2 hu2 hk2 C2 hl H2
  rw [List.length_set] at hl
  exact hk t' V' (hc2.trans hc1) (hu1.trans hu2) (hk1.trans hk2) C2 hl H2

/-- The growth at byte `C = cap`: `do_reserve_and_handle` doubles the `Vec`, then one `next`
and one byte store. -/
theorem note_grow_step {L : List (Word × Nat)} {Gd : MachineState → Prop} {n : Nat} {P : Prop} {s : MachineState} {sp sp0 out a1 p v : Word} {J G K R Q V : List Word}
    {j : Word} (E : NoteEnv sp sp0 out a1 G K R Q) {C : Nat}
    (hC : C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256 ∨ C = 512 ∨ C = 1024) (hVl : C / 8 ≤ V.length)
    (H : NoteHead sp sp0 out p v J G K R Q L j C C V s) (Cx : NoteCtx sp0 v G K R Q s)
    (hreserve : ∀ (u : MachineState) (W : List Word) (L' : List (Word × Nat)), W.length = C / 8 →
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
    (hk : ∀ (t : MachineState) (p' : Word) (V' : List Word), t.code = s.code →
      Unchanged (noteLoopW sp) s t → Kept s t → NoteCtx sp0 v G K R Q t → V'.length = C / 4 + 1 →
      NoteHead sp sp0 out p' v J G K R Q L j (2 * C) (C + 1) V' t → SafeN Gd n P t) :
    SafeN Gd n P s := by
  have e8 : 8 * (C / 8) = C := by omega
  have hlo := H.hlo
  have hhi := H.hhi
  have hWl : (V.take (C / 8)).length = C / 8 := by simp [List.length_take]; omega
  have hokW : RegionOk Ro.layout.roBase Ro.layout.textHi p (C / 8) := H.hok.sub' 0 (C / 8) (by omega) (self_add_zero p)
  have hpC : p.toNat + C ≤ 0x1c00000000 := by omega
  refine from_iter_note_grow s sp sp0 out v p (bw (noteBit G K v R Q C)) J G K R Q (noteState sp0 J j (C + 1))
    (V.take (C / 8)) j E.Gl E.Kl E.Rl E.Ql C hC (by simp) rfl hWl H.hpc Cx.code Cx.codeN Cx.cw H.ro H.heap H.hsp E.stk
    H.hout H.hp H.hn H.htwo rfl H.hbit H.hvec E.okV H.hblk E.okBlk (Region.take H.hbuf (C / 8))
    hokW H.hlo hpC
    Cx.Gr E.okG Cx.Kr E.okK Cx.Vr E.okVv Cx.Rr E.okR Cx.Qr E.okQ E.sp0_lo E.sp0_hi
    (dj_G E.djBM) (dj_K E.djBM) (dj_V E.djBM) (dj_R E.djBM) (dj_Q E.djBM)
    (dj_G E.djFM) (dj_K E.djFM) (dj_V E.djFM) (dj_R E.djFM) (dj_Q E.djFM)
    E.djFBlk (dj_G E.djHM) (dj_K E.djHM) (dj_V E.djHM) (dj_R E.djHM) (dj_Q E.djHM) E.djHS hreserve ?_
  intro t p' V' I' bit' hpc' hcode' hun hsp' hs0' hs1' hs2' hs3' hbit' hs4' h3 h4 h22 h23 h24 h25
    h26 h27 hV' _ hIv' hBlk' hVl' hV'r hpre hb0 hok' hlo' hhi' hro' hheap'
  have hunF : Unchanged (noteLoopW sp) s t := by
    refine Unchanged.trans_cover (Unchanged.refl _ s) hun ?_
    intro r hr
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    · exact coverF48 E.stk (self_add_zero _) (by omega) (by omega)
    · exact noteCoverV E.stk (self_add_zero sp) (by omega) (by omega)
    · exact noteCoverV E.stk (i := 3) rfl (by omega) (by omega)
    · exact ⟨(0x78040620#64, 4162), by simp, le_refl _, le_refl _⟩
    · exact ⟨(0x78048980#64, 14780690128), by simp, le_refl _, le_refl _⟩
  have hdjM : ∀ r ∈ [(sp - 0x180#64, 48), (sp, 3), (sp + 0x18#64, 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)],
      MachineChecked.RiscV.Sym.Disjoint r.1 r.2 (sp0 + 18446744073709551408#64) 17 := by
    intro r hr
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    · exact E.djFM
    · exact E.djVM
    · exact E.djBM
    · exact E.djHM.ctl_of_heap
    · exact E.djHM.arena_of_heap
  refine hk t p' V' hcode' hunF ⟨h3, h4, h22, h23, h24, h25, h26, h27⟩ (Cx.step E hcode' hun hdjM)
    hVl' ?_
  refine ⟨hpc', hsp', hs0', hs1', hs2', hs3', by rw [hs4', ← hbit'], hV', ?_, hV'r, ?_, ?_, hlo', ?_, hro', ?_⟩
  · rw [hIv']; exact hBlk'
  · have hbW : BitsUpToF (noteBit G K v R Q) (V.take (C / 8)) C := BitsUpToF.take H.hbits (by omega) hVl
    have hbV : BitsUpToF (noteBit G K v R Q) V' C := BitsUpToF.prefix hbW (k := C / 8) (by omega) hpre
    have h1 := BitsUpToF.byte0 (k := C / 8) (by rwa [e8]) (by rw [e8]; exact hb0)
    rwa [e8] at h1
  · rw [hVl']; exact hok'
  · rw [hVl']; omega
  · rw [show 2 * C / 8 = C / 4 by omega]; exact hheap'

/-- The exit from byte 1088: two more bits, the `None`, the `Vec` stored at `out`, the registers
restored. `Bv` is the buffer: 257 words, bytes `o < 1090` the message bits. -/
theorem note_tail_step {L : List (Word × Nat)} {Gd : MachineState → Prop} {nb : Nat} {P : Prop} {s : MachineState} {sp sp0 out a1 p v : Word} {J G K R Q V O : List Word}
    {j rav s0v s1v s2v s3v s4v s5v : Word} (E : NoteEnv sp sp0 out a1 G K R Q) (hOl : O.length = 3)
    (hVl : V.length = 257) (hra1 : rav &&& ~~~1#64 = rav)
    (H : NoteHead sp sp0 out p v J G K R Q L j 2048 1088 V s) (C : NoteCtx sp0 v G K R Q s)
    (hF : Region (sp + 0xa8#64) [s5v, s4v, s3v, s2v, s1v, s0v, rav] s) (hO : Region out O s)
    (hk : ∀ (t : MachineState) (Bv : List Word), t.pc = rav → t.code = s.code →
      Unchanged [(sp - 0x180#64, 48), (sp, 3), (sp + 0x18#64, 18), (p + 1088#64, 2), (out, 3)] s t →
      Kept s t → t.getReg .x2 = sp + 0xe0#64 → t.getReg .x8 = s0v → t.getReg .x9 = s1v →
      t.getReg .x18 = s2v → t.getReg .x19 = s3v → t.getReg .x20 = s4v → t.getReg .x21 = s5v →
      Region out [2048#64, p, 1090#64] t → Bv.length = 257 → BitsUpToF (noteBit G K v R Q) Bv 1090 →
      Region p Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi p 257 → 0x78048980 ≤ p.toNat →
      p.toNat + 8 * 257 ≤ 0x1c00000000 → RoImage Ro.layout t → Run.HeapAt ((p, 256) :: L) t → SafeN Gd nb P t) :
    SafeN Gd nb P s := by
  have hlo := H.hlo
  have hhi := H.hhi
  have hnw : p.toNat + 8 * V.length < 2 ^ 64 := by omega
  have djP : ∀ {b : Word} {n : Nat}, MachineChecked.RiscV.Sym.Disjoint 0x78040620#64 14780694332 b n →
      MachineChecked.RiscV.Sym.Disjoint p V.length b n := fun h => h.of_heap (by omega) hhi
  have hW : Region (p + 1088#64) [V[136]!, V[137]!] s := by
    have h := (Region.shift H.hbuf 136).take 2
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
      List.take_succ_cons, List.take_succ_cons, List.take_zero, ← getBang (by omega),
      ← getBang (by omega)] at h
    exact h
  have hdjW : ∀ {b : Word} {n : Nat}, MachineChecked.RiscV.Sym.Disjoint p V.length b n →
      MachineChecked.RiscV.Sym.Disjoint (p + 1088#64) 2 b n := fun h => h.sub_left (i := 136) rfl (by omega)
  have hdjWS := hdjW (djP E.djHS)
  refine from_iter_note_tail s sp sp0 out v p (bw (noteBit G K v R Q 1088)) V[136]! V[137]! J G K R Q
    (noteState sp0 J j 1089) O j E.Gl E.Kl E.Rl E.Ql hOl (noteState_length _ _ _ _) rfl rav s0v s1v s2v s3v s4v s5v hra1 H.hpc
    C.code C.codeN C.cw H.ro H.heap hlo (by have := H.hhi; rw [hVl] at this; omega) E.outlo
    H.hsp E.stk H.hout H.hp H.hn H.htwo rfl H.hbit H.hvec E.okV H.hblk
    E.okBlk hF E.okSv hO E.okO hW (H.hok.sub' 136 2 (by omega) rfl)
    C.Gr E.okG C.Kr E.okK C.Vr E.okVv C.Rr E.okR C.Qr E.okQ E.sp0_lo E.sp0_hi
    (dj_G E.djBM) (dj_K E.djBM) (dj_V E.djBM) (dj_R E.djBM) (dj_Q E.djBM)
    (dj_G E.djFM) (dj_K E.djFM) (dj_V E.djFM) (dj_R E.djFM) (dj_Q E.djFM) E.djFBlk
    (hdjWS.sub_right (self_add_zero _) (by omega)).symm (hdjWS.sub_right (frn_0 sp) (by omega)).symm
    (hdjW (djP (dj_G E.djHM))) (hdjW (djP (dj_K E.djHM))) (hdjW (djP (dj_V E.djHM)))
    (hdjW (djP (dj_R E.djHM))) (hdjW (djP (dj_Q E.djHM)))
    E.djS28O.symm (hdjW (djP E.djHO)).symm E.djFO
    (dj_G E.djOM) (dj_K E.djOM) (dj_V E.djOM) (dj_R E.djOM) (dj_Q E.djOM) ?_
  intro t I' w' hpc' hcode' hun hsp' hs0' hs1' hs2' hs3' hs4' hs5' h3 h4 h22 h23 h24 h25 h26 h27
    hO' _ _ _ _ hW' hb hro' hheap'
  have hpre : Region p (V.take 136) t := by
    refine (Region.take H.hbuf 136).of_unchanged' hun (n := 136) (by simp [List.length_take]; omega) ?_
    intro r hr
    have hd : ∀ {b : Word} {n : Nat}, MachineChecked.RiscV.Sym.Disjoint p V.length b n → MachineChecked.RiscV.Sym.Disjoint p 136 b n :=
      fun h => h.sub_left (self_add_zero p) (by omega)
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    · exact hd (djP E.djHS) |>.sub_right (self_add_zero _) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (frn_0 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (frn_18 sp) (by omega)
    · exact MachineChecked.RiscV.Sym.Disjoint.within (N := V.length) (by omega) (self_add_zero p) (j := 136) rfl (by omega)
        (by omega) (Or.inl (by omega))
    · exact hd (djP E.djHO)
  have hw2 : Region (p + BitVec.ofNat 64 (8 * 136)) [w'] t := hW'.take 1
  -- the words after 136: word 137 as the call left it, the rest untouched
  have hw4 : Region (p + BitVec.ofNat 64 (8 * 138)) (V.drop 138) t := by
    refine (Region.shift H.hbuf 138).of_unchanged' hun (n := V.length - 138)
      (by simp [List.length_drop]) ?_
    intro r hr
    have hd : ∀ {b : Word} {n : Nat}, MachineChecked.RiscV.Sym.Disjoint p V.length b n →
        MachineChecked.RiscV.Sym.Disjoint (p + BitVec.ofNat 64 (8 * 138)) (V.length - 138) b n :=
      fun h => h.sub_left rfl (by omega)
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    · exact hd (djP E.djHS) |>.sub_right (self_add_zero _) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (frn_0 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (frn_18 sp) (by omega)
    · exact MachineChecked.RiscV.Sym.Disjoint.within (N := V.length) (by omega) rfl (j := 136) rfl (by omega) (by omega)
        (Or.inr (by omega))
    · exact hd (djP E.djHO)
  have hw3 : Region (p + BitVec.ofNat 64 (8 * 137)) (V.drop 137) t := by
    have h := hW'.shift 1
    simp only [List.drop_succ_cons, List.drop_zero] at h
    have e : p + 1088#64 + BitVec.ofNat 64 (8 * 1) = p + BitVec.ofNat 64 (8 * 137) := word_next p 136
    rw [e] at h
    rw [List.drop_eq_getElem_cons (by omega), ← getBang (by omega)]
    refine Region.append' h hw4 ?_
    rw [List.length_singleton]; exact (word_next p 137).symm
  have hBv : Region p (V.set 136 w') t := Region.set_of_parts 136 w' (by omega) hpre hw2 hw3
  refine hk t (V.set 136 w') hpc' hcode' hun ⟨h3, h4, h22, h23, h24, h25, h26, h27⟩ hsp' hs0' hs1' hs2'
    hs3' hs4' hs5' hO' (by rw [List.length_set, hVl]) ?_ hBv (by rw [← hVl]; exact H.hok) hlo
    (by rw [← hVl]; exact hhi) hro' hheap'
  exact BitsUpToF.set w' 2 (by omega) (by omega) H.hbits hb

/-- The prologue: from the entry to the loop head at byte 1, the `Vec` of one word allocated,
the caller's block advanced once and copied to the frame. -/
theorem note_pro_step {L : List (Word × Nat)} {Gd : MachineState → Prop} {n : Nat} {P : Prop} {s : MachineState} {sp sp0 out a1 ra v : Word} {J G K R Q O : List Word}
    {j : Word} (E : NoteEnv sp sp0 out a1 G K R Q) (hOl : O.length = 3)
    (hpc : s.pc = 0x7801dfb4#64) (C : NoteCtx sp0 v G K R Q s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeZ : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hra : s.getReg .x1 = ra) (hsp : s.getReg .x2 = sp + 0xe0#64)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = a1)
    (hO : Region out O s) (hCb : Region a1 (noteState sp0 J j 0) s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (halloc : ∀ (u : MachineState) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801e028#64 → u.getReg .x2 = sp → StackOk Ro.layout 0x30 sp →
      u.getReg .x10 = 8#64 → u.getReg .x11 = 1#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B0 : List Word), t.pc = 0x7801e028#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B0.length = 1 → Region ptr B0 t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 8 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 1) :: L') t → SafeN Gd n P t) → SafeN Gd n P u)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN Gd n P u)
    (hk : ∀ (t : MachineState) (ptr w : Word), t.code = s.code →
      Unchanged [(sp - 0x180#64, 48), (sp, 28), (a1, 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Kept s t → NoteCtx sp0 v G K R Q t → NoteHead sp sp0 out ptr v J G K R Q L j 8 1 [w] t →
      Region (sp + 0xa8#64) [s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18,
        s.getReg .x9, s.getReg .x8, ra] t →
      Region out O t → (∃ I1 : List Word, I1.length = 18 ∧ Region a1 I1 t) → SafeN Gd n P t) :
    SafeN Gd n P s := by
  refine from_iter_note_pro s sp sp0 out a1 ra v J G K R Q (noteState sp0 J j 0) O j E.Gl E.Kl E.Rl E.Ql (by simp) rfl
    hOl hpc C.code C.codeN hcodeM hcodeZ C.cw hro hheap hra hsp E.stk E.okFr ha0 ha1 hO E.okO hCb E.okC E.a1lo
    C.Gr E.okG C.Kr E.okK C.Vr E.okVv C.Rr E.okR C.Qr E.okQ E.sp0_lo E.sp0_hi E.djS28O E.djS28C
    (dj_G E.djS28M) (dj_K E.djS28M) (dj_V E.djS28M) (dj_R E.djS28M) (dj_Q E.djS28M)
    (dj_G E.djBM) (dj_K E.djBM) (dj_V E.djBM) (dj_R E.djBM) (dj_Q E.djBM) E.djFBlk E.djFC
    (dj_G E.djFM) (dj_K E.djFM) (dj_V E.djFM) (dj_R E.djFM) (dj_Q E.djFM) E.djFO E.djBC E.djOC
    (dj_G E.djOM) (dj_K E.djOM) (dj_V E.djOM) (dj_R E.djOM) (dj_Q E.djOM)
    (dj_G E.djCM) (dj_K E.djCM) (dj_V E.djCM) (dj_R E.djCM) (dj_Q E.djCM)
    (dj_G E.djHM) (dj_K E.djHM) (dj_V E.djHM) (dj_R E.djHM) (dj_Q E.djHM) E.djHO E.djHC halloc hhandle_rv ?_
  intro t ptr w bit0 bit1 I1 I2 hpc' hcode' hun hsp' hs0' hs1' hs2' hs3' hb1 hs4' h3 h4 h22 h23 h24
    h25 h26 h27 hI2l hI2 hR hI1l hR1 hO' hb0 hW hw hok' hlo' hhi' hro' hheap'
  rw [list18_cells I2 hI2l] at hR
  have hdjM : ∀ r ∈ [(sp - 0x180#64, 48), (sp, 28), (a1, 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)],
      MachineChecked.RiscV.Sym.Disjoint r.1 r.2 (sp0 + 18446744073709551408#64) 17 := by
    intro r hr
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    · exact E.djFM
    · exact E.djS28M
    · exact E.djCM
    · exact E.djHM.ctl_of_heap
    · exact E.djHM.arena_of_heap
  refine hk t ptr w hcode' hun ⟨h3, h4, h22, h23, h24, h25, h26, h27⟩ (C.step E hcode' hun hdjM)
    ?_ (hR.shift 21) hO' ⟨I1, hI1l, hR1⟩
  refine ⟨hpc', hsp', hs0', hs1', hs2', hs3', by rw [hs4', ← hb1], hR.take 3, ?_, hW, ?_, ?_, hlo', ?_, hro', hheap'⟩
  · rw [show noteState sp0 J j (1 + 1) = [I2[0]!, I2[1]!, I2[2]!, I2[3]!, I2[4]!, I2[5]!, I2[6]!, I2[7]!, I2[8]!, I2[9]!, I2[10]!, I2[11]!, I2[12]!, I2[13]!, I2[14]!, I2[15]!, I2[16]!, I2[17]!] from hI2.trans (list18_cells I2 hI2l)]
    exact (hR.shift 3).take 18
  · refine BitsUpToF.byte0 (k := 0) (fun o ho => absurd ho (by omega)) ?_
    simp only [List.getElem!_cons_zero, Nat.mul_zero]
    rw [hb0]; exact hw
  · exact ⟨hok'.aligned, hok'.inMem, Or.inr (by simp only [Ro.layout_textHi]; omega)⟩
  · simp only [List.length_singleton, Nat.mul_one]; exact hhi'

end Cases.Zip2005
