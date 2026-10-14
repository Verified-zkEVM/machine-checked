import Cases.Zip2005.Sinsemilla.FromIterIvk
import Cases.Zip2005.Sinsemilla.FromIterIvkGrow
import Cases.Zip2005.Sinsemilla.FromIterIvkTail
import Cases.Zip2005.Sinsemilla.FromIterIvkPro
import Cases.Zip2005.Sinsemilla.FromIterKit
import Cases.Zip2005.Sinsemilla.LoopKit
import Cases.Zip2005.Image.Ro

/-!
# `from_iter`'s loop, glued

The loop of `Vec<bool>::from_iter` (`0x7801e110`) over `commit_ivk`'s padded bit iterator,
from its head (`0x7801e230`) back to its head: a word of bytes at a time (`from_iter_ivk_word8`,
`from_iter_ivk_word`), the growth of the `Vec` when it is full (`from_iter_ivk_grow`), and the
induction over the words of a phase (between two growths). `IvkHead` is the loop invariant:
the `Vec` `(cap, p, n)`, the iterator block at message position `n + 1`, the next bit in `s4`,
and the bytes written so far the message bits (`BitsUpTo`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- The call's fixed facts: the 76-word frame `[sp - 0x1b0, sp + 0xb0)` (`sp` the frame the
loop runs in, the entry `sp + 0xb0`), the message words `A`, `B` at `commit_ivk`'s frame `sp0`,
the output `Vec` header `out`, the caller's iterator block `a1`. -/
structure IvkEnv (sp sp0 out a1 : Word) (A B : List Word) (T : HasherT) : Prop where
  Al : A.length = 4
  Bl : B.length = 4
  stk : StackOk Ro.layout 0x1b0 sp
  okFr : RegionOk Ro.layout.roBase Ro.layout.textHi sp 22
  okO : RegionOk Ro.layout.roBase Ro.layout.textHi out 3
  okC : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12
  okA : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrA sp0) 4
  okB : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrB sp0) 4
  sp0_lo : 0x10000 ≤ sp0.toNat
  sp0_hi : sp0.toNat ≤ 0x78000000
  djSA : AsmVerif.RiscV.Sym.Disjoint (sp - 0x1b0#64) 76 (ptrA sp0) 4
  djSB : AsmVerif.RiscV.Sym.Disjoint (sp - 0x1b0#64) 76 (ptrB sp0) 4
  djSO : AsmVerif.RiscV.Sym.Disjoint (sp - 0x1b0#64) 76 out 3
  djSC : AsmVerif.RiscV.Sym.Disjoint (sp - 0x1b0#64) 76 a1 12
  djOA : AsmVerif.RiscV.Sym.Disjoint out 3 (ptrA sp0) 4
  djOB : AsmVerif.RiscV.Sym.Disjoint out 3 (ptrB sp0) 4
  djOC : AsmVerif.RiscV.Sym.Disjoint out 3 a1 12
  djCA : AsmVerif.RiscV.Sym.Disjoint a1 12 (ptrA sp0) 4
  djCB : AsmVerif.RiscV.Sym.Disjoint a1 12 (ptrB sp0) 4
  djAB : AsmVerif.RiscV.Sym.Disjoint (ptrA sp0) 4 (ptrB sp0) 4
  djHA : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 (ptrA sp0) 4
  djHB : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 (ptrB sp0) 4
  djHO : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 out 3
  djHC : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 a1 12
  arena : Arena6 T
  ok : Ok6 T

namespace IvkEnv

variable {sp sp0 out a1 : Word} {A B : List Word} {T : HasherT}

theorem stk100 (E : IvkEnv sp sp0 out a1 A B T) : StackOk Ro.layout 0x100 sp := ⟨E.stk.aligned, by have := E.stk.lo; omega, E.stk.hi⟩
theorem stk10 (E : IvkEnv sp sp0 out a1 A B T) : StackOk Ro.layout 0x10 sp := ⟨E.stk.aligned, by have := E.stk.lo; omega, E.stk.hi⟩
theorem okV (E : IvkEnv sp sp0 out a1 A B T) : RegionOk Ro.layout.roBase Ro.layout.textHi sp 3 := E.okFr.sub' 0 3 (by omega) (self_add_zero sp)
theorem okBlk (E : IvkEnv sp sp0 out a1 A B T) : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x18#64) 12 := E.okFr.sub' 3 12 (by omega) rfl
theorem okSv (E : IvkEnv sp sp0 out a1 A B T) : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x78#64) 7 := E.okFr.sub' 15 7 (by omega) rfl
theorem djHS (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 (sp - 0x1b0#64) 76 :=
  AsmVerif.RiscV.Sym.Disjoint.heap_frame76 E.stk
theorem djFA (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp - 0x10#64) 2 (ptrA sp0) 4 := E.djSA.sub_left (fr_m10 sp) (by omega)
theorem djFB (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp - 0x10#64) 2 (ptrB sp0) 4 := E.djSB.sub_left (fr_m10 sp) (by omega)
theorem djFO (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp - 0x10#64) 2 out 3 := E.djSO.sub_left (fr_m10 sp) (by omega)
theorem djFC (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp - 0x10#64) 2 a1 12 := E.djSC.sub_left (fr_m10 sp) (by omega)
theorem djF32A (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp - 0x100#64) 32 (ptrA sp0) 4 := E.djSA.sub_left (fr_m100 sp) (by omega)
theorem djF32B (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp - 0x100#64) 32 (ptrB sp0) 4 := E.djSB.sub_left (fr_m100 sp) (by omega)
theorem djF32O (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp - 0x100#64) 32 out 3 := E.djSO.sub_left (fr_m100 sp) (by omega)
theorem djF32C (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp - 0x100#64) 32 a1 12 := E.djSC.sub_left (fr_m100 sp) (by omega)
theorem djVA (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint sp 3 (ptrA sp0) 4 := E.djSA.sub_left (fr_0 sp) (by omega)
theorem djVB (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint sp 3 (ptrB sp0) 4 := E.djSB.sub_left (fr_0 sp) (by omega)
theorem djVO (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint sp 3 out 3 := E.djSO.sub_left (fr_0 sp) (by omega)
theorem djVC (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint sp 3 a1 12 := E.djSC.sub_left (fr_0 sp) (by omega)
theorem djS22A (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint sp 22 (ptrA sp0) 4 := E.djSA.sub_left (fr_0 sp) (by omega)
theorem djS22B (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint sp 22 (ptrB sp0) 4 := E.djSB.sub_left (fr_0 sp) (by omega)
theorem djS22O (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint sp 22 out 3 := E.djSO.sub_left (fr_0 sp) (by omega)
theorem djS22C (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint sp 22 a1 12 := E.djSC.sub_left (fr_0 sp) (by omega)
theorem djBA (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp + 0x18#64) 12 (ptrA sp0) 4 := E.djSA.sub_left (fr_18 sp) (by omega)
theorem djBB (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp + 0x18#64) 12 (ptrB sp0) 4 := E.djSB.sub_left (fr_18 sp) (by omega)
theorem djBO (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp + 0x18#64) 12 out 3 := E.djSO.sub_left (fr_18 sp) (by omega)
theorem djBC (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp + 0x18#64) 12 a1 12 := E.djSC.sub_left (fr_18 sp) (by omega)
theorem djF6A (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp - 0x30#64) 6 (ptrA sp0) 4 := E.djSA.sub_left (fr_m30 sp) (by omega)
theorem djF6B (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp - 0x30#64) 6 (ptrB sp0) 4 := E.djSB.sub_left (fr_m30 sp) (by omega)
theorem djF6O (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp - 0x30#64) 6 out 3 := E.djSO.sub_left (fr_m30 sp) (by omega)
theorem djF6C (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp - 0x30#64) 6 a1 12 := E.djSC.sub_left (fr_m30 sp) (by omega)
theorem djFBlk (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp - 0x10#64) 2 (sp + 0x18#64) 12 :=
  AsmVerif.RiscV.Sym.Disjoint.within (frame_nowrap E.stk) (fr_m10 sp) (fr_18 sp) (by omega) (by omega) (by omega)
theorem djSvF (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp + 0x78#64) 7 (sp - 0x10#64) 2 :=
  AsmVerif.RiscV.Sym.Disjoint.within (frame_nowrap E.stk) (fr_78 sp) (fr_m10 sp) (by omega) (by omega) (by omega)
theorem djSvF32 (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp + 0x78#64) 7 (sp - 0x100#64) 32 :=
  AsmVerif.RiscV.Sym.Disjoint.within (frame_nowrap E.stk) (fr_78 sp) (fr_m100 sp) (by omega) (by omega) (by omega)
theorem djSvV (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp + 0x78#64) 7 sp 3 :=
  AsmVerif.RiscV.Sym.Disjoint.within (frame_nowrap E.stk) (fr_78 sp) (fr_0 sp) (by omega) (by omega) (by omega)
theorem djSvBlk (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp + 0x78#64) 7 (sp + 0x18#64) 12 :=
  AsmVerif.RiscV.Sym.Disjoint.within (frame_nowrap E.stk) (fr_78 sp) (fr_18 sp) (by omega) (by omega) (by omega)
theorem djSvH (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp + 0x78#64) 7 0x78040620#64 14780694332 :=
  (E.djHS.sub_right (fr_78 sp) (by omega)).symm
theorem djSvO (E : IvkEnv sp sp0 out a1 A B T) : AsmVerif.RiscV.Sym.Disjoint (sp + 0x78#64) 7 out 3 := E.djSO.sub_left (fr_78 sp) (by omega)

end IvkEnv

/-- The state at the loop head, byte `n` with capacity `cap`, the buffer `V` at `p`. -/
structure IvkHead (sp sp0 out p : Word) (J A B : List Word) (T : HasherT) (j : Word) (cap n : Nat) (V : List Word)
    (t : MachineState) : Prop where
  hpc : t.pc = 0x7801e230#64
  hsp : t.getReg .x2 = sp
  hout : t.getReg .x8 = out
  hp : t.getReg .x9 = p
  hn : t.getReg .x18 = BitVec.ofNat 64 n
  htwo : t.getReg .x19 = 2#64
  hbit : t.getReg .x20 = bw (ivkBit A B n)
  hvec : Region sp [BitVec.ofNat 64 cap, p, BitVec.ofNat 64 n] t
  hblk : Region (sp + 0x18#64) (ivkState sp0 J j (n + 1)) t
  hbuf : Region p V t
  hbits : BitsUpTo A B V n
  hok : RegionOk Ro.layout.roBase Ro.layout.textHi p V.length
  hlo : 0x78048980 ≤ p.toNat
  hhi : p.toNat + 8 * V.length ≤ 0x1c00000000
  away : Away6 p V.length T

/-- What the loop needs of a state besides the head: the code, the message words, the
`unwrap` failure arm. -/
structure IvkCtx (G : MachineState → Prop) (n : Nat) (P : Prop) (sp0 : Word) (A B : List Word) (T : HasherT) (t : MachineState) : Prop where
  code : CodeAt F_7801e110.base F_7801e110.prog t
  codeN : CodeAt F_78021e7c.base F_78021e7c.prog t
  cw : CodeWithin Ro.layout.textLo Ro.layout.textHi t
  Ar : Region (ptrA sp0) A t
  Br : Region (ptrB sp0) B t
  K : Kept6 T t
  unwrap : ∀ u : MachineState, u.pc = 0x7803f364#64 → u.code = t.code → SafeN G n P u

/-- The context after writes off the message words and the six, the six given. -/
theorem IvkCtx.step' {G : MachineState → Prop} {n : Nat} {P : Prop} {sp0 : Word} {A B : List Word} {T : HasherT} {s t : MachineState}
    (C : IvkCtx G n P sp0 A B T s) (hc : t.code = s.code) {W : List (Word × Nat)} (hu : Unchanged W s t)
    (hA : ∀ r ∈ W, AsmVerif.RiscV.Sym.Disjoint (ptrA sp0) A.length r.1 r.2)
    (hB : ∀ r ∈ W, AsmVerif.RiscV.Sym.Disjoint (ptrB sp0) B.length r.1 r.2) (hK : Kept6 T t) : IvkCtx G n P sp0 A B T t :=
  ⟨codeAt_of_code_eq hc C.code, codeAt_of_code_eq hc C.codeN, codeWithin_of_code_eq hc C.cw,
   C.Ar.of_unchanged hu hA, C.Br.of_unchanged hu hB, hK,
   fun u h1 h2 => C.unwrap u h1 (h2.trans hc)⟩

theorem IvkCtx.step {G : MachineState → Prop} {n : Nat} {P : Prop} {sp0 : Word} {A B : List Word} {T : HasherT} {s t : MachineState}
    (C : IvkCtx G n P sp0 A B T s) (hc : t.code = s.code) {W : List (Word × Nat)} (hu : Unchanged W s t)
    (hA : ∀ r ∈ W, AsmVerif.RiscV.Sym.Disjoint (ptrA sp0) A.length r.1 r.2)
    (hB : ∀ r ∈ W, AsmVerif.RiscV.Sym.Disjoint (ptrB sp0) B.length r.1 r.2)
    (hK : ∀ r ∈ W, Away6 r.1 r.2 T) : IvkCtx G n P sp0 A B T t :=
  C.step' hc hu hA hB (C.K.of_unchanged hu hK)

/-- The loop's write set: its callees' frames, the `Vec` header and the block copy, the heap.
The saved registers at `sp + 0x78` and the output header lie outside it. -/
abbrev loopW (sp : Word) : List (Word × Nat) :=
  [(sp - 0x100#64, 32), (sp, 15), (0x78040620#64, 4162), (0x78048980#64, 14780690128)]

theorem fl_m10 (sp : Word) : sp - 0x10#64 = sp - 0x100#64 + BitVec.ofNat 64 (8 * 30) := by
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem loop_nowrap32 {sp : Word} (h : StackOk Ro.layout 0x1b0 sp) : (sp - 0x100#64).toNat + 8 * 32 ≤ 2 ^ 64 := by
  rw [toNat_sub_lit sp 0x100 (by have := h.lo; omega)]; have := (Nat.le_trans h.hi (Nat.le_of_eq Ro.layout_stackTop)); omega

theorem loop_nowrap15 {sp : Word} (h : StackOk Ro.layout 0x1b0 sp) : sp.toNat + 8 * 15 ≤ 2 ^ 64 := by
  have := (Nat.le_trans h.hi (Nat.le_of_eq Ro.layout_stackTop)); omega

/-- The callees' frames cover an offset block. -/
theorem coverF32 {sp : Word} (hstk : StackOk Ro.layout 0x1b0 sp) {b : Word} {i n : Nat}
    (hb : b = sp - 0x100#64 + BitVec.ofNat 64 (8 * i)) (hin : i + n ≤ 32) (hn : 0 < n) :
    ∃ r' ∈ loopW sp, Covers r'.1 r'.2 b n :=
  ⟨(sp - 0x100#64, 32), by simp, covers_of_sub (loop_nowrap32 hstk) hb hin hn⟩

theorem coverV {sp : Word} (hstk : StackOk Ro.layout 0x1b0 sp) {b : Word} {i n : Nat}
    (hb : b = sp + BitVec.ofNat 64 (8 * i)) (hin : i + n ≤ 15) (hn : 0 < n) :
    ∃ r' ∈ loopW sp, Covers r'.1 r'.2 b n :=
  ⟨(sp, 15), by simp, covers_of_sub (loop_nowrap15 hstk) hb hin hn⟩

theorem coverH {sp : Word} {b : Word} {n : Nat} (hlo : 0x78048980 ≤ b.toNat)
    (hhi : b.toNat + 8 * n ≤ 0x1c00000000) :
    ∃ r' ∈ loopW sp, Covers r'.1 r'.2 b n :=
  ⟨(0x78048980#64, 14780690128), by simp, covers_arena hlo hhi⟩

/-- One word of the loop from byte `8m`: eight `next` calls, eight byte stores. -/
theorem ivk_word8_step {G : MachineState → Prop} {nb : Nat} {P : Prop} {s : MachineState} {sp sp0 out a1 p : Word} {J A B V : List Word} {T : HasherT}
    {j : Word} (E : IvkEnv sp sp0 out a1 A B T) {cap m : Nat} (hcap : cap ≤ 512)
    (hm8 : 8 * (m + 1) ≤ cap) (hm : m ≤ 62) (hmV : m < V.length)
    (H : IvkHead sp sp0 out p J A B T j cap (8 * m) V s) (C : IvkCtx G nb P sp0 A B T s)
    (hk : ∀ (t : MachineState) (w' : Word), t.code = s.code → Unchanged (loopW sp) s t →
      Kept s t → IvkCtx G nb P sp0 A B T t →
      IvkHead sp sp0 out p J A B T j cap (8 * (m + 1)) (V.set m w') t → SafeN G nb P t) :
    SafeN G nb P s := by
  have hlo := H.hlo
  have hhi := H.hhi
  have hnw : p.toNat + 8 * V.length < 2 ^ 64 := by omega
  have hq : ∀ r : Nat, p + (BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 r) =
      p + BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 r := fun r => (BitVec.add_assoc _ _ _).symm
  have hc : ∀ r : Nat, r < 8 →
      (BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 r == BitVec.ofNat 64 cap) = false := fun r hr => by
    rw [BitVec.ofNat_add_ofNat]; exact ofNat_beq_false (by omega) (by omega) (by omega)
  have hokq : RegionOk Ro.layout.roBase Ro.layout.textHi (p + BitVec.ofNat 64 (8 * m)) 1 := H.hok.sub' m 1 (by omega) rfl
  have djP : ∀ {b : Word} {n : Nat}, AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 b n →
      AsmVerif.RiscV.Sym.Disjoint p V.length b n := fun h => h.of_heap (by omega) hhi
  have hdjq : ∀ {b : Word} {n : Nat}, AsmVerif.RiscV.Sym.Disjoint p V.length b n →
      AsmVerif.RiscV.Sym.Disjoint (p + BitVec.ofNat 64 (8 * m)) 1 b n := fun h => h.sub_left rfl (by omega)
  have hdjqS := hdjq (djP E.djHS)
  refine from_iter_ivk_word8 s sp sp0 out p (BitVec.ofNat 64 (8 * m)) (p + BitVec.ofNat 64 (8 * m))
    (BitVec.ofNat 64 cap) V[m]! (bw (ivkBit A B (8 * m))) J A B (ivkState sp0 J j (8 * m + 1)) j E.Al E.Bl
    m hm (by simp) rfl rfl (hq 1) (hq 2) (hq 3) (hq 4) (hq 5) (hq 6) (hq 7)
    (ofNat_beq_false (by omega) (by omega) (by omega))
    (hc 1 (by omega)) (hc 2 (by omega)) (hc 3 (by omega)) (hc 4 (by omega)) (hc 5 (by omega))
    (hc 6 (by omega)) (hc 7 (by omega))
    H.hpc C.code C.codeN C.cw H.hsp E.stk10 H.hout H.hp H.hn H.htwo rfl H.hbit H.hvec E.okV H.hblk
    E.okBlk (Region.window H.hbuf m hmV) hokq C.Ar E.okA C.Br E.okB E.sp0_lo E.sp0_hi E.djBA E.djBB E.djFA
    E.djFB E.djAB (hdjqS.sub_right (fr_m10 sp) (by omega)).symm
    (hdjqS.sub_right (fr_0 sp) (by omega)).symm (hdjqS.sub_right (fr_18 sp) (by omega)).symm
    E.djFBlk (hdjq (djP E.djHA)) (hdjq (djP E.djHB)) C.unwrap ?_
  intro t I' w' bit' hpc' hcode' hun hsp' hs0' hs1' hs2' hs3' h3 h4 h22 h23 h24 h25 h26 h27 hbit' hs4'
    hV' _ hIv' hBlk' hW' hb
  rw [show 8 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 8 * (m + 1) by omega] at hbit'
  rw [show 8 * m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 8 * (m + 1) + 1 by omega] at hIv'
  rw [BitVec.ofNat_add_ofNat, show 8 * m + 8 = 8 * (m + 1) by omega] at hV' hs2'
  -- the frame condition, covered
  have hunF : Unchanged (loopW sp) s t := by
    refine Unchanged.trans_cover (Unchanged.refl _ s) hun ?_
    intro r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact coverF32 E.stk (fl_m10 sp) (by omega) (by omega)
    · exact coverV E.stk (self_add_zero sp) (by omega) (by omega)
    · exact coverV E.stk (i := 3) rfl (by omega) (by omega)
    · exact coverH (by rw [toNat_add_lit p (8 * m) (by omega)]; omega)
        (by rw [toNat_add_lit p (8 * m) (by omega)]; omega)
  have hdjA : ∀ r ∈ [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (p + BitVec.ofNat 64 (8 * m), 1)],
      AsmVerif.RiscV.Sym.Disjoint (ptrA sp0) A.length r.1 r.2 := by
    intro r hr
    rw [E.Al]
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact E.djFA.symm
    · exact E.djVA.symm
    · exact E.djBA.symm
    · exact (hdjq (djP E.djHA)).symm
  have hdjB : ∀ r ∈ [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (p + BitVec.ofNat 64 (8 * m), 1)],
      AsmVerif.RiscV.Sym.Disjoint (ptrB sp0) B.length r.1 r.2 := by
    intro r hr
    rw [E.Bl]
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact E.djFB.symm
    · exact E.djVB.symm
    · exact E.djBB.symm
    · exact (hdjq (djP E.djHB)).symm
  -- the buffer: the words before `m`, word `m`, the words after
  have hpre : Region p (V.take m) t := by
    refine (Region.take H.hbuf m).of_unchanged' hun (n := m) (by simp [List.length_take]; omega) ?_
    intro r hr
    have hd : ∀ {b : Word} {n : Nat}, AsmVerif.RiscV.Sym.Disjoint p V.length b n → AsmVerif.RiscV.Sym.Disjoint p m b n :=
      fun h => h.sub_left (self_add_zero p) (by omega)
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact hd (djP E.djHS) |>.sub_right (fr_m10 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (fr_0 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (fr_18 sp) (by omega)
    · exact AsmVerif.RiscV.Sym.Disjoint.within (N := V.length) (by omega) (self_add_zero p) rfl (by omega) (by omega) (Or.inl (by omega))
  have hpost : Region (p + BitVec.ofNat 64 (8 * (m + 1))) (V.drop (m + 1)) t := by
    refine (Region.shift H.hbuf (m + 1)).of_unchanged' hun (n := V.length - (m + 1))
      (by simp [List.length_drop]) ?_
    intro r hr
    have hd : ∀ {b : Word} {n : Nat}, AsmVerif.RiscV.Sym.Disjoint p V.length b n →
        AsmVerif.RiscV.Sym.Disjoint (p + BitVec.ofNat 64 (8 * (m + 1))) (V.length - (m + 1)) b n :=
      fun h => h.sub_left rfl (by omega)
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact hd (djP E.djHS) |>.sub_right (fr_m10 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (fr_0 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (fr_18 sp) (by omega)
    · exact AsmVerif.RiscV.Sym.Disjoint.within (N := V.length) (by omega) rfl rfl (by omega) (by omega) (Or.inr (by omega))
  have hdjK : ∀ r ∈ [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (p + BitVec.ofNat 64 (8 * m), 1)],
      Away6 r.1 r.2 T := by
    intro r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact Away6.of_heap E.arena (E.djHS.sub_right (fr_m10 sp) (by omega))
    · exact Away6.of_heap E.arena (E.djHS.sub_right (fr_0 sp) (by omega))
    · exact Away6.of_heap E.arena (E.djHS.sub_right (fr_18 sp) (by omega))
    · exact H.away.sub rfl (by omega)
  refine hk t w' hcode' hunF ⟨h3, h4, h22, h23, h24, h25, h26, h27⟩ (C.step hcode' hun hdjA hdjB hdjK) ?_
  refine ⟨hpc', hsp', hs0', hs1', hs2', hs3', by rw [hs4', ← hbit'], hV', ?_, ?_, ?_, ?_, H.hlo, ?_, ?_⟩
  · rw [hIv']; exact hBlk'
  · exact Region.set_of_parts m w' hmV hpre hW' hpost
  · exact BitsUpTo.set w' 8 (le_refl _) hmV H.hbits hb
  · rw [List.length_set]; exact H.hok
  · rw [List.length_set]; exact H.hhi
  · exact H.away.len (by rw [List.length_set])

/-- The rest of a word from byte `8m + 1`: seven `next` calls, seven byte stores, byte 0 kept. -/
theorem ivk_word7_step {G : MachineState → Prop} {nb : Nat} {P : Prop} {s : MachineState} {sp sp0 out a1 p : Word} {J A B V : List Word} {T : HasherT}
    {j : Word} (E : IvkEnv sp sp0 out a1 A B T) {cap m : Nat} (hcap : cap ≤ 512)
    (hm8 : 8 * (m + 1) ≤ cap) (hm : m ≤ 62) (hmV : m < V.length)
    (H : IvkHead sp sp0 out p J A B T j cap (8 * m + 1) V s) (C : IvkCtx G nb P sp0 A B T s)
    (hk : ∀ (t : MachineState) (w' : Word), t.code = s.code → Unchanged (loopW sp) s t →
      Kept s t → IvkCtx G nb P sp0 A B T t →
      IvkHead sp sp0 out p J A B T j cap (8 * (m + 1)) (V.set m w') t → SafeN G nb P t) :
    SafeN G nb P s := by
  have hlo := H.hlo
  have hhi := H.hhi
  have hnw : p.toNat + 8 * V.length < 2 ^ 64 := by omega
  have hq : ∀ r : Nat, p + (BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 r) =
      p + BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 r := fun r => (BitVec.add_assoc _ _ _).symm
  have hc : ∀ r : Nat, r < 8 →
      (BitVec.ofNat 64 (8 * m) + BitVec.ofNat 64 r == BitVec.ofNat 64 cap) = false := fun r hr => by
    rw [BitVec.ofNat_add_ofNat]; exact ofNat_beq_false (by omega) (by omega) (by omega)
  have hokq : RegionOk Ro.layout.roBase Ro.layout.textHi (p + BitVec.ofNat 64 (8 * m)) 1 := H.hok.sub' m 1 (by omega) rfl
  have djP : ∀ {b : Word} {n : Nat}, AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 b n →
      AsmVerif.RiscV.Sym.Disjoint p V.length b n := fun h => h.of_heap (by omega) hhi
  have hdjq : ∀ {b : Word} {n : Nat}, AsmVerif.RiscV.Sym.Disjoint p V.length b n →
      AsmVerif.RiscV.Sym.Disjoint (p + BitVec.ofNat 64 (8 * m)) 1 b n := fun h => h.sub_left rfl (by omega)
  have hdjqS := hdjq (djP E.djHS)
  have hn1 : s.getReg .x18 = BitVec.ofNat 64 (8 * m) + 1#64 := by rw [H.hn, BitVec.ofNat_add]
  have hvec1 : Region sp [BitVec.ofNat 64 cap, p, BitVec.ofNat 64 (8 * m) + 1#64] s := by
    rw [← BitVec.ofNat_add]; exact H.hvec
  refine from_iter_ivk_word s sp sp0 out p (BitVec.ofNat 64 (8 * m)) (p + BitVec.ofNat 64 (8 * m))
    (BitVec.ofNat 64 cap) V[m]! (bw (ivkBit A B (8 * m + 1))) J A B (ivkState sp0 J j (8 * m + 2)) j
    E.Al E.Bl m hm (by simp) rfl (hq 1) (hq 2) (hq 3) (hq 4) (hq 5) (hq 6) (hq 7)
    (hc 1 (by omega)) (hc 2 (by omega)) (hc 3 (by omega)) (hc 4 (by omega)) (hc 5 (by omega))
    (hc 6 (by omega)) (hc 7 (by omega))
    H.hpc C.code C.codeN C.cw H.hsp E.stk10 H.hout H.hp hn1 H.htwo rfl H.hbit hvec1 E.okV
    (by have := H.hblk; rwa [show 8 * m + 1 + 1 = 8 * m + 2 by omega] at this)
    E.okBlk (Region.window H.hbuf m hmV) hokq C.Ar E.okA C.Br E.okB E.sp0_lo E.sp0_hi E.djBA E.djBB E.djFA
    E.djFB E.djAB (hdjqS.sub_right (fr_m10 sp) (by omega)).symm
    (hdjqS.sub_right (fr_0 sp) (by omega)).symm (hdjqS.sub_right (fr_18 sp) (by omega)).symm
    E.djFBlk (hdjq (djP E.djHA)) (hdjq (djP E.djHB)) C.unwrap ?_
  intro t I' w' bit' hpc' hcode' hun hsp' hs0' hs1' hs2' hs3' h3 h4 h22 h23 h24 h25 h26 h27 hbit' hs4'
    hV' _ hIv' hBlk' hW' hb0 hb
  rw [show 8 * m + 2 + 1 + 1 + 1 + 1 + 1 + 1 = 8 * (m + 1) by omega] at hbit'
  rw [show 8 * m + 2 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = 8 * (m + 1) + 1 by omega] at hIv'
  rw [BitVec.ofNat_add_ofNat, show 8 * m + 8 = 8 * (m + 1) by omega] at hV' hs2'
  have hunF : Unchanged (loopW sp) s t := by
    refine Unchanged.trans_cover (Unchanged.refl _ s) hun ?_
    intro r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact coverF32 E.stk (fl_m10 sp) (by omega) (by omega)
    · exact coverV E.stk (self_add_zero sp) (by omega) (by omega)
    · exact coverV E.stk (i := 3) rfl (by omega) (by omega)
    · exact coverH (by rw [toNat_add_lit p (8 * m) (by omega)]; omega)
        (by rw [toNat_add_lit p (8 * m) (by omega)]; omega)
  have hdjA : ∀ r ∈ [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (p + BitVec.ofNat 64 (8 * m), 1)],
      AsmVerif.RiscV.Sym.Disjoint (ptrA sp0) A.length r.1 r.2 := by
    intro r hr
    rw [E.Al]
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact E.djFA.symm
    · exact E.djVA.symm
    · exact E.djBA.symm
    · exact (hdjq (djP E.djHA)).symm
  have hdjB : ∀ r ∈ [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (p + BitVec.ofNat 64 (8 * m), 1)],
      AsmVerif.RiscV.Sym.Disjoint (ptrB sp0) B.length r.1 r.2 := by
    intro r hr
    rw [E.Bl]
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact E.djFB.symm
    · exact E.djVB.symm
    · exact E.djBB.symm
    · exact (hdjq (djP E.djHB)).symm
  have hpre : Region p (V.take m) t := by
    refine (Region.take H.hbuf m).of_unchanged' hun (n := m) (by simp [List.length_take]; omega) ?_
    intro r hr
    have hd : ∀ {b : Word} {n : Nat}, AsmVerif.RiscV.Sym.Disjoint p V.length b n → AsmVerif.RiscV.Sym.Disjoint p m b n :=
      fun h => h.sub_left (self_add_zero p) (by omega)
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact hd (djP E.djHS) |>.sub_right (fr_m10 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (fr_0 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (fr_18 sp) (by omega)
    · exact AsmVerif.RiscV.Sym.Disjoint.within (N := V.length) (by omega) (self_add_zero p) rfl (by omega) (by omega) (Or.inl (by omega))
  have hpost : Region (p + BitVec.ofNat 64 (8 * (m + 1))) (V.drop (m + 1)) t := by
    refine (Region.shift H.hbuf (m + 1)).of_unchanged' hun (n := V.length - (m + 1))
      (by simp [List.length_drop]) ?_
    intro r hr
    have hd : ∀ {b : Word} {n : Nat}, AsmVerif.RiscV.Sym.Disjoint p V.length b n →
        AsmVerif.RiscV.Sym.Disjoint (p + BitVec.ofNat 64 (8 * (m + 1))) (V.length - (m + 1)) b n :=
      fun h => h.sub_left rfl (by omega)
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact hd (djP E.djHS) |>.sub_right (fr_m10 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (fr_0 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (fr_18 sp) (by omega)
    · exact AsmVerif.RiscV.Sym.Disjoint.within (N := V.length) (by omega) rfl rfl (by omega) (by omega) (Or.inr (by omega))
  have hdjK : ∀ r ∈ [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (p + BitVec.ofNat 64 (8 * m), 1)],
      Away6 r.1 r.2 T := by
    intro r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact Away6.of_heap E.arena (E.djHS.sub_right (fr_m10 sp) (by omega))
    · exact Away6.of_heap E.arena (E.djHS.sub_right (fr_0 sp) (by omega))
    · exact Away6.of_heap E.arena (E.djHS.sub_right (fr_18 sp) (by omega))
    · exact H.away.sub rfl (by omega)
  refine hk t w' hcode' hunF ⟨h3, h4, h22, h23, h24, h25, h26, h27⟩ (C.step hcode' hun hdjA hdjB hdjK) ?_
  refine ⟨hpc', hsp', hs0', hs1', hs2', hs3', by rw [hs4', ← hbit'], hV', ?_, ?_, ?_, ?_, H.hlo, ?_, ?_⟩
  · rw [hIv']; exact hBlk'
  · exact Region.set_of_parts m w' hmV hpre hW' hpost
  · exact BitsUpTo.set7 w' hmV H.hbits hb0 hb
  · rw [List.length_set]; exact H.hok
  · rw [List.length_set]; exact H.hhi
  · exact H.away.len (by rw [List.length_set])

/-- `k` whole words from byte `8m`. -/
theorem ivk_words8 {G : MachineState → Prop} {n : Nat} {P : Prop} {sp sp0 out a1 : Word} {J A B : List Word} {T : HasherT} {j : Word}
    (E : IvkEnv sp sp0 out a1 A B T) {cap : Nat} (hcap : cap ≤ 512) (k : Nat) :
    ∀ (m : Nat) (s : MachineState) (p : Word) (V : List Word), 8 * (m + k) ≤ cap → m + k ≤ 63 →
      m + k ≤ V.length →
      IvkHead sp sp0 out p J A B T j cap (8 * m) V s → IvkCtx G n P sp0 A B T s →
      (∀ (t : MachineState) (V' : List Word), t.code = s.code → Unchanged (loopW sp) s t →
        Kept s t → IvkCtx G n P sp0 A B T t → V'.length = V.length →
        IvkHead sp sp0 out p J A B T j cap (8 * (m + k)) V' t → SafeN G n P t) → SafeN G n P s := by
  induction k with
  | zero =>
    intro m s p V _ _ _ H C hk
    exact hk s V rfl (Unchanged.refl _ s) (Kept.refl s) C rfl H
  | succ k ih =>
    intro m s p V h8 h63 hV H C hk
    refine ivk_word8_step E hcap (by omega) (by omega) (by omega) H C ?_
    intro t w' hc1 hu1 hk1 C1 H1
    refine ih (m + 1) t p (V.set m w') (by omega) (by omega) (by rw [List.length_set]; omega) H1 C1 ?_
    intro t' V' hc2 hu2 hk2 C2 hl H2
    rw [show m + 1 + k = m + (k + 1) by omega] at H2
    rw [List.length_set] at hl
    exact hk t' V' (hc2.trans hc1) (hu1.trans hu2) (hk1.trans hk2) C2 hl H2

/-- A phase: from byte `8m + 1` (the byte after a growth, or the first) to byte `8(m + 1 + k)`. -/
theorem ivk_phase {G : MachineState → Prop} {n : Nat} {P : Prop} {sp sp0 out a1 : Word} {J A B : List Word} {T : HasherT} {j : Word}
    (E : IvkEnv sp sp0 out a1 A B T) {cap : Nat} (hcap : cap ≤ 512) (m k : Nat) (s : MachineState)
    (p : Word) (V : List Word) (h8 : 8 * (m + 1 + k) ≤ cap) (h63 : m + 1 + k ≤ 63)
    (hV : m + 1 + k ≤ V.length)
    (H : IvkHead sp sp0 out p J A B T j cap (8 * m + 1) V s) (C : IvkCtx G n P sp0 A B T s)
    (hk : ∀ (t : MachineState) (V' : List Word), t.code = s.code → Unchanged (loopW sp) s t →
      Kept s t → IvkCtx G n P sp0 A B T t → V'.length = V.length →
      IvkHead sp sp0 out p J A B T j cap (8 * (m + 1 + k)) V' t → SafeN G n P t) : SafeN G n P s := by
  refine ivk_word7_step E hcap (by omega) (by omega) (by omega) H C ?_
  intro t w' hc1 hu1 hk1 C1 H1
  refine ivk_words8 E hcap k (m + 1) t p (V.set m w') h8 h63 (by rw [List.length_set]; omega) H1 C1 ?_
  intro t' V' hc2 hu2 hk2 C2 hl H2
  rw [List.length_set] at hl
  exact hk t' V' (hc2.trans hc1) (hu1.trans hu2) (hk1.trans hk2) C2 hl H2

/-- The growth at byte `C = cap`: `do_reserve_and_handle` doubles the `Vec`, then one `next`
and one byte store. -/
theorem ivk_grow_step {G : MachineState → Prop} {n : Nat} {P : Prop} {s : MachineState} {sp sp0 out a1 p : Word} {J A B V : List Word} {T : HasherT}
    {j : Word} (E : IvkEnv sp sp0 out a1 A B T) {C : Nat}
    (hC : C = 8 ∨ C = 16 ∨ C = 32 ∨ C = 64 ∨ C = 128 ∨ C = 256) (hVl : C / 8 ≤ V.length)
    (H : IvkHead sp sp0 out p J A B T j C C V s) (Cx : IvkCtx G n P sp0 A B T s)
    (hreserve : ∀ (u : MachineState) (W : List Word), W.length = C / 8 →
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
        AsmVerif.RiscV.Sym.Disjoint T.b1 10 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b2 138 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b3 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b4 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b5 1024 p' (C / 4 + 1) → AsmVerif.RiscV.Sym.Disjoint T.b6 516 p' (C / 4 + 1) → SafeN G n P t) → SafeN G n P u)
    (hk : ∀ (t : MachineState) (p' : Word) (V' : List Word), t.code = s.code →
      Unchanged (loopW sp) s t → Kept s t → IvkCtx G n P sp0 A B T t → V'.length = C / 4 + 1 →
      IvkHead sp sp0 out p' J A B T j (2 * C) (C + 1) V' t → SafeN G n P t) :
    SafeN G n P s := by
  have e8 : 8 * (C / 8) = C := by omega
  have hlo := H.hlo
  have hhi := H.hhi
  have hWl : (V.take (C / 8)).length = C / 8 := by simp [List.length_take]; omega
  have hokW : RegionOk Ro.layout.roBase Ro.layout.textHi p (C / 8) := H.hok.sub' 0 (C / 8) (by omega) (self_add_zero p)
  have hpC : p.toNat + C ≤ 0x1c00000000 := by omega
  have hHS : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 (sp - 0x100#64) 54 :=
    E.djHS.sub_right (fr_m100 sp) (by omega)
  refine from_iter_ivk_grow s sp sp0 out p (bw (ivkBit A B C)) J A B (ivkState sp0 J j (C + 1))
    (V.take (C / 8)) j E.Al E.Bl C hC (by simp) rfl hWl H.hpc Cx.code Cx.codeN Cx.cw H.hsp E.stk100
    H.hout H.hp H.hn H.htwo rfl H.hbit H.hvec E.okV H.hblk E.okBlk (Region.take H.hbuf (C / 8))
    hokW H.hlo hpC
    Cx.Ar E.okA Cx.Br E.okB E.sp0_lo E.sp0_hi E.djBA E.djBB E.djFA E.djFB E.djF32A E.djF32B E.djAB
    E.djFBlk E.djHA E.djHB hHS T Cx.K E.arena E.ok hreserve Cx.unwrap ?_
  intro t p' V' I' bit' hpc' hcode' hun hsp' hs0' hs1' hs2' hs3' hbit' hs4' h3 h4 h22 h23 h24 h25
    h26 h27 hV' _ hIv' hBlk' hVl' hV'r hpre hb0 hok' hlo' hhi' hk1 hk2 hk3 hk4 hk5 hk6 hf1 hf2 hf3 hf4 hf5 hf6
  have hunF : Unchanged (loopW sp) s t := by
    refine Unchanged.trans_cover (Unchanged.refl _ s) hun ?_
    intro r hr
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    · exact coverF32 E.stk (self_add_zero _) (by omega) (by omega)
    · exact coverV E.stk (self_add_zero sp) (by omega) (by omega)
    · exact coverV E.stk (i := 3) rfl (by omega) (by omega)
    · exact ⟨(0x78040620#64, 4162), by simp, le_refl _, le_refl _⟩
    · exact ⟨(0x78048980#64, 14780690128), by simp, le_refl _, le_refl _⟩
  have hdjA : ∀ r ∈ [(sp - 0x100#64, 32), (sp, 3), (sp + 0x18#64, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)],
      AsmVerif.RiscV.Sym.Disjoint (ptrA sp0) A.length r.1 r.2 := by
    intro r hr
    rw [E.Al]
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    · exact E.djF32A.symm
    · exact E.djVA.symm
    · exact E.djBA.symm
    · exact E.djHA.ctl_of_heap.symm
    · exact E.djHA.arena_of_heap.symm
  have hdjB : ∀ r ∈ [(sp - 0x100#64, 32), (sp, 3), (sp + 0x18#64, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)],
      AsmVerif.RiscV.Sym.Disjoint (ptrB sp0) B.length r.1 r.2 := by
    intro r hr
    rw [E.Bl]
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    · exact E.djF32B.symm
    · exact E.djVB.symm
    · exact E.djBB.symm
    · exact E.djHB.ctl_of_heap.symm
    · exact E.djHB.arena_of_heap.symm
  refine hk t p' V' hcode' hunF ⟨h3, h4, h22, h23, h24, h25, h26, h27⟩
    (Cx.step' hcode' hun hdjA hdjB ⟨hk1, hk2, hk3, hk4, hk5, hk6⟩) hVl' ?_
  refine ⟨hpc', hsp', hs0', hs1', hs2', hs3', by rw [hs4', ← hbit'], hV', ?_, hV'r, ?_, ?_, hlo', ?_, ?_⟩
  · rw [hIv']; exact hBlk'
  · have hbW : BitsUpTo A B (V.take (C / 8)) C := BitsUpTo.take H.hbits (by omega) hVl
    have hbV : BitsUpTo A B V' C := BitsUpTo.prefix hbW (k := C / 8) (by omega) hpre
    have h1 := BitsUpTo.byte0 (k := C / 8) (by rwa [e8]) (by rw [e8]; exact hb0)
    rwa [e8] at h1
  · rw [hVl']; exact hok'
  · rw [hVl']; omega
  · exact (⟨hf1, hf2, hf3, hf4, hf5, hf6⟩ : Away6 p' (C / 4 + 1) T).len hVl'.symm

/-- The exit from byte 504: six more bits, the `None`, the `Vec` stored at `out`, the registers
restored. `Bv` is the buffer: 65 words, bytes `o < 510` the message bits. -/
theorem ivk_tail_step {G : MachineState → Prop} {nb : Nat} {P : Prop} {s : MachineState} {sp sp0 out a1 p : Word} {J A B V O : List Word} {T : HasherT}
    {j rav s0v s1v s2v s3v s4v s5v : Word} (E : IvkEnv sp sp0 out a1 A B T) (hOl : O.length = 3)
    (hVl : V.length = 65) (hra1 : rav &&& ~~~1#64 = rav)
    (H : IvkHead sp sp0 out p J A B T j 512 504 V s) (C : IvkCtx G nb P sp0 A B T s)
    (hF : Region (sp + 0x78#64) [s5v, s4v, s3v, s2v, s1v, s0v, rav] s) (hO : Region out O s)
    (hk : ∀ (t : MachineState) (Bv : List Word), t.pc = rav → t.code = s.code →
      Unchanged [(sp - 0x10#64, 2), (sp, 3), (sp + 0x18#64, 12), (p + 504#64, 2), (out, 3)] s t →
      Kept s t → t.getReg .x2 = sp + 0xb0#64 → t.getReg .x8 = s0v → t.getReg .x9 = s1v →
      t.getReg .x18 = s2v → t.getReg .x19 = s3v → t.getReg .x20 = s4v → t.getReg .x21 = s5v →
      Region out [512#64, p, 510#64] t → Bv.length = 65 → BitsUpTo A B Bv 510 → Region p Bv t →
      RegionOk Ro.layout.roBase Ro.layout.textHi p 65 → 0x78048980 ≤ p.toNat → p.toNat + 8 * 65 ≤ 0x1c00000000 →
      Kept6 T t → SafeN G nb P t) : SafeN G nb P s := by
  have hlo := H.hlo
  have hhi := H.hhi
  have hnw : p.toNat + 8 * V.length < 2 ^ 64 := by omega
  have djP : ∀ {b : Word} {n : Nat}, AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 b n →
      AsmVerif.RiscV.Sym.Disjoint p V.length b n := fun h => h.of_heap (by omega) hhi
  have hdrop : V.drop 63 = [V[63]!, V[64]!] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
      List.drop_eq_nil_of_le (by omega), ← getBang (by omega), ← getBang (by omega)]
  have hW : Region (p + 504#64) [V[63]!, V[64]!] s := by
    have h := Region.shift H.hbuf 63
    rw [hdrop] at h
    exact h
  have hdjW : ∀ {b : Word} {n : Nat}, AsmVerif.RiscV.Sym.Disjoint p V.length b n →
      AsmVerif.RiscV.Sym.Disjoint (p + 504#64) 2 b n := fun h => h.sub_left (i := 63) rfl (by omega)
  have hdjWS := hdjW (djP E.djHS)
  refine from_iter_ivk_tail s sp sp0 out p (bw (ivkBit A B 504)) V[63]! V[64]! J A B
    (ivkState sp0 J j 505) O j E.Al E.Bl hOl (by simp) rfl rav s0v s1v s2v s3v s4v s5v hra1 H.hpc
    C.code C.codeN C.cw H.hsp E.stk100 H.hout H.hp H.hn H.htwo rfl H.hbit H.hvec E.okV H.hblk
    E.okBlk hF E.okSv hO E.okO hW (H.hok.sub' 63 2 (by omega) rfl) C.Ar E.okA C.Br E.okB E.sp0_lo
    E.sp0_hi E.djBA E.djBB E.djFA E.djFB E.djAB E.djFBlk
    (hdjWS.sub_right (fr_m10 sp) (by omega)).symm (hdjWS.sub_right (fr_0 sp) (by omega)).symm
    (hdjW (djP E.djHA)) (hdjW (djP E.djHB)) E.djS22O.symm (hdjW (djP E.djHO)).symm E.djFO E.djOA
    E.djOB C.unwrap ?_
  intro t I' w' hpc' hcode' hun hsp' hs0' hs1' hs2' hs3' hs4' hs5' h3 h4 h22 h23 h24 h25 h26 h27
    hO' _ _ _ _ hW' hb
  have hpre : Region p (V.take 63) t := by
    refine (Region.take H.hbuf 63).of_unchanged' hun (n := 63) (by simp [List.length_take]; omega) ?_
    intro r hr
    have hd : ∀ {b : Word} {n : Nat}, AsmVerif.RiscV.Sym.Disjoint p V.length b n → AsmVerif.RiscV.Sym.Disjoint p 63 b n :=
      fun h => h.sub_left (self_add_zero p) (by omega)
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    · exact hd (djP E.djHS) |>.sub_right (fr_m10 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (fr_0 sp) (by omega)
    · exact hd (djP E.djHS) |>.sub_right (fr_18 sp) (by omega)
    · exact AsmVerif.RiscV.Sym.Disjoint.within (N := V.length) (by omega) (self_add_zero p) (j := 63) rfl (by omega)
        (by omega) (Or.inl (by omega))
    · exact hd (djP E.djHO)
  have hw2 : Region (p + BitVec.ofNat 64 (8 * 63)) [w'] t := hW'.take 1
  have hw3 : Region (p + BitVec.ofNat 64 (8 * 64)) (V.drop 64) t := by
    have h := hW'.shift 1
    have e : p + 504#64 + BitVec.ofNat 64 (8 * 1) = p + BitVec.ofNat 64 (8 * 64) := word_next p 63
    rw [e] at h
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega), ← getBang (by omega)]
    exact h
  have hBv : Region p (V.set 63 w') t := Region.set_of_parts 63 w' (by omega) hpre hw2 hw3
  refine hk t (V.set 63 w') hpc' hcode' hun ⟨h3, h4, h22, h23, h24, h25, h26, h27⟩ hsp' hs0' hs1' hs2'
    hs3' hs4' hs5' hO' (by rw [List.length_set, hVl]) ?_ hBv (by rw [← hVl]; exact H.hok) hlo
    (by rw [← hVl]; exact hhi) ?_
  · exact BitsUpTo.set w' 6 (by omega) (by omega) H.hbits hb
  · refine C.K.of_unchanged hun ?_
    intro r hr
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    · exact Away6.of_heap E.arena (E.djHS.sub_right (fr_m10 sp) (by omega))
    · exact Away6.of_heap E.arena (E.djHS.sub_right (fr_0 sp) (by omega))
    · exact Away6.of_heap E.arena (E.djHS.sub_right (fr_18 sp) (by omega))
    · exact H.away.sub (i := 63) rfl (by omega)
    · exact Away6.of_heap E.arena E.djHO

/-- The prologue: from the entry to the loop head at byte 1, the `Vec` of one word allocated,
the caller's block advanced once and copied to the frame. -/
theorem ivk_pro_step {G : MachineState → Prop} {n : Nat} {P : Prop} {s : MachineState} {sp sp0 out a1 ra : Word} {J A B O : List Word} {T : HasherT}
    {j : Word} (E : IvkEnv sp sp0 out a1 A B T) (hOl : O.length = 3)
    (hpc : s.pc = 0x7801e110#64) (C : IvkCtx G n P sp0 A B T s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeZ : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hra : s.getReg .x1 = ra) (hsp : s.getReg .x2 = sp + 0xb0#64)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = a1)
    (hO : Region out O s) (hCb : Region a1 (ivkState sp0 J j 0) s)
    (halloc : ∀ (u : MachineState), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801e184#64 → u.getReg .x2 = sp → StackOk Ro.layout 0x30 sp →
      u.getReg .x10 = 8#64 → u.getReg .x11 = 1#64 →
      Region T.b1 T.L1 u → Region T.b2 T.L2 u → Region T.b3 T.L3 u → Region T.b4 T.L4 u → Region T.b5 T.L5 u → Region T.b6 T.L6 u →
      (∀ (t : MachineState) (ptr : Word) (B0 : List Word), t.pc = 0x7801e184#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B0.length = 1 → Region ptr B0 t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 ≤ 0x1c00000000 →
        Region T.b1 T.L1 t → Region T.b2 T.L2 t → Region T.b3 T.L3 t → Region T.b4 T.L4 t → Region T.b5 T.L5 t → Region T.b6 T.L6 t →
        AsmVerif.RiscV.Sym.Disjoint T.b1 10 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b2 138 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b3 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b4 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b5 1024 ptr 1 → AsmVerif.RiscV.Sym.Disjoint T.b6 516 ptr 1 → SafeN G n P t) → SafeN G n P u)
    (hhandle_rv : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → SafeN G n P u)
    (hk : ∀ (t : MachineState) (ptr w : Word), t.code = s.code →
      Unchanged [(sp - 0x30#64, 6), (sp, 22), (a1, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Kept s t → IvkCtx G n P sp0 A B T t → IvkHead sp sp0 out ptr J A B T j 8 1 [w] t →
      Region (sp + 0x78#64) [s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18,
        s.getReg .x9, s.getReg .x8, ra] t →
      Region out O t → (∃ I1 : List Word, I1.length = 12 ∧ Region a1 I1 t) → SafeN G n P t) :
    SafeN G n P s := by
  refine from_iter_ivk_pro s sp sp0 out a1 ra J A B (ivkState sp0 J j 0) O j E.Al E.Bl (by simp) rfl
    hOl hpc C.code C.codeN hcodeM hcodeZ C.cw hra hsp E.stk E.okFr ha0 ha1 hO E.okO hCb E.okC C.Ar
    E.okA C.Br E.okB E.sp0_lo E.sp0_hi E.djS22O E.djS22C E.djS22A E.djS22B E.djBA E.djBB E.djFBlk
    E.djFC E.djFA E.djFB E.djF6A E.djF6B E.djF6C E.djF6O E.djBC E.djOC E.djOA E.djOB E.djCA E.djCB
    E.djAB E.djHA E.djHB E.djHO E.djHC T C.K E.arena E.ok halloc C.unwrap hhandle_rv ?_
  intro t ptr w bit0 bit1 I1 I2 hpc' hcode' hun hsp' hs0' hs1' hs2' hs3' hb1 hs4' h3 h4 h22 h23 h24
    h25 h26 h27 hI2l hI2 hR hI1l hR1 hO' hb0 hW hw hok' hlo' hhi' hk1 hk2 hk3 hk4 hk5 hk6 hf1 hf2 hf3 hf4 hf5 hf6
  rw [list12_cells I2 hI2l] at hR
  have hdjA : ∀ r ∈ [(sp - 0x30#64, 6), (sp, 22), (a1, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)],
      AsmVerif.RiscV.Sym.Disjoint (ptrA sp0) A.length r.1 r.2 := by
    intro r hr
    rw [E.Al]
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    · exact E.djF6A.symm
    · exact E.djS22A.symm
    · exact E.djCA.symm
    · exact E.djHA.ctl_of_heap.symm
    · exact E.djHA.arena_of_heap.symm
  have hdjB : ∀ r ∈ [(sp - 0x30#64, 6), (sp, 22), (a1, 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)],
      AsmVerif.RiscV.Sym.Disjoint (ptrB sp0) B.length r.1 r.2 := by
    intro r hr
    rw [E.Bl]
    rcases mem5 hr with rfl | rfl | rfl | rfl | rfl
    · exact E.djF6B.symm
    · exact E.djS22B.symm
    · exact E.djCB.symm
    · exact E.djHB.ctl_of_heap.symm
    · exact E.djHB.arena_of_heap.symm
  refine hk t ptr w hcode' hun ⟨h3, h4, h22, h23, h24, h25, h26, h27⟩
    (C.step' hcode' hun hdjA hdjB ⟨hk1, hk2, hk3, hk4, hk5, hk6⟩) ?_ (hR.shift 15) hO' ⟨I1, hI1l, hR1⟩
  refine ⟨hpc', hsp', hs0', hs1', hs2', hs3', by rw [hs4', ← hb1], hR.take 3, ?_, hW, ?_, ?_, hlo', ?_, ?_⟩
  · rw [show ivkState sp0 J j (1 + 1) = [I2[0]!, I2[1]!, I2[2]!, I2[3]!, I2[4]!, I2[5]!, I2[6]!,
      I2[7]!, I2[8]!, I2[9]!, I2[10]!, I2[11]!] from hI2.trans (list12_cells I2 hI2l)]
    exact (hR.shift 3).take 12
  · refine BitsUpTo.byte0 (k := 0) (fun o ho => absurd ho (by omega)) ?_
    simp only [List.getElem!_cons_zero, Nat.mul_zero]
    rw [hb0]; exact hw
  · exact ⟨hok'.aligned, hok'.inMem, Or.inr (by simp only [Ro.layout_textHi]; omega)⟩
  · simp only [List.length_singleton, Nat.mul_one]; exact hhi'
  · exact (⟨hf1, hf2, hf3, hf4, hf5, hf6⟩ : Away6 ptr 1 T).len (by simp)

end Cases.Zip2005
