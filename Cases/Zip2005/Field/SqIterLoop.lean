import Cases.Zip2005.Field.SqIterBody
import Cases.Zip2005.Field.SqIterGrow
import Cases.Zip2005.Image.Ro

/-!
# `Vec<Fp>::from_iter` of `SqrtTables::new`: the loop, by induction

The loop head (`0x7803292c`) as an invariant over the length `k` (`1 ≤ k < 256`), the capacity `c`
(a power of two in `[4, 256]`, `k ≤ c`, and `c < 2k` unless `c = 4`) and the buffer `p`; one
iteration is `sq_iter_body` (`k < c`) or `sq_iter_grow` (`k = c`). At the exit the length is 256,
and so is the capacity.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- The loop's frame: `do_reserve_and_handle`'s frame, `from_iter`'s, the heap. -/
abbrev sqW (sp : Word) : List (Word × Nat) :=
  [(sp - 0x100#64, 32), (sp, 27), (0x78040620#64, 4162), (0x78048980#64, 14780690128)]

/-- What the loop keeps of its stack pointer and the generator's block. -/
structure SqEnv (sp g : Word) : Prop where
  stk : StackOk Ro.layout 0x100 sp
  sphi : sp.toNat + 0x140 ≤ 0x78000000
  glo : sp.toNat + 0x140 ≤ g.toNat
  ghi : g.toNat + 32 ≤ 0x78000000
  okF : RegionOk Ro.layout.roBase Ro.layout.textHi sp 27
  okH : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 8#64) 6
  okJ : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x38#64) 20
  okG : RegionOk Ro.layout.roBase Ro.layout.textHi g 4

/-- The capacities on the way to 256. -/
def SqCap (c : Nat) : Prop :=
  c = 4 ∨ c = 8 ∨ c = 16 ∨ c = 32 ∨ c = 64 ∨ c = 128 ∨ c = 256

/-- The loop head with `k` elements stored in a buffer `p` of capacity `c`. -/
structure SqHead (sp out g x3v x4v : Word) (G S J : List Word) (k c p : Word) (t : MachineState) : Prop where
  pc : t.pc = 0x7803292c#64
  r2 : t.getReg .x2 = sp
  r3 : t.getReg .x3 = x3v
  r4 : t.getReg .x4 = x4v
  r8 : t.getReg .x8 = BitVec.ofNat 64 (32 * k.toNat)
  r9 : t.getReg .x9 = p
  r19 : t.getReg .x19 = g
  r20 : t.getReg .x20 = 0x224698fc094cf91b#64
  r21 : t.getReg .x21 = 0x992d30ed00000001#64
  r22 : t.getReg .x22 = 0x4000000000000000#64
  r23 : t.getReg .x23 = 0x70cb2996efc89a65#64
  r24 : t.getReg .x24 = 0x21f1c4ff1e2278d5#64
  r25 : t.getReg .x25 = 257#64
  r26 : t.getReg .x26 = k + 1#64
  r27 : t.getReg .x27 = sp + 0xb8#64
  Hr : Region (sp + 8#64) [out, 0xac9fba6a4077fc57#64, 0xcf3f8e8753a769a9#64, c, p, k] t
  Jl : J.length = 20
  Jr : Region (sp + 0x38#64) J t
  Sr : Region (sp + 0xd8#64) S t
  Gr : Region g G t
  okP : RegionOk Ro.layout.roBase Ro.layout.textHi p (4 * c.toNat)
  plo : 0x78048980 ≤ p.toNat
  phi : p.toNat + 32 * c.toNat ≤ 0x1c00000000
  cap : SqCap c.toNat
  kc : k.toNat ≤ c.toNat
  kc2 : c.toNat < 2 * k.toNat ∨ c.toNat = 4
  k1 : 1 ≤ k.toNat
  k256 : k.toNat < 256

theorem sq_cap_le {c : Nat} (h : SqCap c) : 4 ≤ c ∧ c ≤ 256 := by
  unfold SqCap at h; omega

theorem toNat_succ_lt {k : Word} (h : k.toNat < 256) : (k + 1#64).toNat = k.toNat + 1 := by
  rw [BitVec.toNat_add]; simp only [BitVec.toNat_ofNat]; omega

theorem ofNat_32_succ {k : Word} (h : k.toNat < 256) :
    BitVec.ofNat 64 (32 * k.toNat) + 32#64 = BitVec.ofNat 64 (32 * (k + 1#64).toNat) := by
  rw [toNat_succ_lt h]; apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

theorem add_two_eq {k : Word} : k + 2#64 = k + 1#64 + 1#64 := by
  rw [BitVec.add_assoc]; rfl

theorem lt256_of_beq {k : Word} (h : k.toNat < 256) (hb : (k + 2#64 == 257#64) = false) :
    (k + 1#64).toNat < 256 := by
  rw [toNat_succ_lt h]
  have : k.toNat ≠ 255 := by
    intro he; apply absurd hb; rw [beq_eq_false_iff_ne, not_not]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  omega

theorem eq255_of_beq {k : Word} (h : k.toNat < 256) (hb : (k + 2#64 == 257#64) = true) :
    k.toNat = 255 := by
  rw [beq_iff_eq] at hb
  have := congrArg BitVec.toNat hb
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this; omega

theorem list4_cells (Q : List Word) (h : Q.length = 4) : Q = [Q[0]!, Q[1]!, Q[2]!, Q[3]!] := by
  match Q, h with
  | [_, _, _, _], _ => rfl

theorem mem2 {α : Type} {r r1 r2 : α} (h : r ∈ [r1, r2]) : r = r1 ∨ r = r2 := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using h

theorem mem3 {α : Type} {r r1 r2 r3 : α} (h : r ∈ [r1, r2, r3]) : r = r1 ∨ r = r2 ∨ r = r3 := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using h

theorem mem4 {α : Type} {r r1 r2 r3 r4 : α} (h : r ∈ [r1, r2, r3, r4]) :
    r = r1 ∨ r = r2 ∨ r = r3 ∨ r = r4 := by
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using h

theorem toNat_sp_sub (sp : Word) (h : 0x100 ≤ sp.toNat) : (sp - 0x100#64).toNat = sp.toNat - 0x100 := by
  rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega

theorem toNat_sp_add (sp : Word) (c : Nat) (h : sp.toNat + c < 2 ^ 64) (hc : c < 2 ^ 64) :
    (sp + BitVec.ofNat 64 c).toNat = sp.toNat + c := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

set_option maxHeartbeats 4000000 in
theorem sq_loop {Gd : MachineState → Prop} {nb : Nat} {P : Prop} {L : List (Word × Nat)} (s t0 : MachineState) (sp out g x3v x4v : Word) (G S : List Word)
    (hGl : G.length = 4) (hSl : S.length = 13) (E : SqEnv sp g)
    (hcode : CodeAt F_780326cc.base F_780326cc.prog s) (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hres : SqReserve Gd nb P s.code)
    (hx : ∀ (t : MachineState) (J : List Word) (c p l : Word), t.pc = 0x78032a40#64 → t.code = s.code →
      Unchanged (sqW sp) t0 t → t.getReg .x2 = sp → t.getReg .x3 = x3v → t.getReg .x4 = x4v →
      Region (sp + 8#64) [out, 0xac9fba6a4077fc57#64, 0xcf3f8e8753a769a9#64, c, p, l] t →
      J.length = 20 → Region (sp + 0x38#64) J t → Region (sp + 0xd8#64) S t →
      c.toNat = 256 → l.toNat = 256 →
      RegionOk Ro.layout.roBase Ro.layout.textHi p 1024 → 0x78048980 ≤ p.toNat → p.toNat + 0x2000 ≤ 0x1c00000000 →
      RoImage Ro.layout t → Run.HeapAt ((p, 1024) :: L) t → SafeN Gd nb P t) :
    ∀ (n : Nat) (t : MachineState) (J : List Word) (k c p : Word), t.code = s.code → RoImage Ro.layout t →
      Run.HeapAt ((p, 4 * c.toNat) :: L) t →
      Unchanged (sqW sp) t0 t → SqHead sp out g x3v x4v G S J k c p t → 256 - k.toNat = n →
      SafeN Gd nb P t := by
  intro n
  induction n with
  | zero => intro t J k c p _ _ _ _ H hn; have := H.k256; omega
  | succ n ih =>
    intro t J k c p hc hro hheap hU H hn
    have hcd := codeAt_of_code_eq hc hcode
    have hcdM := codeAt_of_code_eq hc hcodeM
    have hcwt : CodeWithin Ro.layout.textLo Ro.layout.textHi t := fun a ha => hcw a (hc ▸ ha)
    have hcap := sq_cap_le H.cap
    have hk1 := H.k1
    have hk256 := H.k256
    have hkc := H.kc
    have hkc2 := H.kc2
    have hplo := H.plo
    have hphi := H.phi
    have hsphi := E.sphi
    have hglo := E.glo
    have hghi := E.ghi
    have hslo := E.stk.lo
    have hd8 : (sp + 0xd8#64).toNat = sp.toNat + 0xd8 := toNat_sp_add sp 0xd8 (by omega) (by omega)
    have hkn : (k + 1#64).toNat = k.toNat + 1 := toNat_succ_lt hk256
    by_cases hkc' : k = c
    · -- the buffer is full: `reserve`, then the store
      subst hkc'
      have hcap' : k.toNat = 4 ∨ k.toNat = 8 ∨ k.toNat = 16 ∨ k.toNat = 32 ∨ k.toNat = 64 ∨
          k.toNat = 128 := by
        have := H.cap; unfold SqCap at this; omega
      refine sq_iter_grow t sp out g p k (BitVec.ofNat 64 (32 * k.toNat)) G J hGl H.Jl hcap'
        (by rw [BitVec.toNat_ofNat]; omega) H.pc hcd hcdM hcwt hro hheap H.r2 E.stk H.r8 H.r9 H.r19 H.r20
        H.r21 H.r22 H.r23 H.r24 H.r25 H.r26 H.r27 H.Hr E.okF E.okH H.Jr E.okJ H.Gr E.okG E.sphi E.glo
        E.ghi H.plo H.phi (hc ▸ hres) ?_
      intro t2 p' J' hpc2 hc2 hun2 r2 r8 r9 r19 r20 r21 r22 r23 r24 r25 r26 r27 r3 r4 hH2 hJl2 hJ2
        hokP2 hplo2 hphi2 hheap2
      have hkk : (k + k).toNat = 2 * k.toNat := by
        rw [BitVec.toNat_add]; omega
      have hdisj : ∀ {b : Word} {m : Nat}, b.toNat + 8 * m ≤ 0x78000000 → sp.toNat + 0x140 ≤ b.toNat →
          ∀ r ∈ sqW sp, MachineChecked.RiscV.Sym.Disjoint b m r.1 r.2 := by
        intro b m h1 h2 r hr
        rcases mem4 hr with rfl | rfl | rfl | rfl
        · unfold MachineChecked.RiscV.Sym.Disjoint; dsimp only; rw [toNat_sp_sub sp (by omega)]; omega
        · unfold MachineChecked.RiscV.Sym.Disjoint; dsimp only; omega
        · unfold MachineChecked.RiscV.Sym.Disjoint; dsimp only; simp only [BitVec.toNat_ofNat]; omega
        · unfold MachineChecked.RiscV.Sym.Disjoint; dsimp only; simp only [BitVec.toNat_ofNat]; omega
      have hdS : ∀ r ∈ sqW sp, MachineChecked.RiscV.Sym.Disjoint (sp + 0xd8#64) 13 r.1 r.2 := by
        intro r hr
        rcases mem4 hr with rfl | rfl | rfl | rfl
        · unfold MachineChecked.RiscV.Sym.Disjoint; dsimp only; rw [toNat_sp_sub sp (by omega)]; omega
        · unfold MachineChecked.RiscV.Sym.Disjoint; dsimp only; omega
        · unfold MachineChecked.RiscV.Sym.Disjoint; dsimp only; simp only [BitVec.toNat_ofNat]; omega
        · unfold MachineChecked.RiscV.Sym.Disjoint; dsimp only; simp only [BitVec.toNat_ofNat]; omega
      refine ih t2 J' (k + 1#64) (k + k) p' (hc2.trans hc)
        (hro.of_unchanged hun2 ?_)
        (by rw [hkk, show 4 * (2 * k.toNat) = 8 * k.toNat by ring]; exact hheap2)
        (hU.trans_cover hun2 (fun r hr => ⟨r, hr, by unfold Covers; omega⟩)) ?_
        (by omega)
      · intro r hr
        rcases mem4 hr with rfl | rfl | rfl | rfl
        · left; dsimp only; rw [toNat_sp_sub sp (by omega)]; simp only [Ro.layout_roBase]; omega
        · left; dsimp only; simp only [Ro.layout_roBase]; omega
        · right; dsimp only; simp only [Ro.layout_roBase, Ro.layout_roBytes, BitVec.toNat_ofNat]; omega
        · right; dsimp only; simp only [Ro.layout_roBase, Ro.layout_roBytes, BitVec.toNat_ofNat]; omega
      exact SqHead.mk
        (pc := hpc2)
        (r2 := r2)
        (r3 := r3.trans H.r3)
        (r4 := r4.trans H.r4)
        (r8 := (by rw [r8, ofNat_32_succ hk256]))
        (r9 := r9)
        (r19 := r19)
        (r20 := r20)
        (r21 := r21)
        (r22 := r22)
        (r23 := r23)
        (r24 := r24)
        (r25 := r25)
        (r26 := (by rw [r26, add_two_eq]))
        (r27 := r27)
        (Hr := hH2)
        (Jl := hJl2)
        (Jr := hJ2)
        (Sr := H.Sr.of_unchanged' hun2 hSl hdS)
        (Gr := H.Gr.of_unchanged' hun2 hGl (hdisj (by omega) (by omega)))
        (okP := (by rw [hkk, show 4 * (2 * k.toNat) = 8 * k.toNat by ring]; exact hokP2))
        (plo := hplo2)
        (phi := (by rw [hkk]; omega))
        (cap := (by unfold SqCap; rw [hkk]; omega))
        (kc := (by rw [hkk, hkn]; omega))
        (kc2 := (by rw [hkk, hkn]; omega))
        (k1 := (by rw [hkn]; omega))
        (k256 := (by rw [hkn]; omega))
    · -- room in the buffer: the store at slot `k`
      have hkc'' : (k == c) = false := by rw [beq_eq_false_iff_ne]; exact hkc'
      have hlt : k.toNat < c.toNat := by
        rcases Nat.lt_or_eq_of_le hkc with h | h
        · exact h
        · exact absurd (BitVec.eq_of_toNat_eq h) hkc'
      obtain ⟨q, hq⟩ : ∃ q, p + BitVec.ofNat 64 (32 * k.toNat) = q := ⟨_, rfl⟩
      have hqn : q.toNat = p.toNat + 32 * k.toNat := by
        rw [← hq]; exact toNat_sp_add p _ (by omega) (by omega)
      have hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi q 4 :=
        H.okP.sub' (4 * k.toNat) 4 (by omega) (by rw [← hq, show 8 * (4 * k.toNat) = 32 * k.toNat by ring])
      obtain ⟨Q, hQ, hQl⟩ := Region.exists_junk q 4 t
      rw [list4_cells Q hQl] at hQ
      have hdQF : MachineChecked.RiscV.Sym.Disjoint q 4 sp 27 := by unfold MachineChecked.RiscV.Sym.Disjoint; omega
      have hdQG : MachineChecked.RiscV.Sym.Disjoint q 4 g 4 := by unfold MachineChecked.RiscV.Sym.Disjoint; omega
      have hW : ∀ r ∈ [(sp, 27), (q, 4)], ∃ r' ∈ sqW sp, Covers r'.1 r'.2 r.1 r.2 := by
        intro r hr
        rcases mem2 hr with rfl | rfl
        · exact ⟨(sp, 27), by simp, by unfold Covers; dsimp only; omega⟩
        · exact ⟨(0x78048980#64, 14780690128), by simp, by unfold Covers; dsimp only; simp only [BitVec.toNat_ofNat]; omega⟩
      have hdS : ∀ r ∈ [(sp, 27), (q, 4)], MachineChecked.RiscV.Sym.Disjoint (sp + 0xd8#64) 13 r.1 r.2 := by
        intro r hr
        rcases mem2 hr with rfl | rfl
        · unfold MachineChecked.RiscV.Sym.Disjoint; dsimp only; omega
        · unfold MachineChecked.RiscV.Sym.Disjoint; dsimp only; omega
      have hdG : ∀ r ∈ [(sp, 27), (q, 4)], MachineChecked.RiscV.Sym.Disjoint g 4 r.1 r.2 := by
        intro r hr
        rcases mem2 hr with rfl | rfl
        · unfold MachineChecked.RiscV.Sym.Disjoint; dsimp only; omega
        · unfold MachineChecked.RiscV.Sym.Disjoint; dsimp only; omega
      have hroW : ∀ r ∈ [(sp, 27), (q, 4)], r.1.toNat + 8 * r.2 ≤ Ro.layout.roBase ∨ Ro.layout.roBase + Ro.layout.roBytes ≤ r.1.toNat := by
        intro r hr
        rcases mem2 hr with rfl | rfl
        · left; dsimp only; simp only [Ro.layout_roBase]; omega
        · right; dsimp only; simp only [Ro.layout_roBase, Ro.layout_roBytes]; omega
      -- the store stays in the frame and the buffer: the heap invariant is kept
      have hkeep : ∀ t2, Unchanged [(sp, 27), (q, 4)] t t2 → Run.HeapAt ((p, 4 * c.toNat) :: L) t2 :=
        fun t2 hun2 => Carry.of_unchanged hheap hun2
          (openW_cons (openBlock_range (lo := 0) (hi := 0x78040620) (b := sp) (n := 27) _ _ (by simp [Run.ranges])
            (Nat.zero_le _) (by omega))
            (openW_cons (openBlock_live (b := q) (n := 4) _ _ List.mem_cons_self (by omega) (by omega))
              (openW_nil _ _)))
      refine sq_iter_body t sp out g p k c (BitVec.ofNat 64 (32 * k.toNat)) q Q[0]! Q[1]! Q[2]! Q[3]!
        G J hGl H.Jl hkc'' hq H.pc hcd hcdM hcwt hro H.r2 H.r8 H.r9 H.r19 H.r20 H.r21 H.r22 H.r23
        H.r24 H.r25 H.r26 H.r27 H.Hr E.okF E.okH H.Jr E.okJ H.Gr E.okG hQ hokQ (by omega) E.sphi E.glo
        E.ghi hdQF hdQG ?_ ?_
      · intro t2 J' Q' hpc2 hc2 hun2 r2 r8 r9 r19 r20 r21 r22 r23 r24 r25 r26 r27 r3 r4 hH2 hJl2 hJ2 _ _ hb
        have hk' := lt256_of_beq hk256 hb
        refine ih t2 J' (k + 1#64) c p (hc2.trans hc) (hro.of_unchanged hun2 hroW) (hkeep t2 hun2)
          (hU.trans_cover hun2 hW) ?_ (by omega)
        exact SqHead.mk
          (pc := hpc2)
          (r2 := r2)
          (r3 := r3.trans H.r3)
          (r4 := r4.trans H.r4)
          (r8 := (by rw [r8, ofNat_32_succ hk256]))
          (r9 := r9)
          (r19 := r19)
          (r20 := r20)
          (r21 := r21)
          (r22 := r22)
          (r23 := r23)
          (r24 := r24)
          (r25 := r25)
          (r26 := (by rw [r26, add_two_eq]))
          (r27 := r27)
          (Hr := hH2)
          (Jl := hJl2)
          (Jr := hJ2)
          (Sr := H.Sr.of_unchanged' hun2 hSl hdS)
          (Gr := H.Gr.of_unchanged' hun2 hGl hdG)
          (okP := H.okP)
          (plo := H.plo)
          (phi := H.phi)
          (cap := H.cap)
          (kc := (by rw [hkn]; omega))
          (kc2 := (by rw [hkn]; omega))
          (k1 := (by rw [hkn]; omega))
          (k256 := hk')
      · intro t2 J' Q' hpc2 hc2 hun2 r2 r3 r4 hH2 hJl2 hJ2 _ _ hb
        have hk' := eq255_of_beq hk256 hb
        have hc256 : c.toNat = 256 := by have := H.cap; unfold SqCap at this; omega
        refine hx t2 J' c p (k + 1#64) hpc2 (hc2.trans hc) (hU.trans_cover hun2 hW) r2
          (r3.trans H.r3) (r4.trans H.r4) hH2 hJl2 hJ2
          (H.Sr.of_unchanged' hun2 hSl hdS) hc256 (by rw [hkn]; omega)
          (by have := H.okP; rw [hc256] at this; exact this) H.plo (by have := H.phi; rw [hc256] at this; omega)
          (hro.of_unchanged hun2 hroW) (by have h := hkeep t2 hun2; rw [hc256] at h; exact h)

end Cases.Zip2005
