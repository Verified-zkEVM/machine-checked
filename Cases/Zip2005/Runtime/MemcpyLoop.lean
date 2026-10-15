import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Kit.RegionGlue
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Image.F_7801b4d8
import Cases.Zip2005.Image.Ro

/-!
# `memcpy`'s aligned 32-byte loop, by induction

`memcpy(dst, src, n)` with both pointers 8-aligned and `n ≥ 32` runs the loop at
`0x7801b640`: four doublewords loaded, the pointers advanced, the count decremented, four stored,
`bltu 31, count` back. Unrolling it for a large `n` builds a region literal per store and does not
fit in memory (6144 bytes: 768 cells, >16 GB); so the loop is a lemma at its back-edge check
`0x7801b66c`, by induction on the iterations left, with one iteration stepped per induction step.
Only the next four source words and the four destination cells are regions the executor sees;
the rest of the source and the part already copied are carried under `Keep`, which the executor
does not read, and are re-cut by hand at the back edge.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- A fact the executor is to leave alone (a region of symbolic length). -/
def Keep (p : Prop) : Prop := p

theorem Keep.mk {p : Prop} (h : p) : Keep p := h
theorem Keep.out {p : Prop} (h : Keep p) : p := h

/-- The next four words of a list, from `j`. -/
theorem drop_window4 (S : List Word) (j : Nat) (h : j + 4 ≤ S.length) :
    S.drop j = S[j]! :: S[j + 1]! :: S[j + 2]! :: S[j + 3]! :: S.drop (j + 4) := by
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega),
    List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
  simp only [getElem!_pos S j (by omega), getElem!_pos S (j + 1) (by omega),
    getElem!_pos S (j + 2) (by omega), getElem!_pos S (j + 3) (by omega)]

theorem take_add4 (S : List Word) (j : Nat) (h : j + 4 ≤ S.length) :
    S.take j ++ [S[j]!, S[j + 1]!, S[j + 2]!, S[j + 3]!] = S.take (j + 4) := by
  rw [List.take_add, drop_window4 S j h]
  rfl

theorem ofNat_mul_add4 (j : Nat) :
    BitVec.ofNat 64 (8 * (j + 4)) = BitVec.ofNat 64 (8 * j) + 32#64 := by
  rw [show 8 * (j + 4) = 8 * j + 32 by omega, BitVec.ofNat_add]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- The loop from its back-edge check, `m` iterations left, `j` words copied so far. -/
theorem memcpy_loop32 {G : MachineState → Prop} {nb : Nat} {P : Prop} (s₀ : MachineState) (ra dst src : Word) (S : List Word) (N : Nat)
    (hSl : S.length = N) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst N) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src N)
    (hdj : Disjoint dst N src N)
    (hk : ∀ u, u.pc = ra → CalleeSaved s₀ u → u.code = s₀.code → u.privateInput = s₀.privateInput →
      Unchanged [(dst, N)] s₀ u → Region dst S u → SafeN G nb P u) :
    ∀ m j (t : MachineState) (p q : Word), N - j = 4 * m → j ≤ N →
      p = src + BitVec.ofNat 64 (8 * j) → q = dst + BitVec.ofNat 64 (8 * j) →
      t.pc = 0x7801b66c#64 → CodeAt F_7801b4d8.base F_7801b4d8.prog t → CodeWithin Ro.layout.textLo Ro.layout.textHi t →
      t.getReg .x1 = ra → ra &&& ~~~1#64 = ra →
      t.getReg .x11 = p → t.getReg .x13 = q → t.getReg .x12 = BitVec.ofNat 64 (8 * (N - j)) →
      t.getReg .x14 = 31#64 →
      Keep (Region p (S.drop j) t) → Keep (Region dst (S.take j) t) →
      CalleeSaved s₀ t → t.code = s₀.code → t.privateInput = s₀.privateInput →
      Unchanged [(dst, N)] s₀ t → SafeN G nb P t := by
  intro m
  induction m with
  | zero =>
    intro j t p q hm hj hp hq hpc hcode hcw hra hra1 hx11 hx13 hx12 hx14 hrest hdone hcs hcode₀ hI
      hu₀
    have hjN : j = N := by omega
    rw [show 8 * (N - j) = 0 by omega] at hx12
    have hu := Unchanged.refl ([] : List (Word × Nat)) t
    sym_exec
    sym_close hk
    -- everything is copied: the carried prefix is the whole list
    have h := (Keep.out hdone).of_unchanged' hunch rfl (fun r hr => by simp at hr)
    rwa [hjN, ← hSl, List.take_length] at h
  | succ m ih =>
    intro j t p q hm hj hp hq hpc hcode hcw hra hra1 hx11 hx13 hx12 hx14 hrest hdone hcs hcode₀ hI
      hu₀
    have hj4 : j + 4 ≤ N := by omega
    have hm' : N - (j + 4) = 4 * m := by omega
    have hN := hokS.inMem
    have h31 : 31 < (BitVec.ofNat 64 (8 * (N - j))).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by unfold SP1_MAX_MEMORY at hN; omega)]; omega
    have hokp : RegionOk Ro.layout.textLo Ro.layout.textHi p 4 := hokS.sub' j 4 hj4 hp
    have hokq : RegionOk Ro.layout.textLo Ro.layout.textHi q 4 := hokD.sub' j 4 hj4 hq
    have hdjqp : Disjoint q 4 p 4 := hdj.of_sub hq hj4 hp hj4
    have hwin : Region p [S[j]!, S[j + 1]!, S[j + 2]!, S[j + 3]!] t := by
      have h := (Keep.out hrest).take 4
      rwa [drop_window4 S j (by omega)] at h
    obtain ⟨D4, hD4, hD4l⟩ := Region.exists_junk q 4 t
    have hp' : p + 32#64 = src + BitVec.ofNat 64 (8 * (j + 4)) := by
      rw [hp, ofNat_mul_add4, BitVec.add_assoc]
    have hq' : q + 32#64 = dst + BitVec.ofNat 64 (8 * (j + 4)) := by
      rw [hq, ofNat_mul_add4, BitVec.add_assoc]
    have hnwD := hokD.nowrap
    have hnwS := hokS.nowrap
    have hqN : q.toNat = dst.toNat + 8 * j := by
      rw [hq, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * j) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    have hq0 := hq
    have hu := Unchanged.refl [(q, 4)] t
    -- `hm`, `hp`, `hq` would be rewrite rules for the executor: the count and the pointers must
    -- stay the atoms the regions are stated over
    clear hm hp hq
    sym_exec stop [0x7801b66c, 0x7801b670]
    -- the back edge: four more words are copied
    sym_close ih (j + 4) _ (p + 32#64) (q + 32#64)
    all_goals sym_subst
    · -- the count, down by 32 (`toNat_ofNat'`: the `rfl` form of the lemma makes the kernel
      -- evaluate the wrapped literal, E1)
      rw [hx12]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, Bn.toNat_ofNat', Bn.toNat_ofNat', Bn.toNat_ofNat']
      omega
    · refine Keep.mk ?_
      have h := ((Keep.out hrest).shift 4).of_unchanged' hunch (n := N - (j + 4))
        (by simp [List.length_drop]; omega) ?_
      · rw [List.drop_drop] at h
        exact h
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        exact (hdj.of_sub hq0 hj4 (show p + BitVec.ofNat 64 (8 * 4) = src + BitVec.ofNat 64 (8 * (j + 4)) from hp')
          (by omega)).symm
    · refine Keep.mk ?_
      rw [← take_add4 S j (by omega)]
      refine Region.append' ((Keep.out hdone).of_unchanged' hunch (n := j)
        (by simp [List.length_take]; omega) ?_) hR1 ?_
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        dsimp only
        exact ⟨Or.inl (by omega), by omega, by omega⟩
      · rw [show (S.take j).length = j by simp [List.length_take]; omega]
        apply BitVec.eq_of_toNat_eq
        rw [hqN, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * j) (by omega),
          Nat.mod_eq_of_lt (by omega)]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 6144)` on 8-aligned, disjoint regions of 768 doublewords: the first
    iteration stepped, the loop lemma for the other 191. -/
theorem memcpy6144_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (S : List Word)
    (hSl : S.length = 768)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 6144#64)
    (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 768)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 768)
    (hdj : Disjoint dst 768 src 768)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 768)] s t →
      Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hokD4 : RegionOk Ro.layout.textLo Ro.layout.textHi dst 4 := hokD.sub' 0 4 (by omega) (by simp)
  have hokS4 : RegionOk Ro.layout.textLo Ro.layout.textHi src 4 := hokS.sub' 0 4 (by omega) (by simp)
  have e4 : [S[0]!, S[1]!, S[2]!, S[3]!] = S.take 4 := by
    have e := take_add4 S 0 (by omega)
    simpa only [List.take_zero, List.nil_append, Nat.zero_add] using e
  have hwin : Region src [S[0]!, S[1]!, S[2]!, S[3]!] s := by
    have h := hS.take 4
    rwa [← e4] at h
  have hrest : Keep (Region (src + 32#64) (S.drop 4) s) := Keep.mk (hS.shift 4)
  have hdone : Keep (Region dst (S.take 0) s) := Keep.mk (fun i hi => by simp at hi)
  have hdjds : Disjoint dst 4 src 4 := by unfold AsmVerif.RiscV.Sym.Disjoint at hdj ⊢; omega
  obtain ⟨D4, hD4, hD4l⟩ := Region.exists_junk dst 4 s
  clear hS
  have hu := Unchanged.refl [(dst, 4)] s
  have hI : s.privateInput = s.privateInput := rfl
  sym_exec stop [0x7801b66c]
  -- after the first iteration: the loop lemma with 191 to go
  sym_close (memcpy_loop32 s ra dst src S 768 hSl hokD hokS hdj
    (fun u h1 h2 h3 _ h4 h5 => hk u h1 h2 h3 h4 h5) 191 4) _ (src + 32#64) (dst + 32#64)
  all_goals sym_subst
  all_goals first
    | rfl
    | rw [hx12]
    | exact hx11
    | exact hx13
    | exact Keep.mk ((Keep.out hrest).of_unchanged' hunch rfl (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        unfold AsmVerif.RiscV.Sym.Disjoint at hdj ⊢
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_drop, hSl]
        omega))
    | exact Keep.mk (by rw [← e4]; exact hR1)
    | skip
  -- the frame: this run's block lies in the lemma's
  refine Unchanged.trans_cover (Unchanged.refl _ s) hunch ?_
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  refine ⟨(dst, 768), by simp, ?_, ?_⟩ <;> dsimp only <;> omega

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `memcpy(dst, src, 32 m)`, `m ≥ 1`, on 8-aligned, disjoint regions of `4 m` doublewords: the
    first iteration stepped, the loop lemma for the other `m - 1`. -/
theorem memcpy_mul4_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (S : List Word)
    (m : Nat) (hm : 1 ≤ m) (hSl : S.length = 4 * m)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = BitVec.ofNat 64 (8 * (4 * m)))
    (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst (4 * m))
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src (4 * m))
    (hdj : Disjoint dst (4 * m) src (4 * m))
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → t.privateInput = s.privateInput →
      Unchanged [(dst, 4 * m)] s t → Region dst S t → SafeN G n P t) :
    SafeN G n P s := by
  have hN := hokS.inMem
  unfold SP1_MAX_MEMORY at hN
  have h31 : 31 < (BitVec.ofNat 64 (8 * (4 * m))).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  have hokD4 : RegionOk Ro.layout.textLo Ro.layout.textHi dst 4 := hokD.sub' 0 4 (by omega) (by simp)
  have hokS4 : RegionOk Ro.layout.textLo Ro.layout.textHi src 4 := hokS.sub' 0 4 (by omega) (by simp)
  have e4 : [S[0]!, S[1]!, S[2]!, S[3]!] = S.take 4 := by
    have e := take_add4 S 0 (by omega)
    simpa only [List.take_zero, List.nil_append, Nat.zero_add] using e
  have hwin : Region src [S[0]!, S[1]!, S[2]!, S[3]!] s := by
    have h := hS.take 4
    rwa [← e4] at h
  have hrest : Keep (Region (src + 32#64) (S.drop 4) s) := Keep.mk (hS.shift 4)
  have hdone : Keep (Region dst (S.take 0) s) := Keep.mk (fun i hi => by simp at hi)
  have hdjds : Disjoint dst 4 src 4 := by unfold AsmVerif.RiscV.Sym.Disjoint at hdj ⊢; omega
  obtain ⟨D4, hD4, hD4l⟩ := Region.exists_junk dst 4 s
  clear hS
  have hu := Unchanged.refl [(dst, 4)] s
  have hI : s.privateInput = s.privateInput := rfl
  sym_exec stop [0x7801b66c]
  -- after the first iteration: the loop lemma with `m - 1` to go
  sym_close (memcpy_loop32 s ra dst src S (4 * m) hSl hokD hokS hdj hk (m - 1) 4) _ (src + 32#64)
    (dst + 32#64)
  all_goals sym_subst
  all_goals first
    | rfl
    | omega
    | rw [hx12]
    | exact hx11
    | exact hx13
    | exact Keep.mk ((Keep.out hrest).of_unchanged' hunch rfl (fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        subst hr
        unfold AsmVerif.RiscV.Sym.Disjoint at hdj ⊢
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, List.length_drop, hSl]
        omega))
    | exact Keep.mk (by rw [← e4]; exact hR1)
    | skip
  · -- the count, down by 32
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, Bn.toNat_ofNat', Bn.toNat_ofNat', Bn.toNat_ofNat']
    omega
  -- the frame: this run's block lies in the lemma's
  refine Unchanged.trans_cover (Unchanged.refl _ s) hunch ?_
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  refine ⟨(dst, 4 * m), by simp, ?_, ?_⟩ <;> dsimp only <;> omega

end Cases.Zip2005
