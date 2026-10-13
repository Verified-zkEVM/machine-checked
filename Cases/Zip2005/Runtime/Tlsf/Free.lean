/-
  Cases.Zip2005.Runtime.Tlsf.Free

  What `dealloc` does to the heap, as theorems about the model (phase D4).

  `dealloc` frees a used block, merging it with its physical neighbours when they are free.
  A free neighbour first leaves its list from wherever it sits (`Shape.unlink`, memory
  `unlinkMem` in the code's order; at a list's head this is `Shape.pop`). The freed block and
  the detached neighbours then become one free block (`Shape.merge`: its header and the next
  block's back link), which is filed at the head of its class (`Shape.push`, stated for any
  memory with the right values at the doublewords the code writes, so the code's write order
  does not matter).
-/

import Cases.Zip2005.Runtime.Tlsf.Update

namespace Cases.Zip2005.Runtime.Tlsf

/-- A node's links, from its place in the list. -/
theorem Dll.mid {m : Word → Word} {x : Word} {post : List Word} :
    ∀ {pre p}, Dll m p (pre ++ x :: post) →
      m (x + 0x18#64) = pre.getLast?.getD p ∧ m (x + 0x10#64) = post.headD 0#64
  | [], _, ⟨h1, h2, _⟩ => ⟨h1, h2⟩
  | y :: pre, _, ⟨_, _, h3⟩ => by
    have := Dll.mid (pre := pre) h3
    rw [List.getLast?_cons]
    simpa using this

/-- **Unlinking a node with a predecessor `pv`**: `pv` forwards to the node's successor, which
    points back to `pv`. -/
theorem Dll.unlink {m m' : Word → Word} {x pv : Word} {post : List Word} :
    ∀ {pre p}, Dll m p (pre ++ pv :: x :: post) → (pre ++ pv :: x :: post).Nodup →
      m' (pv + 0x10#64) = post.headD 0#64 →
      (∀ z zs, post = z :: zs → m' (z + 0x18#64) = pv) →
      (∀ y ∈ pre ++ pv :: post, y ≠ pv → m' (y + 0x10#64) = m (y + 0x10#64)) →
      (∀ y ∈ pre ++ pv :: post, (∀ z zs, post = z :: zs → y ≠ z) →
        m' (y + 0x18#64) = m (y + 0x18#64)) →
      Dll m' p (pre ++ pv :: post)
  | [], p, ⟨h1, _, h3, h4, h5⟩, hnd, e10, e18, k10, k18 => by
    simp only [List.nil_append, List.nodup_cons, List.mem_cons, not_or] at hnd
    obtain ⟨⟨_, hpv⟩, hx, hnd⟩ := hnd
    refine ⟨?_, e10, ?_⟩
    · rw [k18 pv (by simp) fun z zs he e => hpv (by rw [he, e]; exact List.mem_cons_self ..)]
      exact h1
    · cases post with
      | nil => trivial
      | cons z zs =>
        obtain ⟨-, h5, h6⟩ := h5
        have hz : z ≠ pv := fun e => hpv (by rw [e]; exact List.mem_cons_self ..)
        refine ⟨e18 z zs rfl, ?_, h6.congr fun w hw => ?_⟩
        · rw [k10 z (by simp) hz]; exact h5
        · have hw1 : w ≠ pv := fun e => hpv (by rw [← e]; exact List.mem_cons_of_mem _ hw)
          have hw2 : w ≠ z := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hw)
          exact ⟨k10 w (by simp [hw]) hw1,
            k18 w (by simp [hw]) fun z' zs' he => by cases he; exact hw2⟩
  | y :: pre, p, ⟨h1, h2, h3⟩, hnd, e10, e18, k10, k18 => by
    simp only [List.cons_append, List.nodup_cons] at hnd
    obtain ⟨hy, hnd⟩ := hnd
    have hypv : y ≠ pv := fun e => hy (by rw [e]; simp)
    refine ⟨?_, ?_, Dll.unlink h3 hnd e10 e18 (fun w hw => k10 w (by simp [hw]))
      (fun w hw => k18 w (by simp [hw]))⟩
    · rw [k18 y (by simp) fun z zs he e => hy (by rw [e, he]; simp)]; exact h1
    · rw [k10 y (by simp) hypv, h2]
      cases pre <;> rfl

/-- Memory after `dealloc` unlinks the free block `x` from list `(f, s)`, in the code's order:
    the successor points back past `x`; the predecessor forwards past it, or, with none, the
    head moves on and, if the list empties, its bits clear as in `popMem`. -/
def unlinkMem (self : Word) (m : Word → Word) (f s x : Word) : Word → Word :=
  let nx := m (x + 0x10#64)
  let pv := m (x + 0x18#64)
  let m1 := if nx = 0#64 then m else upd m (nx + 0x18#64) pv
  if pv = 0#64 then
    let m2 := upd m1 (headAddr self f s) nx
    if nx = 0#64 then
      let t := m2 (slBm self f) &&& ~~~(1#64 <<< s.toNat)
      let m3 := upd m2 (slBm self f) t
      if t = 0#64 then upd m3 (flBm self) (m3 (flBm self) &&& ~~~(1#64 <<< f.toNat)) else m3
    else m2
  else upd m1 (pv + 0x10#64) nx

namespace Shape

variable {self base : Word} {m : Word → Word} {bs : List Blk} {L : Word → Word → List Word}
  {out : Word → Prop}

/-- At the head of its list, unlinking is popping. -/
theorem unlink_head (h : Shape self base m bs L out) {f s x : Word} {xs : List Word}
    (hf : f < 64#64) (hs : s < 64#64) (hL : L f s = x :: xs) :
    unlinkMem self m f s x = popMem self m f s (xs.headD 0#64) := by
  have hc := h.ctlOk
  have hH := headAddr_inCtl hc hf hs
  have hdll := h.links f s
  rw [hL] at hdll
  obtain ⟨h18, h10, -⟩ := hdll
  have h18' : m (x + 0x18#64) = 0#64 := h18
  have h10' : m (x + 0x10#64) = xs.headD 0#64 := h10
  have hy : xs.headD 0#64 ≠ 0#64 → xs.headD 0#64 ∈ L f s := fun hz => by
    cases xs with
    | nil => exact (hz rfl).elim
    | cons y ys => rw [hL]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  generalize xs.headD 0#64 = nx at h10' hy
  unfold unlinkMem popMem
  simp only [h18', h10', if_true]
  by_cases hz : nx = 0#64
  · subst hz
    simp only [if_true, upd_ne (headAddr_ne_slBm hf hs hf).symm, upd_ne (slBm_ne_flBm hf).symm,
      upd_ne (headAddr_ne_flBm hf hs).symm]
  · simp only [if_neg hz]
    have hne : nx + 0x18#64 ≠ headAddr self f s := h.ne_ctl (h.nodeA (hy hz)) (by decide) hH
    funext a
    unfold upd
    by_cases e1 : a = headAddr self f s
    · rw [if_pos e1, if_pos e1, if_neg (by rw [e1]; exact hne.symm)]
    · rw [if_neg e1, if_neg e1]

/-- **Unlinking any node of a free list** detaches it. -/
theorem unlink (h : Shape self base m bs L out) {f s x : Word}
    (hf : f < 64#64) (hs : s < 64#64) (hx : x ∈ L f s) :
    Shape self base (unlinkMem self m f s x) bs (Lset L f s ((L f s).erase x))
      (fun a => out a ∨ a = x) := by
  obtain ⟨pre, post, hL⟩ := List.append_of_mem hx
  have hnd := h.nodup f s
  rw [hL] at hnd
  have hxpre : x ∉ pre := fun hm => (List.nodup_append.mp hnd).2.2 x hm x (List.mem_cons_self ..) rfl
  have her : (L f s).erase x = pre ++ post := by
    rw [hL, List.erase_append_right _ hxpre, List.erase_cons_head]
  rw [her]
  rcases List.eq_nil_or_concat pre with rfl | ⟨pre', pv, rfl⟩
  · simp only [List.nil_append] at hL ⊢
    rw [h.unlink_head hf hs hL]
    exact h.pop hf hs hL
  -- `x` has a predecessor `pv`.
  simp only [List.concat_eq_append, List.append_assoc, List.singleton_append]
  have hL' : L f s = pre' ++ pv :: x :: post := by rw [hL]; simp
  have hnd' : (pre' ++ pv :: x :: post).Nodup := hL' ▸ h.nodup f s
  have hdll : Dll m 0 (pre' ++ pv :: x :: post) := hL' ▸ h.links f s
  have hmid := Dll.mid (pre := pre' ++ [pv]) (by simpa using hdll)
  simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
    Option.getD_some] at hmid
  obtain ⟨h18, h10⟩ := hmid
  have hpv : pv ∈ L f s := by rw [hL']; simp
  have hpvA := h.nodeA hpv
  have hpv0 := h.node_ne_zero hpv
  have hc := h.ctlOk
  generalize hnxe : post.headD 0#64 = nx at h10
  have hnxL : nx ≠ 0#64 → nx ∈ L f s ∧ ∃ zs, post = nx :: zs := by
    intro hz
    cases post with
    | nil => exact (hz hnxe.symm).elim
    | cons z zs => rw [← hnxe, hL']; exact ⟨by simp, zs, rfl⟩
  have hm' : unlinkMem self m f s x =
      upd (if nx = 0#64 then m else upd m (nx + 0x18#64) pv) (pv + 0x10#64) nx := by
    unfold unlinkMem; simp only [h10, h18, if_neg hpv0]
  rw [hm']
  -- What the writes leave alone.
  have keepA : ∀ z c, (A32 z ∧ base.toNat ≤ z.toNat ∧ z.toNat < 2 ^ 40) → c < 32#64 →
      (z ≠ pv ∨ c ≠ 0x10#64) → (nx ≠ 0#64 → z ≠ nx ∨ c ≠ 0x18#64) →
      upd (if nx = 0#64 then m else upd m (nx + 0x18#64) pv) (pv + 0x10#64) nx (z + c) =
        m (z + c) := by
    intro z c hz hc' h1 h2
    rw [upd_ne (key_ne hz.1 hpvA.1 hc' (by decide) h1)]
    split
    · rfl
    · rename_i hn
      rw [upd_ne (key_ne hz.1 (h.nodeA (hnxL hn).1).1 hc' (by decide) (h2 hn))]
  have keepC : ∀ k, InCtl self k →
      upd (if nx = 0#64 then m else upd m (nx + 0x18#64) pv) (pv + 0x10#64) nx k = m k := by
    intro k hk
    rw [upd_ne (fun e => h.ne_ctl hpvA (by decide) hk e.symm)]
    split
    · rfl
    · rename_i hn
      rw [upd_ne (fun e => h.ne_ctl (h.nodeA (hnxL hn).1) (by decide) hk e.symm)]
  have hcl : ∀ {f' s'}, ¬ (f' = f ∧ s' = s) → ∀ z ∈ L f' s', z ∉ L f s := by
    rintro f' s' hne z hz hz'
    exact hne (h.class_uniq hz hz')
  have hne_ne : pre' ++ pv :: post ≠ [] := by simp
  refine ⟨h.chain.congr fun b hb => ⟨?_, keepA _ _ (h.blkA hb) (by decide) (.inr (by decide))
      (fun _ => .inr (by decide))⟩,
    h.layout, fun f' s' hf' hs' => ?_, fun f' s' => ?_, fun b hb hu hno => ?_,
    fun f' s' z hz => ?_, fun f' s' hne => ?_, fun f' s' => ?_, fun f' s' hf' hs' => ?_,
    fun f' hf' => ?_⟩
  · have := keepA _ 0#64 (h.blkA hb) (by decide) (.inr (by decide)) (fun _ => .inr (by decide))
    simpa using this
  · rw [keepC _ (headAddr_inCtl hc hf' hs'), h.heads f' s' hf' hs']
    unfold Lset
    split
    · rename_i he; rw [he.1, he.2, hL']; cases pre' <;> rfl
    · rfl
  · unfold Lset
    by_cases he : f' = f ∧ s' = s
    · rw [if_pos he]
      have hmem : ∀ y ∈ pre' ++ pv :: post, y ∈ L f s := fun y hy => by
        rw [hL']; simp only [List.mem_append, List.mem_cons] at hy ⊢
        rcases hy with h1 | h1 | h1
        · exact .inl h1
        · exact .inr (.inl h1)
        · exact .inr (.inr (.inr h1))
      refine Dll.unlink hdll hnd' (by rw [upd_same, hnxe]) (fun z zs hp => ?_)
        (fun y hy hne => ?_) (fun y hy hne => ?_)
      · have hz0 : nx ≠ 0#64 := by
          rw [← hnxe, hp]; exact h.node_ne_zero (by rw [hL', hp]; simp)
        have hnz : nx = z := by rw [← hnxe, hp]; rfl
        subst hnz
        rw [upd_ne (key_ne (h.nodeA (hnxL hz0).1).1 hpvA.1 (by decide) (by decide)
          (.inr (by decide))), if_neg hz0, upd_same]
      · exact keepA _ _ (h.nodeA (hmem y hy)) (by decide) (.inl hne) (fun _ => .inr (by decide))
      · exact keepA _ _ (h.nodeA (hmem y hy)) (by decide) (.inr (by decide)) fun hn => by
          obtain ⟨-, zs, hp⟩ := hnxL hn
          exact .inl (hne nx zs hp)
    · rw [if_neg he]
      exact (h.links f' s').congr fun z hz => by
        have hz' := hcl he z hz
        have h1 : z ≠ pv := fun e => hz' (e ▸ hpv)
        have h2 : nx ≠ 0#64 → z ≠ nx := fun hn e => hz' (e ▸ (hnxL hn).1)
        exact ⟨keepA _ _ (h.nodeA hz) (by decide) (.inl h1) (fun hn => .inl (h2 hn)),
          keepA _ _ (h.nodeA hz) (by decide) (.inr (by decide)) (fun hn => .inl (h2 hn))⟩
  · have hf0 := h.filed b hb hu (fun ho => hno (.inl ho))
    unfold Lset
    split
    · rename_i he
      rw [he.1, he.2, hL'] at hf0
      have hbx : b.a ≠ x := fun e => hno (.inr e)
      simp only [List.mem_append, List.mem_cons] at hf0 ⊢
      rcases hf0 with h1 | h1 | h1 | h1
      · exact .inl h1
      · exact .inr (.inl h1)
      · exact (hbx h1).elim
      · exact .inr (.inr h1)
    · exact hf0
  · unfold Lset at hz
    split at hz
    · rename_i he
      rw [he.1, he.2]
      have hzL : z ∈ L f s := by
        rw [hL']; simp only [List.mem_append, List.mem_cons] at hz ⊢
        rcases hz with h1 | h1 | h1
        · exact .inl h1
        · exact .inr (.inl h1)
        · exact .inr (.inr (.inr h1))
      obtain ⟨ho, hb⟩ := h.members f s z hzL
      refine ⟨fun e => e.elim ho fun e => ?_, hb⟩
      subst e
      have := List.nodup_append.mp hnd'
      simp only [List.mem_append, List.mem_cons] at hz
      rcases hz with hz | hz | hz
      · exact this.2.2 z hz z (by simp) rfl
      · exact (List.nodup_cons.mp this.2.1).1 (by rw [hz]; simp)
      · exact (List.nodup_cons.mp (List.nodup_cons.mp this.2.1).2).1 hz
    · rename_i he
      obtain ⟨ho, hb⟩ := h.members f' s' z hz
      refine ⟨fun e => e.elim ho fun e => ?_, hb⟩
      subst e; exact hcl he z hz hx
  · unfold Lset at hne
    split at hne
    · rename_i he; rw [he.1, he.2]; exact ⟨hf, hs⟩
    · exact h.range f' s' hne
  · unfold Lset
    split
    · have := h.nodup f s
      rw [hL'] at this
      rw [List.nodup_append] at this ⊢
      refine ⟨this.1, (List.nodup_cons.mpr ⟨fun hm => ?_, ?_⟩), fun a ha b hb => ?_⟩
      · exact (List.nodup_cons.mp this.2.1).1 (List.mem_cons_of_mem _ hm)
      · exact (List.nodup_cons.mp (List.nodup_cons.mp this.2.1).2).2
      · refine this.2.2 a ha b ?_
        simp only [List.mem_cons] at hb ⊢
        rcases hb with h1 | h1
        · exact .inl h1
        · exact .inr (.inr h1)
    · exact h.nodup f' s'
  · rw [keepC _ (slBm_inCtl hc hf'), h.slbm f' s' hf' hs']
    unfold Lset
    split
    · rename_i he; rw [he.1, he.2, hL']; cases pre' <;> rfl
    · rfl
  · rw [keepC _ (flBm_inCtl hc), keepC _ (slBm_inCtl hc hf')]
    exact h.flbm f' hf'

theorem a32_sub {x y : Word} (hx : A32 x) (hy : A32 y) : (y - x) &&& 31#64 = 0#64 := by
  have : ∀ x y : BitVec 64, x &&& 31#64 = 0#64 → y &&& 31#64 = 0#64 → (y - x) &&& 31#64 = 0#64 := by
    intro x y; bv_decide
  exact this x y hx hy

/-- **Merging consecutive blocks** `c :: cs`, each used or detached, into one free block of
    size `S` reaching the next block `q`: its header, and `q`'s back link. The merged block is
    detached. -/
theorem merge (h : Shape self base m bs L out) {pre cs post : List Blk} {c q : Blk} {S : Word}
    (hbs : bs = pre ++ (c :: cs) ++ q :: post)
    (hcs : ∀ d ∈ c :: cs, d.used = true ∨ out d.a) (hS : c.a + S = q.a) :
    Shape self base (upd (upd m c.a S) (q.a + 8#64) c.a)
      (pre ++ ⟨c.a, S, false, false⟩ :: q :: post) L (fun a => out a ∨ a = c.a) := by
  have hbs' : bs = pre ++ c :: (cs ++ q :: post) := by rw [hbs]; simp
  have hbq : bs = (pre ++ c :: cs) ++ q :: post := hbs
  have hcb : c ∈ bs := by rw [hbs']; simp
  have hqb : q ∈ bs := by rw [hbq]; simp
  have hcA := h.blkA hcb
  have hqA := h.blkA hqb
  obtain ⟨hpre_c, hpost_c⟩ := h.around hbs'
  obtain ⟨hpre_q, hpost_q⟩ := h.around hbq
  have hcq : c.a.toNat + c.sz.toNat ≤ q.a.toNat := hpre_q c (by simp)
  have hcsz := sz_ge (h.blk hcb).2.2.2.2
  have hqsz := sz_ge (h.blk hqb).2.2.2.2
  have hq40 := h.layout.2.2 q hqb
  have hSn : S.toNat = q.a.toNat - c.a.toNat := by
    have : S = q.a - c.a := by rw [← hS]; bv_omega
    rw [this, BitVec.toNat_sub]; omega
  have hS31 : S &&& 31#64 = 0#64 := by
    have : S = q.a - c.a := by rw [← hS]; bv_omega
    rw [this]; exact a32_sub hcA.1 hqA.1
  have hSok : SizeOk S := by
    constructor
    · rw [BitVec.le_def]; simp; omega
    · rw [BitVec.lt_def]; simp; omega
  -- What the two writes leave alone.
  have keepA : ∀ z d, (A32 z ∧ base.toNat ≤ z.toNat ∧ z.toNat < 2 ^ 40) → d < 32#64 →
      (z ≠ c.a ∨ 0#64 ≠ d) → (z ≠ q.a ∨ d ≠ 8#64) →
      upd (upd m c.a S) (q.a + 8#64) c.a (z + d) = m (z + d) := by
    intro z d hz hd h1 h2
    rw [upd_ne (key_ne hz.1 hqA.1 hd (by decide) h2),
      upd_ne (fun e => key_ne0 hcA.1 hz.1 hd (h1.elim (fun h => .inl (Ne.symm h)) .inr) e.symm)]
  have keepC : ∀ k, InCtl self k → upd (upd m c.a S) (q.a + 8#64) c.a k = m k := by
    intro k hk
    rw [upd_ne (fun e => h.ne_ctl hqA (by decide) hk e.symm),
      upd_ne (fun e => h.ne_ctl0 hcA hk e.symm)]
  have hne_c : ∀ d ∈ pre ++ q :: post, d.a ≠ c.a := by
    intro d hd e
    rcases List.mem_append.mp hd with hd | hd
    · have h1 := hpre_c d hd; rw [e] at h1
      have := sz_ge (h.blk (b := d) (by rw [hbs']; simp [hd])).2.2.2.2; omega
    · rcases List.mem_cons.mp hd with rfl | hd
      · rw [e] at hcq; omega
      · have := hpost_q d hd; rw [e] at this; omega
  have hne_q : ∀ d ∈ pre ++ post, d.a ≠ q.a := by
    intro d hd e
    rcases List.mem_append.mp hd with hd | hd
    · have h1 := hpre_q d (by simp [hd]); rw [e] at h1
      have := sz_ge (h.blk (b := d) (by rw [hbs']; simp [hd])).2.2.2.2
      omega
    · have := hpost_q d hd; rw [e] at this; omega
  -- The new chain's blocks: the merged one, or an old one outside `c :: cs`.
  have hold : ∀ d ∈ bs, d.used = false → ¬ out d.a → d ∈ pre ++ q :: post := by
    intro d hd hu ho
    rw [hbs] at hd
    simp only [List.mem_append, List.mem_cons] at hd
    rcases hd with (hd | hd | hd) | hd | hd
    · exact List.mem_append_left _ hd
    · subst hd; rcases hcs d (by simp) with e | e
      · rw [hu] at e; exact absurd e (by decide)
      · exact (ho e).elim
    · rcases hcs d (by simp [hd]) with e | e
      · rw [hu] at e; exact absurd e (by decide)
      · exact (ho e).elim
    · subst hd; simp
    · simp [hd]
  have hsub : ∀ d ∈ pre ++ q :: post, d ∈ bs := by
    intro d hd; rw [hbs]; simp only [List.mem_append, List.mem_cons] at hd ⊢
    rcases hd with hd | hd | hd
    · exact .inl (.inl hd)
    · exact .inr (.inl hd)
    · exact .inr (.inr hd)
  have hnew : ∀ d ∈ pre ++ ⟨c.a, S, false, false⟩ :: q :: post,
      d = ⟨c.a, S, false, false⟩ ∨ d ∈ pre ++ q :: post := by
    intro d hd
    simp only [List.mem_append, List.mem_cons] at hd
    rcases hd with hd | hd | hd | hd
    · exact .inr (List.mem_append_left _ hd)
    · exact .inl hd
    · subst hd; simp
    · simp [hd]
  refine ⟨?_, ⟨h.layout.1, h.layout.2.1, fun d hd => ?_⟩, fun f s hf hs => ?_, fun f s => ?_,
    fun d hd hu hno => ?_, fun f s z hz => ?_, h.range, h.nodup, fun f s hf hs => ?_,
    fun f hf => ?_⟩
  · -- chain
    have hch := h.chain
    rw [hbs'] at hch
    obtain ⟨a', p', hseg, hc⟩ := (chain_append (List.cons_ne_nil _ _)).mp hch
    obtain ⟨hc1, hc2, hc3, -, -, hc6⟩ := hc
    have hcl : c.last = false := by
      cases hl : c.last
      · rfl
      · rw [if_pos hl] at hc6; exact absurd hc6.1 (by simp)
    rw [if_neg (by simp [hcl])] at hc6
    have hch2 : Chain m (a' + c.sz) a' ((cs ++ [q]) ++ post) := by simpa using hc6
    -- Through `cs` to `q`.
    have hseg2 : ∃ e pe, Seg m (a' + c.sz) a' cs e pe ∧ Chain m e pe (q :: post) :=
      (chain_append (List.cons_ne_nil _ _)).mp (by simpa using hch2)
    obtain ⟨e, pe, -, hq⟩ := hseg2
    obtain ⟨hq1, hq2, -, hq4, hq5, hq6⟩ := hq
    subst hc1 hq1
    refine (chain_append (List.cons_ne_nil _ _)).mpr ⟨c.a, p', hseg.congr fun d hd => ?_, ?_⟩
    · have hdb : d ∈ pre ++ q :: post := List.mem_append_left _ hd
      have hdA := h.blkA (hsub d hdb)
      have k0 := keepA _ 0#64 hdA (by decide) (.inl (hne_c d hdb))
        (.inl (hne_q d (List.mem_append_left _ hd)))
      simp only [BitVec.add_zero] at k0
      exact ⟨k0,
        keepA _ _ hdA (by decide) (.inl (hne_c d hdb)) (.inl (hne_q d (List.mem_append_left _ hd)))⟩
    · refine ⟨rfl, ?_, ?_, hS31, hSok, ?_⟩
      · rw [upd_ne (key_ne0 hcA.1 hqA.1 (by decide) (.inr (by decide))), upd_same]
        exact hdr_free
      · rw [keepA _ _ hcA (by decide) (.inr (by decide))
          (.inl fun e => hne_c q (by simp) e.symm)]; exact hc3
      · simp only [Bool.false_eq_true, if_false]
        rw [hS]
        refine ⟨rfl, ?_, upd_same .., hq4, hq5, ?_⟩
        · rw [upd_ne (key_ne0 hqA.1 hqA.1 (by decide) (.inr (by decide))),
            upd_ne (fun e => hne_c q (by simp) e)]
          exact hq2
        · by_cases hl : q.last = true
          · rw [if_pos hl] at hq6 ⊢; exact hq6
          · rw [if_neg hl] at hq6 ⊢
            refine hq6.congr fun d hd => ?_
            have hdb : d ∈ pre ++ post := List.mem_append_right _ hd
            have hdb' : d ∈ pre ++ q :: post := by simp [hd]
            have hdA := h.blkA (hsub d hdb')
            have k0 := keepA _ 0#64 hdA (by decide) (.inl (hne_c d hdb')) (.inl (hne_q d hdb))
            simp only [BitVec.add_zero] at k0
            exact ⟨k0,
              keepA _ _ hdA (by decide) (.inl (hne_c d hdb')) (.inl (hne_q d hdb))⟩
  · -- layout
    rcases hnew d hd with rfl | hd
    · simp only; omega
    · exact h.layout.2.2 d (hsub d hd)
  · rw [keepC _ (headAddr_inCtl h.ctlOk hf hs)]; exact h.heads f s hf hs
  · exact (h.links f s).congr fun z hz => by
      have hzA := h.nodeA hz
      exact ⟨keepA _ _ hzA (by decide) (.inr (by decide)) (.inr (by decide)),
        keepA _ _ hzA (by decide) (.inr (by decide)) (.inr (by decide))⟩
  · rcases hnew d hd with rfl | hd'
    · exact (hno (.inr rfl)).elim
    · exact h.filed d (hsub d hd') hu fun ho => hno (.inl ho)
  · obtain ⟨ho, d, hd, rfl, hu, hf, hs⟩ := h.members f s z hz
    have hd' := hold d hd hu ho
    refine ⟨fun e => e.elim ho fun e => hne_c d hd' e, d, ?_, rfl, hu, hf, hs⟩
    simp only [List.mem_append, List.mem_cons] at hd' ⊢
    rcases hd' with hd' | hd' | hd'
    · exact .inl hd'
    · exact .inr (.inr (.inl hd'))
    · exact .inr (.inr (.inr hd'))
  · rw [keepC _ (slBm_inCtl h.ctlOk hf)]; exact h.slbm f s hf hs
  · rw [keepC _ (flBm_inCtl h.ctlOk), keepC _ (slBm_inCtl h.ctlOk hf)]; exact h.flbm f hf

set_option maxHeartbeats 4000000 in
/-- **Filing a detached free block** `t` (size `S`) at the head of its class: whatever memory
    `m'` has the new head, the block's links, the old head's back link and the two bitmap bits
    in place, and the other doublewords of the shape as they were. -/
theorem push (h : Shape self base m bs L out) {t S : Word}
    (hb : (⟨t, S, false, false⟩ : Blk) ∈ bs) (hot : out t)
    (hout : ∀ b ∈ bs, b.used = false → out b.a → b.a = t) {m' : Word → Word}
    (eH : m' (headAddr self (flOf S) (slOf S)) = t)
    (e10 : m' (t + 0x10#64) = (L (flOf S) (slOf S)).headD 0#64)
    (e18 : m' (t + 0x18#64) = 0#64)
    (eh : ∀ z zs, L (flOf S) (slOf S) = z :: zs → m' (z + 0x18#64) = t)
    (eF : m' (flBm self) = m (flBm self) ||| 1#64 <<< (flOf S).toNat)
    (eS : m' (slBm self (flOf S)) = m (slBm self (flOf S)) ||| 1#64 <<< (slOf S).toNat)
    (eo : ∀ a, Key self bs a → a ≠ headAddr self (flOf S) (slOf S) → a ≠ t + 0x10#64 →
      a ≠ t + 0x18#64 → (∀ z zs, L (flOf S) (slOf S) = z :: zs → a ≠ z + 0x18#64) →
      a ≠ flBm self → a ≠ slBm self (flOf S) → m' a = m a) :
    Shape self base m' bs (Lset L (flOf S) (slOf S) (t :: L (flOf S) (slOf S)))
      (fun _ => False) := by
  have hc := h.ctlOk
  have htA := h.blkA hb
  have hSok := (h.blk hb).2.2.2.2
  have hf2 := flOf_lt hSok
  have hs2 := slOf_lt S
  generalize hf2e : flOf S = f2 at *
  generalize hs2e : slOf S = s2 at *
  have hH := headAddr_inCtl hc hf2 hs2
  have hSL := slBm_inCtl hc hf2
  have hFL := flBm_inCtl hc
  -- `t` is no node.
  have ht_not : ∀ f s, t ∉ L f s := fun f s ht => (h.members f s t ht).1 hot
  have nodeT : ∀ f s z, z ∈ L f s → z ≠ t := fun f s z hz e => ht_not f s (e ▸ hz)
  -- Keys of the arena and of the control block.
  have kA : ∀ z d, (A32 z ∧ base.toNat ≤ z.toNat ∧ z.toNat < 2 ^ 40) → d < 32#64 →
      Key self bs (z + d) → (z ≠ t ∨ d ≠ 0x10#64) → (z ≠ t ∨ d ≠ 0x18#64) →
      (∀ w ws, L f2 s2 = w :: ws → z ≠ w ∨ d ≠ 0x18#64) → m' (z + d) = m (z + d) := by
    intro z d hz hd hk h1 h2 h3
    exact eo _ hk (h.ne_ctl hz hd hH) (key_ne hz.1 htA.1 hd (by decide) h1)
      (key_ne hz.1 htA.1 hd (by decide) h2)
      (fun w ws hw => key_ne hz.1 (h.nodeA (by rw [hw]; exact List.mem_cons_self ..)).1 hd
        (by decide) (h3 w ws hw))
      (h.ne_ctl hz hd hFL) (h.ne_ctl hz hd hSL)
  have kC : ∀ k, InCtl self k → k ≠ headAddr self f2 s2 → k ≠ flBm self → k ≠ slBm self f2 →
      m' k = m k := by
    intro k hk h1 h2 h3
    exact eo _ (.inl hk) h1 (fun e => h.ne_ctl htA (by decide) hk e.symm)
      (fun e => h.ne_ctl htA (by decide) hk e.symm)
      (fun w ws hw e => h.ne_ctl (h.nodeA (by rw [hw]; exact List.mem_cons_self ..)) (by decide)
        hk e.symm) h2 h3
  -- A block's own keys.
  have kB : ∀ b ∈ bs, m' b.a = m b.a ∧ m' (b.a + 8#64) = m (b.a + 8#64) := by
    intro b hb'
    have hbA := h.blkA hb'
    have hk0 : Key self bs (b.a + 0#64) := .inr ⟨b, hb', .inl (by simp)⟩
    have k0 := kA b.a 0#64 hbA (by decide) hk0
      (.inr (by decide)) (.inr (by decide)) (fun _ _ _ => .inr (by decide))
    simp only [BitVec.add_zero] at k0
    exact ⟨k0, kA _ _ hbA (by decide) (.inr ⟨b, hb', .inr (.inl rfl)⟩) (.inr (by decide))
      (.inr (by decide)) (fun _ _ _ => .inr (by decide))⟩
  -- A node's links, away from `t` and from the old head's back link.
  have kN : ∀ f s z, z ∈ L f s → m' (z + 0x10#64) = m (z + 0x10#64) ∧
      ((∀ w ws, L f2 s2 = w :: ws → z ≠ w) → m' (z + 0x18#64) = m (z + 0x18#64)) := by
    intro f s z hz
    obtain ⟨-, b, hb', rfl, hu, -⟩ := h.members f s z hz
    have hbA := h.blkA hb'
    have hzt := nodeT f s _ hz
    exact ⟨kA _ _ hbA (by decide) (.inr ⟨b, hb', .inr (.inr ⟨hu, .inl rfl⟩)⟩) (.inl hzt)
        (.inr (by decide)) (fun _ _ _ => .inr (by decide)),
      fun hw => kA _ _ hbA (by decide) (.inr ⟨b, hb', .inr (.inr ⟨hu, .inr rfl⟩)⟩) (.inr (by decide))
        (.inl hzt) (fun w ws e => .inl (hw w ws e))⟩
  refine ⟨h.chain.congr kB, h.layout, fun f s hf hs => ?_, fun f s => ?_, fun d hd hu _ => ?_,
    fun f s z hz => ?_, fun f s hne => ?_, fun f s => ?_, fun f s hf hs => ?_, fun f hf => ?_⟩
  · -- heads
    unfold Lset
    by_cases he : f = f2 ∧ s = s2
    · rw [if_pos he, he.1, he.2, eH]; rfl
    · rw [if_neg he, kC _ (headAddr_inCtl hc hf hs) (fun e => he (headAddr_inj hf hs hf2 hs2 e))
        (headAddr_ne_flBm hf hs) (headAddr_ne_slBm hf hs hf2)]
      exact h.heads f s hf hs
  · -- links
    unfold Lset
    by_cases he : f = f2 ∧ s = s2
    · rw [if_pos he]
      refine ⟨e18, e10, ?_⟩
      cases hl : L f2 s2 with
      | nil => trivial
      | cons z zs =>
        have hzL : z ∈ L f2 s2 := by rw [hl]; exact List.mem_cons_self ..
        have hdll := h.links f2 s2
        rw [hl] at hdll
        obtain ⟨-, hz10, hzs⟩ := hdll
        have hnd := h.nodup f2 s2
        rw [hl] at hnd
        refine ⟨eh z zs hl, by rw [(kN _ _ _ hzL).1]; exact hz10, hzs.congr fun w hw => ?_⟩
        have hwL : w ∈ L f2 s2 := by rw [hl]; exact List.mem_cons_of_mem _ hw
        have hwz : w ≠ z := fun e => (List.nodup_cons.mp hnd).1 (e ▸ hw)
        exact ⟨(kN _ _ _ hwL).1, (kN _ _ _ hwL).2 fun w' ws' e => by
          rw [hl] at e; cases e; exact hwz⟩
    · rw [if_neg he]
      exact (h.links f s).congr fun w hw => ⟨(kN _ _ _ hw).1, (kN _ _ _ hw).2 fun w' ws' e hww => by
        subst hww
        exact he (h.class_uniq hw (by rw [e]; exact List.mem_cons_self ..))⟩
  · -- filed
    by_cases hdt : d.a = t
    · have := h.uniq hd hb hdt
      subst this
      unfold Lset; simp [hf2e, hs2e]
    · have := h.filed d hd hu (fun ho => hdt (hout d hd hu ho))
      unfold Lset
      split
      · rename_i he; rw [he.1, he.2] at this; exact List.mem_cons_of_mem _ this
      · exact this
  · -- members
    unfold Lset at hz
    split at hz
    · rename_i he
      rw [he.1, he.2]
      rcases List.mem_cons.mp hz with rfl | hz
      · exact ⟨id, _, hb, rfl, rfl, hf2e, hs2e⟩
      · exact ⟨id, (h.members f2 s2 z hz).2⟩
    · exact ⟨id, (h.members f s z hz).2⟩
  · -- range
    unfold Lset at hne
    split at hne
    · rename_i he; rw [he.1, he.2]; exact ⟨hf2, hs2⟩
    · exact h.range f s hne
  · -- nodup
    unfold Lset
    split
    · exact List.nodup_cons.mpr ⟨ht_not f2 s2, h.nodup f2 s2⟩
    · exact h.nodup f s
  · -- second-level bitmaps
    have hs6 := lt64 hs
    have hs2n := lt64 hs2
    unfold Lset
    by_cases he : f = f2
    · subst he
      rw [eS, getLsbD_set _ hs2n]
      by_cases hss : s = s2
      · subst hss; simp
      · have : s.toNat ≠ s2.toNat := fun e => hss (BitVec.eq_of_toNat_eq e)
        rw [if_neg (fun e => hss e.2), h.slbm f s hf hs]; simp [this]
    · rw [if_neg (fun e => he e.1), kC _ (slBm_inCtl hc hf) (fun e => headAddr_ne_slBm hf2 hs2 hf e.symm)
        (slBm_ne_flBm hf) (fun e => he (slBm_inj hf hf2 e))]
      exact h.slbm f s hf hs
  · -- first-level bitmap
    have hf6 := lt64 hf
    have hf2n := lt64 hf2
    have hs2n := lt64 hs2
    rw [eF, getLsbD_set _ hf2n]
    by_cases he : f = f2
    · subst he
      rw [eS]
      have : (m (slBm self f) ||| 1#64 <<< s2.toNat) ≠ 0#64 := fun e => by
        have := congrArg (fun w => w.getLsbD s2.toNat) e
        simp only [getLsbD_set _ hs2n] at this; simp at this
      simp [this]
    · have : f.toNat ≠ f2.toNat := fun e => he (BitVec.eq_of_toNat_eq e)
      rw [kC _ (slBm_inCtl hc hf) (fun e => headAddr_ne_slBm hf2 hs2 hf e.symm)
        (slBm_ne_flBm hf) (fun e => he (slBm_inj hf hf2 e)), h.flbm f hf]
      simp [this]

end Shape

end Cases.Zip2005.Runtime.Tlsf
