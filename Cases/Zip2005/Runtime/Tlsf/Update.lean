/-
  Cases.Zip2005.Runtime.Tlsf.Update

  What `alloc` does to the heap, as theorems about the model (phase D4).

  After the pop (`Shape.pop`) the chosen block is detached. If it fits the request exactly it
  is marked used (`Shape.mark`); otherwise it is split (`Shape.split`): the front becomes the
  used block, the rest a free block filed at the head of its class, with the next block's
  back link, the bitmaps and the headers updated in the order the code writes them
  (`splitMem`). Either way the heap is whole again, nothing detached.

  The doublewords written are told apart by their positions: every block is 32-aligned and
  lies in the arena, past the control block, so each (dis)equality is arithmetic `omega`
  settles from the blocks' positions (`kd`, `uev`).
-/

import Cases.Zip2005.Runtime.Tlsf.Heap
namespace Cases.Zip2005.Runtime.Tlsf
/-- Memory after `alloc` splits the detached block at `x` (size `S`) at `N`: the next
    block's back link, the remainder's header and links, its list's head and back link, the
    bitmaps, and finally `x`'s header, used. In the code's order. -/
def splitMem (self : Word) (m : Word → Word) (x S N : Word) : Word → Word :=
  let y := x + N
  let R := S - N
  let f2 := flOf R
  let s2 := slOf R
  let m := upd m (x + S + 8#64) y
  let h2 := m (headAddr self f2 s2)
  let m := upd m (headAddr self f2 s2) y
  let m := upd (upd (upd (upd m y R) (y + 8#64) x) (y + 0x10#64) h2) (y + 0x18#64) 0#64
  let m := if h2 = 0#64 then m else upd m (h2 + 0x18#64) y
  let m := upd m (flBm self) (m (flBm self) ||| 1#64 <<< f2.toNat)
  let m := upd m (slBm self f2) (m (slBm self f2) ||| 1#64 <<< s2.toNat)
  upd m x (N + 1#64)

theorem A32.mod {z : Word} (h : A32 z) : z.toNat % 32 = 0 := by
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_and, show (31#64).toNat = 2 ^ 5 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod] at this
  simpa using this

theorem hdr_free {x S : Word} : S = Blk.hdr ⟨x, S, false, false⟩ := by
  simp [Blk.hdr]

theorem lt_pow40 {N S : BitVec 64} (h1 : N < S) (h2 : S < 1#64 <<< 40) : N < 1#64 <<< 40 := by
  bv_decide

theorem add_sub_cancel' {x N S : BitVec 64} : x + N + (S - N) = x + S := by bv_omega

theorem ne_nat {a b : Word} (h : a.toNat ≠ b.toNat) : a ≠ b := fun e => h (e ▸ rfl)

theorem toNat_add_lt {z c : Word} (hz : z.toNat < 2 ^ 40) (hc : c.toNat < 2 ^ 40) :
    (z + c).toNat = z.toNat + c.toNat := by
  rw [BitVec.toNat_add]; omega

theorem rem_ok {S N : BitVec 64} (hS : S &&& 31#64 = 0#64) (hSok : SizeOk S)
    (hN : N &&& 31#64 = 0#64) (hNS : N < S) : (S - N) &&& 31#64 = 0#64 ∧ SizeOk (S - N) := by
  obtain ⟨h1, h2⟩ := hSok
  unfold SizeOk; bv_decide

/-- Discharge a doubleword (dis)equality from the `toNat` facts in context. -/
macro "kd" : tactic => `(tactic|
  first | with_reducible rfl | with_reducible assumption | (apply ne_nat; omega))

/-- Evaluate a chain of `upd`s at a point, each step's (dis)equality by `kd`. -/
macro "uev" : tactic => `(tactic|
  repeat (first | with_reducible rw [upd_same] | (with_reducible rw [upd_ne]; rotate_left; kd)))

namespace Shape

variable {self base : Word} {m : Word → Word} {bs : List Blk} {L : Word → Word → List Word}
  {out : Word → Prop}

/-- A doubleword inside one block is none of another's first 32 bytes. -/
theorem blk_ne (h : Shape self base m bs L out) {b c : Blk} (hb : b ∈ bs) (hc : c ∈ bs)
    (hne : b ≠ c) {k d : Word} (hk : b.a.toNat ≤ k.toNat ∧ k.toNat < b.a.toNat + b.sz.toNat)
    (hd : d < 32#64) : k ≠ c.a + d := by
  intro e
  have hcA := h.blkA hc
  have hcs := sz_ge (h.blk hc).2.2.2.2
  rw [BitVec.lt_def] at hd; simp only [BitVec.toNat_ofNat] at hd
  have : (c.a + d).toNat = c.a.toNat + d.toNat := by rw [BitVec.toNat_add]; omega
  rw [← e] at this
  rcases h.disj hb hc hne with h1 | h1 <;> omega

/-- Around a block of the chain: its predecessors end at or before it, its successors begin at
    or after its end. -/
theorem around (h : Shape self base m bs L out) {pre post : List Blk} {b : Blk}
    (hbs : bs = pre ++ b :: post) :
    (∀ c ∈ pre, c.a.toNat + c.sz.toNat ≤ b.a.toNat) ∧
      (∀ d ∈ post, b.a.toNat + b.sz.toNat ≤ d.a.toNat) := by
  have hs := (h.chain.sorted h.layout.2.2).1
  rw [hbs, List.pairwise_append, List.pairwise_cons] at hs
  exact ⟨fun c hc => hs.2.2 c hc b (List.mem_cons_self ..), hs.2.1.1⟩

theorem ne_of_pre (h : Shape self base m bs L out) {pre post : List Blk} {b c : Blk}
    (hbs : bs = pre ++ b :: post) (hc : c ∈ pre) : c ≠ b := fun e => by
  have := (h.around hbs).1 c hc
  have := sz_ge (h.blk (b := c) (by rw [hbs]; exact List.mem_append_left _ hc)).2.2.2.2
  rw [e] at *; omega

theorem ne_of_post (h : Shape self base m bs L out) {pre post : List Blk} {b c : Blk}
    (hbs : bs = pre ++ b :: post) (hc : c ∈ post) : c ≠ b := fun e => by
  have := (h.around hbs).2 c hc
  have := sz_ge (h.blk (b := b) (by rw [hbs]; exact List.mem_append_right _ (List.mem_cons_self ..))).2.2.2.2
  rw [e] at *; omega

theorem mem_of_pre {pre post : List Blk} {b c : Blk} (hbs : bs = pre ++ b :: post)
    (hc : c ∈ pre) : c ∈ bs := by rw [hbs]; exact List.mem_append_left _ hc

theorem mem_of_post {pre post : List Blk} {b c : Blk} (hbs : bs = pre ++ b :: post)
    (hc : c ∈ post) : c ∈ bs := by
  rw [hbs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hc)

theorem hdr_used {x S : Word} (hS : S &&& 31#64 = 0#64) :
    S + 1#64 = Blk.hdr ⟨x, S, true, false⟩ := by
  have : ∀ S : BitVec 64, S &&& 31#64 = 0#64 → S + 1#64 = (S ||| 1#64) ||| 0#64 := by
    intro S h; bv_decide
  exact this S hS

/-- **Marking a detached free block used**, when it fits exactly. -/
theorem mark (h : Shape self base m bs L (fun a => False ∨ a = x)) {pre post : List Blk}
    {S : Word} (hbs : bs = pre ++ ⟨x, S, false, false⟩ :: post) :
    Shape self base (upd m x (S + 1#64)) (pre ++ ⟨x, S, true, false⟩ :: post) L
      (fun _ => False) := by
  have hb : (⟨x, S, false, false⟩ : Blk) ∈ bs := by
    rw [hbs]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hbA := h.blkA hb
  obtain ⟨_, _, _, hS31, hSok⟩ := h.blk hb
  have hpost : post ≠ [] := by
    rintro rfl
    have := h.chain
    rw [hbs] at this
    obtain ⟨a', p', _, hc⟩ := (chain_append (List.cons_ne_nil _ _)).mp this
    simp [Chain] at hc
  -- The rest of the chain keeps its headers.
  have keep : ∀ c ∈ bs, c ≠ ⟨x, S, false, false⟩ →
      upd m x (S + 1#64) c.a = m c.a ∧ upd m x (S + 1#64) (c.a + 8#64) = m (c.a + 8#64) :=
    fun c hc hne => ⟨upd_ne (fun e => h.blk_ne hc hb hne (k := c.a) (d := 0#64)
        ⟨Nat.le_refl _, by have := sz_ge (h.blk hc).2.2.2.2; omega⟩ (by decide) (by simpa using e)),
      upd_ne (fun e => key_ne0 hbA.1 (h.blkA hc).1 (by decide) (.inr (by decide)) e.symm)⟩
  have hc := h.ctlOk
  have hnew : ∀ c, c ∈ pre ++ ⟨x, S, true, false⟩ :: post →
      c = ⟨x, S, true, false⟩ ∨ (c ∈ bs ∧ c ≠ ⟨x, S, false, false⟩) := by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact .inr ⟨mem_of_pre hbs hc, h.ne_of_pre hbs hc⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact .inl rfl
      · exact .inr ⟨mem_of_post hbs hc, h.ne_of_post hbs hc⟩
  have hold : ∀ c ∈ bs, c = ⟨x, S, false, false⟩ ∨ c ∈ pre ++ ⟨x, S, true, false⟩ :: post := by
    intro c hc
    rw [hbs] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact .inr (List.mem_append_left _ hc)
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact .inl rfl
      · exact .inr (List.mem_append_right _ (List.mem_cons_of_mem _ hc))
  have kc : ∀ k, InCtl self k → upd m x (S + 1#64) k = m k := fun k hk =>
    upd_ne (fun e => h.ne_ctl0 hbA hk e.symm)
  refine ⟨?_, ⟨h.layout.1, h.layout.2.1, fun c hc => ?_⟩, fun f s hf hs => ?_, fun f s => ?_,
    fun c hc hu _ => ?_, fun f s z hz => ?_, h.range, h.nodup, fun f s hf hs => ?_,
    fun f hf => ?_⟩
  · have hch := h.chain
    rw [hbs] at hch
    obtain ⟨a', p', hseg, hc⟩ := (chain_append (List.cons_ne_nil _ _)).mp hch
    refine (chain_append (List.cons_ne_nil _ _)).mpr ⟨a', p', hseg.congr fun c hc =>
      keep c (mem_of_pre hbs hc) (h.ne_of_pre hbs hc), ?_⟩
    obtain ⟨h1, _, h3, h4, h5, h6⟩ := hc
    simp only [Bool.false_eq_true, if_false] at h1 h4 h5 h6
    subst h1
    refine ⟨rfl, ?_, ?_, h4, h5, ?_⟩
    · rw [upd_same]; exact hdr_used h4
    · rw [upd_ne (by bv_omega)]; exact h3
    · simp only [Bool.false_eq_true, if_false]
      exact h6.congr fun c hc => keep c (mem_of_post hbs hc) (h.ne_of_post hbs hc)
  · rcases hnew c hc with rfl | ⟨hc, _⟩
    · exact h.layout.2.2 ⟨x, S, false, false⟩ hb
    · exact h.layout.2.2 c hc
  · rw [kc _ (headAddr_inCtl hc hf hs)]; exact h.heads f s hf hs
  · exact (h.links f s).congr fun z hz =>
      ⟨upd_ne (fun e => key_ne0 hbA.1 (h.nodeA hz).1 (by decide) (.inr (by decide)) e.symm),
        upd_ne (fun e => key_ne0 hbA.1 (h.nodeA hz).1 (by decide) (.inr (by decide)) e.symm)⟩
  · rcases hnew c hc with rfl | ⟨hc, hne⟩
    · simp at hu
    · exact h.filed c hc hu fun o => o.elim id fun e => hne (h.uniq hc hb e)
  · obtain ⟨ho, b0, hb0, rfl, hu, hf, hs⟩ := h.members f s z hz
    refine ⟨id, b0, ?_, rfl, hu, hf, hs⟩
    rcases hold b0 hb0 with rfl | hb0'
    · exact (ho (.inr rfl)).elim
    · exact hb0'
  · rw [kc _ (slBm_inCtl hc hf)]; exact h.slbm f s hf hs
  · rw [kc _ (flBm_inCtl hc), kc _ (slBm_inCtl hc hf)]; exact h.flbm f hf

set_option maxHeartbeats 4000000 in
/-- **Splitting a detached free block**: the front `N` bytes become used, the rest a free
    block filed in its class. -/
theorem split (h : Shape self base m bs L (fun a => False ∨ a = x)) {pre post : List Blk}
    {S N : Word} (hbs : bs = pre ++ ⟨x, S, false, false⟩ :: post) (hN : N &&& 31#64 = 0#64)
    (hN32 : 32#64 ≤ N) (hNS : N < S) :
    Shape self base (splitMem self m x S N)
      (pre ++ ⟨x, N, true, false⟩ :: ⟨x + N, S - N, false, false⟩ :: post)
      (Lset L (flOf (S - N)) (slOf (S - N)) ((x + N) :: L (flOf (S - N)) (slOf (S - N))))
      (fun _ => False) := by
  have hb : (⟨x, S, false, false⟩ : Blk) ∈ bs := by
    rw [hbs]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have hbA := h.blkA hb
  obtain ⟨_, _, hxS, hS31, hSok⟩ := h.blk hb
  dsimp only at hxS hS31 hSok hbA
  have hc := h.ctlOk
  obtain ⟨hR31, hRok⟩ := rem_ok hS31 hSok hN hNS
  have hf2 := flOf_lt hRok
  have hs2 := slOf_lt (S - N)
  generalize hf2e : flOf (S - N) = f2 at *
  generalize hs2e : slOf (S - N) = s2 at *
  -- Sizes and addresses as numbers.
  have hN1 : 32 ≤ N.toNat := by rw [BitVec.le_def] at hN32; simpa using hN32
  have hN2 : N.toNat < S.toNat := by rw [BitVec.lt_def] at hNS; exact hNS
  have hR : (S - N).toNat = S.toNat - N.toNat := by rw [BitVec.toNat_sub]; omega
  have hR1 := sz_ge hRok
  have hlay := h.layout.1
  have hxb := hbA.2.1
  have hx40 := hbA.2.2
  have t1 : (x + S + 8#64).toNat = x.toNat + S.toNat + 8 := by
    rw [BitVec.toNat_add, BitVec.toNat_add]; simp; omega
  have tS : (x + S).toNat = x.toNat + S.toNat := by rw [BitVec.toNat_add]; omega
  have ty : (x + N).toNat = x.toNat + N.toNat := by rw [BitVec.toNat_add]; omega
  have ty8 : (x + N + 8#64).toNat = x.toNat + N.toNat + 8 := by
    rw [BitVec.toNat_add, ty]; simp; omega
  have ty16 : (x + N + 0x10#64).toNat = x.toNat + N.toNat + 16 := by
    rw [BitVec.toNat_add, ty]; simp; omega
  have ty24 : (x + N + 0x18#64).toNat = x.toNat + N.toNat + 24 := by
    rw [BitVec.toNat_add, ty]; simp; omega
  have tH := headAddr_toNat hc hf2 hs2
  have tFL := flBm_toNat hc
  have tSL := slBm_toNat hc hf2
  have hf2n := lt64 hf2
  have hs2n := lt64 hs2
  simp only [ctlSize] at hlay
  -- The next block.
  have hch := h.chain
  rw [hbs] at hch
  obtain ⟨a', p', hseg, hcb⟩ := (chain_append (List.cons_ne_nil _ _)).mp hch
  obtain ⟨h1, _, hx8, _, _, hrest⟩ := hcb
  simp only [Bool.false_eq_true, if_false] at h1 hrest
  subst h1
  cases post with
  | nil => exact hrest.elim
  | cons c post' =>
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := hrest
  -- The head of the remainder's list.
  have hh2 := h.heads f2 s2 hf2 hs2
  generalize hh2e : (L f2 s2).headD 0#64 = h2 at hh2
  have hh2n : h2 ≠ 0#64 → h2 ∈ L f2 s2 ∧ (h2.toNat + 32 ≤ x.toNat ∨ x.toNat + S.toNat ≤ h2.toNat) ∧
      h2.toNat < 2 ^ 40 ∧ A32 h2 ∧ base.toNat ≤ h2.toNat := by
    intro hne
    have hm : h2 ∈ L f2 s2 := by
      cases hl : L f2 s2 with
      | nil => rw [hl] at hh2e; exact (hne hh2e.symm).elim
      | cons z zs => rw [hl] at hh2e; rw [← hh2e]; exact List.mem_cons_self ..
    obtain ⟨ho, c2, hc2m, rfl, _, _, _⟩ := h.members f2 s2 h2 hm
    have hne2 : c2 ≠ ⟨x, S, false, false⟩ := fun e => ho (.inr (by rw [e]))
    have := h.disj hc2m hb hne2
    have := sz_ge (h.blk hc2m).2.2.2.2
    have := h.blkA hc2m
    exact ⟨hm, by simp only at *; omega, this.2.2, this.1, this.2.1⟩
  have t7 : h2 ≠ 0#64 → (h2 + 0x18#64).toNat = h2.toNat + 24 := fun hne => by
    have := (hh2n hne).2.2.1
    rw [BitVec.toNat_add]; simp; omega
  -- The new memory, key by key.
  have hread : upd m (x + S + 8#64) (x + N) (headAddr self f2 s2) = h2 := by
    rw [upd_ne (by kd)]; exact hh2
  have e_other : ∀ a, a ≠ x + S + 8#64 → a ≠ headAddr self f2 s2 → a ≠ x + N →
      a ≠ x + N + 8#64 → a ≠ x + N + 0x10#64 → a ≠ x + N + 0x18#64 →
      (h2 ≠ 0#64 → a ≠ h2 + 0x18#64) → a ≠ flBm self → a ≠ slBm self f2 → a ≠ x →
      splitMem self m x S N a = m a := by
    intro a d1 d2 d3 d4 d5 d6 d7 d8 d9 d10
    simp only [splitMem, hf2e, hs2e, hread]
    by_cases hz : h2 = 0#64
    · rw [if_pos hz]; uev
    · have d7 := d7 hz
      rw [if_neg hz]; uev
  have e1 : splitMem self m x S N (x + S + 8#64) = x + N := by
    simp only [splitMem, hf2e, hs2e, hread]
    by_cases hz : h2 = 0#64
    · rw [if_pos hz]; uev
    · obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; rw [if_neg hz]; uev
  have e2 : splitMem self m x S N (headAddr self f2 s2) = x + N := by
    simp only [splitMem, hf2e, hs2e, hread]
    by_cases hz : h2 = 0#64
    · rw [if_pos hz]; uev
    · obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; rw [if_neg hz]; uev
  have e3 : splitMem self m x S N (x + N) = S - N := by
    simp only [splitMem, hf2e, hs2e, hread]
    by_cases hz : h2 = 0#64
    · rw [if_pos hz]; uev
    · obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; rw [if_neg hz]; uev
  have e4 : splitMem self m x S N (x + N + 8#64) = x := by
    simp only [splitMem, hf2e, hs2e, hread]
    by_cases hz : h2 = 0#64
    · rw [if_pos hz]; uev
    · obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; rw [if_neg hz]; uev
  have e5 : splitMem self m x S N (x + N + 0x10#64) = h2 := by
    simp only [splitMem, hf2e, hs2e, hread]
    by_cases hz : h2 = 0#64
    · rw [if_pos hz]; uev
    · obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; rw [if_neg hz]; uev
  have e6 : splitMem self m x S N (x + N + 0x18#64) = 0#64 := by
    simp only [splitMem, hf2e, hs2e, hread]
    by_cases hz : h2 = 0#64
    · rw [if_pos hz]; uev
    · obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; rw [if_neg hz]; uev
  have e8 : splitMem self m x S N (flBm self) = m (flBm self) ||| 1#64 <<< f2.toNat := by
    simp only [splitMem, hf2e, hs2e, hread]
    by_cases hz : h2 = 0#64
    · rw [if_pos hz]; uev
    · obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; rw [if_neg hz]; uev
  have e9 : splitMem self m x S N (slBm self f2) = m (slBm self f2) ||| 1#64 <<< s2.toNat := by
    simp only [splitMem, hf2e, hs2e, hread]
    by_cases hz : h2 = 0#64
    · rw [if_pos hz]; uev
    · obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; rw [if_neg hz]; uev
  have e10 : splitMem self m x S N (x) = N + 1#64 := by
    simp only [splitMem, hf2e, hs2e, hread]
    by_cases hz : h2 = 0#64
    · rw [if_pos hz]; uev
    · obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; rw [if_neg hz]; uev
  have e7 : h2 ≠ 0#64 → splitMem self m x S N (h2 + 0x18#64) = x + N := by
    intro hz
    obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz
    simp only [splitMem, hf2e, hs2e, hread]
    rw [if_neg hz]; uev
  generalize splitMem self m x S N = m2 at e_other e1 e2 e3 e4 e5 e6 e7 e8 e9 e10
  have hxm := A32.mod hbA.1
  have hSm := A32.mod hS31
  have hNm := A32.mod hN
  have hcb : c ∈ bs := by rw [hbs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hcsz := sz_ge (h.blk hcb).2.2.2.2
  -- Where any other block lies, as numbers.
  have blkN : ∀ d ∈ bs, d ≠ ⟨x, S, false, false⟩ →
      d.a.toNat % 32 = 0 ∧ (d.a.toNat + d.sz.toNat ≤ x.toNat ∨ x.toNat + S.toNat ≤ d.a.toNat) ∧
      (d ≠ c → d.a.toNat + d.sz.toNat ≤ x.toNat + S.toNat ∨
        x.toNat + S.toNat + c.sz.toNat ≤ d.a.toNat) ∧
      base.toNat ≤ d.a.toNat ∧ d.a.toNat + d.sz.toNat < 2 ^ 40 ∧ 32 ≤ d.sz.toNat ∧
      (d.a + 8#64).toNat = d.a.toNat + 8 ∧ (d.a + 0x10#64).toNat = d.a.toNat + 16 ∧
      (d.a + 0x18#64).toNat = d.a.toNat + 24 := by
    intro d hd hne
    obtain ⟨hdA, hdb, hd40, _, hdok⟩ := h.blk hd
    have := sz_ge hdok
    have h1 := h.disj hd hb hne
    simp only at h1
    refine ⟨A32.mod hdA, by omega, fun hdc => ?_, hdb, hd40, this, ?_, ?_, ?_⟩
    · have := h.disj hd hcb hdc
      rw [hc1, tS] at this; omega
    all_goals rw [BitVec.toNat_add]; simp; omega
  -- The new chain's blocks: the two halves, or an old one other than the split block.
  have hnew : ∀ d ∈ pre ++ ⟨x, N, true, false⟩ :: ⟨x + N, S - N, false, false⟩ :: c :: post',
      d = ⟨x, N, true, false⟩ ∨ d = ⟨x + N, S - N, false, false⟩ ∨
        (d ∈ bs ∧ d ≠ ⟨x, S, false, false⟩) := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact .inr (.inr ⟨mem_of_pre hbs hd, h.ne_of_pre hbs hd⟩)
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact .inl rfl
      rcases List.mem_cons.mp hd with rfl | hd
      · exact .inr (.inl rfl)
      exact .inr (.inr ⟨mem_of_post hbs hd, h.ne_of_post hbs hd⟩)
  have hold : ∀ d ∈ bs, d ≠ ⟨x, S, false, false⟩ →
      d ∈ pre ++ ⟨x, N, true, false⟩ :: ⟨x + N, S - N, false, false⟩ :: c :: post' := by
    intro d hd hne
    rw [hbs] at hd
    rcases List.mem_append.mp hd with hd | hd
    · exact List.mem_append_left _ hd
    · rcases List.mem_cons.mp hd with rfl | hd
      · exact (hne rfl).elim
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd))
  -- Nodes of the free lists are other blocks.
  have nodeN : ∀ f s z, z ∈ L f s → ∃ d ∈ bs, d ≠ ⟨x, S, false, false⟩ ∧ d.a = z := by
    intro f s z hz
    obtain ⟨ho, d, hd, rfl, _⟩ := h.members f s z hz
    exact ⟨d, hd, fun e => ho (.inr (by rw [e])), rfl⟩
  -- The remainder is no node.
  have hy_not : ∀ f s, x + N ∉ L f s := by
    intro f s hy
    obtain ⟨d, hd, hne, he⟩ := nodeN f s _ hy
    obtain ⟨hdm, h1, -⟩ := blkN d hd hne
    rw [he, ty] at h1; omega
  have tx8 : (x + 8#64).toNat = x.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  have tcS : c.a.toNat = x.toNat + S.toNat := by rw [hc1, tS]
  -- Facts for a node `w` of a list, as numbers; `w` is not `h2` when it is not `h2`.
  have nodeF : ∀ f s w, w ∈ L f s → ∃ d ∈ bs, d.a = w ∧ d.a.toNat % 32 = 0 ∧
      (d.a.toNat + d.sz.toNat ≤ x.toNat ∨ x.toNat + S.toNat ≤ d.a.toNat) ∧
      base.toNat ≤ d.a.toNat ∧ d.a.toNat + d.sz.toNat < 2 ^ 40 ∧ 32 ≤ d.sz.toNat ∧
      (d.a + 0x10#64).toNat = d.a.toNat + 16 ∧ (d.a + 0x18#64).toNat = d.a.toNat + 24 := by
    intro f s w hw
    obtain ⟨d, hd, hne, rfl⟩ := nodeN f s w hw
    obtain ⟨a1, a2, -, a4, a5, a6, -, a8, a9⟩ := blkN d hd hne
    exact ⟨d, hd, rfl, a1, a2, a4, a5, a6, a8, a9⟩
  have h2mem : h2 ≠ 0#64 → h2 ∈ L f2 s2 := fun hz => (hh2n hz).1
  refine ⟨?_, ⟨h.layout.1, h.layout.2.1, fun d hd => ?_⟩, fun f s hf hs => ?_, fun f s => ?_,
    fun d hd hu _ => ?_, fun f s z hz => ?_, fun f s hne => ?_, fun f s => ?_,
    fun f s hf hs => ?_, fun f hf => ?_⟩
  · -- chain
    refine (chain_append (List.cons_ne_nil _ _)).mpr ⟨x, p', hseg.congr fun d hd => ?_, ?_⟩
    · obtain ⟨_, _, _, _, _, _, _, _, _⟩ := blkN d (mem_of_pre hbs hd) (h.ne_of_pre hbs hd)
      have := (h.around hbs).1 d hd
      simp only at this
      exact ⟨by (rw [e_other (d.a)]; any_goals (first | kd | (intro hz; obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; have := A32.mod (hh2n hz).2.2.2.1; kd))), by (rw [e_other (d.a + 8#64)]; any_goals (first | kd | (intro hz; obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; have := A32.mod (hh2n hz).2.2.2.1; kd)))⟩
    · refine ⟨rfl, ?_, ?_, hN, ⟨hN32, lt_pow40 hNS hSok.2⟩, ?_⟩
      · rw [e10]; exact hdr_used hN
      · (rw [e_other (x + 8#64)]; any_goals (first | kd | (intro hz; obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; have := A32.mod (hh2n hz).2.2.2.1; kd)))
        try exact hx8
      · simp only [Bool.false_eq_true, if_false]
        refine ⟨rfl, ?_, e4, hR31, hRok, ?_⟩
        · rw [e3]; exact hdr_free
        · simp only [Bool.false_eq_true, if_false]
          rw [add_sub_cancel']
          refine ⟨hc1, ?_, e1, hc4, hc5, ?_⟩
          · (rw [e_other (x + S)]; any_goals (first | kd | (intro hz; obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; have := A32.mod (hh2n hz).2.2.2.1; kd)))
            try exact hc2
          · have hsorted := h.around (pre := pre ++ [⟨x, S, false, false⟩]) (post := post') (b := c)
              (by rw [hbs]; simp)
            by_cases hl : c.last = true
            · rw [if_pos hl] at hc6 ⊢; exact hc6
            · rw [if_neg hl] at hc6 ⊢
              refine hc6.congr fun d hd => ?_
              have hdb : d ∈ bs := by
                rw [hbs]; exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd))
              have hdc := hsorted.2 d hd
              have hne : d ≠ ⟨x, S, false, false⟩ := fun e => by
                rw [e] at hdc; simp only at hdc; omega
              obtain ⟨_, _, _, _, _, _, _, _, _⟩ := blkN d hdb hne
              exact ⟨by (rw [e_other (d.a)]; any_goals (first | kd | (intro hz; obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; have := A32.mod (hh2n hz).2.2.2.1; kd))), by (rw [e_other (d.a + 8#64)]; any_goals (first | kd | (intro hz; obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; have := A32.mod (hh2n hz).2.2.2.1; kd)))⟩
  · -- layout
    rcases hnew d hd with rfl | rfl | ⟨hdb, _⟩
    · simp only; omega
    · simp only; rw [ty, hR]; omega
    · exact h.layout.2.2 d hdb
  · -- heads
    unfold Lset
    by_cases he : f = f2 ∧ s = s2
    · rw [if_pos he, he.1, he.2, e2]; rfl
    · rw [if_neg he]
      have tH' := headAddr_toNat hc hf hs
      have := lt64 hf; have := lt64 hs
      have : f.toNat ≠ f2.toNat ∨ s.toNat ≠ s2.toNat := by
        by_cases e1 : f.toNat = f2.toNat
        · exact .inr fun e2 => he ⟨BitVec.eq_of_toNat_eq e1, BitVec.eq_of_toNat_eq e2⟩
        · exact .inl e1
      (rw [e_other (headAddr self f s)]; any_goals (first | kd | (intro hz; obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; have := A32.mod (hh2n hz).2.2.2.1; kd)))
      exact h.heads f s hf hs
  · -- links
    unfold Lset
    by_cases he : f = f2 ∧ s = s2
    · rw [if_pos he]
      refine ⟨e6, by rw [e5]; exact hh2e.symm, ?_⟩
      cases hl : L f2 s2 with
      | nil => trivial
      | cons z zs =>
        have hz0 : z = h2 := by rw [hl] at hh2e; exact hh2e
        subst hz0
        have hzL : z ∈ L f2 s2 := by rw [hl]; exact List.mem_cons_self ..
        have hzne := h.node_ne_zero hzL
        have hdll := h.links f2 s2
        rw [hl] at hdll
        obtain ⟨-, hz10, hzs⟩ := hdll
        have hnd := h.nodup f2 s2
        rw [hl] at hnd
        refine ⟨e7 hzne, ?_, hzs.congr fun w hw => ?_⟩
        · obtain ⟨d, _, hdz, _, _, _, _, _, _, _⟩ := nodeF _ _ _ hzL
          subst hdz
          (rw [e_other (d.a + 0x10#64)]; any_goals (first | kd | (intro hz; obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; have := A32.mod (hh2n hz).2.2.2.1; kd)))
          try exact hz10
        · have hwL : w ∈ L f2 s2 := by rw [hl]; exact List.mem_cons_of_mem _ hw
          have hwz : w.toNat ≠ z.toNat := fun e =>
            (List.nodup_cons.mp hnd).1 (by rw [← BitVec.eq_of_toNat_eq e]; exact hw)
          obtain ⟨d, _, hdw, _, _, _, _, _, _, _⟩ := nodeF _ _ _ hwL
          subst hdw
          exact ⟨by (rw [e_other (d.a + 0x10#64)]; any_goals (first | kd | (intro hz; obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; have := A32.mod (hh2n hz).2.2.2.1; kd))), by (rw [e_other (d.a + 0x18#64)]; any_goals (first | kd | (intro hz; obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; have := A32.mod (hh2n hz).2.2.2.1; kd)))⟩
    · rw [if_neg he]
      refine (h.links f s).congr fun w hw => ?_
      have hwh : h2 ≠ 0#64 → w.toNat ≠ h2.toNat := by
        intro hz e
        have hw' : h2 ∈ L f s := by rw [← BitVec.eq_of_toNat_eq e]; exact hw
        exact he (h.class_uniq hw' (h2mem hz))
      obtain ⟨d, _, hdw, _, _, _, _, _, _, _⟩ := nodeF _ _ _ hw
      subst hdw
      exact ⟨by (rw [e_other (d.a + 0x10#64)]; any_goals (first | kd | (intro hz; obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; have := hwh hz; have := A32.mod (hh2n hz).2.2.2.1; kd))), by (rw [e_other (d.a + 0x18#64)]; any_goals (first | kd | (intro hz; obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; have := hwh hz; have := A32.mod (hh2n hz).2.2.2.1; kd)))⟩
  · -- filed
    rcases hnew d hd with rfl | rfl | ⟨hdb, hne⟩
    · simp at hu
    · unfold Lset; simp [hf2e, hs2e]
    · have := h.filed d hdb hu (fun o => o.elim id fun e => hne (h.uniq hdb hb e))
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
      · exact ⟨id, ⟨x + N, S - N, false, false⟩,
          List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)), rfl, rfl, hf2e,
          hs2e⟩
      · obtain ⟨ho, d, hd, rfl, hu, hf, hs⟩ := h.members f2 s2 z hz
        exact ⟨id, d, hold d hd (fun e => ho (.inr (by rw [e]))), rfl, hu, hf, hs⟩
    · obtain ⟨ho, d, hd, rfl, hu, hf, hs⟩ := h.members f s z hz
      exact ⟨id, d, hold d hd (fun e => ho (.inr (by rw [e]))), rfl, hu, hf, hs⟩
  · -- range
    unfold Lset at hne
    split at hne
    · rename_i he; rw [he.1, he.2]; exact ⟨hf2, hs2⟩
    · exact h.range f s hne
  · -- nodup
    unfold Lset
    split
    · exact List.nodup_cons.mpr ⟨hy_not f2 s2, h.nodup f2 s2⟩
    · exact h.nodup f s
  · -- second-level bitmaps
    have hs6 := lt64 hs
    unfold Lset
    by_cases he : f = f2
    · subst he
      rw [e9, getLsbD_set _ hs2n]
      by_cases hss : s = s2
      · subst hss; simp
      · have : s.toNat ≠ s2.toNat := fun e => hss (BitVec.eq_of_toNat_eq e)
        rw [if_neg (fun e => hss e.2), h.slbm f s hf hs]; simp [this]
    · have tSL' := slBm_toNat hc hf
      have := lt64 hf
      have : f.toNat ≠ f2.toNat := fun e => he (BitVec.eq_of_toNat_eq e)
      rw [if_neg (fun e => he e.1)]
      (rw [e_other (slBm self f)]; any_goals (first | kd | (intro hz; obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; have := A32.mod (hh2n hz).2.2.2.1; kd)))
      exact h.slbm f s hf hs
  · -- first-level bitmap
    have hf6 := lt64 hf
    rw [e8, getLsbD_set _ hf2n]
    by_cases he : f = f2
    · subst he
      rw [e9]
      have : (m (slBm self f) ||| 1#64 <<< s2.toNat) ≠ 0#64 := fun e => by
        have := congrArg (fun w => w.getLsbD s2.toNat) e
        simp only [getLsbD_set _ hs2n] at this; simp at this
      simp [this]
    · have tSL' := slBm_toNat hc hf
      have : f.toNat ≠ f2.toNat := fun e => he (BitVec.eq_of_toNat_eq e)
      (rw [e_other (slBm self f)]; any_goals (first | kd | (intro hz; obtain ⟨-, _, _, _, _⟩ := hh2n hz; have := t7 hz; have := A32.mod (hh2n hz).2.2.2.1; kd)))
      rw [h.flbm f hf]; simp [this]

end Shape
end Cases.Zip2005.Runtime.Tlsf
