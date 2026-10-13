/-
  Cases.Zip2005.Runtime.Dealloc.Spec

  rlsf's `dealloc` (`0x7801c620`), end to end (phase D4).

  The executor segments (`Dealloc.Exec`) meet the heap model: a free next block leaves its
  list (`Tlsf.Shape.unlink`), so does a free previous block, and the freed block with the
  detached neighbours is filed as one free block (`release`: `Shape.merge` then `Shape.push`,
  in the memory `relMem` the code leaves). `unlink_frame` and `relMem_other` say that nothing
  outside the allocator's own doublewords changes.

  `spec`: from `Rep` and a pointer `alloc` granted for a used block `b` (just past its header,
  or, for a large alignment, with `b`'s address stored below it — `Alloc.Grant`), `dealloc`
  returns with `Rep` re-established, every other used block kept, and memory unchanged
  outside `Alloc.Mine` and `b`'s bytes (`Done`).
-/

import Cases.Zip2005.Runtime.Dealloc.Exec
import Cases.Zip2005.Runtime.Alloc.Spec

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Cases.Zip2005.Runtime.Dealloc

open RiscvZkvm.Rv64
open AsmVerif.RiscV AsmVerif.RiscV.Frame AsmVerif.RiscV.Check AsmVerif.RiscV.Exec
  Cases.Zip2005.Image

open Tlsf in
/-- **Freeing**: consecutive blocks `c :: cs`, each used or detached, reaching `q`, become one
    free block filed at the head of its class — in the memory `dealloc` leaves. -/
theorem release {self base : Word} {m : Word → Word} {bs : List Blk} {L : Word → Word → List Word}
    {out : Word → Prop} (h : Shape self base m bs L out) {pre cs post : List Blk} {c q : Blk}
    {S : Word} (hbs : bs = pre ++ (c :: cs) ++ q :: post)
    (hcs : ∀ d ∈ c :: cs, d.used = true ∨ out d.a) (hS : c.a + S = q.a)
    (hout : ∀ d ∈ pre ++ q :: post, ¬ out d.a) :
    Shape self base (relMem self m c.a S q.a) (pre ++ ⟨c.a, S, false, false⟩ :: q :: post)
      (Lset L (flOf S) (slOf S) (c.a :: L (flOf S) (slOf S))) (fun _ => False) := by
  have hm := h.merge hbs hcs hS
  have hbm : (⟨c.a, S, false, false⟩ : Blk) ∈ pre ++ ⟨c.a, S, false, false⟩ :: q :: post := by simp
  have hqm : q ∈ bs := by rw [hbs]; simp
  have hcm : c ∈ bs := by rw [hbs]; simp
  -- Numbers.
  have hc := h.ctlOk
  have hlay := h.layout.1
  simp only [ctlSize] at hlay
  have hcA := h.blkA hcm
  have hqA := h.blkA hqm
  obtain ⟨-, -, hS40, hS31, hSok⟩ := hm.blk hbm
  simp only at hS40 hS31 hSok
  have hSge := Shape.sz_ge hSok
  have hf := flOf_lt hSok
  have hs := slOf_lt S
  have hqS : q.a.toNat = c.a.toNat + S.toNat := by rw [← hS, BitVec.toNat_add]; omega
  have tH := headAddr_toNat hc hf hs
  have tFL := flBm_toNat hc
  have tSL := slBm_toNat hc hf
  have hf6 := lt64 hf
  have hs6 := lt64 hs
  have t10 : (c.a + 0x10#64).toNat = c.a.toNat + 16 := by rw [BitVec.toNat_add]; simp; omega
  have t18 : (c.a + 0x18#64).toNat = c.a.toNat + 24 := by rw [BitVec.toNat_add]; simp; omega
  have tq8 : (q.a + 8#64).toNat = q.a.toNat + 8 := by rw [BitVec.toNat_add]; simp; omega
  have hcm32 := A32.mod hcA.1
  -- The old head of the class.
  generalize hhe : m (headAddr self (flOf S) (slOf S)) = hd
  have hhd : hd = (L (flOf S) (slOf S)).headD 0#64 := by rw [← hhe]; exact h.heads _ _ hf hs
  have hdN : hd ≠ 0#64 → hd ∈ L (flOf S) (slOf S) := fun hz => by
    cases hl : L (flOf S) (slOf S) with
    | nil => rw [hl] at hhd; exact (hz hhd).elim
    | cons z zs => rw [hl] at hhd; rw [hhd]; simp
  have hdF : hd ≠ 0#64 → hd.toNat % 32 = 0 ∧ base.toNat ≤ hd.toNat ∧ hd.toNat < 2 ^ 40 ∧
      hd.toNat ≠ c.a.toNat ∧ (hd + 0x18#64).toNat = hd.toNat + 24 := fun hz => by
    have hn := hdN hz
    have hA := h.nodeA hn
    obtain ⟨ho, d, hd, hda, hdu, -⟩ := h.members _ _ _ hn
    refine ⟨A32.mod hA.1, hA.2.1, hA.2.2, fun e => ?_, by rw [BitVec.toNat_add]; simp; omega⟩
    have he : d.a = c.a := by rw [hda]; exact BitVec.eq_of_toNat_eq e
    have := h.uniq hd hcm he
    subst this
    rcases hcs d (by simp) with hu | ho'
    · rw [hdu] at hu; exact absurd hu (by simp)
    · exact ho (hda ▸ ho')
  -- `relMem`, unfolded, with the old head named.
  have hread : upd m c.a S (headAddr self (flOf S) (slOf S)) = hd := by
    rw [upd_ne (by kd)]; exact hhe
  -- The doublewords `dealloc` writes are distinct.
  have tq := A32.mod hqA.1
  have d_T_T16 : c.a ≠ (c.a + 0x10#64) := by kd
  have d_T_T24 : c.a ≠ (c.a + 0x18#64) := by kd
  have d_T_E8 : c.a ≠ (q.a + 8#64) := by kd
  have d_T_H : c.a ≠ headAddr self (flOf S) (slOf S) := by kd
  have d_T_F : c.a ≠ flBm self := by kd
  have d_T_SL : c.a ≠ slBm self (flOf S) := by kd
  have d_T_Z : c.a ≠ self := by kd
  have d_T16_T24 : (c.a + 0x10#64) ≠ (c.a + 0x18#64) := by kd
  have d_T16_E8 : (c.a + 0x10#64) ≠ (q.a + 8#64) := by kd
  have d_T16_H : (c.a + 0x10#64) ≠ headAddr self (flOf S) (slOf S) := by kd
  have d_T16_F : (c.a + 0x10#64) ≠ flBm self := by kd
  have d_T16_SL : (c.a + 0x10#64) ≠ slBm self (flOf S) := by kd
  have d_T16_Z : (c.a + 0x10#64) ≠ self := by kd
  have d_T24_E8 : (c.a + 0x18#64) ≠ (q.a + 8#64) := by kd
  have d_T24_H : (c.a + 0x18#64) ≠ headAddr self (flOf S) (slOf S) := by kd
  have d_T24_F : (c.a + 0x18#64) ≠ flBm self := by kd
  have d_T24_SL : (c.a + 0x18#64) ≠ slBm self (flOf S) := by kd
  have d_T24_Z : (c.a + 0x18#64) ≠ self := by kd
  have d_E8_H : (q.a + 8#64) ≠ headAddr self (flOf S) (slOf S) := by kd
  have d_E8_F : (q.a + 8#64) ≠ flBm self := by kd
  have d_E8_SL : (q.a + 8#64) ≠ slBm self (flOf S) := by kd
  have d_E8_Z : (q.a + 8#64) ≠ self := by kd
  have d_H_F : headAddr self (flOf S) (slOf S) ≠ flBm self := by kd
  have d_H_SL : headAddr self (flOf S) (slOf S) ≠ slBm self (flOf S) := by kd
  have d_H_Z : headAddr self (flOf S) (slOf S) ≠ self := by kd
  have d_F_SL : flBm self ≠ slBm self (flOf S) := by kd
  have d_F_Z : flBm self ≠ self := by kd
  have d_SL_Z : slBm self (flOf S) ≠ self := by kd
  -- `relMem` at the doublewords the shape needs.
  have hR : ∀ a, (hd ≠ 0#64 → a ≠ hd + 0x18#64) → relMem self m c.a S q.a a =
      if a = self then m self + 1#64
      else if a = slBm self (flOf S) then m (slBm self (flOf S)) ||| 1#64 <<< (slOf S).toNat
      else if a = q.a + 8#64 then c.a
      else if a = flBm self then m (flBm self) ||| 1#64 <<< (flOf S).toNat
      else if a = c.a + 0x18#64 then 0#64
      else if a = c.a + 0x10#64 then hd
      else if a = headAddr self (flOf S) (slOf S) then c.a
      else if a = c.a then S
      else m a := by
    intro a ha
    by_cases hz : hd = 0#64
    · simp only [relMem, upd, hhe, if_pos hz, Ne.symm d_T_H, Ne.symm d_T_F, Ne.symm d_T_SL, Ne.symm d_T_Z, Ne.symm d_T16_F, Ne.symm d_T16_SL, Ne.symm d_T16_Z, Ne.symm d_T24_F, Ne.symm d_T24_SL, Ne.symm d_T24_Z, Ne.symm d_E8_Z, Ne.symm d_H_F, Ne.symm d_H_SL, Ne.symm d_H_Z, Ne.symm d_F_SL, Ne.symm d_F_Z, if_false]
    · have := hdF hz
      have d_D_T : hd + 0x18#64 ≠ c.a := by kd
      have d_D_T16 : hd + 0x18#64 ≠ (c.a + 0x10#64) := by kd
      have d_D_T24 : hd + 0x18#64 ≠ (c.a + 0x18#64) := by kd
      have d_D_E8 : hd + 0x18#64 ≠ (q.a + 8#64) := by kd
      have d_D_H : hd + 0x18#64 ≠ headAddr self (flOf S) (slOf S) := by kd
      have d_D_F : hd + 0x18#64 ≠ flBm self := by kd
      have d_D_SL : hd + 0x18#64 ≠ slBm self (flOf S) := by kd
      have d_D_Z : hd + 0x18#64 ≠ self := by kd
      have ha := ha hz
      simp only [relMem, upd, hhe, if_neg hz, Ne.symm d_T_H, Ne.symm d_T_F, Ne.symm d_T_SL, Ne.symm d_T_Z, Ne.symm d_T16_F, Ne.symm d_T16_SL, Ne.symm d_T16_Z, Ne.symm d_T24_F, Ne.symm d_T24_SL, Ne.symm d_T24_Z, Ne.symm d_E8_Z, Ne.symm d_H_F, Ne.symm d_H_SL, Ne.symm d_H_Z, Ne.symm d_F_SL, Ne.symm d_F_Z, Ne.symm d_D_F, Ne.symm d_D_SL, Ne.symm d_D_Z, if_false,
        ha]
  have hRd : hd ≠ 0#64 → relMem self m c.a S q.a (hd + 0x18#64) = c.a := by
    intro hz
    have := hdF hz
    have d_D_T : hd + 0x18#64 ≠ c.a := by kd
    have d_D_T16 : hd + 0x18#64 ≠ (c.a + 0x10#64) := by kd
    have d_D_T24 : hd + 0x18#64 ≠ (c.a + 0x18#64) := by kd
    have d_D_E8 : hd + 0x18#64 ≠ (q.a + 8#64) := by kd
    have d_D_H : hd + 0x18#64 ≠ headAddr self (flOf S) (slOf S) := by kd
    have d_D_F : hd + 0x18#64 ≠ flBm self := by kd
    have d_D_SL : hd + 0x18#64 ≠ slBm self (flOf S) := by kd
    have d_D_Z : hd + 0x18#64 ≠ self := by kd
    simp only [relMem, upd, hhe, if_neg hz, Ne.symm d_T_H, Ne.symm d_T_F, Ne.symm d_T_SL, Ne.symm d_T_Z, Ne.symm d_T16_F, Ne.symm d_T16_SL, Ne.symm d_T16_Z, Ne.symm d_T24_F, Ne.symm d_T24_SL, Ne.symm d_T24_Z, Ne.symm d_E8_Z, Ne.symm d_H_F, Ne.symm d_H_SL, Ne.symm d_H_Z, Ne.symm d_F_SL, Ne.symm d_F_Z, d_D_T, d_D_T16, d_D_T24, d_D_E8, d_D_H, d_D_F, d_D_SL, d_D_Z, Ne.symm d_D_F, Ne.symm d_D_SL, Ne.symm d_D_Z, if_false,
      if_true]
  have hD : ∀ a, a = headAddr self (flOf S) (slOf S) ∨ a = c.a + 0x10#64 ∨ a = c.a + 0x18#64 ∨
      a = flBm self ∨ a = slBm self (flOf S) → hd ≠ 0#64 → a ≠ hd + 0x18#64 := by
    intro a ha hz
    have := hdF hz
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> kd
  refine hm.push hbm (.inr rfl) (fun d hd' _ ho => ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- only the merged block is detached
    rcases List.mem_append.mp hd' with hd' | hd'
    · exact ho.elim (fun o => (hout d (by simp [hd']) o).elim) id
    · rcases List.mem_cons.mp hd' with rfl | hd'
      · rfl
      · exact ho.elim (fun o => (hout d (by simp only [List.mem_append]; exact .inr hd') o).elim) id
  · rw [hR _ (hD _ (.inl rfl))]; simp only [d_H_F, d_H_SL, d_H_Z, Ne.symm d_T_H, Ne.symm d_T16_H, Ne.symm d_T24_H, Ne.symm d_E8_H, if_true, if_false]
  · rw [hR _ (hD _ (.inr (.inl rfl))), ← hhd]
    simp only [d_T16_T24, d_T16_E8, d_T16_H, d_T16_F, d_T16_SL, d_T16_Z, Ne.symm d_T_T16, if_true, if_false]
  · rw [hR _ (hD _ (.inr (.inr (.inl rfl))))]
    simp only [d_T24_E8, d_T24_H, d_T24_F, d_T24_SL, d_T24_Z, Ne.symm d_T_T24, Ne.symm d_T16_T24, if_true, if_false]
  · intro z zs hl
    have hz : hd ≠ 0#64 := by rw [hhd, hl]; exact h.node_ne_zero (by rw [hl]; simp)
    have : z = hd := by rw [hhd, hl]; rfl
    subst this
    exact hRd hz
  · rw [hR _ (hD _ (.inr (.inr (.inr (.inl rfl)))))]
    simp only [d_F_Z, d_F_SL, Ne.symm d_E8_F, if_true, if_false]
    rw [upd_ne (Ne.symm d_E8_F), upd_ne (Ne.symm d_T_F)]
  · rw [hR _ (hD _ (.inr (.inr (.inr (.inr rfl)))))]
    simp only [d_SL_Z, if_true, if_false]
    rw [upd_ne (Ne.symm d_E8_SL), upd_ne (Ne.symm d_T_SL)]
  · intro a hk h1 h2 h3 h4 h5 h6
    have hz' : hd ≠ 0#64 → a ≠ hd + 0x18#64 := fun hz => by
      cases hl : L (flOf S) (slOf S) with
      | nil => rw [hl] at hhd; exact (hz hhd).elim
      | cons z zs =>
        have : hd = z := by rw [hhd, hl]; rfl
        rw [this]; exact h4 z zs hl
    have hZ : a ≠ self := by
      rcases hk with hk | ⟨d, hd'', hk⟩
      · intro e; have := hk.1; rw [e] at this; omega
      · have hdA := hm.blkA hd''
        intro e
        have te := congrArg BitVec.toNat e
        rcases hk with hk | hk | ⟨-, hk | hk⟩ <;> subst hk <;>
          (try rw [BitVec.toNat_add] at te) <;> (try simp at te) <;> omega
    rw [hR _ hz']
    simp only [hZ, h6, h5, h3, h2, h1, if_false]
    unfold upd
    by_cases e1 : a = q.a + 8#64
    · simp [e1]
    · simp only [e1, if_false]


open Tlsf in
/-- `relMem` leaves alone every doubleword it does not write. -/
theorem relMem_other {self t S e a : Word} {m : Word → Word} (h1 : a ≠ self)
    (h2 : a ≠ slBm self (flOf S)) (h3 : a ≠ e + 8#64) (h4 : a ≠ flBm self) (h5 : a ≠ t + 0x18#64)
    (h6 : a ≠ t + 0x10#64) (h7 : a ≠ headAddr self (flOf S) (slOf S)) (h8 : a ≠ t)
    (h9 : upd m t S (headAddr self (flOf S) (slOf S)) ≠ 0#64 →
      a ≠ upd m t S (headAddr self (flOf S) (slOf S)) + 0x18#64) :
    relMem self m t S e a = m a := by
  by_cases hz : upd m t S (headAddr self (flOf S) (slOf S)) = 0#64
  · simp only [relMem, if_pos hz]
    simp only [upd, h1, h2, h3, h4, h5, h6, h7, h8, if_false]
  · have h9 := h9 hz
    simp only [relMem, if_neg hz]
    simp only [upd] at h9 ⊢
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, if_false]

open Tlsf in
/-- `unlinkMem` leaves alone everything but the control block and its list's links. -/
theorem unlink_other {self base : Word} {m : Word → Word} {bs : List Blk}
    {L : Word → Word → List Word} {out : Word → Prop} (h : Shape self base m bs L out)
    {f s x a : Word} (hx : x ∈ L f s) (ha1 : a ≠ headAddr self f s) (ha2 : a ≠ slBm self f)
    (ha3 : a ≠ flBm self) (hn : ∀ z ∈ L f s, a ≠ z + 0x10#64 ∧ a ≠ z + 0x18#64) :
    unlinkMem self m f s x a = m a := by
  obtain ⟨l1, l2, hL⟩ := List.append_of_mem hx
  have hdll := h.links f s
  rw [hL] at hdll
  obtain ⟨h18, h10⟩ := Dll.mid hdll
  have h18' : m (x + 0x18#64) = l1.getLast?.getD 0#64 := h18
  have h10' : m (x + 0x10#64) = l2.headD 0#64 := h10
  generalize hnf : l2.headD 0#64 = nf at h10'
  generalize hpf : l1.getLast?.getD 0#64 = pf at h18'
  have hnfL : nf ≠ 0#64 → nf ∈ L f s := fun hz => by
    cases l2 with
    | nil => exact (hz hnf.symm).elim
    | cons z zs => rw [hL, ← hnf]; simp
  have hpfL : pf ≠ 0#64 → pf ∈ L f s := fun hz => by
    rcases List.eq_nil_or_concat l1 with rfl | ⟨l1', z, rfl⟩
    · exact (hz hpf.symm).elim
    · rw [hL, ← hpf]; simp
  rw [Dealloc.unlinkMem_eq]
  simp only [h10', h18']
  by_cases hn0 : nf = 0#64
  · by_cases hp0 : pf = 0#64
    · simp only [if_pos hn0, if_pos hp0, popTail]
      split <;> simp only [upd, ha1, ha2, ha3, if_false]
    · simp only [if_pos hn0, if_neg hp0, upd, (hn _ (hpfL hp0)).1, if_false]
  · have e1 := (hn _ (hnfL hn0)).2
    by_cases hp0 : pf = 0#64
    · simp only [if_neg hn0, if_pos hp0, popTail, upd, e1, ha1, if_false]
    · simp only [if_neg hn0, if_neg hp0, upd, e1, (hn _ (hpfL hp0)).1, if_false]

open Tlsf in
/-- The lock after `relMem`: one more than before. -/
theorem relMem_self {self t S e : Word} {m : Word → Word}
    (h3 : self ≠ e + 8#64) (h4 : self ≠ flBm self) (h5 : self ≠ t + 0x18#64)
    (h6 : self ≠ t + 0x10#64) (h7 : self ≠ headAddr self (flOf S) (slOf S)) (h8 : self ≠ t)
    (h9 : upd m t S (headAddr self (flOf S) (slOf S)) ≠ 0#64 →
      self ≠ upd m t S (headAddr self (flOf S) (slOf S)) + 0x18#64) :
    relMem self m t S e self = m self + 1#64 := by
  have hs : ∀ v, upd (upd (rel5 self m t S e) (slBm self (flOf S)) v) self
      (rel5 self m t S e self + 1#64) self = rel5 self m t S e self + 1#64 := fun _ => upd_same ..
  rw [relMem_eq, hs]
  congr 1
  unfold rel5 rel4 rel3
  by_cases hz : upd m t S (headAddr self (flOf S) (slOf S)) = 0#64
  · simp only [if_pos hz]
    simp only [upd, h3, h4, h5, h6, h7, h8, if_false]
  · have h9 := h9 hz
    simp only [if_neg hz]
    simp only [upd] at h9 ⊢
    simp only [h3, h4, h5, h6, h7, h8, h9, if_false]

/-- What `dealloc`'s caller gets back: the return (`Out`) with memory `M'`; the heap well formed
    again, with every other used block kept; and nothing changed but the allocator's own
    doublewords and the freed block. -/
def Done (s0 : MachineState) (base : Word) (bs : List Tlsf.Blk) (b : Tlsf.Blk)
    (t : MachineState) : Prop :=
  ∃ M', Out s0 M' t ∧ ∃ bs' L', Tlsf.Rep (s0.getReg .x10) base M' bs' L' ∧
    (∀ c ∈ bs, c.used = true → c ≠ b → c ∈ bs') ∧
    (∀ a, ¬ Alloc.Mine (s0.getReg .x10) bs a →
      ¬ (b.a.toNat ≤ a.toNat ∧ a.toNat < b.a.toNat + b.sz.toNat) → M' a = s0.getMem a)

theorem notMine_ctl {self a k : Word} {bs : List Tlsf.Blk} (ha : ¬ Alloc.Mine self bs a)
    (hk : Tlsf.InCtl self k ∨ k = self) : a ≠ k := by
  rintro rfl
  apply ha
  left
  rcases hk with hk | rfl
  · exact ⟨by have := hk.1; omega, hk.2⟩
  · exact ⟨Nat.le_refl _, by simp [Tlsf.ctlSize]⟩

theorem notMine_blk {self a : Word} {bs : List Tlsf.Blk} {d : Tlsf.Blk} (ha : ¬ Alloc.Mine self bs a)
    (hd : d ∈ bs) (hu : d.used = false) {c : Word} (hc : c.toNat < d.sz.toNat)
    (hw : d.a.toNat + d.sz.toNat < 2 ^ 40) : a ≠ d.a + c := by
  rintro rfl
  apply ha
  right
  refine ⟨d, hd, .inr ⟨hu, ?_, ?_⟩⟩ <;> rw [BitVec.toNat_add] <;> omega

theorem notMine_8 {self a : Word} {bs : List Tlsf.Blk} {d : Tlsf.Blk} (ha : ¬ Alloc.Mine self bs a)
    (hd : d ∈ bs) : a ≠ d.a + 8#64 := by
  rintro rfl
  exact ha (.inr ⟨d, hd, .inl rfl⟩)

/-- From `0x7801c818`, with the neighbours unlinked: file the merged block `c :: cs` (which
    holds `b`) and return. -/
theorem finish {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    {M3 : Word → Word} {base : Word} {bs : List Tlsf.Blk} {L3 : Word → Word → List Word}
    {out3 : Word → Prop} {pre0 cs rest : List Tlsf.Blk} {b c r : Tlsf.Blk} {S : Word}
    (hs : St s0 M3 y) (hpc : y.pc = 0x7801c818#64)
    (hsh : Tlsf.Shape (s0.getReg .x10) base M3 bs L3 out3)
    (hbs : bs = pre0 ++ (c :: cs) ++ r :: rest)
    (hcs : ∀ d ∈ c :: cs, d.used = true ∨ out3 d.a) (hS : c.a + S = r.a)
    (hout : ∀ d ∈ pre0 ++ r :: rest, ¬ out3 d.a)
    (hlock : M3 (s0.getReg .x10) = 0xffffffffffffffff#64)
    (hbin : b ∈ c :: cs) (hothers : ∀ d ∈ c :: cs, d ≠ b → d.used = false)
    (hfr : ∀ a, ¬ Alloc.Mine (s0.getReg .x10) bs a →
      ¬ (b.a.toNat ≤ a.toNat ∧ a.toNat < b.a.toNat + b.sz.toNat) → M3 a = s0.getMem a)
    (hsp : 0x20 ≤ (s0.getReg .x2).toNat) (hspc : (s0.getReg .x2).toNat ≤ (s0.getReg .x10).toNat)
    (r10 : y.getReg .x10 = r.a) (r11 : y.getReg .x11 = S) (r12 : y.getReg .x12 = c.a)
    (hk : ∀ t, Done s0 base bs b t → SafeN G n P t) : SafeN G n P y := by
  have hc := hsh.ctlOk
  have hlay := hsh.layout.1
  simp only [Tlsf.ctlSize] at hlay
  have hbs' : bs = pre0 ++ c :: (cs ++ r :: rest) := by rw [hbs]; simp
  have hcm : c ∈ bs := by rw [hbs']; simp
  have hrm : r ∈ bs := by rw [hbs]; simp
  have hbm : b ∈ bs := by rw [hbs]; exact List.mem_append_left _ (List.mem_append_right _ hbin)
  have hcA := hsh.blkA hcm
  have hrA := hsh.blkA hrm
  have hcr : c.a.toNat + c.sz.toNat ≤ r.a.toNat := (hsh.around hbs').2 r (by simp)
  have hcsz := Tlsf.Shape.sz_ge (hsh.blk hcm).2.2.2.2
  have hbsz := Tlsf.Shape.sz_ge (hsh.blk hbm).2.2.2.2
  have hb40 := hsh.layout.2.2 b hbm
  have hr40 := hsh.layout.2.2 r hrm
  have hSn : S.toNat = r.a.toNat - c.a.toNat := by
    have : S = r.a - c.a := by rw [← hS]; bv_omega
    rw [this, BitVec.toNat_sub]; omega
  have hSok : Tlsf.SizeOk S := by
    constructor
    · rw [BitVec.le_def]; simp; omega
    · rw [BitVec.lt_def]; simp; omega
  have hS0 : S ≠ 0#64 := fun e => by rw [e] at hSn; simp at hSn; omega
  have hf := Tlsf.flOf_lt hSok
  have hsl := Tlsf.slOf_lt S
  have offA : ∀ z k : Word, (s0.getReg .x10).toNat ≤ z.toNat → z.toNat < 2 ^ 40 → k.toNat < 32 →
      ¬ InFrame (s0.getReg .x2) (z + k) := fun z k h1 h2 h3 =>
    offN hspc (by rw [BitVec.toNat_add]; omega)
  have hH := Tlsf.headAddr_inCtl hc hf hsl
  -- The old head of the merged block's class.
  have hhd : Tlsf.upd M3 c.a S (Tlsf.headAddr (s0.getReg .x10) (Tlsf.flOf S) (Tlsf.slOf S)) =
      (L3 (Tlsf.flOf S) (Tlsf.slOf S)).headD 0#64 := by
    rw [Tlsf.upd_ne (fun e => hsh.ne_ctl0 hcA hH e.symm)]; exact hsh.heads _ _ hf hsl
  have hdN : ∀ hd, hd = (L3 (Tlsf.flOf S) (Tlsf.slOf S)).headD 0#64 → hd ≠ 0#64 →
      hd ∈ L3 (Tlsf.flOf S) (Tlsf.slOf S) := fun hd e hz => by
    cases hl : L3 (Tlsf.flOf S) (Tlsf.slOf S) with
    | nil => rw [hl] at e; exact (hz e).elim
    | cons z zs => rw [hl] at e; rw [e]; simp
  refine relSeg hs hpc hsp hspc hc hS0 hf r10 r11 r12
    (fun k hk => offA _ _ (by omega) hcA.2.2 hk) (offA _ _ (by omega) hrA.2.2 (by decide))
    (fun hz => by
      rw [hhd] at hz ⊢
      have := hsh.nodeA (hdN _ rfl hz)
      exact offA _ _ (by omega) this.2.2 (by decide)) ?_
  intro t ht
  have hrel := release hsh hbs hcs hS hout
  refine hk t ⟨_, ht, _, _, Tlsf.rep_iff.mpr ⟨?_, hrel⟩, fun d hd hu hne => ?_, fun a ha hb' => ?_⟩
  · -- the lock is released
    have hz : ∀ k : Word, k.toNat < 32 → ∀ z : Word, (s0.getReg .x10).toNat + 0x8210 ≤ z.toNat →
        z.toNat < 2 ^ 40 → s0.getReg .x10 ≠ z + k := fun k hk z h1 h2 e => by
      have := congrArg BitVec.toNat e
      rw [BitVec.toNat_add] at this; omega
    rw [relMem_self (hz _ (by decide) _ (by omega) hrA.2.2)
      (fun e => by have := (Tlsf.flBm_inCtl hc).1; rw [← e] at this; omega)
      (hz _ (by decide) _ (by omega) hcA.2.2) (hz _ (by decide) _ (by omega) hcA.2.2)
      (fun e => by have := hH.1; rw [← e] at this; omega)
      (by simpa using hz 0#64 (by decide) _ (by omega) hcA.2.2)
      (fun hz' => by
        rw [hhd] at hz' ⊢
        have := hsh.nodeA (hdN _ rfl hz')
        exact hz _ (by decide) _ (by omega) this.2.2), hlock]
    rfl
  · -- every other used block stays
    rw [hbs] at hd
    simp only [List.mem_append, List.mem_cons] at hd ⊢
    rcases hd with (hd | hd | hd) | hd | hd
    · exact .inl hd
    · subst hd
      rw [hothers _ (by simp) hne] at hu; exact absurd hu (by simp)
    · rw [hothers d (by simp [hd]) hne] at hu; exact absurd hu (by simp)
    · exact .inr (.inr (.inl hd))
    · exact .inr (.inr (.inr hd))
  · -- the frame
    have hcne : ∀ k : Word, k.toNat < 32 → a ≠ c.a + k := by
      intro k hk e
      by_cases hcb : c = b
      · subst hcb
        apply hb'
        rw [e, BitVec.toNat_add]; omega
      · exact notMine_blk ha hcm (hothers c (by simp) hcb) (by omega) (hsh.layout.2.2 c hcm) e
    rw [relMem_other (notMine_ctl ha (.inr rfl)) (notMine_ctl ha (.inl (Tlsf.slBm_inCtl hc hf)))
      (notMine_8 ha hrm) (notMine_ctl ha (.inl (Tlsf.flBm_inCtl hc))) (hcne _ (by decide))
      (hcne _ (by decide)) (notMine_ctl ha (.inl hH)) (by simpa using hcne 0#64 (by decide))
      (fun hz => by
        rw [hhd] at hz ⊢
        obtain ⟨-, d, hd, hda, hdu, -⟩ := hsh.members _ _ _ (hdN _ rfl hz)
        rw [← hda]
        exact notMine_blk ha hd hdu (by have := Tlsf.Shape.sz_ge (hsh.blk hd).2.2.2.2; simp; omega)
          (hsh.layout.2.2 d hd))]
    exact hfr a ha hb'

open Tlsf in
/-- Unlinking leaves alone what the allocator does not own. -/
theorem unlink_frame {self base : Word} {m : Word → Word} {bs : List Blk}
    {L : Word → Word → List Word} {out : Word → Prop} (h : Shape self base m bs L out)
    {f s x a : Word} (hf : f < 64#64) (hs : s < 64#64) (hx : x ∈ L f s)
    (ha : ¬ Alloc.Mine self bs a) : unlinkMem self m f s x a = m a := by
  have hc := h.ctlOk
  refine unlink_other h hx (notMine_ctl ha (.inl (headAddr_inCtl hc hf hs)))
    (notMine_ctl ha (.inl (slBm_inCtl hc hf))) (notMine_ctl ha (.inl (flBm_inCtl hc)))
    fun z hz => ?_
  obtain ⟨-, d, hd, rfl, hu, -⟩ := h.members _ _ _ hz
  have := Shape.sz_ge (h.blk hd).2.2.2.2
  exact ⟨notMine_blk ha hd hu (by simp; omega) (h.layout.2.2 d hd),
    notMine_blk ha hd hu (by simp; omega) (h.layout.2.2 d hd)⟩

open Tlsf in
/-- Unlinking leaves the lock alone. -/
theorem unlink_self {self base : Word} {m : Word → Word} {bs : List Blk}
    {L : Word → Word → List Word} {out : Word → Prop} (h : Shape self base m bs L out)
    {f s x : Word} (hf : f < 64#64) (hs : s < 64#64) (hx : x ∈ L f s) :
    unlinkMem self m f s x self = m self := by
  have hc := h.ctlOk
  have hlay := h.layout.1
  simp only [ctlSize] at hlay
  have nC : ∀ k, InCtl self k → self ≠ k := fun k hk e => by
    have := hk.1; rw [← e] at this; omega
  refine unlink_other h hx (nC _ (headAddr_inCtl hc hf hs)) (nC _ (slBm_inCtl hc hf))
    (nC _ (flBm_inCtl hc)) fun z hz => ?_
  have hA := h.nodeA hz
  have nA : ∀ k : Word, k.toNat < 32 → self ≠ z + k := fun k hk e => by
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_add] at this; omega
  exact ⟨nA _ (by decide), nA _ (by decide)⟩

/-- **rlsf's `dealloc` (`0x7801c620`).** Entered with a well-formed heap at `a0`, the pointer
    `a1` that `alloc` granted for a used block `b` at alignment `a2` (just past its header, or,
    for a large alignment, with `b`'s address stored just below it), and a frame of 32 bytes on
    the stack: it returns, with the callee-saved registers and the code as they were, the heap
    well formed again with every other used block kept, and nothing changed but the
    allocator's own doublewords and `b`'s bytes. It never panics: the lock is free. -/
theorem spec {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 : MachineState} {base : Word}
    {bs : List Tlsf.Blk} {L : Word → Word → List Word} {b : Tlsf.Blk}
    (hpc : s0.pc = 0x7801c620#64) (hcode : s0.code = C)
    (hrep : Tlsf.Rep (s0.getReg .x10) base s0.getMem bs L)
    (hb : b ∈ bs) (hbu : b.used = true) (hbl : b.last = false)
    (hsmall : s0.getReg .x12 ≤ 31#64 → s0.getReg .x11 = b.a + 16#64)
    (hbig : ¬ s0.getReg .x12 ≤ 31#64 →
      s0.getMem (s0.getReg .x11 + 0xfffffffffffffff8#64) = b.a ∧
      b.a.toNat ≤ (s0.getReg .x11 + 0xfffffffffffffff8#64).toNat ∧
      (s0.getReg .x11 + 0xfffffffffffffff8#64).toNat < b.a.toNat + b.sz.toNat)
    (hsp : 0x20 ≤ (s0.getReg .x2).toNat) (hspc : (s0.getReg .x2).toNat ≤ (s0.getReg .x10).toNat)
    (hk : ∀ t, Done s0 base bs b t → SafeN G n P t) : SafeN G n P s0 := by
  obtain ⟨hlock, hsh0⟩ := Tlsf.rep_iff.mp hrep
  have hsh1 := hsh0.congr (m' := Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64)
    fun a ha => Tlsf.upd_ne (Alloc.key_ne_self hsh0 ha)
  have hc := hsh0.ctlOk
  have hlay := hsh0.layout.1
  simp only [Tlsf.ctlSize] at hlay
  have hbA := hsh0.blkA hb
  have hself := offN (a := s0.getReg .x10) hspc (Nat.le_refl _)
  have hM1 : ∀ a, ¬ Alloc.Mine (s0.getReg .x10) bs a →
      Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64 a = s0.getMem a :=
    fun a ha => Tlsf.upd_ne (notMine_ctl ha (.inr rfl))
  have hL1 : Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64 (s0.getReg .x10) =
      0xffffffffffffffff#64 := Tlsf.upd_same ..
  refine entry hpc hcode hlock hsp hself (fun h => offN hspc (by have := (hbig h).2.1; omega)) ?_
  intro y hs hpcy r9
  have r9' : y.getReg .x9 = b.a := by
    rw [r9]; unfold blkOf
    split
    · rename_i h; rw [hsmall h]; bv_omega
    · rename_i h
      obtain ⟨e, h1, -⟩ := hbig h
      rw [Tlsf.upd_ne (fun e' => by rw [e'] at h1; omega), e]
  obtain ⟨pre, post, hbs⟩ := List.append_of_mem hb
  -- The chain around `b`.
  have hch := hsh0.chain
  rw [hbs] at hch
  obtain ⟨a', p', hseg, hcb⟩ := (Tlsf.chain_append (List.cons_ne_nil _ _)).mp hch
  obtain ⟨hb1, -, -, -, -, hb6⟩ := hcb
  rw [if_neg (by simp [hbl])] at hb6
  cases post with
  | nil => exact hb6.elim
  | cons q post' =>
  obtain ⟨hq1, -, -, -, -, hq6⟩ := hb6
  subst hb1
  have hqm : q ∈ bs := by rw [hbs]; simp
  -- The previous block, if any, ends at `b`.
  have hprev : ∀ pre' p, pre = pre' ++ [p] → p.a + p.sz = b.a ∧ p ∈ bs := by
    intro pre' p e
    subst e
    obtain ⟨-, e2, -, -⟩ := seg_last hseg
    exact ⟨e2.symm, by rw [hbs]; simp⟩
  -- Blocks before `b` are not blocks after it.
  have hpre_ne : ∀ d ∈ pre, ∀ x ∈ q :: post', d.a ≠ x.a := by
    intro d hd x hx e
    have := (hsh0.around hbs).1 d hd
    have := (hsh0.around hbs).2 x hx
    have := Tlsf.Shape.sz_ge (hsh0.blk (b := d) (by rw [hbs]; simp [hd])).2.2.2.2
    have := Tlsf.Shape.sz_ge (hsh0.blk hb).2.2.2.2
    rw [e] at *; omega
  refine nextSeg hs hpcy hsh1 hbs hbu hbl hsp hspc r9' ?_
  intro y2 M2 hs2 hpc2 q9 hcase
  rcases hcase with ⟨hqu, rfl, q10, q11⟩ | ⟨hqu, rfl, q10, q11⟩
  · -- The next block is used.
    refine prevSeg hs2 hpc2 hsh1 hbs (fun _ _ h => h) hsp hspc q9 ?_
    intro y3 M3 t S' hs3 hpc3 q12 q10' q11' hc2
    rcases hc2 with ⟨rfl, rfl, rfl, -⟩ | ⟨pre', p, hpre, hpu, rfl, rfl, rfl⟩
    · refine finish (c := b) (cs := []) (pre0 := pre) (r := q) (rest := post') hs3 hpc3 hsh1
        (by rw [hbs]; simp) (fun d hd => by simp at hd; subst hd; exact .inl hbu)
        (by rw [q11, hq1]) (fun _ _ h => h) hL1 (by simp)
        (fun d hd hne => by simp at hd; exact absurd hd hne) (fun a ha _ => hM1 a ha) hsp hspc
        (by rw [q10', q10]) q11' q12 hk
    · -- The previous block is free: it starts the merged block.
      obtain ⟨hp1, hpm⟩ := hprev pre' p hpre
      have hpsz := (hsh0.blk hpm).2.2.2.2
      have hf := Tlsf.flOf_lt hpsz
      have hsl := Tlsf.slOf_lt p.sz
      have hpL := hsh1.filed p hpm hpu id
      have hsh3 := hsh1.unlink hf hsl hpL
      have hbs3 : bs = pre' ++ p :: (b :: q :: post') := by rw [hbs, hpre]; simp
      have hpb : ∀ d ∈ pre', d.a ≠ p.a := fun d hd e => by
        have := (hsh0.around hbs3).1 d hd
        have := Tlsf.Shape.sz_ge (hsh0.blk (b := d) (by rw [hbs3]; simp [hd])).2.2.2.2
        rw [e] at *; omega
      refine finish (c := p) (cs := [b]) (pre0 := pre') (r := q) (rest := post') hs3 hpc3 hsh3
        (by rw [hbs3]; simp) (fun d hd => ?_) (by rw [q11, hq1, ← hp1]; bv_omega) (fun d hd => ?_)
        (by rw [unlink_self hsh1 hf hsl hpL]; exact hL1) (by simp)
        (fun d hd hne => ?_) (fun a ha _ => by rw [unlink_frame hsh1 hf hsl hpL ha]; exact hM1 a ha)
        hsp hspc (by rw [q10', q10]) q11' q12 hk
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
        rcases hd with rfl | rfl
        · exact .inr (.inr rfl)
        · exact .inl hbu
      · rintro (h | h)
        · exact h
        · simp only [List.mem_append, List.mem_cons] at hd
          rcases hd with hd | rfl | hd
          · exact hpb d hd h
          · exact hpre_ne p (by rw [hpre]; simp) _ (by simp) h.symm
          · exact hpre_ne p (by rw [hpre]; simp) d (by simp [hd]) h.symm
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
        rcases hd with rfl | rfl
        · exact hpu
        · exact absurd rfl hne
  · -- The next block is free: it joins the merged block.
    have hqsz := (hsh0.blk hqm).2.2.2.2
    have hfq := Tlsf.flOf_lt hqsz
    have hsq := Tlsf.slOf_lt q.sz
    have hqL := hsh1.filed q hqm hqu id
    have hsh2 := hsh1.unlink hfq hsq hqL
    have hql : q.last = false := by
      cases hl : q.last
      · rfl
      · have := hsh0.chain.last_used q hqm hl; rw [hqu] at this; exact absurd this (by simp)
    rw [if_neg (by simp [hql])] at hq6
    cases post' with
    | nil => exact hq6.elim
    | cons r rest =>
    obtain ⟨hr1, -⟩ := hq6
    have hrm : r ∈ bs := by rw [hbs]; simp
    have hqr : ∀ d ∈ r :: rest, d.a ≠ q.a := fun d hd e => by
      have h1 := (hsh0.around (pre := pre ++ [b]) (b := q) (post := r :: rest) (by rw [hbs]; simp)).2 d hd
      have := Tlsf.Shape.sz_ge hqsz
      rw [e] at h1; omega
    have hL2 := unlink_self hsh1 hfq hsq hqL
    have hM2 : ∀ a, ¬ Alloc.Mine (s0.getReg .x10) bs a →
        Tlsf.unlinkMem (s0.getReg .x10) (Tlsf.upd s0.getMem (s0.getReg .x10) 0xffffffffffffffff#64)
          (Tlsf.flOf q.sz) (Tlsf.slOf q.sz) q.a a = s0.getMem a := fun a ha => by
      rw [unlink_frame hsh1 hfq hsq hqL ha]; exact hM1 a ha
    refine prevSeg hs2 hpc2 hsh2 hbs (fun d hd h => h.elim id fun e => hpre_ne d hd q (by simp) e)
      hsp hspc q9 ?_
    intro y3 M3 t S' hs3 hpc3 q12 q10' q11' hc2
    rcases hc2 with ⟨rfl, rfl, rfl, -⟩ | ⟨pre', p, hpre, hpu, rfl, rfl, rfl⟩
    · refine finish (c := b) (cs := [q]) (pre0 := pre) (r := r) (rest := rest) hs3 hpc3 hsh2
        (by rw [hbs]; simp) (fun d hd => ?_) (by rw [q11, hr1]; bv_omega) (fun d hd => ?_)
        (by rw [hL2]; exact hL1) (by simp) (fun d hd hne => ?_) (fun a ha _ => hM2 a ha) hsp hspc
        (by rw [q10', q10, hr1, hq1]) q11' q12 hk
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
        rcases hd with rfl | rfl
        · exact .inl hbu
        · exact .inr (.inr rfl)
      · rintro (h | h)
        · exact h
        · simp only [List.mem_append] at hd
          rcases hd with hd | hd
          · exact hpre_ne d hd q (by simp) h
          · exact hqr d hd h
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
        rcases hd with rfl | rfl
        · exact absurd rfl hne
        · exact hqu
    · -- Both neighbours are free.
      obtain ⟨hp1, hpm⟩ := hprev pre' p hpre
      have hpsz := (hsh0.blk hpm).2.2.2.2
      have hf := Tlsf.flOf_lt hpsz
      have hsl := Tlsf.slOf_lt p.sz
      have hpq : p.a ≠ q.a := hpre_ne p (by rw [hpre]; simp) q (by simp)
      have hpL := hsh2.filed p hpm hpu (fun h => h.elim id hpq)
      have hsh3 := hsh2.unlink hf hsl hpL
      have hbs3 : bs = pre' ++ p :: (b :: q :: r :: rest) := by rw [hbs, hpre]; simp
      have hpb : ∀ d ∈ pre', d.a ≠ p.a := fun d hd e => by
        have := (hsh0.around hbs3).1 d hd
        have := Tlsf.Shape.sz_ge (hsh0.blk (b := d) (by rw [hbs3]; simp [hd])).2.2.2.2
        rw [e] at *; omega
      have hpr : ∀ d ∈ r :: rest, d.a ≠ p.a := fun d hd e =>
        hpre_ne p (by rw [hpre]; simp) d (by simp at hd ⊢; exact .inr hd) e.symm
      refine finish (c := p) (cs := [b, q]) (pre0 := pre') (r := r) (rest := rest) hs3 hpc3 hsh3
        (by rw [hbs3]; simp) (fun d hd => ?_) (by rw [q11, hr1, ← hp1]; bv_omega)
        (fun d hd => ?_) (by rw [unlink_self hsh2 hf hsl hpL, hL2]; exact hL1) (by simp)
        (fun d hd hne => ?_)
        (fun a ha _ => by rw [unlink_frame hsh2 hf hsl hpL ha]; exact hM2 a ha)
        hsp hspc (by rw [q10', q10, hr1, hq1]) q11' q12 hk
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
        rcases hd with rfl | rfl | rfl
        · exact .inr (.inr rfl)
        · exact .inl hbu
        · exact .inr (.inl (.inr rfl))
      · rintro ((h | h) | h)
        · exact h
        · simp only [List.mem_append] at hd
          rcases hd with hd | hd
          · exact hpre_ne d (by rw [hpre]; simp [hd]) q (by simp) h
          · exact hqr d hd h
        · simp only [List.mem_append] at hd
          rcases hd with hd | hd
          · exact hpb d hd h
          · exact hpr d hd h
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hd
        rcases hd with rfl | rfl | rfl
        · exact hpu
        · exact absurd rfl hne
        · exact hqu

end Cases.Zip2005.Runtime.Dealloc
