import Cases.Zip2005.Field.SqInvBody
import Cases.Zip2005.Kit.StoreByteAt
import Cases.Zip2005.Field.SqIterLoop
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `SqrtTables::new`'s `inv` loop, by induction

The invariant sits at the byte store (`0x7803127c`) for element `i` of the last power table
(`tb`, 256 elements): the store (`safe_sb_region`), then `sq_inv_step` to the store for element
`i + 1`. After the store for element 255 the loop's exit is handed the state at `0x78031280`
with one element left. The `inv` table is carried as some list of 138 doublewords.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- The store for element `i`. -/
structure SqInvAt (inv hx tb v2 v3 v4 v9 v25 v26 : Word) (i : Nat) (IV : List Word) (d : Word)
    (t : MachineState) : Prop where
  pc : t.pc = 0x7803127c#64
  r10 : t.getReg .x10 = inv + d
  dlt : d.toNat < 1098
  r21 : t.getReg .x21 = BitVec.ofNat 64 (256 - i)
  r23 : t.getReg .x23 = tb + BitVec.ofNat 64 (32 * (i + 1))
  r24 : t.getReg .x24 = BitVec.ofNat 64 (i + 1)
  r2 : t.getReg .x2 = v2
  r3 : t.getReg .x3 = v3
  r4 : t.getReg .x4 = v4
  r8 : t.getReg .x8 = 1098#64
  r9 : t.getReg .x9 = v9
  r18 : t.getReg .x18 = hx
  r19 : t.getReg .x19 = 1#64
  r20 : t.getReg .x20 = tb + 0x2000#64
  r25 : t.getReg .x25 = v25
  r26 : t.getReg .x26 = v26
  r27 : t.getReg .x27 = inv
  IVl : IV.length = 138
  IVr : Region inv IV t
  ilt : i < 256

theorem ofNat_sub_one {i : Nat} (h : i < 256) :
    BitVec.ofNat 64 (256 - i) + 18446744073709551615#64 = BitVec.ofNat 64 (256 - (i + 1)) := by
  have e1 : BitVec.ofNat 64 (256 - i) = BitVec.ofNat 64 (256 - (i + 1)) + 1#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [e1, BitVec.add_assoc, show (1#64 : Word) + 18446744073709551615#64 = 0#64 by decide,
    BitVec.add_zero]

theorem ofNat_succ' (i : Nat) :
    BitVec.ofNat 64 (i + 1) + 1#64 = BitVec.ofNat 64 (i + 1 + 1) := by
  rw [BitVec.ofNat_add_ofNat]

theorem ne_zero_of_lt {i : Nat} (h : i < 255) :
    (BitVec.ofNat 64 (256 - i) + 18446744073709551615#64 != 0#64) = true := by
  rw [ofNat_sub_one (by omega), bne_iff_ne, ne_eq]; intro he
  have := congrArg BitVec.toNat he
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at this; omega

theorem step_ptr {tb : Word} {i : Nat} (h : i + 1 < 256) (hnw : tb.toNat + 0x2000 ≤ 0x1c00000000) :
    tb + BitVec.ofNat 64 (32 * (i + 1)) +
      ((if (0#64).ult ((tb + BitVec.ofNat 64 (32 * (i + 1))) ^^^ (tb + 0x2000#64)) = true then 1#64
        else 0#64) <<< 5) = tb + BitVec.ofNat 64 (32 * (i + 1 + 1)) := by
  have e1 : (tb + BitVec.ofNat 64 (32 * (i + 1))).toNat = tb.toNat + 32 * (i + 1) := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 32 * (i + 1) < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (by omega)]
  have e2 : (tb + 0x2000#64).toNat = tb.toNat + 0x2000 := by
    rw [BitVec.toNat_add, show (0x2000#64 : Word).toNat = 0x2000 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hne : tb + BitVec.ofNat 64 (32 * (i + 1)) ≠ tb + 0x2000#64 := by
    intro he; have := congrArg BitVec.toNat he; rw [e1, e2] at this; omega
  have hx : (0#64).ult ((tb + BitVec.ofNat 64 (32 * (i + 1))) ^^^ (tb + 0x2000#64)) = true := by
    have h0 : (tb + BitVec.ofNat 64 (32 * (i + 1))) ^^^ (tb + 0x2000#64) ≠ 0#64 := by
      intro h0; exact hne (BitVec.xor_eq_zero_iff.mp h0)
    have h1 : ((tb + BitVec.ofNat 64 (32 * (i + 1))) ^^^ (tb + 0x2000#64)).toNat ≠ 0 :=
      fun hz => h0 (BitVec.eq_of_toNat_eq (by rw [hz]; rfl))
    unfold BitVec.ult; rw [decide_eq_true_eq]; simp only [BitVec.toNat_ofNat]; omega
  rw [if_pos hx, show (1#64 : Word) <<< 5 = 32#64 by decide, BitVec.add_assoc, BitVec.ofNat_add_ofNat,
    show 32 * (i + 1) + 32 = 32 * (i + 1 + 1) by ring]

set_option maxRecDepth 100000 in
theorem sq_inv_fetch {s : MachineState} (hcode : CodeAt F_78030a94.base F_78030a94.prog s)
    (hpc : s.pc = 0x7803127c#64) : s.code s.pc = some (.SB .x10 .x22 0#12) :=
  fetch_of_codeAt hcode 506 (by decide) (by rfl) (by rw [hpc]; rfl)

set_option maxHeartbeats 4000000 in
theorem sq_inv_loop {G : MachineState → Prop} {nb : Nat} {P : Prop} {Lh : List (Word × Nat)} (s t0 : MachineState) (inv hx tb v2 v3 v4 v9 v25 v26 : Word)
    (hcode : CodeAt F_78030a94.base F_78030a94.prog s) (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hstk2 : StackOk Ro.layout 0 v2)
    (hokIV : RegionOk Ro.layout.roBase Ro.layout.textHi inv 138) (hokTB : RegionOk Ro.layout.roBase Ro.layout.textHi tb 1024)
    (htb : tb.toNat + 0x2000 ≤ 0x1c00000000)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G nb P u)
    (hexit : ∀ (t : MachineState) (IV : List Word), t.pc = 0x78031280#64 → t.code = s.code →
      Unchanged [(inv, 138)] t0 t →
      t.getReg .x21 = 1#64 → t.getReg .x23 = tb + 0x2000#64 → t.getReg .x24 = 256#64 →
      t.getReg .x2 = v2 → t.getReg .x3 = v3 → t.getReg .x4 = v4 → t.getReg .x8 = 1098#64 →
      t.getReg .x9 = v9 → t.getReg .x18 = hx → t.getReg .x19 = 1#64 →
      t.getReg .x20 = tb + 0x2000#64 → t.getReg .x25 = v25 → t.getReg .x26 = v26 →
      t.getReg .x27 = inv → IV.length = 138 → Region inv IV t → RoImage Ro.layout t →
      Run.HeapAt ((inv, 138) :: Lh) t → SafeN G nb P t) :
    ∀ (n : Nat) (t : MachineState) (i : Nat) (IV : List Word) (d : Word), t.code = s.code →
      RoImage Ro.layout t → Run.HeapAt ((inv, 138) :: Lh) t → Unchanged [(inv, 138)] t0 t →
      SqInvAt inv hx tb v2 v3 v4 v9 v25 v26 i IV d t → 255 - i = n → SafeN G nb P t := by
  intro n
  induction n with
  | zero =>
    intro t i IV d hc hro hheap hU H hn
    have hi : i = 255 := by have := H.ilt; omega
    subst hi
    have hcd := codeAt_of_code_eq hc hcode
    refine safe_sb_region (sq_inv_fetch hcd H.pc)
      (i := d.toNat / 8) (k := d.toNat % 8) (n := 138) ?_ (by have := H.dlt; omega) (by omega) H.IVl
      H.IVr (hokIV.weaken (by decide) (by decide)) (fun a ha => hcw a (hc ▸ ha)) ?_
    · rw [H.r10, show signExtend12 0#12 = 0#64 by rfl, BitVec.add_zero]
      congr 1; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; have := H.dlt; omega
    intro t1 hpc1 hr1 hc1 hun1 L hL hR
    refine hexit t1 L (by rw [hpc1, H.pc]; rfl) (hc1.trans hc)
      (hU.trans_cover hun1 (fun r hr => ⟨r, hr, by unfold Covers; omega⟩))
      ((hr1 _).trans H.r21) ((hr1 _).trans H.r23) ((hr1 _).trans H.r24) ((hr1 _).trans H.r2)
      ((hr1 _).trans H.r3) ((hr1 _).trans H.r4) ((hr1 _).trans H.r8) ((hr1 _).trans H.r9)
      ((hr1 _).trans H.r18) ((hr1 _).trans H.r19) ((hr1 _).trans H.r20) ((hr1 _).trans H.r25)
      ((hr1 _).trans H.r26) ((hr1 _).trans H.r27) hL hR
      (hro.of_unchanged hun1 (fun r hr => by
        rw [List.mem_singleton] at hr; subst hr; have := hokIV.offCode
        rcases this with h | h
        · left; exact h
        · right; simp only [Ro.layout_roBase, Ro.layout_roBytes, Ro.layout_textHi] at h ⊢; omega))
      (Carry.of_unchanged hheap hun1
        (openW_cons (openBlock_live _ _ List.mem_cons_self (le_refl _) (le_refl _)) (openW_nil _ _)))
  | succ n ih =>
    intro t i IV d hc hro hheap hU H hn
    have hi : i < 255 := by omega
    have hcd := codeAt_of_code_eq hc hcode
    refine safe_sb_region (sq_inv_fetch hcd H.pc)
      (i := d.toNat / 8) (k := d.toNat % 8) (n := 138) ?_ (by have := H.dlt; omega) (by omega) H.IVl
      H.IVr (hokIV.weaken (by decide) (by decide)) (fun a ha => hcw a (hc ▸ ha)) ?_
    · rw [H.r10, show signExtend12 0#12 = 0#64 by rfl, BitVec.add_zero]
      congr 1; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; have := H.dlt; omega
    intro t1 hpc1 hr1 hc1 hun1 L hL hR
    have hc1s := hc1.trans hc
    have hroW : ∀ r ∈ [(inv, 138)], r.1.toNat + 8 * r.2 ≤ Ro.layout.roBase ∨ Ro.layout.roBase + Ro.layout.roBytes ≤ r.1.toNat := by
      intro r hr
      rw [List.mem_singleton] at hr; subst hr; have := hokIV.offCode
      rcases this with h | h
      · left; exact h
      · right; simp only [Ro.layout_roBase, Ro.layout_roBytes, Ro.layout_textHi] at h ⊢; omega
    have hro1 := hro.of_unchanged hun1 hroW
    have hheap1 : Run.HeapAt ((inv, 138) :: Lh) t1 := Carry.of_unchanged hheap hun1
      (openW_cons (openBlock_live _ _ List.mem_cons_self (le_refl _) (le_refl _)) (openW_nil _ _))
    -- the next element, a block of the table
    have hokE : RegionOk Ro.layout.roBase Ro.layout.textHi (tb + BitVec.ofNat 64 (32 * (i + 1))) 4 :=
      hokTB.sub' (4 * (i + 1)) 4 (by omega) (by rw [show 8 * (4 * (i + 1)) = 32 * (i + 1) by ring])
    obtain ⟨E, hE, hEl⟩ := Region.exists_junk (tb + BitVec.ofNat 64 (32 * (i + 1))) 4 t1
    rw [list4_cells E hEl] at hE
    refine sq_inv_step t1 inv hx (tb + BitVec.ofNat 64 (32 * (i + 1))) (tb + 0x2000#64)
      (BitVec.ofNat 64 (256 - i)) (BitVec.ofNat 64 (i + 1)) E[0]! E[1]! E[2]! E[3]! L hL
      (ne_zero_of_lt hi) (by rw [hpc1, H.pc]; rfl) (codeAt_of_code_eq hc1s hcode)
      (codeAt_of_code_eq hc1s hcodeL) (fun a ha => hcw a (hc1s ▸ ha)) hro1
      hheap1 ((hr1 _).trans H.r2) hstk2 ((hr1 _).trans H.r8) ((hr1 _).trans H.r18) ((hr1 _).trans H.r19) ((hr1 _).trans H.r20)
      ((hr1 _).trans H.r21) ((hr1 _).trans H.r23) ((hr1 _).trans H.r24) ((hr1 _).trans H.r27) hR
      hokIV hE hokE (fun u sp' L' hu hcu => hpp u sp' L' hu (hcu.trans hc1s)) ?_
    intro t2 d' e' hpc2 hc2 hun2 r10 hd' r21 r22 r23 he' r24 r2 r3 r4 r8 r9 r18 r19 r20 r25 r26 r27 hIV2
    have hU2 : Unchanged [(inv, 138)] t0 t2 :=
      (hU.trans_cover hun1 (fun r hr => ⟨r, hr, by unfold Covers; omega⟩)).trans_cover hun2
        (fun r hr => absurd hr (by simp))
    refine ih t2 (i + 1) L d' (hc2.trans hc1s) (hro1.of_unchanged hun2 (fun r hr => absurd hr (by simp)))
      (Carry.of_unchanged hheap1 hun2 (openW_nil _ _)) hU2 ?_ (by omega)
    exact SqInvAt.mk hpc2 r10 hd' (by rw [r21, ofNat_sub_one H.ilt])
      (by rw [r23, ← he', step_ptr (by omega) htb]) (by rw [r24, ofNat_succ']) (r2.trans ((hr1 _).trans H.r2))
      (r3.trans ((hr1 _).trans H.r3)) (r4.trans ((hr1 _).trans H.r4)) r8
      (r9.trans ((hr1 _).trans H.r9)) r18 r19 r20 (r25.trans ((hr1 _).trans H.r25))
      (r26.trans ((hr1 _).trans H.r26)) r27 hL hIV2 (by omega)

end Cases.Zip2005
