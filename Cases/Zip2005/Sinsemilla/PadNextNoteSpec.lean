import Cases.Zip2005.Sinsemilla.PadNextNote0
import Cases.Zip2005.Sinsemilla.PadNextNoteA
import Cases.Zip2005.Sinsemilla.PadNextNote256
import Cases.Zip2005.Sinsemilla.PadNextNoteB
import Cases.Zip2005.Sinsemilla.PadNextNote512
import Cases.Zip2005.Sinsemilla.PadNextNoteC
import Cases.Zip2005.Sinsemilla.PadNextNote576
import Cases.Zip2005.Sinsemilla.PadNextNoteD
import Cases.Zip2005.Sinsemilla.PadNextNote831
import Cases.Zip2005.Sinsemilla.PadNextNoteE
import Cases.Zip2005.Sinsemilla.PadNextNote1086
import Cases.Zip2005.Sinsemilla.PadNextNoteF
import Cases.Zip2005.Sinsemilla.PadNextNote1090
import Cases.Zip2005.Image.Ro

/-!
# `Pad<…>::next` (0x78021720, the note commitment's message iterator): one specification over
the message position

`noteState sp J j k` is the iterator block after `k` calls (`0 ≤ k ≤ 1091`): `g★_d`'s byte
cursor live through position 256, `pk★_d`'s through 512, `v`'s through 576, `ρ`'s `Take`
cursor through 831, `ψ`'s through 1086, then the four padding zeros (1086 bits ≡ 6 mod 10)
and `None`. `pad_next_note_spec` glues the thirteen phase lemmas: call `k < 1090` yields
message bit `k` (`noteBit`), call 1090 yields `None` (2).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- The iterator block after `k` calls. -/
def noteState (sp : Word) (J : List Word) (j : Word) (k : Nat) : List Word :=
  if k = 0 then noteBlk0 sp J j
  else if k ≤ 256 then
    noteBlkA sp J j 0#8 (sp + 18446744073709551408#64 + BitVec.ofNat 64 (k / 8)) (BitVec.ofNat 8 (k % 8))
      (BitVec.ofNat 64 k)
  else if k ≤ 512 then
    noteBlkB sp J j (sp + 18446744073709551440#64 + BitVec.ofNat 64 ((k - 256) / 8)) (BitVec.ofNat 8 ((k - 256) % 8))
      (BitVec.ofNat 64 k)
  else if k ≤ 576 then
    noteBlkC sp J j (sp + 18446744073709551472#64 + BitVec.ofNat 64 ((k - 512) / 8)) (BitVec.ofNat 8 ((k - 512) % 8))
      (BitVec.ofNat 64 k)
  else if k ≤ 831 then
    noteBlkD sp J j (BitVec.ofNat 64 (255 - (k - 576)))
      (sp + 18446744073709551480#64 + BitVec.ofNat 64 (8 * ((k - 576) / 64))) (BitVec.ofNat 8 ((k - 576) % 64))
      (BitVec.ofNat 64 k)
  else if k ≤ 1086 then
    noteBlkE sp J j (BitVec.ofNat 64 (255 - (k - 831)))
      (sp + 18446744073709551512#64 + BitVec.ofNat 64 (8 * ((k - 831) / 64))) (BitVec.ofNat 8 ((k - 831) % 64))
      (BitVec.ofNat 64 k)
  else noteBlkP sp J (BitVec.ofNat 64 (1090 - k))

@[simp] theorem noteState_length (sp : Word) (J : List Word) (j : Word) (k : Nat) :
    (noteState sp J j k).length = 18 := by
  unfold noteState
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

/-! ## The phases, as rewrite rules -/

theorem noteState_0 (sp : Word) (J : List Word) (j : Word) : noteState sp J j 0 = noteBlk0 sp J j := by
  rw [noteState, if_pos rfl]

theorem noteState_A (sp : Word) (J : List Word) (j : Word) (k : Nat) (hk1 : 1 ≤ k) (hk : k ≤ 256) :
    noteState sp J j k = noteBlkA sp J j 0#8 (sp + 18446744073709551408#64 + BitVec.ofNat 64 (k / 8))
      (BitVec.ofNat 8 (k % 8)) (BitVec.ofNat 64 k) := by
  rw [noteState, if_neg (by omega), if_pos hk]

theorem noteState_B (sp : Word) (J : List Word) (j : Word) (k : Nat) (hk1 : 257 ≤ k) (hk : k ≤ 512) :
    noteState sp J j k = noteBlkB sp J j (sp + 18446744073709551440#64 + BitVec.ofNat 64 ((k - 256) / 8))
      (BitVec.ofNat 8 ((k - 256) % 8)) (BitVec.ofNat 64 k) := by
  rw [noteState, if_neg (by omega), if_neg (by omega), if_pos hk]

theorem noteState_C (sp : Word) (J : List Word) (j : Word) (k : Nat) (hk1 : 513 ≤ k) (hk : k ≤ 576) :
    noteState sp J j k = noteBlkC sp J j (sp + 18446744073709551472#64 + BitVec.ofNat 64 ((k - 512) / 8))
      (BitVec.ofNat 8 ((k - 512) % 8)) (BitVec.ofNat 64 k) := by
  rw [noteState, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hk]

theorem noteState_D (sp : Word) (J : List Word) (j : Word) (k : Nat) (hk1 : 577 ≤ k) (hk : k ≤ 831) :
    noteState sp J j k = noteBlkD sp J j (BitVec.ofNat 64 (255 - (k - 576)))
      (sp + 18446744073709551480#64 + BitVec.ofNat 64 (8 * ((k - 576) / 64))) (BitVec.ofNat 8 ((k - 576) % 64))
      (BitVec.ofNat 64 k) := by
  rw [noteState, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos hk]

theorem noteState_E (sp : Word) (J : List Word) (j : Word) (k : Nat) (hk1 : 832 ≤ k) (hk : k ≤ 1086) :
    noteState sp J j k = noteBlkE sp J j (BitVec.ofNat 64 (255 - (k - 831)))
      (sp + 18446744073709551512#64 + BitVec.ofNat 64 (8 * ((k - 831) / 64))) (BitVec.ofNat 8 ((k - 831) % 64))
      (BitVec.ofNat 64 k) := by
  rw [noteState, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos hk]

theorem noteState_P (sp : Word) (J : List Word) (j : Word) (k : Nat) (hk : 1087 ≤ k) :
    noteState sp J j k = noteBlkP sp J (BitVec.ofNat 64 (1090 - k)) := by
  rw [noteState, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

set_option maxHeartbeats 4000000 in
theorem pad_next_note_spec {P : Prop} (s : MachineState) (ra spn sp iter v : Word)
    (J G K R Q : List Word)
    (hGl : G.length = 4) (hKl : K.length = 4) (hRl : R.length = 4) (hQl : Q.length = 4) (j : Word)
    (k : Nat) (hk1090 : k ≤ 1090)
    (hpc : s.pc = 0x78021720#64) (hcode : CodeAt F_78021720.base F_78021720.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x180 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter (noteState sp J j k) s)
    (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi iter 18)
    (hGr : Region (sp + 18446744073709551408#64) G s) (hokG : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551408#64) 4)
    (hKr : Region (sp + 18446744073709551440#64) K s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551440#64) 4)
    (hVr : Region (sp + 18446744073709551472#64) [v] s) (hokV : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551472#64) 1)
    (hRr : Region (sp + 18446744073709551480#64) R s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551480#64) 4)
    (hQr : Region (sp + 18446744073709551512#64) Q s) (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551512#64) 4)
    (hdjIG : Disjoint iter 18 (sp + 18446744073709551408#64) 4) (hdjIK : Disjoint iter 18 (sp + 18446744073709551440#64) 4)
    (hdjIV : Disjoint iter 18 (sp + 18446744073709551472#64) 1) (hdjIR : Disjoint iter 18 (sp + 18446744073709551480#64) 4)
    (hdjIQ : Disjoint iter 18 (sp + 18446744073709551512#64) 4)
    (hdjS : Disjoint (spn - 0x180#64) 48 iter 18)
    (hdjSG : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551408#64) 4) (hdjSK : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551440#64) 4)
    (hdjSV : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551472#64) 1) (hdjSR : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551480#64) 4)
    (hdjSQ : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551512#64) 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x180#64, 48), (iter, 18)] s t →
      Region iter (noteState sp J j (k + 1)) t →
      t.getReg .x10 = (if k < 1090 then bw (noteBit G K v R Q k) else 2#64) → Safe P t) :
    Safe P s := by
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · -- the first call
    rw [noteState_0] at hI
    refine pad_next_note_0_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl j hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [noteState_A _ _ _ 1 (by decide) (by decide), show (1 / 8 : Nat) = 0 from rfl, show (1 % 8 : Nat) = 1 from rfl, BitVec.add_zero]
      exact h5
    · rw [h6, if_pos (by decide)]
  rcases Nat.lt_or_ge k 256 with h256 | h256
  · -- `g★_d`'s bits
    rw [noteState_A _ _ _ k hk1 (by omega), BitVec.add_assoc] at hI
    refine pad_next_note_a_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl j k hk1 (by omega) _ rfl hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [noteState_A _ _ _ (k + 1) (by omega) (by omega)]
      exact h5
    · rw [h6, if_pos (by omega)]
  rcases Nat.eq_or_lt_of_le h256 with h256' | h257
  · subst h256'
    -- the change to `pk★_d`'s bits
    rw [noteState_A _ _ _ 256 (by decide) (by decide), show (256 / 8 : Nat) = 32 from rfl, show (256 % 8 : Nat) = 0 from rfl, show sp + 18446744073709551408#64 + 32#64 = sp + 18446744073709551440#64 from by rw [BitVec.add_assoc]; rfl] at hI
    refine pad_next_note_256_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl j hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [noteState_B _ _ _ (256 + 1) (by decide) (by decide), show ((256 + 1 - 256) / 8 : Nat) = 0 from rfl, show ((256 + 1 - 256) % 8 : Nat) = 1 from rfl, BitVec.add_zero]
      exact h5
    · rw [h6, if_pos (by decide)]
  rcases Nat.lt_or_ge k 512 with h512 | h512
  · obtain ⟨m, rfl⟩ : ∃ m, k = 256 + m := ⟨k - 256, by omega⟩
    -- `pk★_d`'s bits
    rw [noteState_B _ _ _ (256 + m) (by omega) (by omega), Nat.add_sub_cancel_left, BitVec.add_assoc] at hI
    refine pad_next_note_b_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl j m (by omega) (by omega) _ rfl hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [noteState_B _ _ _ (256 + m + 1) (by omega) (by omega), show 256 + m + 1 - 256 = m + 1 by omega]
      exact h5
    · rw [h6, if_pos (by omega)]
  rcases Nat.eq_or_lt_of_le h512 with h512' | h513
  · subst h512'
    -- the change to `v`'s bits
    rw [noteState_B _ _ _ 512 (by decide) (by decide), show ((512 - 256) / 8 : Nat) = 32 from rfl, show ((512 - 256) % 8 : Nat) = 0 from rfl, show sp + 18446744073709551440#64 + 32#64 = sp + 18446744073709551472#64 from by rw [BitVec.add_assoc]; rfl] at hI
    refine pad_next_note_512_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl j hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [noteState_C _ _ _ (512 + 1) (by decide) (by decide), show ((512 + 1 - 512) / 8 : Nat) = 0 from rfl, show ((512 + 1 - 512) % 8 : Nat) = 1 from rfl, BitVec.add_zero]
      exact h5
    · rw [h6, if_pos (by decide)]
  rcases Nat.lt_or_ge k 576 with h576 | h576
  · obtain ⟨m, rfl⟩ : ∃ m, k = 512 + m := ⟨k - 512, by omega⟩
    -- `v`'s bits
    rw [noteState_C _ _ _ (512 + m) (by omega) (by omega), Nat.add_sub_cancel_left, BitVec.add_assoc] at hI
    refine pad_next_note_c_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl j m (by omega) (by omega) _ rfl hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [noteState_C _ _ _ (512 + m + 1) (by omega) (by omega), show 512 + m + 1 - 512 = m + 1 by omega]
      exact h5
    · rw [h6, if_pos (by omega)]
  rcases Nat.eq_or_lt_of_le h576 with h576' | h577
  · subst h576'
    -- the change to `ρ`'s bits
    rw [noteState_C _ _ _ 576 (by decide) (by decide), show ((576 - 512) / 8 : Nat) = 8 from rfl, show ((576 - 512) % 8 : Nat) = 0 from rfl, show sp + 18446744073709551472#64 + 8#64 = sp + 18446744073709551480#64 from by rw [BitVec.add_assoc]; rfl] at hI
    refine pad_next_note_576_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl j hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [noteState_D _ _ _ (576 + 1) (by decide) (by decide), show (255 - (576 + 1 - 576) : Nat) = 254 from rfl, show (8 * ((576 + 1 - 576) / 64) : Nat) = 0 from rfl, show ((576 + 1 - 576) % 64 : Nat) = 1 from rfl, BitVec.add_zero]
      exact h5
    · rw [h6, if_pos (by decide)]
  rcases Nat.lt_or_ge k 831 with h831 | h831
  · obtain ⟨m, rfl⟩ : ∃ m, k = 576 + m := ⟨k - 576, by omega⟩
    -- `ρ`'s bits
    rw [noteState_D _ _ _ (576 + m) (by omega) (by omega), Nat.add_sub_cancel_left, BitVec.add_assoc] at hI
    refine pad_next_note_d_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl j m (by omega) (by omega) _ rfl hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [noteState_D _ _ _ (576 + m + 1) (by omega) (by omega), show 576 + m + 1 - 576 = m + 1 by omega]
      exact h5
    · rw [h6, if_pos (by omega)]
  rcases Nat.eq_or_lt_of_le h831 with h831' | h832
  · subst h831'
    -- the change to `ψ`'s bits
    rw [noteState_D _ _ _ 831 (by decide) (by decide), show (255 - (831 - 576) : Nat) = 0 from rfl, show (8 * ((831 - 576) / 64) : Nat) = 24 from rfl, show ((831 - 576) % 64 : Nat) = 63 from rfl, show sp + 18446744073709551480#64 + 24#64 = sp + 18446744073709551504#64 from by rw [BitVec.add_assoc]; rfl] at hI
    refine pad_next_note_831_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl j hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [noteState_E _ _ _ (831 + 1) (by decide) (by decide), show (255 - (831 + 1 - 831) : Nat) = 254 from rfl, show (8 * ((831 + 1 - 831) / 64) : Nat) = 0 from rfl, show ((831 + 1 - 831) % 64 : Nat) = 1 from rfl, BitVec.add_zero]
      exact h5
    · rw [h6, if_pos (by decide)]
  rcases Nat.lt_or_ge k 1086 with h1086 | h1086
  · obtain ⟨m, rfl⟩ : ∃ m, k = 831 + m := ⟨k - 831, by omega⟩
    -- `ψ`'s bits
    rw [noteState_E _ _ _ (831 + m) (by omega) (by omega), Nat.add_sub_cancel_left, BitVec.add_assoc] at hI
    refine pad_next_note_e_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl j m (by omega) (by omega) _ rfl hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [noteState_E _ _ _ (831 + m + 1) (by omega) (by omega), show 831 + m + 1 - 831 = m + 1 by omega]
      exact h5
    · rw [h6, if_pos (by omega)]
  rcases Nat.eq_or_lt_of_le h1086 with h1086' | h1087
  · subst h1086'
    -- the message exhausted: the padding begins
    rw [noteState_E _ _ _ 1086 (by decide) (by decide), show (255 - (1086 - 831) : Nat) = 0 from rfl, show (8 * ((1086 - 831) / 64) : Nat) = 24 from rfl, show ((1086 - 831) % 64 : Nat) = 63 from rfl, show sp + 18446744073709551512#64 + 24#64 = sp + 18446744073709551536#64 from by rw [BitVec.add_assoc]; rfl] at hI
    refine pad_next_note_1086_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl j hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [noteState_P _ _ _ (1086 + 1) (by decide), show (1090 - (1086 + 1) : Nat) = 3 from rfl]
      exact h5
    · rw [h6, if_pos (by decide)]
  rcases Nat.lt_or_ge k 1090 with h1090 | h1090
  · -- the padding
    rw [noteState_P _ _ _ k (by omega)] at hI
    refine pad_next_note_f_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl (1090 - k) (by omega) (by omega) hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [noteState_P _ _ _ (k + 1) (by omega), show (1090 - (k + 1) : Nat) = 1090 - k - 1 by omega]
      exact h5
    · rw [h6, if_pos h1090, show (1090 - (1090 - k) : Nat) = k by omega]
  · -- the end
    have hk' : k = 1090 := by omega
    subst hk'
    rw [noteState_P _ _ _ 1090 (by decide), show (1090 - 1090 : Nat) = 0 from rfl] at hI
    refine pad_next_note_1090_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
    intro t h1 h2 h3 h4 h5 h6
    refine hk t h1 h2 h3 h4 ?_ ?_
    · rw [noteState_P _ _ _ (1090 + 1) (by decide), show (1090 - (1090 + 1) : Nat) = 0 from rfl]
      exact h5
    · rw [h6, if_neg (by decide)]

/-- The calls that yield a bit: `k < 1090`. -/
theorem pad_next_note_lt_spec {P : Prop} (s : MachineState) (ra spn sp iter v : Word)
    (J G K R Q : List Word)
    (hGl : G.length = 4) (hKl : K.length = 4) (hRl : R.length = 4) (hQl : Q.length = 4) (j : Word)
    (k : Nat) (hk1090 : k < 1090)
    (hpc : s.pc = 0x78021720#64) (hcode : CodeAt F_78021720.base F_78021720.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x180 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter (noteState sp J j k) s)
    (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi iter 18)
    (hGr : Region (sp + 18446744073709551408#64) G s) (hokG : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551408#64) 4)
    (hKr : Region (sp + 18446744073709551440#64) K s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551440#64) 4)
    (hVr : Region (sp + 18446744073709551472#64) [v] s) (hokV : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551472#64) 1)
    (hRr : Region (sp + 18446744073709551480#64) R s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551480#64) 4)
    (hQr : Region (sp + 18446744073709551512#64) Q s) (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551512#64) 4)
    (hdjIG : Disjoint iter 18 (sp + 18446744073709551408#64) 4) (hdjIK : Disjoint iter 18 (sp + 18446744073709551440#64) 4)
    (hdjIV : Disjoint iter 18 (sp + 18446744073709551472#64) 1) (hdjIR : Disjoint iter 18 (sp + 18446744073709551480#64) 4)
    (hdjIQ : Disjoint iter 18 (sp + 18446744073709551512#64) 4)
    (hdjS : Disjoint (spn - 0x180#64) 48 iter 18)
    (hdjSG : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551408#64) 4) (hdjSK : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551440#64) 4)
    (hdjSV : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551472#64) 1) (hdjSR : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551480#64) 4)
    (hdjSQ : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551512#64) 4)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x180#64, 48), (iter, 18)] s t →
      Region iter (noteState sp J j (k + 1)) t →
      t.getReg .x10 = bw (noteBit G K v R Q k) → Safe P t) :
    Safe P s := by
  refine pad_next_note_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl j k (by omega) hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
  intro t h1 h2 h3 h4 h5 h6
  exact hk t h1 h2 h3 h4 h5 (by rw [h6, if_pos hk1090])

/-- The same, with the block as a list variable related to the model (the form the executor
    matches at a call inside `from_iter`'s loop). -/
theorem pad_next_note_var_spec {P : Prop} (s : MachineState) (ra spn sp iter v : Word)
    (J G K R Q I : List Word)
    (hGl : G.length = 4) (hKl : K.length = 4) (hRl : R.length = 4) (hQl : Q.length = 4) (j : Word)
    (k : Nat) (hk1090 : k < 1090) (hIl : I.length = 18) (hIv : noteState sp J j k = I)
    (hpc : s.pc = 0x78021720#64) (hcode : CodeAt F_78021720.base F_78021720.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x180 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter I s)
    (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi iter 18)
    (hGr : Region (sp + 18446744073709551408#64) G s) (hokG : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551408#64) 4)
    (hKr : Region (sp + 18446744073709551440#64) K s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551440#64) 4)
    (hVr : Region (sp + 18446744073709551472#64) [v] s) (hokV : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551472#64) 1)
    (hRr : Region (sp + 18446744073709551480#64) R s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551480#64) 4)
    (hQr : Region (sp + 18446744073709551512#64) Q s) (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551512#64) 4)
    (hdjIG : Disjoint iter 18 (sp + 18446744073709551408#64) 4) (hdjIK : Disjoint iter 18 (sp + 18446744073709551440#64) 4)
    (hdjIV : Disjoint iter 18 (sp + 18446744073709551472#64) 1) (hdjIR : Disjoint iter 18 (sp + 18446744073709551480#64) 4)
    (hdjIQ : Disjoint iter 18 (sp + 18446744073709551512#64) 4)
    (hdjS : Disjoint (spn - 0x180#64) 48 iter 18)
    (hdjSG : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551408#64) 4) (hdjSK : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551440#64) 4)
    (hdjSV : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551472#64) 1) (hdjSR : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551480#64) 4)
    (hdjSQ : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551512#64) 4)
    (hk : ∀ (t : MachineState) (I' : List Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(spn - 0x180#64, 48), (iter, 18)] s t →
      I'.length = 18 → noteState sp J j (k + 1) = I' → Region iter I' t →
      t.getReg .x10 = bw (noteBit G K v R Q k) → Safe P t) :
    Safe P s := by
  subst hIv
  refine pad_next_note_lt_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl j k hk1090 hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
  intro t h1 h2 h3 h4 h5 h6
  exact hk t _ h1 h2 h3 h4 (noteState_length _ _ _ _) rfl h5 h6

/-- The same over the block's eighteen cells (the form the executor unifies at a call inside
    `from_iter`'s loop: the model equation in the cells it tracks). -/
theorem pad_next_note_cells_spec {P : Prop} (s : MachineState) (ra spn sp iter v : Word)
    (J G K R Q : List Word) (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 : Word)
    (hGl : G.length = 4) (hKl : K.length = 4) (hRl : R.length = 4) (hQl : Q.length = 4) (j : Word)
    (k : Nat) (hIv : noteState sp J j k = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17]) (hk1090 : k < 1090)
    (hpc : s.pc = 0x78021720#64) (hcode : CodeAt F_78021720.base F_78021720.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x180 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17] s)
    (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi iter 18)
    (hGr : Region (sp + 18446744073709551408#64) G s) (hokG : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551408#64) 4)
    (hKr : Region (sp + 18446744073709551440#64) K s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551440#64) 4)
    (hVr : Region (sp + 18446744073709551472#64) [v] s) (hokV : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551472#64) 1)
    (hRr : Region (sp + 18446744073709551480#64) R s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551480#64) 4)
    (hQr : Region (sp + 18446744073709551512#64) Q s) (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551512#64) 4)
    (hdjIG : Disjoint iter 18 (sp + 18446744073709551408#64) 4) (hdjIK : Disjoint iter 18 (sp + 18446744073709551440#64) 4)
    (hdjIV : Disjoint iter 18 (sp + 18446744073709551472#64) 1) (hdjIR : Disjoint iter 18 (sp + 18446744073709551480#64) 4)
    (hdjIQ : Disjoint iter 18 (sp + 18446744073709551512#64) 4)
    (hdjS : Disjoint (spn - 0x180#64) 48 iter 18)
    (hdjSG : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551408#64) 4) (hdjSK : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551440#64) 4)
    (hdjSV : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551472#64) 1) (hdjSR : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551480#64) 4)
    (hdjSQ : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551512#64) 4)
    (hk : ∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' i12' i13' i14' i15' i16' i17' bit : Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(spn - 0x180#64, 48), (iter, 18)] s t →
      noteState sp J j (k + 1) = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11', i12', i13', i14', i15', i16', i17'] → Region iter [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11', i12', i13', i14', i15', i16', i17'] t →
      bw (noteBit G K v R Q k) = bit → (bit == 2#64) = false → bit &&& 255#64 = bit →
      t.getReg .x10 = bit → Safe P t) :
    Safe P s := by
  refine pad_next_note_var_spec s ra spn sp iter v J G K R Q _ hGl hKl hRl hQl j k hk1090 rfl hIv
    hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
  intro t I' h1 h2 h3 h4 hl hIv' h5 h6
  rw [list18_cells I' hl] at hIv' h5
  exact hk t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 hIv' h5 rfl (bw_ne_two _) (bw_and255 _) h6

/-- Call 1090, over the block's cells: `None` (2), `Pad` spent. -/
theorem pad_next_note_end_cells_spec {P : Prop} (s : MachineState) (ra spn sp iter v : Word)
    (J G K R Q : List Word) (i0 i1 i2 i3 i4 i5 i6 i7 i8 i9 i10 i11 i12 i13 i14 i15 i16 i17 : Word)
    (hGl : G.length = 4) (hKl : K.length = 4) (hRl : R.length = 4) (hQl : Q.length = 4) (j : Word)
    (hIv : noteState sp J j 1090 = [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17])
    (hpc : s.pc = 0x78021720#64) (hcode : CodeAt F_78021720.base F_78021720.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = spn) (hstk : StackOk Ro.layout 0x180 spn)
    (hsp_lo : 0x10000 ≤ sp.toNat) (hsp_hi : sp.toNat ≤ 0x78000000)
    (ha0 : s.getReg .x10 = iter)
    (hI : Region iter [i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10, i11, i12, i13, i14, i15, i16, i17] s)
    (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi iter 18)
    (hGr : Region (sp + 18446744073709551408#64) G s) (hokG : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551408#64) 4)
    (hKr : Region (sp + 18446744073709551440#64) K s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551440#64) 4)
    (hVr : Region (sp + 18446744073709551472#64) [v] s) (hokV : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551472#64) 1)
    (hRr : Region (sp + 18446744073709551480#64) R s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551480#64) 4)
    (hQr : Region (sp + 18446744073709551512#64) Q s) (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 18446744073709551512#64) 4)
    (hdjIG : Disjoint iter 18 (sp + 18446744073709551408#64) 4) (hdjIK : Disjoint iter 18 (sp + 18446744073709551440#64) 4)
    (hdjIV : Disjoint iter 18 (sp + 18446744073709551472#64) 1) (hdjIR : Disjoint iter 18 (sp + 18446744073709551480#64) 4)
    (hdjIQ : Disjoint iter 18 (sp + 18446744073709551512#64) 4)
    (hdjS : Disjoint (spn - 0x180#64) 48 iter 18)
    (hdjSG : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551408#64) 4) (hdjSK : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551440#64) 4)
    (hdjSV : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551472#64) 1) (hdjSR : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551480#64) 4)
    (hdjSQ : Disjoint (spn - 0x180#64) 48 (sp + 18446744073709551512#64) 4)
    (hk : ∀ (t : MachineState) (i0' i1' i2' i3' i4' i5' i6' i7' i8' i9' i10' i11' i12' i13' i14' i15' i16' i17' : Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code → Unchanged [(spn - 0x180#64, 48), (iter, 18)] s t →
      noteState sp J j 1091 = [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11', i12', i13', i14', i15', i16', i17'] → Region iter [i0', i1', i2', i3', i4', i5', i6', i7', i8', i9', i10', i11', i12', i13', i14', i15', i16', i17'] t →
      t.getReg .x10 = 2#64 → Safe P t) :
    Safe P s := by
  rw [← hIv] at hI
  refine pad_next_note_spec s ra spn sp iter v J G K R Q hGl hKl hRl hQl j 1090 (by decide) hpc hcode hcw hra hra1 hsp hstk hsp_lo hsp_hi ha0 hI hokI hGr hokG hKr hokK hVr hokV hRr hokR hQr hokQ hdjIG hdjIK hdjIV hdjIR hdjIQ hdjS hdjSG hdjSK hdjSV hdjSR hdjSQ ?_
  intro t h1 h2 h3 h4 h5 h6
  rw [list18_cells _ (noteState_length sp J j 1091)] at h5
  exact hk t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 rfl h5 (by rw [h6, if_neg (by decide)])

end Cases.Zip2005
