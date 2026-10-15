import Cases.Zip2005.Sinsemilla.FromIterNoteSpec
import Cases.Zip2005.Runtime.ReserveOr
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `from_iter` of `NoteCommitment::derive`'s iterator, as its callers' contract

`from_iter_nc_contract` proves the contract `hfrom_nc` that `note_commitment_derive_spec` and
`main_spec` state (ledger A8) from the function's specification `from_iter_nc_spec`, under the
allocator's two instances at `from_iter`'s call sites (`halloc_nc`, `hreserve_nc`: ledger A4, A5)
and the reserve failure arm (A11). The contract asks for the 137 words that hold the 1090 bytes;
the function's buffer is 257 words (capacity 2048), of which those are the first.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

theorem ncMsg_eq (sp0 : Word) : sp0 - 0xb50#64 + 0xa80#64 = sp0 + 18446744073709551408#64 := by
  bv_omega

theorem ncMsg_toNat {sp0 : Word} (h : StackOk Ro.layout 0xb50 sp0) :
    (sp0 + 18446744073709551408#64).toNat = sp0.toNat - 208 := by
  have := h.lo; bv_omega

theorem frame_nc_sub (sp : Word) : sp - 0xe0#64 - 0x180#64 = sp - 0x260#64 := by
  bv_omega

theorem byteAt_take {Bv : List Word} {n o : Nat} (h : o / 8 < n) : byteAt (Bv.take n) o = byteAt Bv o := by
  unfold byteAt
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_take, if_pos h]

set_option maxHeartbeats 4000000 in
theorem from_iter_nc_contract {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState)
    (hcode : CodeAt F_7801dfb4.base F_7801dfb4.prog s) (hcodeN : CodeAt F_78021720.base F_78021720.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeZ : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (halloc_nc : ∀ (u : MachineState) (sp : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801e028#64 → u.getReg .x2 = sp → StackOk Ro.layout 0x30 sp →
      u.getReg .x10 = 8#64 → u.getReg .x11 = 1#64 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (ptr : Word) (B0 : List Word), t.pc = 0x7801e028#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B0.length = 1 → Region ptr B0 t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 8 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 1) :: L') t → SafeN G n P t) → SafeN G n P u)
    (hcodeR : CodeAt F_780221a4.base F_780221a4.prog s) (hcodeG : CodeAt F_7802225c.base F_7802225c.prog s)
    (hrealloc_nc : ReallocOrNc G n P s.code)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u) :
    ∀ (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word) (sp0 : Word)
      (J0 : List Word) (g0 g1 g2 g3 p0 p1 p2 p3 v r0 r1 r2 r3 q0 q1 q2 q3 : Word) (L' : List (Word × Nat)), O1.length = 3 →
      u.pc = 0x7801dfb4#64 → u.code = s.code → u.getReg .x1 = 0x78020dc4#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x260 sp' → u.getReg .x10 = a0' → u.getReg .x11 = a1' →
      Region a0' O1 u → Region a1' [0#64, j] u →
      Region (a1' + 0x10#64) (iterW sp0 J0) u →
      Region (a1' + 0x88#64) [0#64] u →
      Region (sp0 - 0xb50#64 + 0xa80#64) ([g0, g1, g2, g3, p0, p1, p2, p3, v] ++
        reprW [r0, r1, r2, r3] ++ reprW [q0, q1, q2, q3]) u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 3 → RegionOk Ro.layout.roBase Ro.layout.textHi a1' 18 →
      Disjoint (sp' - 0x260#64) 76 a0' 3 → Disjoint (sp' - 0x260#64) 76 a1' 18 →
      Disjoint a0' 3 a1' 18 →
      StackOk Ro.layout 0xb50 sp0 →
      Disjoint (sp' - 0x260#64) 76 (sp0 - 0xb50#64 + 0xa80#64) 17 → Disjoint a0' 3 (sp0 - 0xb50#64 + 0xa80#64) 17 → Disjoint a1' 18 (sp0 - 0xb50#64 + 0xa80#64) 17 →
      Disjoint 0x78040620#64 14780694332 a0' 3 → Disjoint 0x78040620#64 14780694332 a1' 18 →
      a0'.toNat + 8 * 3 ≤ 0x78040620 → a1'.toNat + 8 * 18 ≤ 0x78040620 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (cap ptr : Word) (J Bv : List Word), t.pc = 0x78020dc4#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x260#64, 76), (a0', 3), (a1', 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        J.length = 18 → Region a0' [cap, ptr, 1090#64] t → cap ≠ 0#64 → Region a1' J t →
        Bv.length = 137 →
        (∀ o, o < 1090 → byteAt Bv o = bw (noteBit [g0, g1, g2, g3] [p0, p1, p2, p3] v
          (reprW [r0, r1, r2, r3]) (reprW [q0, q1, q2, q3]) o)) →
        Region ptr Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 137 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 137 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 256) :: L') t →
        SafeN G n P t) → SafeN G n P u := by
  intro u sp' a0' a1' j O1 sp0 J0 g0 g1 g2 g3 p0 p1 p2 p3 v r0 r1 r2 r3 q0 q1 q2 q3 L' hO1l hpc hcu hra hsp
    hstk ha0 ha1 hO hC0 hCit hC88 hM hokO hokC hdjSO hdjSC hdjOC hstk0 hdjSM hdjOM hdjCM hdjHO hdjHC hout ha1lo
    hro hheap hk
  have hlo' := hstk.lo
  have hhi' := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hlo0 := hstk0.lo
  have hhi0 := (Nat.le_trans hstk0.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hal0 := hstk0.aligned
  have hsub : (sp' - 0xe0#64).toNat = sp'.toNat - 0xe0 := toNat_sub_lit sp' 0xe0 (by omega)
  have hstk' : StackOk Ro.layout 0x180 (sp' - 0xe0#64) := ⟨by have := hstk.aligned; omega, by omega, by rw [Ro.layout_stackTop]; omega⟩
  have hokFr : RegionOk Ro.layout.roBase Ro.layout.textHi (sp' - 0xe0#64) 28 :=
    RegionOk.of_nat (by have := hstk.aligned; omega) (by unfold SP1_MAX_MEMORY; omega)
      (Or.inl (by simp only [Ro.layout_roBase]; omega))
  have hsp' : u.getReg .x2 = sp' - 0xe0#64 + 0xe0#64 := by rw [hsp, BitVec.sub_add_cancel]
  -- the message block in the caller's frame: `g_d`, `pk_d`, `v`, `ρ`, `ψ`
  have hM0 := ncMsg_toNat hstk0
  rw [ncMsg_eq] at hM hdjSM hdjOM hdjCM
  have hokM : RegionOk Ro.layout.roBase Ro.layout.textHi (sp0 + 18446744073709551408#64) 17 :=
    RegionOk.of_nat (by omega) (by unfold SP1_MAX_MEMORY; omega) (Or.inl (by simp only [Ro.layout_roBase]; omega))
  have hdjHM : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 (sp0 + 18446744073709551408#64) 17 := by
    unfold AsmVerif.RiscV.Sym.Disjoint; simp only [BitVec.toNat_ofNat]; omega
  have hR4 : (reprW [r0, r1, r2, r3]).length = 4 := by simp [reprW]
  have hQ4 : (reprW [q0, q1, q2, q3]).length = 4 := by simp [reprW]
  have hGr : Region (sp0 + 18446744073709551408#64) [g0, g1, g2, g3] u := hM.sub 0 4 (self_add_zero _) rfl
  have hKr : Region (sp0 + 18446744073709551440#64) [p0, p1, p2, p3] u := hM.sub 4 4 (msg_K sp0) rfl
  have hVr : Region (sp0 + 18446744073709551472#64) [v] u := hM.sub 8 1 (msg_V sp0) rfl
  have hRr : Region (sp0 + 18446744073709551480#64) (reprW [r0, r1, r2, r3]) u :=
    hM.sub 9 4 (msg_R sp0) (by simp [hR4])
  have hQr : Region (sp0 + 18446744073709551512#64) (reprW [q0, q1, q2, q3]) u :=
    hM.sub 13 4 (msg_Q sp0) (by simp [hR4, hQ4, List.take_of_length_le])
  rw [← frame_nc_sub] at hdjSM hdjSO hdjSC
  have hCb : Region a1' (noteState sp0 J0 j 0) u := by
    rw [noteState_0]
    exact Region.append' (Region.append' hC0 hCit rfl) hC88 rfl
  refine from_iter_nc_spec (L := L') u (sp' - 0xe0#64) sp0 a0' a1' 0x78020dc4#64 v J0 [g0, g1, g2, g3] [p0, p1, p2, p3]
    (reprW [r0, r1, r2, r3]) (reprW [q0, q1, q2, q3]) O1 j rfl rfl hR4 hQ4 hO1l hpc
    (codeAt_of_code_eq hcu hcode) (codeAt_of_code_eq hcu hcodeN) (codeAt_of_code_eq hcu hcodeM)
    (codeAt_of_code_eq hcu hcodeZ) (codeWithin_of_code_eq hcu hcw) hro hheap hra (by decide) hsp' hstk' hokFr ha0 ha1
    hO hokO hCb hokC hGr hKr hVr hRr hQr hokM (by omega) hhi0 hdjSM hdjSO hdjSC hdjOM hdjOC hdjCM hdjHM
    hdjHO hdjHC hout ha1lo
    (fun u' L'' h1 h2 => halloc_nc u' _ L'' h1 (h2.trans hcu))
    (fun u' C p W L'' hC hW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hr hh k =>
      reserve_or_nc s hcodeR hcodeG hcw hrealloc_nc hhandle_rv u' _ _ C p W L'' hC hW h1 (h2.trans hcu) h3
        (by decide) h4 h5 (hokFr.sub' 0 3 (by decide) (by simp)) h6 h7 h8 h9 h10 h11 h12 h13 h14 hr hh k)
    (fun u' sp'' L'' h1 h2 => hhandle_rv u' sp'' L'' h1 (h2.trans hcu)) ?_
  intro t ptr Bv I1 hpc' hcs hcode' hun hI1l hOut hR1 hBvl hbits hBv hokBv hlo hhi hheapT
  rw [frame_nc_sub] at hun
  refine hk t 2048#64 ptr I1 (Bv.take 137) hpc' hcs hcode' hun hI1l hOut (by decide) hR1
    (by simp [hBvl]) ?_ (hBv.take 137) (hokBv.sub' 0 137 (by omega) (self_add_zero _)) hlo (by omega) hheapT
  intro o ho
  rw [byteAt_take (by omega)]
  exact hbits o ho

end Cases.Zip2005
