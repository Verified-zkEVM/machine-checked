import Cases.Zip2005.Sinsemilla.FromIterIvkSpec
import Cases.Zip2005.Runtime.ReserveOr
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `from_iter` of `commit_ivk`'s iterator, as its callers' contract

`from_iter_ivk_contract` proves the contract `hfrom_ivk` that `commit_ivk_spec` and `main_spec` state
(ledger A8) from the function's specification `from_iter_ivk_spec`, under the allocator's two
instances at `from_iter`'s call sites (`halloc_fi`, `hreserve_fi`: ledger A4, A5) keeping the
hasher's tables, and the two failure arms (A11). The contract's premises are the facts the
function needs that a caller has at the call: the tables' lengths, bounds and `RegionOk`, the
caller's stack (`StackOk Ro.layout 0xaa0 sp0`, the message words in its frame), the message block off the
callee's frame, its output and its block, those two off the heap.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

theorem ivkMsg_ptrA (sp0 : Word) : sp0 - 0xaa0#64 + 0x9c8#64 = ptrA sp0 := by
  unfold ptrA; bv_omega

theorem ivkMsg_ptrB (sp0 : Word) : ptrA sp0 + BitVec.ofNat 64 (8 * 4) = ptrB sp0 := by
  unfold ptrA ptrB; bv_omega

theorem ptrA_toNat {sp0 : Word} (h : StackOk Ro.layout 0xaa0 sp0) : (ptrA sp0).toNat = sp0.toNat - 216 := by
  have := h.lo; unfold ptrA; bv_omega

theorem frame_ivk_sub (sp : Word) : sp - 0xb0#64 - 0x1b0#64 = sp - 0x260#64 := by
  bv_omega

set_option maxHeartbeats 4000000 in
theorem from_iter_ivk_contract {G : MachineState → Prop} {nb : Nat} {P : Prop} (s : MachineState)
    (hcode : CodeAt F_7801e110.base F_7801e110.prog s) (hcodeN : CodeAt F_78021e7c.base F_78021e7c.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeZ : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (halloc_fi : ∀ (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word),
      0x78040620 ≤ iptr.toNat → 0x78040620 ≤ tg0.toNat → 0x78040620 ≤ tg1.toNat → 0x78040620 ≤ tg2.toNat →
      0x78040620 ≤ tg3.toNat → IV.length = 138 → G0.length = 1024 → G1.length = 1024 →
      G2.length = 1024 → G3.length = 516 → ∀ (u : MachineState) (sp : Word) (L' : List (Word × Nat)), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801e184#64 → u.getReg .x2 = sp → StackOk Ro.layout 0x30 sp →
      u.getReg .x10 = 8#64 → u.getReg .x11 = 1#64 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      RoImage Ro.layout u → Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') u →
      (∀ (t : MachineState) (ptr : Word) (B0 : List Word), t.pc = 0x7801e184#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B0.length = 1 → Region ptr B0 t → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 1 →
        (ptr.toNat = 0 ∨ 0x78048980 ≤ ptr.toNat) → ptr.toNat + 8 ≤ 0x1c00000000 →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
      Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t →
        Disjoint 0x780488a8#64 10 ptr 1 → Disjoint iptr 138 ptr 1 → Disjoint tg0 1024 ptr 1 → Disjoint tg1 1024 ptr 1 → Disjoint tg2 1024 ptr 1 → Disjoint tg3 516 ptr 1 →
        Run.HeapAt ((ptr, 1) :: (iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') t → SafeN G nb P t) → SafeN G nb P u)
    (hcodeR : CodeAt F_780221a4.base F_780221a4.prog s) (hcodeG : CodeAt F_7802225c.base F_7802225c.prog s)
    (hrealloc_fi : ReallocOrFi G nb P s.code)
    (hunwrap_opt : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803f364#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_f364 → SafeN G nb P u)
    (hhandle_rv : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803cf14#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u) :
    ∀ (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word),
      ∀ (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word) (sp0 : Word)
      (J0 : List Word) (a0 a1 a2 a3 n0 n1 n2 n3 : Word) (L' : List (Word × Nat)), O1.length = 3 →
      u.pc = 0x7801e110#64 → u.code = s.code → u.getReg .x1 = 0x780212ac#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x260 sp' → u.getReg .x10 = a0' → u.getReg .x11 = a1' →
      Region a0' O1 u → Region a1' [0#64, j] u →
      Region (a1' + 0x10#64) (iterIvkW sp0 J0) u →
      Region (a1' + 0x58#64) [0#64] u →
      Region (sp0 - 0xaa0#64 + 0x9c8#64) (ivkMsgW [a0, a1, a2, a3] [n0, n1, n2, n3]) u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 3 → RegionOk Ro.layout.roBase Ro.layout.textHi a1' 12 →
      Disjoint (sp' - 0x260#64) 76 a0' 3 → Disjoint (sp' - 0x260#64) 76 a1' 12 →
      Disjoint a0' 3 a1' 12 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      IV.length = 138 → G0.length = 1024 → G1.length = 1024 → G2.length = 1024 → G3.length = 516 →
      0x78048980 ≤ iptr.toNat → iptr.toNat + 8 * 138 ≤ 0x1c00000000 →
      0x78048980 ≤ tg0.toNat → tg0.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg1.toNat → tg1.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg2.toNat → tg2.toNat + 8 * 1024 ≤ 0x1c00000000 →
      0x78048980 ≤ tg3.toNat → tg3.toNat + 8 * 516 ≤ 0x1c00000000 →
      RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 → RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 →
      StackOk Ro.layout 0xaa0 sp0 →
      Disjoint (sp' - 0x260#64) 76 (sp0 - 0xaa0#64 + 0x9c8#64) 8 → Disjoint a0' 3 (sp0 - 0xaa0#64 + 0x9c8#64) 8 → Disjoint a1' 12 (sp0 - 0xaa0#64 + 0x9c8#64) 8 →
      Disjoint 0x78040620#64 14780694332 a0' 3 → Disjoint 0x78040620#64 14780694332 a1' 12 →
      a0'.toNat + 8 * 3 ≤ 0x78040620 → a1'.toNat + 8 * 12 ≤ 0x78040620 →
      RoImage Ro.layout u → Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') u →
      (∀ (t : MachineState) (cap ptr : Word) (J Bv : List Word), t.pc = 0x780212ac#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x260#64, 76), (a0', 3), (a1', 12), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        J.length = 12 → Region a0' [cap, ptr, 510#64] t → cap ≠ 0#64 → Region a1' J t →
        Bv.length = 65 →
        (∀ o, o < 510 → byteAt Bv o = bw (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3]) o)) →
        Region ptr Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 65 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t →
        Run.HeapAt ((ptr, 64) :: (iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') t → SafeN G nb P t) → SafeN G nb P u := by
  intro tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx IV G0 G1 G2 G3 u sp' a0' a1' j O1 sp0 J0 a0 a1 a2 a3 n0 n1 n2 n3 L'
    hO1l hpc hcu hra hsp hstk ha0 ha1 hO hC0 hCit hC58 hM hokO hokC hdjSO hdjSC hdjOC hTB hIVr hG0 hG1 hG2
    hG3 hIVl hG0l hG1l hG2l hG3l hlo1 hhi1 hlo2 hhi2 hlo3 hhi3 hlo4 hhi4 hlo5 hhi5 hok1 hok2 hok3 hok4
    hok5 hstk0 hdjSM hdjOM hdjCM hdjHO hdjHC hout ha1lo hro hheap hk
  let T : HasherT := ⟨0x780488a8#64, iptr, tg0, tg1, tg2, tg3, [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64], IV, G0, G1, G2, G3,
    rfl, hIVl, hG0l, hG1l, hG2l, hG3l⟩
  have hTA : Arena6 T :=
    ⟨show 0x78040620 ≤ (0x780488a8#64).toNat by decide,
     show (0x780488a8#64).toNat + 8 * 10 ≤ 0x1c00000000 by decide,
     show 0x78040620 ≤ iptr.toNat by omega, show iptr.toNat + 8 * 138 ≤ 0x1c00000000 by omega,
     show 0x78040620 ≤ tg0.toNat by omega, show tg0.toNat + 8 * 1024 ≤ 0x1c00000000 by omega,
     show 0x78040620 ≤ tg1.toNat by omega, show tg1.toNat + 8 * 1024 ≤ 0x1c00000000 by omega,
     show 0x78040620 ≤ tg2.toNat by omega, show tg2.toNat + 8 * 1024 ≤ 0x1c00000000 by omega,
     show 0x78040620 ≤ tg3.toNat by omega, show tg3.toNat + 8 * 516 ≤ 0x1c00000000 by omega⟩
  have hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi 0x780488a8#64 10 :=
    RegionOk.of_nat (by decide) (by decide) (Or.inr (by decide))
  have hTO : Ok6 T := ⟨hok0, hok1, hok2, hok3, hok4, hok5⟩
  have hK : Kept6 T u := ⟨hTB, hIVr, hG0, hG1, hG2, hG3⟩
  -- the stack: the loop frame `sp' - 0xb0`, the caller's frame `sp0`
  have hlo' := hstk.lo
  have hhi' := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hlo0 := hstk0.lo
  have hhi0 := (Nat.le_trans hstk0.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hal0 := hstk0.aligned
  have hsub : (sp' - 0xb0#64).toNat = sp'.toNat - 0xb0 := toNat_sub_lit sp' 0xb0 (by omega)
  have hstk' : StackOk Ro.layout 0x1b0 (sp' - 0xb0#64) := ⟨by have := hstk.aligned; omega, by omega, by rw [Ro.layout_stackTop]; omega⟩
  have hokFr : RegionOk Ro.layout.roBase Ro.layout.textHi (sp' - 0xb0#64) 22 :=
    RegionOk.of_nat (by have := hstk.aligned; omega) (by unfold SP1_MAX_MEMORY; omega)
      (Or.inl (by simp only [Ro.layout_roBase]; omega))
  have hsp' : u.getReg .x2 = sp' - 0xb0#64 + 0xb0#64 := by rw [hsp, BitVec.sub_add_cancel]
  -- the message words: `ak`'s at `ptrA sp0`, `nk`'s after them
  have hA4 := ptrA_toNat hstk0
  rw [ivkMsg_ptrA] at hM hdjSM hdjOM hdjCM
  unfold ivkMsgW at hM
  have hAr : Region (ptrA sp0) (reprW [a0, a1, a2, a3]) u := by
    have h := hM.take 4
    rwa [List.take_left' (by simp [reprW])] at h
  have hBr : Region (ptrB sp0) (reprW [n0, n1, n2, n3]) u := by
    have h := hM.shift 4
    rwa [List.drop_left' (by simp [reprW]), ivkMsg_ptrB] at h
  have hokA : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrA sp0) 4 :=
    RegionOk.of_nat (by omega) (by unfold SP1_MAX_MEMORY; omega) (Or.inl (by simp only [Ro.layout_roBase]; omega))
  have hokB : RegionOk Ro.layout.roBase Ro.layout.textHi (ptrB sp0) 4 := by
    rw [← ivkMsg_ptrB]
    exact RegionOk.of_nat (by rw [toNat_add_lit _ _ (by omega)]; omega)
      (by rw [toNat_add_lit _ _ (by omega)]; unfold SP1_MAX_MEMORY; omega)
      (Or.inl (by rw [toNat_add_lit _ _ (by omega)]; simp only [Ro.layout_roBase]; omega))
  have dA : ∀ {b : Word} {n : Nat}, AsmVerif.RiscV.Sym.Disjoint b n (ptrA sp0) 8 → AsmVerif.RiscV.Sym.Disjoint b n (ptrA sp0) 4 :=
    fun h => h.sub_right (self_add_zero _) (by omega)
  have dB : ∀ {b : Word} {n : Nat}, AsmVerif.RiscV.Sym.Disjoint b n (ptrA sp0) 8 → AsmVerif.RiscV.Sym.Disjoint b n (ptrB sp0) 4 :=
    fun h => h.sub_right (ivkMsg_ptrB sp0).symm (by omega)
  have hdjHM : AsmVerif.RiscV.Sym.Disjoint 0x78040620#64 14780694332 (ptrA sp0) 8 := by
    unfold AsmVerif.RiscV.Sym.Disjoint; simp only [BitVec.toNat_ofNat]; omega
  have hdjAB : AsmVerif.RiscV.Sym.Disjoint (ptrA sp0) 4 (ptrB sp0) 4 :=
    AsmVerif.RiscV.Sym.Disjoint.within (N := 8) (by omega) (self_add_zero _) (ivkMsg_ptrB sp0).symm (by omega) (by omega)
      (Or.inl (by omega))
  rw [← frame_ivk_sub] at hdjSM hdjSO hdjSC
  -- the iterator block as `commit_ivk` built it
  have hCb : Region a1' (ivkState sp0 J0 j 0) u := by
    rw [ivkState_zero]
    exact Region.append' (Region.append' hC0 hCit rfl) hC58 rfl
  refine from_iter_ivk_spec (L := L') u (sp' - 0xb0#64) sp0 a0' a1' 0x780212ac#64 J0 (reprW [a0, a1, a2, a3])
    (reprW [n0, n1, n2, n3]) O1 j (by simp [reprW]) (by simp [reprW]) hO1l hpc (codeAt_of_code_eq hcu hcode)
    (codeAt_of_code_eq hcu hcodeN) (codeAt_of_code_eq hcu hcodeM) (codeAt_of_code_eq hcu hcodeZ)
    (codeWithin_of_code_eq hcu hcw) hra (by decide) hsp' hstk' hokFr ha0 ha1 hO hokO hCb hokC hAr hokA hBr
    hokB (by omega) hhi0 (dA hdjSM) (dB hdjSM) hdjSO hdjSC (dA hdjOM) (dB hdjOM) hdjOC (dA hdjCM) (dB hdjCM)
    hdjAB (dA hdjHM) (dB hdjHM) hdjHO hdjHC hout ha1lo T hK hTA hTO hro hheap
    (fun u' L'' h1 h2 =>
      halloc_fi tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx IV G0 G1 G2 G3 hTA.lo2 hTA.lo3 hTA.lo4 hTA.lo5 hTA.lo6 hIVl hG0l hG1l hG2l hG3l u' _ L'' h1 (h2.trans hcu))
    (fun u' C p W L'' hC hW h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 r1 r2 r3 r4 r5 r6 hr hh k =>
      reserve_or_fi s hcodeR hcodeG hcw hrealloc_fi hhandle_rv T hTA rfl u' _ _ C p W L'' hC hW h1 (h2.trans hcu) h3
        (by decide) h4 h5 (hokFr.sub' 0 3 (by decide) (by simp)) h6 h7 h8 h9 h10 h11 h12 h13 h14
        r1 r2 r3 r4 r5 r6 hr hh k)
    (fun u' sp'' L'' h1 h2 => hunwrap_opt u' sp'' L'' h1 (h2.trans hcu)) (fun u' sp'' L'' h1 h2 => hhandle_rv u' sp'' L'' h1 (h2.trans hcu)) ?_
  intro t ptr Bv I1 hpc' hcs hcode' hun hI1l hOut hR1 hBvl hbits hBv hokBv hlo hhi hKt hheapT
  rw [frame_ivk_sub] at hun
  exact hk t 512#64 ptr I1 Bv hpc' hcs hcode' hun hI1l hOut (by decide) hR1 hBvl hbits hBv hokBv hlo hhi
    hKt.r1 hKt.r2 hKt.r3 hKt.r4 hKt.r5 hKt.r6 hheapT

end Cases.Zip2005
