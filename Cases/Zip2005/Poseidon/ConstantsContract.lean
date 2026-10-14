import Cases.Zip2005.Poseidon.Constants
import Cases.Zip2005.Image.Ro

/-!
# `P128Pow5T3::constants()`, as its callers' contract

`constants_contract` proves the contract `hconst` that `prf_nf_spec`, `nullifier_derive_spec` and
`main_spec` state (ledger A7) from the function's specification `constants_spec`, under the
allocator's instance at its call site (`halloc_c`, ledger A4) and the reserve failure arm (A11).
The contract's struct, three regions at `a0'`, is the function's one 75-word output; its
`MDS_INV` is any 36 words, the function's `mdsInvWords`. Restated to be provable: the read-only
image at the call (the constants are read out of it) and the output off the heap.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

theorem const_frame_sub (sp : Word) : sp - 0x50#64 = sp - 0x60#64 + BitVec.ofNat 64 (8 * 2) := by
  bv_omega

set_option maxHeartbeats 4000000 in
theorem constants_contract {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState)
    (hcode : CodeAt F_78023cbc.base F_78023cbc.prog s) (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcodeCpy : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (halloc_c : ∀ (u : MachineState) (sp' : Word), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x78023cf4#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' → u.getReg .x10 = 0x1800#64 →
      u.getReg .x11 = 8#64 →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x78023cf4#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 768 → Region ptr B t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 768 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 0x1800 ≤ 0x1c00000000 → SafeN G n P t) → SafeN G n P u)
    (hhandle_rv : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → SafeN G n P u) :
    ∀ (u : MachineState) (sp' a0' : Word) (O1 O2 O3 : List Word),
      O1.length = 3 → O2.length = 36 → O3.length = 36 →
      u.pc = 0x78023cbc#64 → u.code = s.code → u.getReg .x1 = 0x7802084c#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x60 sp' → u.getReg .x10 = a0' →
      Region a0' O1 u → Region (a0' + 0x18#64) O2 u → Region (a0' + 0x138#64) O3 u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 75 → Disjoint (sp' - 0x60#64) 12 a0' 75 →
      RoImage Ro.layout u → Disjoint 0x78040620#64 14780694332 a0' 75 →
      (∀ t, t.pc = 0x7802084c#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x60#64, 12), (a0', 75), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        ∀ (ptr : Word) (MI : List Word), MI.length = 36 →
        Region a0' [64#64, ptr, 64#64] t → Region (a0' + 0x18#64) Poseidon.mdsWords t →
        Region (a0' + 0x138#64) MI t →
        Region ptr Poseidon.rcWords t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 768 → RegionOk Ro.layout.textLo Ro.layout.textHi ptr 768 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 → SafeN G n P t) → SafeN G n P u := by
  intro u sp' a0' O1 O2 O3 h1 h2 h3 hpc hcu hra hsp hstk ha0 hR1 hR2 hR3 hok hdj hro hdjH hk
  have hlo := hstk.lo
  have hstk50 : StackOk Ro.layout 0x50 sp' := ⟨hstk.aligned, by omega, hstk.hi⟩
  have hO : Region a0' (O1 ++ O2 ++ O3) u :=
    Region.append' (Region.append' hR1 hR2 (by rw [h1])) hR3 (by rw [List.length_append, h1, h2])
  refine constants_spec u 0x7802084c#64 sp' a0' (O1 ++ O2 ++ O3) (by simp [h1, h2, h3]) hpc
    (codeAt_of_code_eq hcu hcode) (codeAt_of_code_eq hcu hcodeSh) (codeAt_of_code_eq hcu hcodeCpy)
    (codeWithin_of_code_eq hcu hcw) hro hra (by decide) hsp hstk50 ha0 hO hok
    (hdj.of_sub (const_frame_sub sp') (by omega) (by rw [Nat.mul_zero, BitVec.add_zero]) (by omega)) hdjH
    (fun u' sp'' g1 g2 g3 g4 g5 g6 g7 k => halloc_c u' sp'' g1 (g2.trans hcu) g3 g4 g5 g6 g7 k)
    (fun u' g1 g2 => hhandle_rv u' g1 (g2.trans hcu)) ?_
  intro t ptr hpc' hcs hcode' hun hOut hRC hok1 hok2 hlo' hhi'
  have hun' : Unchanged [(sp' - 0x60#64, 12), (a0', 75), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t := by
    refine Unchanged.trans_cover (Unchanged.refl _ u) hun ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · refine ⟨(sp' - 0x60#64, 12), by simp, ?_⟩
      unfold Covers
      have e1 : (sp' - 0x60#64).toNat = sp'.toNat - 0x60 := by bv_omega
      have e2 : (sp' - 0x50#64).toNat = sp'.toNat - 0x50 := by bv_omega
      simp only [e1, e2]; omega
    · exact ⟨(a0', 75), by simp, le_refl _, le_refl _⟩
    · exact ⟨(0x78040620#64, 4162), by simp, le_refl _, le_refl _⟩
    · exact ⟨(0x78048980#64, 14780690128), by simp, le_refl _, le_refl _⟩
  rw [List.append_assoc] at hOut
  have L3 : ([64#64, ptr, 64#64] : List Word).length = 3 := rfl
  have hA := hOut.take 3
  rw [List.take_left' L3] at hA
  have hMN := hOut.shift 3
  rw [List.drop_left' L3] at hMN
  have hM := hMN.take 36
  rw [List.take_left' mdsWords_length] at hM
  have hN := hMN.shift 36
  rw [List.drop_left' mdsWords_length] at hN
  exact hk t hpc' hcs hcode' hun' ptr mdsInvWords mdsInvWords_length hA hM
    (by rw [BitVec.add_assoc] at hN; exact hN) hRC hok1 hok2 hlo' hhi'

end Cases.Zip2005
