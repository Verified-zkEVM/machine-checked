/-
  Cases.Zip2005.EpMulFq

  `<Ep as Mul<&Fq>>::mul`: pushes a frame, calls `sp1_pallas::zkvm::mul`, returns.
-/

import Cases.Zip2005.Curve.Mul
import Cases.Zip2005.Image.F_7802827c
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- `<Ep as Mul<&Fq>>::mul`: a frame around `sp1_pallas::zkvm::mul`. -/
theorem ep_mul_fq_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra a0 a1 a2 sp : Word) (pt k O : List Word)
    (hptl : pt.length = 12) (hkl : k.length = 4) (hOl : O.length = 12)
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G n P u)
    (hpc : s.pc = 0x7802827c#64) (hcodeW : CodeAt F_7802827c.base F_7802827c.prog s)
    (hcode : CodeAt F_78031be8.base F_78031be8.prog s)
    (hcodeBB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeMS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeC : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeRp : CodeAt F_78029468.base F_78029468.prog s)
    (hcodeRq : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    (hcodeA : CodeAt F_78035fe0.base F_78035fe0.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hcodeCpy : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcodeD : CodeAt F_780360c8.base F_780360c8.prog s)
    (hcodeL : CodeAt F_780360e0.base F_780360e0.prog s)
    (hcodeAF : CodeAt F_7803a110.base F_7803a110.prog s)
    (hcodeAFI : CodeAt F_7803dd28.base F_7803dd28.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x4a0 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1) (ha2 : s.getReg .x12 = a2)
    (hp : Region a1 pt s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hk : Region a2 k s) (hok2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 12)
    (hd0 : Disjoint (sp - 0x4a0#64) 148 a0 12) (hd1 : Disjoint (sp - 0x4a0#64) 148 a1 12)
    (hd2 : Disjoint (sp - 0x4a0#64) 148 a2 4)
    (hd01 : Disjoint a0 12 a1 12) (hd02 : Disjoint a0 12 a2 4)
    (hk' : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x4a0#64, 148), (a0, 12)] s t → (mulW pt k).length = 12 →
      Region a0 (mulW pt k) t → mulFacts pt k → SafeN G n P t) :
    SafeN G n P s := by
  obtain ⟨FB, hFB, hFBl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x4a0#64) 148 := hstk.frame 148 (by decide)
  have hokFB : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokA.sub' 146 2 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 0x4a0#64, 148), (a0, 12)] s
  have hstkM : StackOk Ro.layout 0x490 (sp - 0x10#64) := by
    obtain ⟨h1, h2, h3⟩ := hstk
    rw [Ro.layout_stackTop] at h3
    have e : (sp - 0x10#64).toNat = sp.toNat - 0x10 := by
      rw [BitVec.toNat_sub, Bn.toNat_ofNat']; omega
    exact ⟨by rw [e]; omega, by rw [e]; omega, by rw [e, Ro.layout_stackTop]; omega⟩
  have M := fun (t : MachineState) (hc : t.code = s.code) (L' : List (Word × Nat)) ra a0 a1 a2 sp pt k O hptl hkl hOl =>
    mul_spec (G := G) (n := n) (P := P) (L := L') t ra a0 a1 a2 sp pt k O hptl hkl hOl
      (fun u sp'' L'' hu hcu => hpanic u sp'' L'' hu (hcu.trans hc))
  sym_exec [M]
  sym_close hk'
  · exact length_mulW pt k
  · have e := acc4_0_def
    rw [list12_eta hptl, list4_eta hkl] at e
    rw [list12_eta (by rw [← e]; exact length_mulW pt k), ← e]
  · rw [list12_eta hptl, list4_eta hkl] at post4_6; exact post4_6

end Cases.Zip2005
