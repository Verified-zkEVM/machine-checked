import Cases.Zip2005.Poseidon.PoseidonSponge
import Cases.Zip2005.Poseidon.PoseidonHash
import Cases.Zip2005.Field.FromU128
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Kit.RegionGlue
import Cases.Zip2005.Field.PowT
import Cases.Zip2005.Image.F_780207e8
import Cases.Zip2005.Image.Ro

/-!
# `orchard::spec::prf_nf` (`0x780207e8`)

`Hash::<Fp, P128Pow5T3, ConstantLength<2>, 3, 2>::init().hash([nk, rho])`: the capacity element
`from_u128(2 << 64)`, the round constants and matrices from `P128Pow5T3::constants()` (a heap
`Vec`, ledger finding T2: the allocator is a contract here), the state `(0, 0, capacity)`, the
input `[Some(nk), Some(rho)]`, one `poseidon_sponge`, and the first squeezed word. The `Vec` is
freed on the way out.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
theorem prf_nf_spec {P : Prop} (s : MachineState) (ra sp out nk rho : Word)
    (n0 n1 n2 n3 r0 r1 r2 r3 : Word)
    (hpc : s.pc = 0x780207e8#64) (hcode : CodeAt F_780207e8.base F_780207e8.prog s)
    (hcodeU : CodeAt F_78029ae8.base F_78029ae8.prog s) (hcodeR : CodeAt F_78028298.base F_78028298.prog s)
    (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeG : CodeAt F_7801e26c.base F_7801e26c.prog s)
    (hcodeF : CodeAt F_7801f120.base F_7801f120.prog s) (hcodeP : CodeAt F_7801ed68.base F_7801ed68.prog s)
    (hcodeX : CodeAt F_7801e704.base F_7801e704.prog s) (hcodeB : CodeAt F_78023a18.base F_78023a18.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s) (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x9b0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = nk) (ha2 : s.getReg .x12 = rho)
    (hN : Region nk [n0, n1, n2, n3] s) (hokN : RegionOk Ro.layout.textLo Ro.layout.textHi nk 4)
    (hR : Region rho [r0, r1, r2, r3] s) (hokR : RegionOk Ro.layout.textLo Ro.layout.textHi rho 4)
    (hnl : leLimbsToNat [n0, n1, n2, n3] < Fp.p) (hrl : leLimbsToNat [r0, r1, r2, r3] < Fp.p)
    (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 4)
    (hd0 : Disjoint (sp - 0x9b0#64) 310 nk 4) (hd1 : Disjoint (sp - 0x9b0#64) 310 rho 4)
    (hd2 : Disjoint (sp - 0x9b0#64) 310 out 4) (hd3 : Disjoint out 4 nk 4) (hd4 : Disjoint out 4 rho 4)
    (hh0 : Disjoint 0x78040620#64 14780694332 nk 4) (hh1 : Disjoint 0x78040620#64 14780694332 rho 4)
    (hh2 : Disjoint 0x78040620#64 14780694332 out 4)
    -- `P128Pow5T3::constants()` at its call site here (ledger T2): a `Vec` of the 64 rows of round
    -- constants (capacity 64, length 64) and the two matrices, the `Vec` in a fresh heap block
    (hconst : ∀ (u : MachineState) (sp' a0' : Word) (O1 O2 O3 : List Word),
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
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 768 ≤ 0x1c00000000 → Safe P t) → Safe P u)
    -- `__rust_dealloc(ptr, 64 * 96, 8)` at its call site here (ledger T2)
    (hdealloc : ∀ (u : MachineState) (sp' ptr : Word) (C : List Word), C.length = 768 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x78020c64#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = 6144#64 →
      u.getReg .x12 = 8#64 → Region ptr C u → 0x78048980 ≤ ptr.toNat →
      ptr.toNat + 8 * 768 ≤ 0x1c00000000 →
      (∀ t, t.pc = 0x78020c64#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Safe P t) → Safe P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x9b0#64, 310), (out, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      ∀ o0 o1 o2 o3 : Word, Region out [o0, o1, o2, o3] t →
      leLimbsToNat [o0, o1, o2, o3] =
        Poseidon.hash2 (leLimbsToNat [n0, n1, n2, n3]) (leLimbsToNat [r0, r1, r2, r3]) →
      Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x9b0#64) 310 := hstk.frame 310 (by decide)
  -- the frame (below it 0x300 bytes for the callees' frames): [0, 0x1f8) scratch, the `constants()` output in three pieces, the sponge state
  -- (later its output), [0x4b0, 0x648) scratch, the save area
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x6b0#64) 63 := hokW.sub' 96 63 (by decide) (by bv_omega)
  have hokB1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x6b0#64 + 0x1f8#64) 3 := hokW.sub' 159 3 (by decide) (by bv_omega)
  have hokB2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x6b0#64 + 0x210#64) 36 := hokW.sub' 162 36 (by decide) (by bv_omega)
  have hokB3 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x6b0#64 + 0x330#64) 36 := hokW.sub' 198 36 (by decide) (by bv_omega)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x6b0#64 + 0x450#64) 12 := hokW.sub' 234 12 (by decide) (by bv_omega)
  have hokD : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x6b0#64 + 0x4b0#64) 51 := hokW.sub' 246 51 (by decide) (by bv_omega)
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x6b0#64 + 0x648#64) 13 := hokW.sub' 297 13 (by decide) (by bv_omega)
  obtain ⟨A, hA, hAl⟩ := Region.exists_junk (sp - 0x6b0#64) 63 s
  obtain ⟨B1, hB1, hB1l⟩ := Region.exists_junk (sp - 0x6b0#64 + 0x1f8#64) 3 s
  obtain ⟨B2, hB2, hB2l⟩ := Region.exists_junk (sp - 0x6b0#64 + 0x210#64) 36 s
  obtain ⟨B3, hB3, hB3l⟩ := Region.exists_junk (sp - 0x6b0#64 + 0x330#64) 36 s
  obtain ⟨C, hC, hCl⟩ := Region.exists_junk (sp - 0x6b0#64 + 0x450#64) 12 s
  obtain ⟨D, hD, hDl⟩ := Region.exists_junk (sp - 0x6b0#64 + 0x4b0#64) 51 s
  obtain ⟨E, hE, hEl⟩ := Region.exists_junk (sp - 0x6b0#64 + 0x648#64) 13 s
  obtain ⟨O, hO, hOl⟩ := Region.exists_junk out 4 s
  have hokH : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hlo := hstk.lo
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hu := Unchanged.refl [(sp - 0x9b0#64, 310), (out, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  sym_exec [from_u128_spec, hconst, memcpy288_spec, memcpy96_spec] stop [0x78020990]
  -- the frame as the sponge sees it: the input, the `Vec` header, the state, the matrix (its
  -- destination straddles two of `constants()`'s pieces), the rest, and the state area split at
  -- the sponge's output
  have hI : Region (sp - 1712#64 + 504#64) [1#64, n0, n1, n2, n3, 1#64, r0, r1, r2, r3] s_111 :=
    Region.append' hR3 (hR4.sub 0 7 (a := sp - 1712#64 + 528#64) (by simp) rfl) (by rw [BitVec.add_assoc]; rfl)
  have hV : Region (sp - 1712#64 + 584#64) [64#64, post26_4, 64#64] s_111 :=
    hR4.sub 7 3 (by rw [BitVec.add_assoc]; rfl) rfl
  have hSt : Region (sp - 1712#64 + 608#64) [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, BitVec.ofNat 64 (acc22_0 >>> (64 * 0)), BitVec.ofNat 64 (acc22_0 >>> (64 * 1)), BitVec.ofNat 64 (acc22_0 >>> (64 * 2)), BitVec.ofNat 64 (acc22_0 >>> (64 * 3))] s_111 :=
    hR4.sub 10 12 (by rw [BitVec.add_assoc]; rfl) rfl
  have hMp : Region (sp - 1712#64 + 704#64) [7128413682704914324#64, 2541518119044464568#64, 2301721381290370669#64, 8497410018793648975#64, 8714509316184371464#64, 3991324137857751228#64, 10614140465288988189#64, 10595461815445677236#64, 15911758082453561645#64, 3307404868635583373#64, 1122944341850886946#64, 1489648621244851419#64, 4613860281249852765#64, 2450264367771645014#64, post26_5[0]!, post26_5[1]!, post26_5[2]!, post26_5[3]!, post26_5[4]!, post26_5[5]!, post26_5[6]!, post26_5[7]!, post26_5[8]!, post26_5[9]!, post26_5[10]!, post26_5[11]!, post26_5[12]!, post26_5[13]!, post26_5[14]!, post26_5[15]!, post26_5[16]!, post26_5[17]!, post26_5[18]!, post26_5[19]!, post26_5[20]!, post26_5[21]!] s_111 :=
    Region.append' (hR4.sub 22 14 (by rw [BitVec.add_assoc]; rfl) rfl)
      (hR5.sub 0 22 (a := sp - 1712#64 + 816#64) (by simp) rfl) (by rw [BitVec.add_assoc]; rfl)
  have hRest : Region (sp - 1712#64 + 992#64) [post26_5[22]!, post26_5[23]!, post26_5[24]!, post26_5[25]!, post26_5[26]!, post26_5[27]!, post26_5[28]!, post26_5[29]!, post26_5[30]!, post26_5[31]!, post26_5[32]!, post26_5[33]!, post26_5[34]!, post26_5[35]!] s_111 :=
    hR5.sub 22 14 (by rw [BitVec.add_assoc]; rfl) rfl
  have hOut : Region (sp - 1712#64 + 1104#64) [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, BitVec.ofNat 64 (acc22_0 >>> (64 * 0)), BitVec.ofNat 64 (acc22_0 >>> (64 * 1))] s_111 :=
    hR6.sub 0 10 (a := sp - 1712#64 + 1104#64) (by simp) rfl
  have hC2 : Region (sp - 1712#64 + 1184#64) [BitVec.ofNat 64 (acc22_0 >>> (64 * 2)), BitVec.ofNat 64 (acc22_0 >>> (64 * 3))] s_111 :=
    hR6.sub 10 2 (by rw [BitVec.add_assoc]; rfl) rfl
  clear hR3 hR4 hR5 hR6
  have hokI : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 1712#64 + 504#64) 10 := hokW.sub' 159 10 (by decide) (by bv_omega)
  have hokV : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 1712#64 + 584#64) 3 := hokW.sub' 169 3 (by decide) (by bv_omega)
  have hokSt : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 1712#64 + 608#64) 12 := hokW.sub' 172 12 (by decide) (by bv_omega)
  have hokMp : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 1712#64 + 704#64) 36 := hokW.sub' 184 36 (by decide) (by bv_omega)
  have hokRest : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 1712#64 + 992#64) 14 := hokW.sub' 220 14 (by decide) (by bv_omega)
  have hokOut : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 1712#64 + 1104#64) 10 := hokW.sub' 234 10 (by decide) (by bv_omega)
  have hokC2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 1712#64 + 1184#64) 2 := hokW.sub' 244 2 (by decide) (by bv_omega)
  clear hokB1 hokB2 hokB3 hokC
  -- what the sponge needs of the state and the input
  have hcapdef := acc22_0_def
  have hcap : leLimbsToNat [BitVec.ofNat 64 (acc22_0 >>> (64 * 0)), BitVec.ofNat 64 (acc22_0 >>> (64 * 1)), BitVec.ofNat 64 (acc22_0 >>> (64 * 2)), BitVec.ofNat 64 (acc22_0 >>> (64 * 3))] = acc22_0 := cells_lt (acc22_0_def ▸ Fp.mul_lt _ _)
  have hxl2 : leLimbsToNat [BitVec.ofNat 64 (acc22_0 >>> (64 * 0)), BitVec.ofNat 64 (acc22_0 >>> (64 * 1)), BitVec.ofNat 64 (acc22_0 >>> (64 * 2)), BitVec.ofNat 64 (acc22_0 >>> (64 * 3))] < Fp.p := by rw [hcap, ← acc22_0_def]; exact Fp.mul_lt _ _
  have hxl0 : leLimbsToNat [0#64, 0#64, 0#64, 0#64] < Fp.p := by decide
  have hinp : (sp + 18446744073709550408#64 == 0#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; have := hstk.lo; bv_omega
  sym_forget
  sym_reframe
  sym_exec [memcpy288_spec, memcpy96_spec, sponge_spec, hdealloc]
  have hcs : s_77.code = s.code := hcode.trans hcode0
  sym_close hk
  -- the first squeezed word is `Hash::hash([nk, rho])`
  have e := congrArg Prod.fst post11_18
  have z : leLimbsToNat [0#64, 0#64, 0#64, 0#64] = 0 := by decide
  have c : leLimbsToNat [0#64, 2#64, 0#64, 0#64] = 2 ^ 65 := by decide
  rw [hcap, ← hcapdef, c, z] at e
  unfold Poseidon.hash2 Poseidon.capacity
  exact e

end Cases.Zip2005
