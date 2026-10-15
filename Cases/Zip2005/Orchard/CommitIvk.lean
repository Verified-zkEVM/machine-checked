import Cases.Zip2005.Sinsemilla.SinsemillaCommitIvk
import Cases.Zip2005.Sinsemilla.CachedCommitDomain
import Cases.Zip2005.Orchard.NoteCommitDerive
import Cases.Zip2005.Sinsemilla.ExtractPBottom
import Cases.Zip2005.Image.F_780203dc
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `orchard::spec::commit_ivk` (0x780203dc)

`CommitIvk_rivk(I2LEBSP_255(ak) ‖ I2LEBSP_255(nk))`: the domain `(Q, R)` from its raw
coordinates (`cached_commit_domain`), `to_le_bits` of `ak` and `nk` into the frame, the
`Pad<Chain<…>>` iterator over their bits (72 bytes), `CommitDomain::commit` (the `0x78021238`
instantiation, 51 chunks) and `extract_p_bottom` of its `Option<Ep>`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-! ## The model -/

/-- `Q^Orchard-CommitIvk`'s raw `x`, the read-only words at `0x780018a8`. -/
def qIvkX : List Word :=
  [0x6bcb2f92790f82f2#64, 0x421bcc245128a232#64, 0x7dcc81b85aa241fa#64, 0x5bc0cf14aa9c811#64]

/-- … its raw `y`, at `0x780018c8`. -/
def qIvkY : List Word :=
  [0xbe5ae5cecfaddebe#64, 0x46c4351dc96da5f1#64, 0xef59074620de054b#64, 0x1b014cf6d41abee6#64]

/-- `R^Orchard-CommitIvk`'s raw `x`, at `0x780018e8`. -/
def rIvkX : List Word :=
  [0x9823486e5ff8a118#64, 0x2957fe2d31aedc7#64, 0x1634290a40808948#64, 0x25a22ccd5070134e#64]

/-- … its raw `y`, at `0x78001908`. -/
def rIvkY : List Word :=
  [0x3fe793b3e37fdda9#64, 0x6b4442fb1b58a6c7#64, 0xc2c890c4284b5794#64, 0x29cfd29966a2faeb#64]

/-- `Q` as the guest holds it (Jacobian Montgomery limbs, `Z = R`). -/
def qIvkW : List Word := domainPtW qIvkX qIvkY

/-- `R` as the guest holds it. -/
def rIvkW : List Word := domainPtW rIvkX rIvkY

/-- Message bit `i` of `CommitIvk`: the 255 bits of `ak`, then the 255 bits of `nk`, each from
its canonical little-endian representation (`to_le_bits`). -/
def ivkBit (ak nk : List Word) (i : Nat) : Bool :=
  if i < 255 then wordsBit ak i else wordsBit nk (i - 255)

/-- The eight message words the iterator points to: `to_le_bits` of `ak`, then of `nk`. -/
def ivkMsgW (a n : List Word) : List Word := reprW a ++ reprW n

@[simp] theorem ivkMsgW_length (a n : List Word) : (ivkMsgW a n).length = 8 := by
  simp [ivkMsgW, reprW]

/-- The 72-byte iterator block (`Pad<Chain<Take<BitValIter>, Take<BitValIter>>>`) as
`commit_ivk` lays it out at `sp - 0x120` (its own frame `sp' = sp - 0x1e0`, block at
`sp' + 0xc0`), over the block's previous contents `J`: two `Take` halves of 255 bits, each a
bit-slice cursor (`sp' + 0x128` with end `sp' + 0x148`, i.e. `nk`'s bits, stored first; then
`sp' + 0x108` with end `sp' + 0x128`, `ak`'s bits) packed by sub-word stores, and the `Pad`
state byte. Which half the iterator yields first is part of the `from_iter` contract (T2), not
derived from this layout. Reducible: the contract is matched against the executor's cells. -/
@[reducible] def iterIvkW (sp : Word) (J : List Word) : List Word :=
  [255#64, sp + 18446744073709551432#64,
   replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte
     (replaceByte J[2]! 2 (BitVec.truncate 8 ((sp + 18446744073709551464#64) >>> 8))) 3
     (BitVec.truncate 8 ((sp + 18446744073709551464#64) >>> 16)))
     4 (BitVec.truncate 8 ((sp + 18446744073709551464#64) >>> 24)))
     5 (BitVec.truncate 8 ((sp + 18446744073709551464#64) >>> 32)))
     0 (BitVec.truncate 8 0#64))
     1 (BitVec.truncate 8 (sp + 18446744073709551464#64)))
     6 (BitVec.truncate 8 ((sp + 18446744073709551464#64) >>> 40)))
     7 (BitVec.truncate 8 ((sp + 18446744073709551464#64) >>> 48)),
   replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551464#64) >>> 56))) 1
     (BitVec.truncate 8 0#64),
   255#64, sp + 18446744073709551400#64,
   replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte
     (replaceByte J[6]! 3 (BitVec.truncate 8 ((sp + 18446744073709551432#64) >>> 16))) 4
     (BitVec.truncate 8 ((sp + 18446744073709551432#64) >>> 24)))
     5 (BitVec.truncate 8 ((sp + 18446744073709551432#64) >>> 32)))
     6 (BitVec.truncate 8 ((sp + 18446744073709551432#64) >>> 40)))
     0 (BitVec.truncate 8 0#64))
     1 (BitVec.truncate 8 (sp + 18446744073709551432#64)))
     2 (BitVec.truncate 8 ((sp + 18446744073709551432#64) >>> 8)))
     7 (BitVec.truncate 8 ((sp + 18446744073709551432#64) >>> 48)),
   replaceByte (replaceByte J[7]! 0 (BitVec.truncate 8 ((sp + 18446744073709551432#64) >>> 56))) 1
     (BitVec.truncate 8 0#64),
   replaceByte J[8]! 0 (BitVec.truncate 8 1#64)]

theorem ivkFlag_01 (Q Bv : List Word) : ivkFlag Q Bv = 1#8 ∨ ivkFlag Q Bv = 0#8 := by
  unfold ivkFlag; split <;> simp

/-! ## The specification -/

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
set_option asmverif.sym.foldBytes true in
theorem commit_ivk_spec {G : MachineState → Prop} {nb : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out ak nk rivk : Word)
    (a0 a1 a2 a3 n0 n1 n2 n3 k0 k1 k2 k3 : Word)
    (O J : List Word) (hOl : O.length = 5) (hJl : J.length = 9)
    -- the sqrt/generator tables (`FP_TABLES`) in the heap, carried through: the allocator
    -- contracts below keep them (the allocator never writes a live block)
    (tcap iptr ilen tg0 tg1 tg2 tg3 hmod hx : Word) (IV G0 G1 G2 G3 : List Word)
    (hIVl : IV.length = 138) (hG0l : G0.length = 1024) (hG1l : G1.length = 1024)
    (hG2l : G2.length = 1024) (hG3l : G3.length = 516)
    (hTB : Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] s)
    (hIVr : Region iptr IV s) (hG0 : Region tg0 G0 s) (hG1 : Region tg1 G1 s)
    (hG2 : Region tg2 G2 s) (hG3 : Region tg3 G3 s)
    (hok_iptr : RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138) (hok_g0 : RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024)
    (hok_g1 : RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024) (hok_g2 : RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024)
    (hok_g3 : RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516)
    (hlo_iptr : 0x78048980 ≤ iptr.toNat) (hlo_g0 : 0x78048980 ≤ tg0.toNat) (hlo_g1 : 0x78048980 ≤ tg1.toNat)
    (hlo_g2 : 0x78048980 ≤ tg2.toNat) (hlo_g3 : 0x78048980 ≤ tg3.toNat)
    (hhi_iptr : iptr.toNat + 8 * 138 ≤ 0x1c00000000)
    (hhi_g0 : tg0.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g1 : tg1.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g2 : tg2.toNat + 8 * 1024 ≤ 0x1c00000000)
    (hhi_g3 : tg3.toNat + 8 * 516 ≤ 0x1c00000000)
    -- the caller's blocks lie below the heap (on its stack), so off the tables
    (hbelow_out : out.toNat + 8 * 5 ≤ 0x78040620)
    (hbelow_rivk : rivk.toNat + 8 * 4 ≤ 0x78040620)
    (hbelow_ak : ak.toNat + 8 * 4 ≤ 0x78040620)
    (hbelow_nk : nk.toNat + 8 * 4 ≤ 0x78040620)
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN G nb P u)
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u)
    (hunwrap : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dc7c#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_dc7c_10 → u.getReg .x13 ∈ Run.vals_dc7c_13 → u.getReg .x14 ∈ Run.vals_dc7c_14 → SafeN G nb P u)
    (hbounds : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G nb P u)
    (hpc : s.pc = 0x780203dc#64) (hcode : CodeAt F_780203dc.base F_780203dc.prog s)
    -- callees: cached_commit_domain (+ from_raw, from_xy, is_on_curve, mulmod, black_box,
    -- to_curve), to_le_bits (+ to_repr), commit (`0x78021238`) and its callees,
    -- extract_p_bottom (+ memset, conditional_select, to_affine, coordinates)
    (hcodeCD : CodeAt F_78020548.base F_78020548.prog s) (hcodeLB : CodeAt F_78029b18.base F_78029b18.prog s)
    (hcodeCm : CodeAt F_78021238.base F_78021238.prog s) (hcodeEB : CodeAt F_7802340c.base F_7802340c.prog s)
    (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s) (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeBB : CodeAt F_7803a0fc.base F_7803a0fc.prog s) (hcodeCo : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeP : CodeAt F_780237dc.base F_780237dc.prog s) (hcodeRp : CodeAt F_78029468.base F_78029468.prog s)
    (hcodeL : CodeAt F_780234cc.base F_780234cc.prog s) (hcodeIA : CodeAt F_780235e8.base F_780235e8.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s) (hcodeAA : CodeAt F_78035f88.base F_78035f88.prog s)
    (hcodeLR : CodeAt F_780360e0.base F_780360e0.prog s) (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcodeU : CodeAt F_78023864.base F_78023864.prog s) (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeXY : CodeAt F_78026878.base F_78026878.prog s) (hcodeOC : CodeAt F_78026258.base F_78026258.prog s)
    (hcodeFR : CodeAt F_78028298.base F_78028298.prog s) (hcodeTC : CodeAt F_78025854.base F_78025854.prog s)
    (hcodeF : CodeAt F_780239bc.base F_780239bc.prog s) (hcodeBt : CodeAt F_78023544.base F_78023544.prog s)
    (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcodeCS : CodeAt F_78023d7c.base F_78023d7c.prog s)
    (hcodeB : CodeAt F_78023594.base F_78023594.prog s) (hcodeW : CodeAt F_7802827c.base F_7802827c.prog s)
    (hcodeMul : CodeAt F_78031be8.base F_78031be8.prog s) (hcodeRq : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    (hcodeA : CodeAt F_78035fe0.base F_78035fe0.prog s) (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcodeD : CodeAt F_780360c8.base F_780360c8.prog s) (hcodeAF : CodeAt F_7803a110.base F_7803a110.prog s)
    (hcodeAFI : CodeAt F_7803dd28.base F_7803dd28.prog s) (hcodeEA : CodeAt F_78026b44.base F_78026b44.prog s)
    (hcodeED : CodeAt F_7802413c.base F_7802413c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L) s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0xaa0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = ak) (ha2 : s.getReg .x12 = nk)
    (ha3 : s.getReg .x13 = rivk)
    (hA : Region ak [a0, a1, a2, a3] s) (hokA : RegionOk Ro.layout.roBase Ro.layout.textHi ak 4)
    (hN : Region nk [n0, n1, n2, n3] s) (hokN : RegionOk Ro.layout.roBase Ro.layout.textHi nk 4)
    (hK : Region rivk [k0, k1, k2, k3] s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi rivk 4)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 5)
    -- the frame's iterator block before the call: the struct's padding bytes keep these
    (hJ : Region (sp - 0xaa0#64 + 0x980#64) J s)
    (hd0 : Disjoint (sp - 0xaa0#64) 340 out 5) (hd1 : Disjoint (sp - 0xaa0#64) 340 ak 4)
    (hd2 : Disjoint (sp - 0xaa0#64) 340 nk 4) (hd3 : Disjoint (sp - 0xaa0#64) 340 rivk 4)
    (he0 : Disjoint out 5 ak 4) (he1 : Disjoint out 5 nk 4) (he2 : Disjoint out 5 rivk 4)
    (hh0 : Disjoint 0x78040620#64 14780694332 out 5) (hh1 : Disjoint 0x78040620#64 14780694332 rivk 4)
    -- `Vec<bool>::from_iter` of the padded bit iterator (ledger T2): the iterator block as
    -- `commit_ivk` builds it over the message words at `+0x9c8` (`ak`'s bits, then `nk`'s)
    -- yields 510 bytes, byte `o` the message bit `o`
    (hfrom : ∀ (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word) (L' : List (Word × Nat)), O1.length = 3 →
      u.pc = 0x7801e110#64 → u.code = s.code → u.getReg .x1 = 0x780212ac#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x260 sp' → u.getReg .x10 = a0' → u.getReg .x11 = a1' →
      Region a0' O1 u → Region a1' [0#64, j] u →
      Region (a1' + 0x10#64) (iterIvkW sp J) u →
      Region (a1' + 0x58#64) [0#64] u →
      Region (sp - 0xaa0#64 + 0x9c8#64) (ivkMsgW [a0, a1, a2, a3] [n0, n1, n2, n3]) u →
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
      StackOk Ro.layout 0xaa0 sp →
      Disjoint (sp' - 0x260#64) 76 (sp - 0xaa0#64 + 0x9c8#64) 8 → Disjoint a0' 3 (sp - 0xaa0#64 + 0x9c8#64) 8 → Disjoint a1' 12 (sp - 0xaa0#64 + 0x9c8#64) 8 →
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
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → Run.HeapAt ((ptr, 64) :: (iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') t → SafeN G nb P t) → SafeN G nb P u)
    -- `__rust_dealloc` of that `Vec` (ledger T2)
    (hdealloc : ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word) (k : Nat) (L' : List (Word × Nat)), C.length = 65 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780215d8#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap →
      u.getReg .x12 = 1#64 → Region ptr C u → 0x78048980 ≤ ptr.toNat →
      ptr.toNat + 8 * 65 ≤ 0x1c00000000 →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] u → Region iptr IV u →
      Region tg0 G0 u → Region tg1 G1 u → Region tg2 G2 u → Region tg3 G3 u →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: (iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') u →
      (∀ t, t.pc = 0x780215d8#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
        Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L') t → SafeN G nb P t) → SafeN G nb P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0xaa0#64, 340), (out, 5), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (extractPBottomW
        (ivkFlag qIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65))
        (ivkW qIvkW rIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65)
          [k0, k1, k2, k3]) ++
        [replaceByte O[4]! 0
          (ivkFlag qIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65))]) t →
      mulFacts rIvkW [k0, k1, k2, k3] →
      Region 0x780488a8#64 [tcap, iptr, ilen, tg0, tg1, tg2, tg3, hmod, hx, 2#64] t → Region iptr IV t →
      Region tg0 G0 t → Region tg1 G1 t → Region tg2 G2 t → Region tg3 G3 t → Run.HeapAt ((iptr, 138) :: (tg0, 1024) :: (tg1, 1024) :: (tg2, 1024) :: (tg3, 516) :: L) t → SafeN G nb P t) :
    SafeN G nb P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xaa0#64) 340 := hstk.frame 340 (by decide)
  -- the frame (below it 0x8c0 bytes for `commit`): the domain `[Q, R]`, the iterator, the two
  -- bit vectors, `commit`'s output, the save area
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xaa0#64 + 0x8c0#64) 24 := hokW.sub' 280 24 (by decide) (by bv_omega)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xaa0#64 + 0x980#64) 9 := hokW.sub' 304 9 (by decide) (by bv_omega)
  have hokD : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xaa0#64 + 0x9c8#64) 8 := hokW.sub' 313 8 (by decide) (by bv_omega)
  have hokD1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xaa0#64 + 0x9c8#64) 4 := hokW.sub' 313 4 (by decide) (by bv_omega)
  have hokD2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xaa0#64 + 0x9e8#64) 4 := hokW.sub' 317 4 (by decide) (by bv_omega)
  have hokB : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xaa0#64 + 0xa08#64) 13 := hokW.sub' 321 13 (by decide) (by bv_omega)
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xaa0#64 + 0xa70#64) 6 := hokW.sub' 334 6 (by decide) (by bv_omega)
  obtain ⟨A, hA', hAl⟩ := Region.exists_junk (sp - 0xaa0#64 + 0x8c0#64) 24 s
  obtain ⟨D, hD, hDl⟩ := Region.exists_junk (sp - 0xaa0#64 + 0x9c8#64) 8 s
  obtain ⟨B, hB, hBl⟩ := Region.exists_junk (sp - 0xaa0#64 + 0xa08#64) 13 s
  obtain ⟨E, hE, hEl⟩ := Region.exists_junk (sp - 0xaa0#64 + 0xa70#64) 6 s
  -- the generators' raw coordinates in the read-only segment
  have hQx : Region 0x780018a8#64 qIvkX s := (hro.get 12 (by decide)).sub 21 4 (by decide) rfl
  have hokQx : RegionOk Ro.layout.textLo Ro.layout.textHi 0x780018a8#64 4 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 12 (by decide)).sub' 21 4 (by decide) (by decide)
  have hQy : Region 0x780018c8#64 qIvkY s := (hro.get 12 (by decide)).sub 25 4 (by decide) rfl
  have hokQy : RegionOk Ro.layout.textLo Ro.layout.textHi 0x780018c8#64 4 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 12 (by decide)).sub' 25 4 (by decide) (by decide)
  have hRx : Region 0x780018e8#64 rIvkX s := (hro.get 12 (by decide)).sub 29 4 (by decide) rfl
  have hokRx : RegionOk Ro.layout.textLo Ro.layout.textHi 0x780018e8#64 4 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 12 (by decide)).sub' 29 4 (by decide) (by decide)
  have hRy : Region 0x78001908#64 rIvkY s := (hro.get 12 (by decide)).sub 33 4 (by decide) rfl
  have hokRy : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001908#64 4 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 12 (by decide)).sub' 33 4 (by decide) (by decide)
  have hhF : Disjoint 0x78040620#64 14780694332 (sp - 0xaa0#64) 340 := Disjoint.heap_frame (n := 340) hstk (by decide)
  have hokH : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hlo := hstk.lo
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hu := Unchanged.refl [(sp - 0xaa0#64, 340), (out, 5), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  sym_exec [cached_commit_domain_spec, to_le_bits_spec, hpaf] stop [0x78020500]
  -- the iterator block's cells, atom-free, so that `commit`'s contract matches `hfrom`
  region_at (sp - 0xaa0#64 + 0x980#64) in s_76 as hR4
  simp only [← v28_def, ← v29_def, ← v30_def, ← v31_def, ← v32_def, ← v33_def, ← v34_def, ← v35_def, ← v36_def, ← v38_def, ← v39_def, ← v40_def, ← v41_def, ← v42_def, ← v43_def, ← v44_def, ← v45_def, ← v53_def, ← v54_def, ← v55_def, ← v56_def, ← v57_def, ← v58_def, ← v59_def, ← v60_def, ← v61_def, ← v62_def, ← v66_def, ← v67_def, ← v68_def, ← v69_def, ← v70_def, ← v71_def, ← v72_def, ← v75_def] at hR4
  -- the message words are `to_le_bits` of `ak` and `nk`
  region_at (sp - 0xaa0#64 + 0x9c8#64) in s_76 as hR5
  rw [← acc26_0_def, ← acc51_0_def] at hR5
  have eM : [BitVec.ofNat 64 ((leLimbsToNat [a0, a1, a2, a3] * Fp.rInv % Fp.p) >>> (64 * 0)),
      BitVec.ofNat 64 ((leLimbsToNat [a0, a1, a2, a3] * Fp.rInv % Fp.p) >>> (64 * 1)),
      BitVec.ofNat 64 ((leLimbsToNat [a0, a1, a2, a3] * Fp.rInv % Fp.p) >>> (64 * 2)),
      BitVec.ofNat 64 ((leLimbsToNat [a0, a1, a2, a3] * Fp.rInv % Fp.p) >>> (64 * 3)),
      BitVec.ofNat 64 ((leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p) >>> (64 * 0)),
      BitVec.ofNat 64 ((leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p) >>> (64 * 1)),
      BitVec.ofNat 64 ((leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p) >>> (64 * 2)),
      BitVec.ofNat 64 ((leLimbsToNat [n0, n1, n2, n3] * Fp.rInv % Fp.p) >>> (64 * 3))] =
      ivkMsgW [a0, a1, a2, a3] [n0, n1, n2, n3] := by
    simp only [ivkMsgW, reprW, natToLeLimbs_cells4, List.cons_append, List.nil_append, Nat.reduceMul,
      Nat.shiftRight_zero]
  have hR5' := Eq.mp (congrArg (fun L => Region (sp - 0xaa0#64 + 0x9c8#64) L s_76) eM) hR5
  clear hR5
  sym_reframe
  have hcommit := sinsemilla_commit_ivk_spec (L := L) (G := G) (n := nb) (P := P) (M := sp - 0xaa0#64 + 0x9c8#64)
    (tcap := tcap) (iptr := iptr) (ilen := ilen) (tg0 := tg0) (tg1 := tg1) (tg2 := tg2) (tg3 := tg3)
    (hmod := hmod) (hx := hx) (IV := IV) (G0 := G0) (G1 := G1) (G2 := G2) (G3 := G3)
    (Mw := ivkMsgW [a0, a1, a2, a3] [n0, n1, n2, n3])
    (bit := ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) (hMl := ivkMsgW_length _ _)
    (Mok := StackOk Ro.layout 0xaa0 sp) (hMok := hstk)
  sym_exec [hcommit, hpaf, hpanic, hunwrap, hbounds] stop [0x78020518]
  -- the generators are the models' `Q` and `R`
  have hQ : [acc20_0[0]!, acc20_0[1]!, acc20_0[2]!, acc20_0[3]!, acc20_0[4]!, acc20_0[5]!, acc20_0[6]!,
      acc20_0[7]!, acc20_0[8]!, acc20_0[9]!, acc20_0[10]!, acc20_0[11]!] = qIvkW :=
    (cells12_eq _ (acc20_0_def ▸ domainPtW_length _ _)).trans acc20_0_def.symm
  have hR : [acc20_1[0]!, acc20_1[1]!, acc20_1[2]!, acc20_1[3]!, acc20_1[4]!, acc20_1[5]!, acc20_1[6]!,
      acc20_1[7]!, acc20_1[8]!, acc20_1[9]!, acc20_1[10]!, acc20_1[11]!] = rIvkW :=
    (cells12_eq _ (acc20_1_def ▸ domainPtW_length _ _)).trans acc20_1_def.symm
  rw [hQ, hR] at acc6_0_def
  rw [hR] at post6_6
  region_at (sp + 18446744073709551464#64) in t as hCm
  region_at (sp + 18446744073709551464#64 + 96#64) in t as hCf
  rw [hQ] at hCf
  simp only [List.getElem!_cons_zero, List.getElem!_cons_succ] at hCf
  -- `commit`'s point and flag, one block for `extract_p_bottom`
  have hC := Region.append hCm hCf
  simp only [List.cons_append, List.nil_append] at hC
  clear hCm hCf
  have hf01 := ivkFlag_01 qIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65)
  sym_reframe
  sym_exec [extract_p_bottom_spec]
  -- `out`: `Extract_P` of `commit`'s point, then the flag
  have hlen6 : acc6_0.length = 12 := acc6_0_def ▸ ivkW_length _ _ _ _
  region_at out in s_13 as hOut
  rw [cells12_eq _ hlen6, ← acc6_0_def] at hOut
  have hRo : Region out (extractPBottomW (ivkFlag qIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65))
      (ivkW qIvkW rIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65) [k0, k1, k2, k3]) ++
      [replaceByte O[4]! 0 (ivkFlag qIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65))]) s_13 := by
    rw [AsmVerif.RiscV.Sym.List.eq_map_range (extractPBottomW (ivkFlag qIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65))
      (ivkW qIvkW rIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65) [k0, k1, k2, k3]) ++
      [replaceByte O[4]! 0 (ivkFlag qIvkW (boolBytesToWords (ivkBit (reprW [a0, a1, a2, a3]) (reprW [n0, n1, n2, n3])) 65))]) (n := 5) (by simp)]; exact hOut
  clear hOut
  sym_close hk

end Cases.Zip2005
