import Cases.Zip2005.Orchard.Rho
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Field.Cells4
import Cases.Zip2005.Image.F_7801d098
import Cases.Zip2005.Image.F_7801aed0
import Cases.Zip2005.Image.Ro

/-!
# `Zip2005Witness::parse_merkle_path` (0x7801d098)

`[Rho; 32]` from the 32 encodings at `w + 0x20·i`: `Rho::from_bytes` each, collected into a
`Vec<Rho>` (`__rust_alloc` of four, `do_reserve_and_handle` when full: capacity 8, 16, 32), then
moved out (`Some((path, position))`, the position the `u32` at `w + 0x508`), or `None` on the
first non-canonical encoding (the `Vec` freed). The allocator calls are contracts (T2).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- Encoding `i` of the path, as four words. -/
def mpEnc (H : List Word) (i : Nat) : List Word := [H[4 * i]!, H[4 * i + 1]!, H[4 * i + 2]!, H[4 * i + 3]!]

/-- All 32 encodings canonical. -/
def mpOk (H : List Word) : Prop := ∀ i < 32, leLimbsToNat (mpEnc H i) < Fp.p

instance (H : List Word) : Decidable (mpOk H) := by unfold mpOk; infer_instance

/-- The 32 `Rho`s (Montgomery limbs), 128 words. -/
def mpPathW (H : List Word) : List Word :=
  (List.range 32).flatMap (fun i => natToLeLimbs 4 (Fp.mul (leLimbsToNat (mpEnc H i)) Fp.R2))

/-- Word `j` of the path as `parse_merkle_path` leaves it: limb `j % 4` of `Rho` `j / 4`, masked by
its canonicity (`Rho::from_bytes`'s `CtOption`). -/
def mpCell (H : List Word) (j : Nat) : Word :=
  if leLimbsToNat (mpEnc H (j / 4)) < Fp.p then
    BitVec.ofNat 64 (Fp.mul (leLimbsToNat (mpEnc H (j / 4))) Fp.R2 >>> (64 * (j % 4)))
  else 0#64

/-- The `Option<([Rho; 32], u32)>` written over `O` (130 words). -/
def merklePathW (O H : List Word) (pw : Word) : List Word :=
  if mpOk H then 1#64 :: ((List.range 128).map (mpCell H) ++ [replaceWord32 O[129]! 0 (pw.truncate 32)])
  else 0#64 :: (List.range 129).map (fun i => O[i + 1]!)

/-- A canonicity flag read back as a word: not `1` means not canonical. -/
theorem flag_ne_one {c : Prop} [Decidable c] {v : Word}
    (hv : BitVec.zeroExtend 64 (if c then 1#8 else 0#8) = v) (h : (v != 1#64) = true) : ¬ c := by
  intro hc; rw [if_pos hc] at hv; subst hv; exact absurd h (by decide)

/-- A canonicity flag read back as a word: `1` means canonical. -/
theorem flag_eq_one {c : Prop} [Decidable c] {v : Word}
    (hv : BitVec.zeroExtend 64 (if c then 1#8 else 0#8) = v) (h : ¬ (v != 1#64) = true) : c := by
  by_contra hc; rw [if_neg hc] at hv; subst hv; exact h (by decide)

/-- The position: `lw` then `sw` of its low word. -/
theorem trunc32_sext_w32 (w : Word) :
    BitVec.truncate 32 (BitVec.signExtend 64 (extractWord32 w 0)) = BitVec.truncate 32 w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.truncate_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, extractWord32,
    BitVec.getLsbD_ushiftRight]
  interval_cases i <;> simp

/-- With every encoding canonical, the cells are the 32 `Rho`s' limbs. -/
theorem mpCells_eq (H : List Word) (h : mpOk H) : (List.range 128).map (mpCell H) = mpPathW H := by
  have hr : List.range 128 = (List.range 32).flatMap (fun i => [4 * i, 4 * i + 1, 4 * i + 2, 4 * i + 3]) := by
    decide
  rw [hr, List.map_flatMap, mpPathW]
  apply List.flatMap_congr
  intro i hi
  have hi' : i < 32 := List.mem_range.mp hi
  simp only [List.map_cons, List.map_nil, mpCell]
  rw [show 4 * i / 4 = i by omega, show (4 * i + 1) / 4 = i by omega, show (4 * i + 2) / 4 = i by omega,
    show (4 * i + 3) / 4 = i by omega, show 4 * i % 4 = 0 by omega, show (4 * i + 1) % 4 = 1 by omega,
    show (4 * i + 2) % 4 = 2 by omega, show (4 * i + 3) % 4 = 3 by omega, if_pos (h i hi'),
    if_pos (h i hi'), if_pos (h i hi'), if_pos (h i hi'), natToLeLimbs_cells4]
  rfl

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
set_option asmverif.sym.foldBytes true in
theorem parse_merkle_path_spec {G : MachineState → Prop} {nb : Nat} {P : Prop} (s : MachineState) (ra sp out w pw : Word)
    (H O : List Word) (hHl : H.length = 128) (hOl : O.length = 130)
    (hpc : s.pc = 0x7801d098#64) (hcode : CodeAt F_7801d098.base F_7801d098.prog s)
    (hcodeRho : CodeAt F_7801ddd8.base F_7801ddd8.prog s)
    (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcodeMC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x5c0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = w)
    (hH : Region w H s) (hokH : RegionOk Ro.layout.roBase Ro.layout.textHi w 128)
    (hP : Region (w + 0x508#64) [pw] s) (hokP : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 0x508#64) 1)
    (hO : Region out O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi out 130)
    (hd0 : Disjoint (sp - 0x5c0#64) 184 out 130) (hdH : Disjoint (sp - 0x5c0#64) 184 w 128)
    (hdP : Disjoint (sp - 0x5c0#64) 184 (w + 0x508#64) 1)
    (heH : Disjoint out 130 w 128) (heP : Disjoint out 130 (w + 0x508#64) 1)
    (hhO : Disjoint 0x78040620#64 14780694332 out 130) (hhH : Disjoint 0x78040620#64 14780694332 w 128)
    (hhP : Disjoint 0x78040620#64 14780694332 (w + 0x508#64) 1)
    -- `raw_vec::handle_error` diverges (an allocation failure)
    (hhandle : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → SafeN G nb P u)
    -- `__rust_alloc(0x80, 8)` (ledger T2): a fresh 8-aligned block in the arena
    (halloc : ∀ (u : MachineState) (sp' : Word), u.pc = 0x7801bcec#64 → u.code = s.code →
      u.getReg .x1 = 0x7801d114#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
      u.getReg .x10 = 0x80#64 → u.getReg .x11 = 8#64 →
      (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x7801d114#64 → CalleeSaved u t →
        t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        t.getReg .x10 = ptr → B.length = 16 → Region ptr B t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 16 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 0x80 ≤ 0x1c00000000 → SafeN G nb P t) → SafeN G nb P u)
    -- `RawVecInner::reserve::do_reserve_and_handle` on a full `Vec<Rho>` (ledger T2): capacity
    -- doubled (`max(2·cap, len + 1, 4)` with `len = cap ≥ 4`), the old contents moved to a fresh
    -- block, the old one freed
    (hreserve : ∀ (u : MachineState) (sp' hdr ptr : Word) (n : Nat) (B : List Word),
      u.pc = 0x7801cac0#64 → u.code = s.code → u.getReg .x1 = 0x7801d1e8#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x100 sp' → u.getReg .x10 = hdr →
      u.getReg .x11 = BitVec.ofNat 64 n →
      Region hdr [BitVec.ofNat 64 n, ptr, BitVec.ofNat 64 n] u → RegionOk Ro.layout.roBase Ro.layout.textHi hdr 3 →
      Disjoint (sp' - 0x100#64) 32 hdr 3 → Disjoint 0x78040620#64 14780694332 hdr 3 →
      4 ≤ n → n ≤ 16 → B.length = 4 * n → Region ptr B u →
      0x78048980 ≤ ptr.toNat → ptr.toNat + 32 * n ≤ 0x1c00000000 →
      (∀ (t : MachineState) (ptr' : Word) (B' : List Word), t.pc = 0x7801d1e8#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x100#64, 32), (hdr, 3), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region hdr [BitVec.ofNat 64 (2 * n), ptr', BitVec.ofNat 64 n] t → B'.length = 4 * n →
        Region ptr' (B ++ B') t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr' (8 * n) →
        0x78048980 ≤ ptr'.toNat → ptr'.toNat + 64 * n ≤ 0x1c00000000 → SafeN G nb P t) → SafeN G nb P u)
    -- `__rust_dealloc(ptr, 32·cap, 8)` (ledger T2)
    (hdealloc : ∀ (u : MachineState) (sp' r ptr sz : Word), u.pc = 0x7801bd08#64 →
      u.code = s.code → u.getReg .x1 = r → r &&& ~~~1#64 = r → u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' →
      u.getReg .x10 = ptr → u.getReg .x11 = sz → u.getReg .x12 = 8#64 →
      0x78048980 ≤ ptr.toNat →
      (∀ t, t.pc = r → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → SafeN G nb P t) → SafeN G nb P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x5c0#64, 184), (out, 130), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (merklePathW O H pw) t → SafeN G nb P t) :
    SafeN G nb P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x5c0#64) 184 := hstk.frame 184 (by decide)
  -- the frame (`sp' = sp - 0x4b0`): [8, 0x3f0) the 125 words moved out, [0x3f0, 0x408) the `Vec`
  -- header, [0x408, 0x428) and [0x428, 0x448) the `Rho` being pushed, [0x448, 0x470) the
  -- `CtOption<Rho>`, saved registers at 0x470
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x4a8#64) 125 := hokW.sub' 35 125 (by decide) (by bv_omega)
  have hokV : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xc0#64) 3 := hokW.sub' 160 3 (by decide) (by bv_omega)
  have hokR1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xa8#64) 4 := hokW.sub' 163 4 (by decide) (by bv_omega)
  have hokR2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x88#64) 4 := hokW.sub' 167 4 (by decide) (by bv_omega)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 5 := hokW.sub' 171 5 (by decide) (by bv_omega)
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x40#64) 8 := hokW.sub' 176 8 (by decide) (by bv_omega)
  obtain ⟨FA, hFA, hFAl⟩ := Region.exists_junk (sp - 0x4a8#64) 125 s
  obtain ⟨FV, hFV, hFVl⟩ := Region.exists_junk (sp - 0xc0#64) 3 s
  obtain ⟨FR1, hFR1, hFR1l⟩ := Region.exists_junk (sp - 0xa8#64) 4 s
  obtain ⟨FR2, hFR2, hFR2l⟩ := Region.exists_junk (sp - 0x88#64) 4 s
  obtain ⟨FC, hFC, hFCl⟩ := Region.exists_junk (sp - 0x68#64) 5 s
  obtain ⟨FE, hFE, hFEl⟩ := Region.exists_junk (sp - 0x40#64) 8 s
  -- the 32 encodings
  have hH' := hH
  rw [AsmVerif.RiscV.Sym.List.eq_map_range H hHl] at hH'
  have hH0 : Region w [H[0]!, H[1]!, H[2]!, H[3]!] s := hH'.sub 0 4 (BitVec.add_zero w).symm rfl
  have hokH0 : RegionOk Ro.layout.roBase Ro.layout.textHi w 4 := hokH.sub' 0 4 (by decide) (BitVec.add_zero w).symm
  have hH1 : Region (w + 32#64) [H[4]!, H[5]!, H[6]!, H[7]!] s := hH'.sub 4 4 rfl rfl
  have hokH1 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 32#64) 4 := hokH.sub' 4 4 (by decide) rfl
  have hH2 : Region (w + 64#64) [H[8]!, H[9]!, H[10]!, H[11]!] s := hH'.sub 8 4 rfl rfl
  have hokH2 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 64#64) 4 := hokH.sub' 8 4 (by decide) rfl
  have hH3 : Region (w + 96#64) [H[12]!, H[13]!, H[14]!, H[15]!] s := hH'.sub 12 4 rfl rfl
  have hokH3 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 96#64) 4 := hokH.sub' 12 4 (by decide) rfl
  have hH4 : Region (w + 128#64) [H[16]!, H[17]!, H[18]!, H[19]!] s := hH'.sub 16 4 rfl rfl
  have hokH4 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 128#64) 4 := hokH.sub' 16 4 (by decide) rfl
  have hH5 : Region (w + 160#64) [H[20]!, H[21]!, H[22]!, H[23]!] s := hH'.sub 20 4 rfl rfl
  have hokH5 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 160#64) 4 := hokH.sub' 20 4 (by decide) rfl
  have hH6 : Region (w + 192#64) [H[24]!, H[25]!, H[26]!, H[27]!] s := hH'.sub 24 4 rfl rfl
  have hokH6 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 192#64) 4 := hokH.sub' 24 4 (by decide) rfl
  have hH7 : Region (w + 224#64) [H[28]!, H[29]!, H[30]!, H[31]!] s := hH'.sub 28 4 rfl rfl
  have hokH7 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 224#64) 4 := hokH.sub' 28 4 (by decide) rfl
  have hH8 : Region (w + 256#64) [H[32]!, H[33]!, H[34]!, H[35]!] s := hH'.sub 32 4 rfl rfl
  have hokH8 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 256#64) 4 := hokH.sub' 32 4 (by decide) rfl
  have hH9 : Region (w + 288#64) [H[36]!, H[37]!, H[38]!, H[39]!] s := hH'.sub 36 4 rfl rfl
  have hokH9 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 288#64) 4 := hokH.sub' 36 4 (by decide) rfl
  have hH10 : Region (w + 320#64) [H[40]!, H[41]!, H[42]!, H[43]!] s := hH'.sub 40 4 rfl rfl
  have hokH10 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 320#64) 4 := hokH.sub' 40 4 (by decide) rfl
  have hH11 : Region (w + 352#64) [H[44]!, H[45]!, H[46]!, H[47]!] s := hH'.sub 44 4 rfl rfl
  have hokH11 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 352#64) 4 := hokH.sub' 44 4 (by decide) rfl
  have hH12 : Region (w + 384#64) [H[48]!, H[49]!, H[50]!, H[51]!] s := hH'.sub 48 4 rfl rfl
  have hokH12 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 384#64) 4 := hokH.sub' 48 4 (by decide) rfl
  have hH13 : Region (w + 416#64) [H[52]!, H[53]!, H[54]!, H[55]!] s := hH'.sub 52 4 rfl rfl
  have hokH13 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 416#64) 4 := hokH.sub' 52 4 (by decide) rfl
  have hH14 : Region (w + 448#64) [H[56]!, H[57]!, H[58]!, H[59]!] s := hH'.sub 56 4 rfl rfl
  have hokH14 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 448#64) 4 := hokH.sub' 56 4 (by decide) rfl
  have hH15 : Region (w + 480#64) [H[60]!, H[61]!, H[62]!, H[63]!] s := hH'.sub 60 4 rfl rfl
  have hokH15 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 480#64) 4 := hokH.sub' 60 4 (by decide) rfl
  have hH16 : Region (w + 512#64) [H[64]!, H[65]!, H[66]!, H[67]!] s := hH'.sub 64 4 rfl rfl
  have hokH16 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 512#64) 4 := hokH.sub' 64 4 (by decide) rfl
  have hH17 : Region (w + 544#64) [H[68]!, H[69]!, H[70]!, H[71]!] s := hH'.sub 68 4 rfl rfl
  have hokH17 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 544#64) 4 := hokH.sub' 68 4 (by decide) rfl
  have hH18 : Region (w + 576#64) [H[72]!, H[73]!, H[74]!, H[75]!] s := hH'.sub 72 4 rfl rfl
  have hokH18 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 576#64) 4 := hokH.sub' 72 4 (by decide) rfl
  have hH19 : Region (w + 608#64) [H[76]!, H[77]!, H[78]!, H[79]!] s := hH'.sub 76 4 rfl rfl
  have hokH19 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 608#64) 4 := hokH.sub' 76 4 (by decide) rfl
  have hH20 : Region (w + 640#64) [H[80]!, H[81]!, H[82]!, H[83]!] s := hH'.sub 80 4 rfl rfl
  have hokH20 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 640#64) 4 := hokH.sub' 80 4 (by decide) rfl
  have hH21 : Region (w + 672#64) [H[84]!, H[85]!, H[86]!, H[87]!] s := hH'.sub 84 4 rfl rfl
  have hokH21 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 672#64) 4 := hokH.sub' 84 4 (by decide) rfl
  have hH22 : Region (w + 704#64) [H[88]!, H[89]!, H[90]!, H[91]!] s := hH'.sub 88 4 rfl rfl
  have hokH22 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 704#64) 4 := hokH.sub' 88 4 (by decide) rfl
  have hH23 : Region (w + 736#64) [H[92]!, H[93]!, H[94]!, H[95]!] s := hH'.sub 92 4 rfl rfl
  have hokH23 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 736#64) 4 := hokH.sub' 92 4 (by decide) rfl
  have hH24 : Region (w + 768#64) [H[96]!, H[97]!, H[98]!, H[99]!] s := hH'.sub 96 4 rfl rfl
  have hokH24 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 768#64) 4 := hokH.sub' 96 4 (by decide) rfl
  have hH25 : Region (w + 800#64) [H[100]!, H[101]!, H[102]!, H[103]!] s := hH'.sub 100 4 rfl rfl
  have hokH25 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 800#64) 4 := hokH.sub' 100 4 (by decide) rfl
  have hH26 : Region (w + 832#64) [H[104]!, H[105]!, H[106]!, H[107]!] s := hH'.sub 104 4 rfl rfl
  have hokH26 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 832#64) 4 := hokH.sub' 104 4 (by decide) rfl
  have hH27 : Region (w + 864#64) [H[108]!, H[109]!, H[110]!, H[111]!] s := hH'.sub 108 4 rfl rfl
  have hokH27 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 864#64) 4 := hokH.sub' 108 4 (by decide) rfl
  have hH28 : Region (w + 896#64) [H[112]!, H[113]!, H[114]!, H[115]!] s := hH'.sub 112 4 rfl rfl
  have hokH28 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 896#64) 4 := hokH.sub' 112 4 (by decide) rfl
  have hH29 : Region (w + 928#64) [H[116]!, H[117]!, H[118]!, H[119]!] s := hH'.sub 116 4 rfl rfl
  have hokH29 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 928#64) 4 := hokH.sub' 116 4 (by decide) rfl
  have hH30 : Region (w + 960#64) [H[120]!, H[121]!, H[122]!, H[123]!] s := hH'.sub 120 4 rfl rfl
  have hokH30 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 960#64) 4 := hokH.sub' 120 4 (by decide) rfl
  have hH31 : Region (w + 992#64) [H[124]!, H[125]!, H[126]!, H[127]!] s := hH'.sub 124 4 rfl rfl
  have hokH31 : RegionOk Ro.layout.roBase Ro.layout.textHi (w + 992#64) 4 := hokH.sub' 124 4 (by decide) rfl
  clear hH hH'
  have hhF : Disjoint 0x78040620#64 14780694332 (sp - 0x5c0#64) 184 := Disjoint.heap_frame (n := 184) hstk (by decide)
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hlo := hstk.lo
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hu := Unchanged.refl [(sp - 0x5c0#64, 184), (out, 130), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  sym_exec [rho_from_bytes_spec, halloc, hreserve, hdealloc, memcpy1000_spec, hhandle]
  · have hc := flag_ne_one v15_def hbr17
    have hno : ¬ mpOk H := fun hall => hc (hall 0 (by decide))
    have hRo : Region out (merklePathW O H pw) s_30 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v57_def hbr58
    have hno : ¬ mpOk H := fun hall => hc (hall 1 (by decide))
    have hRo : Region out (merklePathW O H pw) s_80 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v88_def hbr89
    have hno : ¬ mpOk H := fun hall => hc (hall 2 (by decide))
    have hRo : Region out (merklePathW O H pw) s_111 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v119_def hbr120
    have hno : ¬ mpOk H := fun hall => hc (hall 3 (by decide))
    have hRo : Region out (merklePathW O H pw) s_142 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v150_def hbr151
    have hno : ¬ mpOk H := fun hall => hc (hall 4 (by decide))
    have hRo : Region out (merklePathW O H pw) s_173 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v188_def hbr189
    have hno : ¬ mpOk H := fun hall => hc (hall 5 (by decide))
    have hRo : Region out (merklePathW O H pw) s_211 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v219_def hbr220
    have hno : ¬ mpOk H := fun hall => hc (hall 6 (by decide))
    have hRo : Region out (merklePathW O H pw) s_242 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v250_def hbr251
    have hno : ¬ mpOk H := fun hall => hc (hall 7 (by decide))
    have hRo : Region out (merklePathW O H pw) s_273 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v281_def hbr282
    have hno : ¬ mpOk H := fun hall => hc (hall 8 (by decide))
    have hRo : Region out (merklePathW O H pw) s_304 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v319_def hbr320
    have hno : ¬ mpOk H := fun hall => hc (hall 9 (by decide))
    have hRo : Region out (merklePathW O H pw) s_342 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v350_def hbr351
    have hno : ¬ mpOk H := fun hall => hc (hall 10 (by decide))
    have hRo : Region out (merklePathW O H pw) s_373 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v381_def hbr382
    have hno : ¬ mpOk H := fun hall => hc (hall 11 (by decide))
    have hRo : Region out (merklePathW O H pw) s_404 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v412_def hbr413
    have hno : ¬ mpOk H := fun hall => hc (hall 12 (by decide))
    have hRo : Region out (merklePathW O H pw) s_435 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v443_def hbr444
    have hno : ¬ mpOk H := fun hall => hc (hall 13 (by decide))
    have hRo : Region out (merklePathW O H pw) s_466 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v474_def hbr475
    have hno : ¬ mpOk H := fun hall => hc (hall 14 (by decide))
    have hRo : Region out (merklePathW O H pw) s_497 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v505_def hbr506
    have hno : ¬ mpOk H := fun hall => hc (hall 15 (by decide))
    have hRo : Region out (merklePathW O H pw) s_528 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v536_def hbr537
    have hno : ¬ mpOk H := fun hall => hc (hall 16 (by decide))
    have hRo : Region out (merklePathW O H pw) s_559 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v574_def hbr575
    have hno : ¬ mpOk H := fun hall => hc (hall 17 (by decide))
    have hRo : Region out (merklePathW O H pw) s_597 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v605_def hbr606
    have hno : ¬ mpOk H := fun hall => hc (hall 18 (by decide))
    have hRo : Region out (merklePathW O H pw) s_628 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v636_def hbr637
    have hno : ¬ mpOk H := fun hall => hc (hall 19 (by decide))
    have hRo : Region out (merklePathW O H pw) s_659 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v667_def hbr668
    have hno : ¬ mpOk H := fun hall => hc (hall 20 (by decide))
    have hRo : Region out (merklePathW O H pw) s_690 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v698_def hbr699
    have hno : ¬ mpOk H := fun hall => hc (hall 21 (by decide))
    have hRo : Region out (merklePathW O H pw) s_721 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v729_def hbr730
    have hno : ¬ mpOk H := fun hall => hc (hall 22 (by decide))
    have hRo : Region out (merklePathW O H pw) s_752 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v760_def hbr761
    have hno : ¬ mpOk H := fun hall => hc (hall 23 (by decide))
    have hRo : Region out (merklePathW O H pw) s_783 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v791_def hbr792
    have hno : ¬ mpOk H := fun hall => hc (hall 24 (by decide))
    have hRo : Region out (merklePathW O H pw) s_814 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v822_def hbr823
    have hno : ¬ mpOk H := fun hall => hc (hall 25 (by decide))
    have hRo : Region out (merklePathW O H pw) s_845 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v853_def hbr854
    have hno : ¬ mpOk H := fun hall => hc (hall 26 (by decide))
    have hRo : Region out (merklePathW O H pw) s_876 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v884_def hbr885
    have hno : ¬ mpOk H := fun hall => hc (hall 27 (by decide))
    have hRo : Region out (merklePathW O H pw) s_907 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v915_def hbr916
    have hno : ¬ mpOk H := fun hall => hc (hall 28 (by decide))
    have hRo : Region out (merklePathW O H pw) s_938 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v946_def hbr947
    have hno : ¬ mpOk H := fun hall => hc (hall 29 (by decide))
    have hRo : Region out (merklePathW O H pw) s_969 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v977_def hbr978
    have hno : ¬ mpOk H := fun hall => hc (hall 30 (by decide))
    have hRo : Region out (merklePathW O H pw) s_1000 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · have hc := flag_ne_one v1008_def hbr1009
    have hno : ¬ mpOk H := fun hall => hc (hall 31 (by decide))
    have hRo : Region out (merklePathW O H pw) s_1031 := by
      unfold merklePathW; rw [if_neg hno]; exact hR1
    clear hR1
    sym_close hk
  · -- `Some`: every encoding canonical
    have hall : mpOk H := by
      intro i hi
      interval_cases i
      · exact flag_eq_one v15_def hbr17
      · exact flag_eq_one v57_def hbr58
      · exact flag_eq_one v88_def hbr89
      · exact flag_eq_one v119_def hbr120
      · exact flag_eq_one v150_def hbr151
      · exact flag_eq_one v188_def hbr189
      · exact flag_eq_one v219_def hbr220
      · exact flag_eq_one v250_def hbr251
      · exact flag_eq_one v281_def hbr282
      · exact flag_eq_one v319_def hbr320
      · exact flag_eq_one v350_def hbr351
      · exact flag_eq_one v381_def hbr382
      · exact flag_eq_one v412_def hbr413
      · exact flag_eq_one v443_def hbr444
      · exact flag_eq_one v474_def hbr475
      · exact flag_eq_one v505_def hbr506
      · exact flag_eq_one v536_def hbr537
      · exact flag_eq_one v574_def hbr575
      · exact flag_eq_one v605_def hbr606
      · exact flag_eq_one v636_def hbr637
      · exact flag_eq_one v667_def hbr668
      · exact flag_eq_one v698_def hbr699
      · exact flag_eq_one v729_def hbr730
      · exact flag_eq_one v760_def hbr761
      · exact flag_eq_one v791_def hbr792
      · exact flag_eq_one v822_def hbr823
      · exact flag_eq_one v853_def hbr854
      · exact flag_eq_one v884_def hbr885
      · exact flag_eq_one v915_def hbr916
      · exact flag_eq_one v946_def hbr947
      · exact flag_eq_one v977_def hbr978
      · exact flag_eq_one v1008_def hbr1009
    subst v15_def v18_def v19_def v20_def v21_def v57_def v59_def v60_def v61_def v62_def v88_def v90_def v91_def v92_def v93_def v119_def v121_def v122_def v123_def v124_def v150_def v152_def v153_def v154_def v155_def acc166_1_def v188_def v190_def v191_def v192_def v193_def v219_def v221_def v222_def v223_def v224_def v250_def v252_def v253_def v254_def v255_def v281_def v283_def v284_def v285_def v286_def acc297_1_def v319_def v321_def v322_def v323_def v324_def v350_def v352_def v353_def v354_def v355_def v381_def v383_def v384_def v385_def v386_def v412_def v414_def v415_def v416_def v417_def v443_def v445_def v446_def v447_def v448_def v474_def v476_def v477_def v478_def v479_def v505_def v507_def v508_def v509_def v510_def v536_def v538_def v539_def v540_def v541_def acc552_1_def v574_def v576_def v577_def v578_def v579_def v605_def v607_def v608_def v609_def v610_def v636_def v638_def v639_def v640_def v641_def v667_def v669_def v670_def v671_def v672_def v698_def v700_def v701_def v702_def v703_def v729_def v731_def v732_def v733_def v734_def v760_def v762_def v763_def v764_def v765_def v791_def v793_def v794_def v795_def v796_def v822_def v824_def v825_def v826_def v827_def v853_def v855_def v856_def v857_def v858_def v884_def v886_def v887_def v888_def v889_def v915_def v917_def v918_def v919_def v920_def v946_def v948_def v949_def v950_def v951_def v977_def v979_def v980_def v981_def v982_def v1008_def v1010_def v1011_def v1012_def v1013_def v1039_def v1040_def v1041_def v1055_def v1065_def
    have hRo : Region out (merklePathW O H pw) s_1079 := by
      rw [merklePathW, if_pos hall, show List.range 128 = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127] from rfl]
      simp only [List.map_cons, List.map_nil, mpCell, mpEnc, List.cons_append, List.nil_append,
        List.getElem!_cons_succ, List.getElem!_cons_zero, Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul,
        Nat.reduceAdd, trunc32_sext_w32] at hR1 ⊢
      exact hR1
    clear hR1
    sym_close hk

end Cases.Zip2005
