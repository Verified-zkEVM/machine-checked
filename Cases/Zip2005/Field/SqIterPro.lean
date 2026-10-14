import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Image.F_780326cc
import Cases.Zip2005.Image.F_7801aed0
import Cases.Zip2005.Image.Ro

/-!
# `Vec<Fp>::from_iter` of `SqrtTables::new`: entry to the loop head (0x780326cc → 0x7803292c)

The iterator is `(0..256).map(|_| { let r = gp; gp *= g; r })` over the state block `it`
(`[&g, 0..256, gp]`): the first element is `gp`, the block's `gp` becomes `gp * g` (two
`mulmod` calls), a buffer of four elements is allocated (`__rust_alloc(0x80, 8)`, the contract
`halloc`, ledger A4) and the element stored, and the loop starts with one element.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- `__rust_alloc(0x80, 8)` at `from_iter`'s call (`0x7803285c`). -/
def SqAlloc (P : Prop) (code : Word → Option Instr) : Prop :=
  ∀ (u : MachineState) (sp' : Word), u.pc = 0x7801bcec#64 → u.code = code →
    u.getReg .x1 = 0x7803285c#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
    u.getReg .x10 = 0x80#64 → u.getReg .x11 = 8#64 →
    (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x7803285c#64 → CalleeSaved u t →
      t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
      t.getReg .x10 = ptr → B.length = 16 → Region ptr B t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 16 →
      0x78048980 ≤ ptr.toNat → ptr.toNat + 0x80 ≤ 0x1c00000000 → Safe P t) →
    Safe P u

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem sq_iter_pro {P : Prop} (s : MachineState) (ra sp out it g w2 w3 w4 w5 : Word)
    (G : List Word) (hGl : G.length = 4)
    (hpc : s.pc = 0x780326cc#64) (hcode : CodeAt F_780326cc.base F_780326cc.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x240 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = it)
    (hI : Region it [g, 0x10000000000#64, w2, w3, w4, w5] s) (hokI : RegionOk Ro.layout.roBase Ro.layout.textHi it 6)
    (hG : Region g G s) (hokG : RegionOk Ro.layout.roBase Ro.layout.textHi g 4)
    (hIlo : sp.toNat ≤ it.toNat) (hIhi : it.toNat + 48 ≤ 0x78000000)
    (hglo : sp.toNat ≤ g.toNat) (hghi : g.toNat + 32 ≤ 0x78000000)
    (hdIG : Disjoint it 6 g 4)
    (halloc : SqAlloc P s.code)
    (hhandle_rv : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → Safe P u)
    (hk : ∀ (t : MachineState) (p : Word) (J : List Word), t.pc = 0x7803292c#64 → t.code = s.code →
      Unchanged [(sp - 0x170#64, 46), (it, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      t.getReg .x2 = sp - 0x140#64 → t.getReg .x8 = 32#64 → t.getReg .x9 = p →
      t.getReg .x19 = g → t.getReg .x20 = 0x224698fc094cf91b#64 →
      t.getReg .x21 = 0x992d30ed00000001#64 → t.getReg .x22 = 0x4000000000000000#64 →
      t.getReg .x23 = 0x70cb2996efc89a65#64 → t.getReg .x24 = 0x21f1c4ff1e2278d5#64 →
      t.getReg .x25 = 257#64 → t.getReg .x26 = 2#64 → t.getReg .x27 = sp - 0x140#64 + 0xb8#64 →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      Region (sp - 0x140#64 + 8#64) [out, 0xac9fba6a4077fc57#64, 0xcf3f8e8753a769a9#64, 4#64, p, 1#64] t →
      J.length = 20 → Region (sp - 0x140#64 + 0x38#64) J t →
      Region (sp - 0x140#64 + 0xd8#64) [s.getReg .x27, s.getReg .x26, s.getReg .x25, s.getReg .x24,
        s.getReg .x23, s.getReg .x22, s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18,
        s.getReg .x9, s.getReg .x8, ra] t →
      Region g G t →
      RegionOk Ro.layout.roBase Ro.layout.textHi p 16 → 0x78048980 ≤ p.toNat → p.toNat + 0x80 ≤ 0x1c00000000 →
      Safe P t) :
    Safe P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x170#64) 46 := hstk.frame 46 (by decide)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hlo := hstk.lo
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x140#64) 40 := hokS.sub' 6 40 (by decide) (by bv_omega)
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x140#64) 1 := hokF.sub' 0 1 (by decide) (by bv_omega)
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x140#64 + 8#64) 6 := hokF.sub' 1 6 (by decide) (by bv_omega)
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x140#64 + 0x38#64) 20 := hokF.sub' 7 20 (by decide) (by bv_omega)
  have hok3 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x140#64 + 0xd8#64) 13 := hokF.sub' 27 13 (by decide) (by bv_omega)
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x140#64) 1 s
  obtain ⟨F1, hF1, hF1l⟩ := Region.exists_junk (sp - 0x140#64 + 8#64) 6 s
  obtain ⟨F2, hF2, hF2l⟩ := Region.exists_junk (sp - 0x140#64 + 0x38#64) 20 s
  obtain ⟨F3, hF3, hF3l⟩ := Region.exists_junk (sp - 0x140#64 + 0xd8#64) 13 s
  clear hokF
  have hu := Unchanged.refl [(sp - 0x170#64, 46), (it, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  unfold SqAlloc at halloc
  sym_exec [uint256_mulmod_spec, halloc, hhandle_rv] stop [0x7803292c]
  · exact absurd (by rw [← v106_def]; decide) hbr127
  · sym_close hk _ post103_0 [v84, v85, v86, v87, w2, w3, w4, w5,
      BitVec.ofNat 64 (acc83_0 >>> (64 * 0)), BitVec.ofNat 64 (acc83_0 >>> (64 * 1)),
      BitVec.ofNat 64 (acc83_0 >>> (64 * 2)), BitVec.ofNat 64 (acc83_0 >>> (64 * 3)), v84, v85, v86, v87,
      11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64]
    · rw [hx25, ← v132_def, ← v131_def, ← v129_def]; rfl
    · rfl

end Cases.Zip2005
