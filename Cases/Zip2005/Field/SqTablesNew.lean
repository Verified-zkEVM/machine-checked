import Cases.Zip2005.Field.SqFromIter
import Cases.Zip2005.Field.SqInvLoop
import Cases.Zip2005.Runtime.MemsetInv
import Cases.Zip2005.Image.F_78030a94
import Cases.Zip2005.Image.Ro

/-!
# `SqrtTables::<Fp>::new` (0x78030a94), as a function

`SqrtTables::new(hash_xor, hash_mod = 1098)`: four power tables of 256 elements (`from_iter`,
`sq_from_iter_spec`), each next generator the last element times the previous one (two `mulmod`
calls); the `inv` table of 1098 bytes (`__rust_alloc(1098, 1)`, `memset(·, 1, 1098)`) filled by
hashing the last table (`sq_inv_loop`, a collision panics); the last table shrunk to 129 elements
(`__rust_realloc`); the struct written out. Shape only: nothing is claimed about the tables'
contents, which `sqrt_alt` does not rely on (ledger A3).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- `__rust_alloc(1098, 1)` at `new`'s call (`0x7803120c`): the `inv` table. -/
def SqAllocInv (G : MachineState → Prop) (n : Nat) (P : Prop) (code : Word → Option Instr) : Prop :=
  ∀ (u : MachineState) (sp' : Word), u.pc = 0x7801bcec#64 → u.code = code →
    u.getReg .x1 = 0x7803120c#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x30 sp' →
    u.getReg .x10 = 1098#64 → u.getReg .x11 = 1#64 →
    (∀ (t : MachineState) (ptr : Word) (B : List Word), t.pc = 0x7803120c#64 → CalleeSaved u t →
      t.code = u.code → Unchanged [(sp' - 0x30#64, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
      t.getReg .x10 = ptr → B.length = 138 → Region ptr B t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 138 →
      0x78048980 ≤ ptr.toNat → ptr.toNat + 1104 ≤ 0x1c00000000 → SafeN G n P t) →
    SafeN G n P u

/-- `__rust_realloc(p, 0x2000, 8, 0x1020)` at `new`'s call (`0x7803139c`): the last table, 256
elements, shrunk to 129. -/
def SqRealloc (G : MachineState → Prop) (n : Nat) (P : Prop) (code : Word → Option Instr) : Prop :=
  ∀ (u : MachineState) (sp' p0 : Word), u.pc = 0x7801bd38#64 → u.code = code →
    u.getReg .x1 = 0x7803139c#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x100 sp' →
    u.getReg .x10 = p0 → u.getReg .x11 = 0x2000#64 → u.getReg .x12 = 8#64 →
    u.getReg .x13 = 0x1020#64 → 0x78048980 ≤ p0.toNat →
    (∀ (t : MachineState) (p' : Word), t.pc = 0x7803139c#64 → CalleeSaved u t →
      t.code = u.code → Unchanged [(sp' - 0x100#64, 32), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
      t.getReg .x10 = p' → RegionOk Ro.layout.roBase Ro.layout.textHi p' 516 →
      0x78048980 ≤ p'.toNat → p'.toNat + 0x1020 ≤ 0x1c00000000 → SafeN G n P t) →
    SafeN G n P u

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem sqrt_tables_new_spec {Gd : MachineState → Prop} {nb : Nat} {P : Prop} (s : MachineState) (ra sp out hxw : Word) (O : List Word)
    (hOl : O.length = 9)
    (hpc : s.pc = 0x78030a94#64) (hcodeN : CodeAt F_78030a94.base F_78030a94.prog s)
    (hcodeFI : CodeAt F_780326cc.base F_780326cc.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcodeMs : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcwS : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hroS : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x3d0 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = hxw) (ha2 : s.getReg .x12 = 1098#64)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 9)
    (hOlo : sp.toNat ≤ out.toNat) (hOhi : out.toNat + 72 ≤ 0x78000000)
    (halloc : SqAlloc Gd nb P s.code) (hres : SqReserve Gd nb P s.code) (halloci : SqAllocInv Gd nb P s.code)
    (hrealloc : SqRealloc Gd nb P s.code)
    (hhandle_rv : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → SafeN Gd nb P u)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → SafeN Gd nb P u)
    (hunwrap_opt : ∀ u : MachineState, u.pc = 0x7803f364#64 → u.code = s.code → SafeN Gd nb P u)
    (hk : ∀ (t : MachineState) (iptr tg0 tg1 tg2 tg3 : Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code →
      Unchanged [(sp - 0x3d0#64, 122), (out, 9), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [1098#64, iptr, 1098#64, tg0, tg1, tg2, tg3, 1098#64,
        replaceWord32 O[8]! 0 (hxw.truncate 32)] t →
      RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 → RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 →
      0x78048980 ≤ iptr.toNat → iptr.toNat + 1104 ≤ 0x1c00000000 →
      0x78048980 ≤ tg0.toNat → tg0.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg1.toNat → tg1.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg2.toNat → tg2.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg3.toNat → tg3.toNat + 0x1020 ≤ 0x1c00000000 →
      RoImage Ro.layout t → SafeN Gd nb P t) :
    SafeN Gd nb P s := by
  have hlo := hstk.lo
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x3d0#64) 122 := hstk.frame 122 (by decide)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x190#64) 50 := hokS.sub' 72 50 (by decide) (by bv_omega)
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x190#64) 16 := hokF.sub' 0 16 (by decide) (by bv_omega)
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x190#64 + 0x80#64) 3 := hokF.sub' 16 3 (by decide) (by bv_omega)
  have hok3 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x190#64 + 0x98#64) 6 := hokF.sub' 19 6 (by decide) (by bv_omega)
  have hok4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x190#64 + 0xc8#64) 12 := hokF.sub' 25 12 (by decide) (by bv_omega)
  have hok5 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x190#64 + 0x128#64) 13 := hokF.sub' 37 13 (by decide) (by bv_omega)
  obtain ⟨F1, hF1, hF1l⟩ := Region.exists_junk (sp - 0x190#64) 16 s
  obtain ⟨F2, hF2, hF2l⟩ := Region.exists_junk (sp - 0x190#64 + 0x80#64) 3 s
  obtain ⟨F3, hF3, hF3l⟩ := Region.exists_junk (sp - 0x190#64 + 0x98#64) 6 s
  obtain ⟨F4, hF4, hF4l⟩ := Region.exists_junk (sp - 0x190#64 + 0xc8#64) 12 s
  obtain ⟨F5, hF5, hF5l⟩ := Region.exists_junk (sp - 0x190#64 + 0x128#64) 13 s
  clear hokF
  have hu := Unchanged.refl [(sp - 0x3d0#64, 122), (out, 9), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  -- `from_iter` at this call site
  have hfi : ∀ (u : MachineState) (ra' sp' out' it g w2 w3 w4 w5 : Word) (G O' : List Word),
      G.length = 4 → O'.length = 3 → u.pc = 0x780326cc#64 → u.code = s.code → RoImage Ro.layout u →
      u.getReg .x1 = ra' → ra' &&& ~~~1#64 = ra' → u.getReg .x2 = sp' → StackOk Ro.layout 0x240 sp' →
      u.getReg .x10 = out' → u.getReg .x11 = it →
      Region it [g, 0x10000000000#64, w2, w3, w4, w5] u → RegionOk Ro.layout.roBase Ro.layout.textHi it 6 →
      Region g G u → RegionOk Ro.layout.roBase Ro.layout.textHi g 4 → Region out' O' u → RegionOk Ro.layout.roBase Ro.layout.textHi out' 3 →
      sp'.toNat ≤ it.toNat → it.toNat + 48 ≤ 0x78000000 → sp'.toNat ≤ g.toNat →
      g.toNat + 32 ≤ 0x78000000 → sp'.toNat ≤ out'.toNat → out'.toNat + 24 ≤ 0x78000000 →
      Disjoint it 6 g 4 → Disjoint out' 3 it 6 →
      (∀ (t : MachineState) (ptr : Word) (T : List Word), t.pc = ra' → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp' - 0x240#64, 72), (out', 3), (it, 6), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        Region out' [256#64, ptr, 256#64] t → T.length = 1024 → Region ptr T t →
        RegionOk Ro.layout.roBase Ro.layout.textHi ptr 1024 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 0x2000 ≤ 0x1c00000000 → SafeN Gd nb P t) → SafeN Gd nb P u :=
    fun u ra' sp' out' it g w2 w3 w4 w5 G O' hGl hOl' hpcu hcu hrou hrau hra1u hspu hstku ha0u ha1u
      hIu hokIu hGu hokGu hOu hokOu h1 h2 h3 h4 h5 h6 hdIG hdOI hku =>
      sq_from_iter_spec u ra' sp' out' it g w2 w3 w4 w5 G O' hGl hOl' hpcu
        (codeAt_of_code_eq hcu hcodeFI) (codeAt_of_code_eq hcu hcodeM) (codeAt_of_code_eq hcu hcodeSh)
        (fun a ha => hcwS a (hcu ▸ ha)) hrou hrau hra1u hspu hstku ha0u ha1u hIu hokIu hGu hokGu hOu
        hokOu h1 h2 h3 h4 h5 h6 hdIG hdOI (hcu.symm ▸ halloc) (hcu.symm ▸ hres)
        (fun v hv hcv => hhandle_rv v hv (hcv.trans hcu)) hku
  unfold SqAllocInv at halloci
  unfold SqRealloc at hrealloc
  sym_exec [hfi, uint256_mulmod_spec, halloci, memset1098_spec, hhandle_rv, hpp, hunwrap_opt]
    stop [0x78031250]
  pick_goal 2
  · -- a fifth power table: the scan's range `4..4` is exhausted
    exfalso
    revert hbr391
    rw [← v389_def, ← v390_def, ← v307_def, ← v303_def, ← v219_def, ← v215_def, ← v131_def]
    decide
  -- the hash loop's first element
  have hokE : RegionOk Ro.layout.roBase Ro.layout.textHi post327_0 4 := post327_9.sub' 0 4 (by decide) (by simp)
  obtain ⟨E, hE, hEl⟩ := Region.exists_junk post327_0 4 s_421
  rw [list4_cells E hEl] at hE
  sym_reframe
  sym_exec [fp_get_lower_32_spec] stop [0x78031274]
  have hb : v8.toNat < 1098 := by rw [← v8_def]; exact remu1098_lt _
  sym_reframe
  sym_exec [hpp] stop [0x7803127c]
  sym_reframe
  refine sq_inv_loop (G := Gd) (nb := nb) (P := P) s s_2 post402_0 hxw post327_0 (sp + 18446744073709551216#64)
    (s.getReg .x3) (s.getReg .x4) 256#64 post327_0 11037532056220336129#64 hcodeN hcodeL hcwS
    post402_9 post327_9 post327_11 hpp ?_ 255 s_2 0 post410_0 v8 hcode0 hro (Unchanged.refl _ _)
    (SqInvAt.mk hpc (hx10.trans v9_def.symm) hb (by rw [hx21]) (by rw [hx23])
      (by rw [hx24]) hx2 hx3 hx4 hx8 hx9 hx18 hx19 hx20 hx25 hx26 hx27 post410_5 hR5
      (by decide)) rfl
  intro t IV hpct hct hUt r21 r23 r24 r2 r3 r4 r8 r9 r18 r19 r20 r25 r26 r27 hIVl hIV hrot
  -- what the loop leaves alone
  have e190 : ∀ c : Nat, c ≤ 0x190 → (sp - 0x190#64 + BitVec.ofNat 64 c).toNat = sp.toNat - 0x190 + c := by
    intro c hc
    rw [BitVec.toNat_add, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have e190' : (sp - 0x190#64).toNat = sp.toNat - 0x190 := by
    rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hdj : ∀ {b : Word} {m : Nat}, b.toNat + 8 * m ≤ 0x78000000 →
      ∀ r ∈ [(post402_0, 138)], AsmVerif.RiscV.Sym.Disjoint b m r.1 r.2 := by
    intro b m h r hr
    rw [List.mem_singleton] at hr; subst hr; unfold AsmVerif.RiscV.Sym.Disjoint; dsimp only; omega
  have hT0 := hR0.of_unchanged' hUt (n := 9) (by simp) (hdj (by omega))
  have hT1 := hR1.of_unchanged' hUt (n := 16) (by simp) (hdj (by rw [e190']; omega))
  have hT2 := hR2.of_unchanged' hUt (n := 3) (by simp) (hdj (by rw [e190 0x80 (by decide)]; omega))
  have hT3 := hR3.of_unchanged' hUt (n := 12) (by simp) (hdj (by rw [e190 0xc8 (by decide)]; omega))
  have hT4 := hR4.of_unchanged' hUt (n := 13) (by simp) (hdj (by rw [e190 0x128 (by decide)]; omega))
  have hframe' : Unchanged [(sp - 0x3d0#64, 122), (out, 9), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t :=
    hframe.trans_cover hUt (fun r hr => ⟨(0x78048980#64, 14780690128), by simp, by
      rw [List.mem_singleton] at hr; subst hr; unfold Covers; dsimp only; simp only [BitVec.toNat_ofNat]
      omega⟩)
  clear hR0 hR1 hR2 hR3 hR4 hR5 hR6 hframe hu hcode0
  have hframe := hframe'
  clear hframe'
  have hu := Unchanged.refl [(sp - 0x3d0#64, 122), (out, 9), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] t
  have hcode0 : t.code = s.code := hct
  have hcwt : CodeWithin Ro.layout.textLo Ro.layout.textHi t := fun a ha => hcwS a (hct ▸ ha)
  have hcN := codeAt_of_code_eq hct hcodeN
  sym_exec [hrealloc, hhandle_rv, hpp]
  sym_close hk _ post402_0 post53_0 post151_0 post239_0


end Cases.Zip2005
