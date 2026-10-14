import Cases.Zip2005.Field.SqTablesNew
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Image.F_78032b38
import Cases.Zip2005.Image.Ro

/-!
# `FP_TABLES`' lazy initialisation (`spin::Once::try_call_once_slow`, 0x78032b38), from state 0

The `Once` at `0x780488a8` (state byte at `+0x48`) uninitialised: the state is set to running,
`SqrtTables::new(0x11be, 1098)` builds the tables into the frame (`sqrt_tables_new_spec`), the
struct is copied into the static, and the state set to complete (`2`). The static lies between
the allocator's control block and its arena, outside every allocator write
(`Proof/Runtime/HeapSplit.lean`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem fp_tables_init_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp : Word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 : Word)
    (hpcS : s.pc = 0x78032b38#64) (hcodeO : CodeAt F_78032b38.base F_78032b38.prog s)
    (hcodeN : CodeAt F_78030a94.base F_78030a94.prog s)
    (hcodeFI : CodeAt F_780326cc.base F_780326cc.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeSh : CodeAt F_7801aed0.base F_7801aed0.prog s)
    (hcodeMs : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcodeCpy : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcwS : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hroS : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x430 sp)
    (ha0 : s.getReg .x10 = 0x780488a8#64)
    (hT : Region 0x780488a8#64 [w0, w1, w2, w3, w4, w5, w6, w7, w8, 0#64] s)
    (halloc : SqAlloc G n P s.code) (hres : SqReserve G n P s.code) (halloci : SqAllocInv G n P s.code)
    (hrealloc : SqRealloc G n P s.code)
    (hhandle_rv : ∀ u : MachineState, u.pc = 0x7803cf14#64 → u.code = s.code → SafeN G n P u)
    (hpp : ∀ u : MachineState, u.pc = 0x7803de20#64 → u.code = s.code → SafeN G n P u)
    (hunwrap_opt : ∀ u : MachineState, u.pc = 0x7803f364#64 → u.code = s.code → SafeN G n P u)
    (hk : ∀ (t : MachineState) (iptr tg0 tg1 tg2 tg3 hx : Word), t.pc = ra → CalleeSaved s t →
      t.code = s.code →
      Unchanged [(sp - 0x430#64, 134), (0x780488a8#64, 10), (0x78040620#64, 4162),
        (0x78048980#64, 14780690128)] s t →
      t.getReg .x10 = 0x780488a8#64 →
      Region 0x780488a8#64 [1098#64, iptr, 1098#64, tg0, tg1, tg2, tg3, 1098#64, hx, 2#64] t →
      RegionOk Ro.layout.roBase Ro.layout.textHi iptr 138 → RegionOk Ro.layout.roBase Ro.layout.textHi tg0 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg1 1024 → RegionOk Ro.layout.roBase Ro.layout.textHi tg2 1024 →
      RegionOk Ro.layout.roBase Ro.layout.textHi tg3 516 →
      0x78048980 ≤ iptr.toNat → iptr.toNat + 1104 ≤ 0x1c00000000 →
      0x78048980 ≤ tg0.toNat → tg0.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg1.toNat → tg1.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg2.toNat → tg2.toNat + 0x2000 ≤ 0x1c00000000 →
      0x78048980 ≤ tg3.toNat → tg3.toNat + 0x1020 ≤ 0x1c00000000 →
      RoImage Ro.layout t → SafeN G n P t) :
    SafeN G n P s := by
  have hlo := hstk.lo
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x430#64) 134 := hstk.frame 134 (by decide)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hokT : RegionOk Ro.layout.textLo Ro.layout.textHi 0x780488a8#64 10 := ⟨by decide, by decide, Or.inr (by decide)⟩
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x60#64) 12 := hokS.sub' 122 12 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x60#64) 12 s
  have hu := Unchanged.refl [(sp - 0x430#64, 134), (0x780488a8#64, 10), (0x78040620#64, 4162),
    (0x78048980#64, 14780690128)] s
  have hnew : ∀ (u : MachineState) (ra' sp' out hxw : Word) (O : List Word), O.length = 9 →
      u.pc = 0x78030a94#64 → u.code = s.code → RoImage Ro.layout u →
      u.getReg .x1 = ra' → ra' &&& ~~~1#64 = ra' → u.getReg .x2 = sp' → StackOk Ro.layout 0x3d0 sp' →
      u.getReg .x10 = out → u.getReg .x11 = hxw → u.getReg .x12 = 1098#64 →
      Region out O u → RegionOk Ro.layout.roBase Ro.layout.textHi out 9 →
      sp'.toNat ≤ out.toNat → out.toNat + 72 ≤ 0x78000000 →
      (∀ (t : MachineState) (iptr tg0 tg1 tg2 tg3 : Word), t.pc = ra' → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp' - 0x3d0#64, 122), (out, 9), (0x78040620#64, 4162),
          (0x78048980#64, 14780690128)] u t →
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
        RoImage Ro.layout t → SafeN G n P t) → SafeN G n P u :=
    fun u ra' sp' out hxw O hOl hpcu hcu hrou hrau hra1u hspu hstku ha0u ha1u ha2u hOu hokOu h1 h2 hku =>
      sqrt_tables_new_spec u ra' sp' out hxw O hOl hpcu (codeAt_of_code_eq hcu hcodeN)
        (codeAt_of_code_eq hcu hcodeFI) (codeAt_of_code_eq hcu hcodeM) (codeAt_of_code_eq hcu hcodeSh)
        (codeAt_of_code_eq hcu hcodeMs) (codeAt_of_code_eq hcu hcodeL) (fun a ha => hcwS a (hcu ▸ ha))
        hrou hrau hra1u hspu hstku ha0u ha1u ha2u hOu hokOu h1 h2 (hcu.symm ▸ halloc)
        (hcu.symm ▸ hres) (hcu.symm ▸ halloci) (hcu.symm ▸ hrealloc)
        (fun v hv hcv => hhandle_rv v hv (hcv.trans hcu)) (fun v hv hcv => hpp v hv (hcv.trans hcu))
        (fun v hv hcv => hunwrap_opt v hv (hcv.trans hcu)) hku
  sym_exec [hnew, memcpy72_spec]
  have h23 : v23 = 2#64 := by rw [← v23_def, ← v7_def]; decide
  subst h23
  sym_close hk _ post15_0 post15_1 post15_2 post15_3 post15_4
    (replaceWord32 [F[1]!, F[2]!, F[3]!, F[4]!, F[5]!, F[6]!, F[7]!, F[8]!, F[9]!][8]! 0
      (BitVec.truncate 32 4542#64))

end Cases.Zip2005
