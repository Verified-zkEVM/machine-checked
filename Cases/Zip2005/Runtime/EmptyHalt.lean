import Cases.Zip2005.Runtime.SyscallHalt
import Cases.Zip2005.Runtime.SyscallWrite
import Cases.Zip2005.Image.F_78035e50
import Cases.Zip2005.Image.F_78035f14
import Cases.Zip2005.Image.F_7801aed0
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `alloc::fmt::format` (0x78035e50) and `empty_input_stream_halt` (0x78035f14)

`format(args)`: when the `Arguments` is a single static piece (`a2` odd: the pointer-tagged
`as_str` case) the `String` is an allocation and a `memcpy`; otherwise (`a2` even, as every
call from the guest, whose `Arguments` is built in a frame) `format_inner` builds it. The
`format_inner` call is a contract (ledger A9, the instance at this return address), its
write set the frame, the `String` and the heap **around the hasher static**: the static survives
it, so the halt that follows can be applied.

`empty_input_stream_halt`: `format!("… {len} …")` into a `String` in the frame, `syscall_write`
of it to fd 2, then `halt_invalid_hint` — `syscall_halt(3)`, which never accepts.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- The heap below the hasher static: `[0x78040620, 0x78048830)`. -/
theorem heapLoOk : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 :=
  ⟨by decide, by decide, Or.inr (by decide)⟩

/-- The heap above the hasher static: `[0x780488a8, 0x1c00000000)`. -/
theorem heapHiOk : RegionOk Ro.layout.textLo Ro.layout.textHi 0x780488a8#64 14780690155 :=
  ⟨by decide, by decide, Or.inr (by decide)⟩

theorem and_one_of_even {a : Word} (h : a.toNat % 2 = 0) : a &&& 1#64 = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.one_mod, Nat.and_one_is_mod, h]

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem fmt_format_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out tpl args : Word) (O : List Word)
    (hOl : O.length = 3)
    (hpc : s.pc = 0x78035e50#64) (hcode : CodeAt F_78035e50.base F_78035e50.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x430 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = tpl) (ha2 : s.getReg .x12 = args)
    (hargs : args.toNat % 2 = 0)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 3)
    (hdj : Disjoint (sp - 0x30#64) 6 out 3)
    (hfmt : ∀ (u : MachineState) (sp' d : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1cc#64 → u.code = s.code →
      u.getReg .x1 = 0x78035e7c#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x400 sp' → u.getReg .x10 = d →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (S : List Word), t.pc = 0x78035e7c#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp' - 0x400#64, 128), (d, 3), (0x78040620#64, 4162), (0x780488a8#64, 14780690155)] u t →
        S.length = 3 → Region d S t → Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hk : ∀ (t : MachineState) (S : List Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x430#64, 134), (out, 3), (0x78040620#64, 4162), (0x780488a8#64, 14780690155)] s t →
      S.length = 3 → Region out S t → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x430#64) 134 := hstk.frame 134 (by decide)
  have hu := Unchanged.refl [(sp - 0x430#64, 134), (out, 3), (0x78040620#64, 4162), (0x780488a8#64, 14780690155)] s
  have hlo := hstk.lo
  have hokLo := heapLoOk
  have hokHi := heapHiOk
  have hargs' := and_one_of_even hargs
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x30#64) 6 := hokS.sub' 128 6 (by decide) (by bv_omega)
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x30#64) 6 s
  sym_exec [hfmt]
  sym_close hk
  rfl

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem empty_input_stream_halt_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (sp len : Word)
    (f h0 h1 h2 h3 cnt b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (hpc : s.pc = 0x78035f14#64) (hcode : CodeAt F_78035f14.base F_78035f14.prog s)
    (hcodeFmt : CodeAt F_78035e50.base F_78035e50.prog s)
    (hcodeWr : CodeAt F_7801b3b0.base F_7801b3b0.prog s)
    (hcodeHi : CodeAt F_78035e44.base F_78035e44.prog s)
    (hcodeHalt : CodeAt F_7801afc0.base F_7801afc0.prog s)
    (hcodeCpy : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSet : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeSha : CodeAt F_780361e0.base F_780361e0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x4b0 sp)
    (ha0 : s.getReg .x10 = len)
    (hST : Region 0x78048830#64 [f, h0, h1, h2, h3, cnt, b0, b1, b2, b3, b4, b5, b6, b7, 0#64] s)
    (hfmt : ∀ (u : MachineState) (sp' d : Word) (L' : List (Word × Nat)), u.pc = 0x7803d1cc#64 → u.code = s.code →
      u.getReg .x1 = 0x78035e7c#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x400 sp' → u.getReg .x10 = d →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (S : List Word), t.pc = 0x78035e7c#64 → CalleeSaved u t →
        t.code = u.code →
        Unchanged [(sp' - 0x400#64, 128), (d, 3), (0x78040620#64, 4162), (0x780488a8#64, 14780690155)] u t →
        S.length = 3 → Region d S t → Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x4b0#64) 150 := hstk.frame 150 (by decide)
  have hu := Unchanged.refl [(sp - 0x4b0#64, 150), (0x78048830#64, 15), (0x78040620#64, 4162),
    (0x780488a8#64, 14780690155)] s
  have hlo := hstk.lo
  have hokST := hasherOk
  have hokLo := heapLoOk
  have hokHi := heapHiOk
  -- the frame (`sp' = sp - 0x40`): [0, 8) unused, the `String` [8, 0x20), the `Arguments`
  -- [0x20, 0x38), the save [0x38, 0x40)
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x40#64) 1 := hokS.sub' 142 1 (by decide) (by bv_omega)
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x38#64) 3 := hokS.sub' 143 3 (by decide) (by bv_omega)
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x20#64) 4 := hokS.sub' 146 4 (by decide) (by bv_omega)
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x40#64) 1 s
  obtain ⟨F1, hF1, hF1l⟩ := Region.exists_junk (sp - 0x38#64) 3 s
  obtain ⟨F2, hF2, hF2l⟩ := Region.exists_junk (sp - 0x20#64) 4 s
  sym_exec [fmt_format_spec, syscall_write_other_spec, hfmt] stop [0x78035e44] 400
  -- `halt_invalid_hint` never returns: its spec is applied by hand at the call (the code facts
  -- over the code map, the stack room below this frame)
  have hcE : ∀ {b : Word} {p : List (Option Instr)}, CodeAt b p s → CodeAt b p s_23 :=
    fun h i hi => (congrFun hcode _).trans (h i hi)
  have hstk' : StackOk Ro.layout 0x470 (sp + 18446744073709551552#64) := by
    have h1 := hstk.aligned; have h2 := hstk.lo; have h3 := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop)); have h4 := sp.isLt
    refine ⟨?_, ?_, ?_⟩ <;> rw [BitVec.toNat_add] <;> simp only [BitVec.toNat_ofNat] <;> omega
  exact halt_invalid_hint_spec s_23 _ f h0 h1 h2 h3 cnt b0 b1 b2 b3 b4 b5 b6 b7 hpc (hcE hcodeHi)
    (hcE hcodeHalt) (hcE hcodeCpy) (hcE hcodeSet) (hcE hcodeSha) hcw hro hcarry hx2 hstk' hR0

end Cases.Zip2005
