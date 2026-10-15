import Cases.Zip2005.Witness.ArrayBytes32Err
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `ArrayVisitor<Bytes32, 32>` (`deserialize_tuple`, 0x78016938)

Both outcomes: `Ok` over the 1024 input bytes from offset 5 when 1024 bytes are left
(`Cases.Zip2005.array_bytes32_ok_spec`), the first element's `Err` otherwise (`Cases.Zip2005.array_bytes32_err_spec`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

theorem array_bytes32_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out de q l : Word)
    (O WW : List Word) (hOl : O.length = 129) (hWl : WW.length = 129)
    (hpc : s.pc = 0x78016938#64) (hcode : CodeAt F_78016938.base F_78016938.prog s)
    (hcodeE : CodeAt F_78019a10.base F_78019a10.prog s)
    (hcodeA : CodeAt F_7801775c.base F_7801775c.prog s)
    (hcodeN : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcodeM : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x900 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = de) (ha2 : s.getReg .x12 = 0x20#64)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 129)
    (hD : Region de [q + 5#64, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q WW s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 129)
    (hdO : Disjoint (sp - 0x900#64) 288 out 129) (hdD : Disjoint (sp - 0x900#64) 288 de 2)
    (heD : Disjoint out 129 de 2) (hOlo : out.toNat + 1032 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x900#64, 288), (out, 129), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (tagBytesW O WW 5 128) t → Region de [q + 1029#64, l - 1024#64] t →
      1024 ≤ l.toNat → Run.HeapAt L t → SafeN G n P t)
    (hkE : ∀ (t : MachineState) (e d0 d1 : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x900#64, 288), (out, 129), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (replaceByte O[0]! 0 1#8 :: e :: O.drop 2) t → Region de [d0, d1] t →
      l.toNat < 1024 → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s := by
  rcases Nat.lt_or_ge l.toNat 1024 with hl | hl
  · exact array_bytes32_err_spec s ra sp out de q l O WW hOl hWl hpc hcode hcodeE hcodeA hcodeN hcodeM hcw hro hheap hra hra1 hsp hstk ha0 ha1 ha2 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hl hio
      (fun t e d0 d1 h1 h2 h3 h4 h5 h6 hH => hkE t e d0 d1 h1 h2 h3 h4 h5 h6 hl hH)
  · exact array_bytes32_ok_spec s ra sp out de q l O WW hOl hWl hpc hcode hcodeE hcodeA hcodeN hcodeM hcw hro hheap hra hra1 hsp hstk ha0 ha1 ha2 hO hokO hD hokD hW hq hokW hdO hdD heD hOlo hDlo hl hio
      (fun t h1 h2 h3 h4 h5 h6 hH => hk t h1 h2 h3 h4 h5 h6 hl hH)

end Cases.Zip2005
