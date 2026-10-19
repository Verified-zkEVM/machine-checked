import Cases.Zip2005.Kit.ByteKit
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Image.F_78019b50
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `SeqAccess::next_element::<u8>` (0x78019b50)

bincode's sequence access over the slice reader: with `c ≠ 0` elements left the count is
decremented and one byte is read from the reader at `q + r` (`r < 8`, the byte's residue in the
input word `W[0]` at `q`): `Ok(Some(b))`, tags `0`, `1` and the byte in the first three bytes of
the output. An empty reader is the boxed `UnexpectedEof` (through the input-stream error
constructor, the contract `hio`, ledger A10); `c = 0` is `Ok(None)`.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

theorem trunc8_zext64 (b : BitVec 8) : BitVec.truncate 8 (BitVec.zeroExtend 64 b) = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  omega

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem next_u8_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (ra sp out acs de q l c : Word) (r : Nat)
    (hr : r < 8) (O W : List Word) (hOl : O.length = 2) (hWl : W.length = 1)
    (hpc : s.pc = 0x78019b50#64) (hcode : CodeAt F_78019b50.base F_78019b50.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x50 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = acs)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.textLo Ro.layout.textHi out 2)
    (hA : Region acs [de, c] s) (hokA : RegionOk Ro.layout.textLo Ro.layout.textHi acs 2)
    (hD : Region de [q + BitVec.ofNat 64 r, l] s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi de 2)
    (hW : Region q W s) (hq : 0x1c00000000 ≤ q.toNat) (hokW : RegionOk Ro.layout.textLo Ro.layout.textHi q 1)
    (hdO : Disjoint (sp - 0x50#64) 10 out 2) (hdA : Disjoint (sp - 0x50#64) 10 acs 2)
    (hdD : Disjoint (sp - 0x50#64) 10 de 2)
    (heA : Disjoint out 2 acs 2) (heD : Disjoint out 2 de 2) (hAD : Disjoint acs 2 de 2)
    (hOlo : out.toNat + 16 ≤ 0x78000000) (hAlo : acs.toNat + 16 ≤ 0x78000000)
    (hDlo : de.toNat + 16 ≤ 0x78000000)
    (hio : ∀ (u : MachineState) (sp' r' : Word) (L' : List (Word × Nat)), u.pc = 0x78036184#64 → u.code = s.code →
      u.getReg .x1 = r' → r' &&& ~~~1#64 = r' → u.getReg .x2 = sp' → StackOk Ro.layout 0x40 sp' →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (e : Word), t.pc = r' → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x40#64, 8), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → t.getReg .x10 = e →
        Run.HeapAt L' t → SafeN G n P t) → SafeN G n P u)
    (hkN : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceByte (replaceByte O[0]! 1 0#8) 0 0#8, O[1]!] t →
      Region acs [de, c] t → Region de [q + BitVec.ofNat 64 r, l] t → c = 0#64 → Run.HeapAt L t → SafeN G n P t)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceByte (replaceByte (replaceByte O[0]! 1 1#8) 2 (extractByte W[0]! r)) 0 0#8, O[1]!] t →
      Region acs [de, c - 1#64] t → Region de [q + BitVec.ofNat 64 (r + 1), l - 1#64] t → c ≠ 0#64 →
      l ≠ 0#64 → Run.HeapAt L t → SafeN G n P t)
    (hkE : ∀ (t : MachineState) (e : Word), t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out [replaceByte O[0]! 0 1#8, e] t → Region acs [de, c - 1#64] t →
      Region de [q + BitVec.ofNat 64 r, l] t → c ≠ 0#64 → l = 0#64 → Run.HeapAt L t → SafeN G n P t) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x50#64) 10 := hstk.frame 10 (by decide)
  have hlo := hstk.lo
  have hokHp : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHpc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHpa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x10#64) 2 := hokS.sub' 8 2 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x10#64) 2 s
  rw [MachineChecked.RiscV.Sym.List.eq_map_range O hOl] at hO
  rw [MachineChecked.RiscV.Sym.List.eq_map_range W hWl] at hW
  interval_cases r <;>
  · have hu := Unchanged.refl [(sp - 0x50#64, 10), (out, 2), (acs, 2), (de, 2),
      (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
    sym_exec [hio]
    · -- `c = 0`: `Ok(None)`
      have hc : c = 0#64 := by simpa using hbr1
      rw [show BitVec.truncate 8 (0#64) = 0#8 from rfl] at v2_def v3_def
      rw [← v3_def, ← v2_def] at hR0
      sym_close hkN
    · -- the reader empty: the boxed error
      have hc : c ≠ 0#64 := by simpa using hbr1
      have hl : l = 0#64 := by simpa using hbr6
      rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v25_def
      rw [← v25_def] at hR0
      rw [show c + 18446744073709551615#64 = c - 1#64 by bv_omega] at hR1
      sym_close (hkE _ post17_0)
    · -- `Ok(Some(b))`
      have hc : c ≠ 0#64 := by simpa using hbr1
      have hl : l ≠ 0#64 := by simpa using hbr6
      rw [show BitVec.truncate 8 (1#64) = 1#8 from rfl] at v14_def
      rw [show BitVec.truncate 8 (0#64) = 0#8 from rfl] at v16_def
      rw [← v10_def, trunc8_zext64] at v15_def
      rw [← v16_def, ← v15_def, ← v14_def] at hR0
      rw [show c + 18446744073709551615#64 = c - 1#64 by bv_omega] at hR1
      rw [show l + 18446744073709551615#64 = l - 1#64 by bv_omega] at hR4
      sym_close hk

end Cases.Zip2005
