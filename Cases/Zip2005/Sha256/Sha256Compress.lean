import Cases.Zip2005.Sha256.Seg1
import Cases.Zip2005.Sha256.Seg2
import Cases.Zip2005.Sha256.Seg3
import Cases.Zip2005.Image.Ro

/-!
# `sha2::sha256::compress256`, one block

The SHA-256 compression function as compiled (straight-line: message schedule and 64 rounds
with the round constants spilled to the frame), specified as a **memory and return**
contract only: it returns to `ra` with the callee-saved registers restored, touches nothing
but its frame and the 32-byte state, and leaves *some* four words in the state. The digest
value is not stated -- `compress256` is reached only from SP1's `syscall_halt`, hashing the
committed public values, which the soundness statement does not mention (ledger, finding S1).

Four segments of about a thousand instructions each (`0x78037204`, `0x780381c4`,
`0x78039184`), joined at boundaries where only `sp`, the two frame cells the epilogue reads
(`st` at `sp - 0x390`, the block end at `sp - 0x188`, the block pointer at `sp - 0x70`) and
the save area are known; everything else is existentially quantified.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `compress256(state, blocks)` with one block: returns, callee-saved registers restored, only
the frame and the state written, some state left. -/
theorem compress256_spec {P : Prop} (s : MachineState) (ra sp st blk : Word) (S B : List Word)
    (hS : S.length = 4) (hB : B.length = 8)
    (hpc : s.pc = 0x780361e0#64) (hcode : CodeAt F_780361e0.base F_780361e0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x390 sp)
    (ha0 : s.getReg .x10 = st) (ha1 : s.getReg .x11 = blk) (ha2 : s.getReg .x12 = 1#64)
    (hRS : Region st S s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi st 4)
    (hRB : Region blk B s) (hokB : RegionOk Ro.layout.roBase Ro.layout.textHi blk 8)
    (hd1 : Disjoint (sp - 0x390#64) 114 st 4) (hd2 : Disjoint (sp - 0x390#64) 114 blk 8)
    (hd3 : Disjoint st 4 blk 8)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x390#64, 114), (st, 4)] s t → (∃ S', S'.length = 4 ∧ Region st S' t) → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x390#64) 114 := hstk.frame 114 (by decide)
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x390#64) 1 := hokW.sub' 0 1 (by decide) (by bv_omega)
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x388#64) 64 := hokW.sub' 1 64 (by decide) (by bv_omega)
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x188#64) 1 := hokW.sub' 65 1 (by decide) (by bv_omega)
  have hok3 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x180#64) 34 := hokW.sub' 66 34 (by decide) (by bv_omega)
  have hok3b : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x70#64) 1 := hokW.sub' 100 1 (by decide) (by bv_omega)
  have hok4 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokW.sub' 101 13 (by decide) (by bv_omega)
  have hlo := hstk.lo
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0x390#64) 1 s
  obtain ⟨F1, hF1, hF1l⟩ := Region.exists_junk (sp - 0x388#64) 64 s
  obtain ⟨F2, hF2, hF2l⟩ := Region.exists_junk (sp - 0x188#64) 1 s
  obtain ⟨F3, hF3, hF3l⟩ := Region.exists_junk (sp - 0x180#64) 34 s
  obtain ⟨F3b, hF3b, hF3bl⟩ := Region.exists_junk (sp - 0x70#64) 1 s
  obtain ⟨F4, hF4, hF4l⟩ := Region.exists_junk (sp - 0x68#64) 13 s
  have hu := Unchanged.refl [(sp - 0x390#64, 114), (st, 4)] s
  -- the three boundaries, innermost first
  have hk3 : ∀ v, v.pc = 0x78039184#64 → v.code = s.code → CodeAt F_780361e0.base F_780361e0.prog v → CodeWithin Ro.layout.textLo Ro.layout.textHi v →
      v.getReg .x2 = sp + 18446744073709550704#64 → v.getReg .x3 = s.getReg .x3 → v.getReg .x4 = s.getReg .x4 →
      Unchanged [(sp - 0x390#64, 114), (st, 4)] s v →
      Region (sp - 0x390#64) [st] v → (∃ J, J.length = 64 ∧ Region (sp - 0x388#64) J v) →
      Region (sp - 0x188#64) [blk + 64#64] v → (∃ J, J.length = 34 ∧ Region (sp - 0x180#64) J v) →
      Region (sp - 0x70#64) [blk] v → Region (sp - 0x68#64) [s.getReg .x27, s.getReg .x26, s.getReg .x25, s.getReg .x24, s.getReg .x23, s.getReg .x22, s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18, s.getReg .x9, s.getReg .x8, ra] v →
      (∃ S', S'.length = 4 ∧ Region st S' v) → (∃ B', B'.length = 8 ∧ Region blk B' v) → Safe P v := by
    intro v vpc vcode vcA vcw vx2 vx3 vx4 vU vF0 ⟨J1, hJ1, vF1⟩ vF2 ⟨J3, hJ3, vF3⟩ vF3b vF4 ⟨S', hS', vS⟩ ⟨B', hB', vB⟩
    exact compress256_seg3 v ra sp st blk (s.getReg .x8) (s.getReg .x9) (s.getReg .x18) (s.getReg .x19) (s.getReg .x20) (s.getReg .x21) (s.getReg .x22) (s.getReg .x23) (s.getReg .x24) (s.getReg .x25) (s.getReg .x26) (s.getReg .x27) J1 J3 S' B' hJ1 hJ3 hS' hB'
      vpc vcA vcw (vx2.trans (by bv_omega)) hstk hra1 vF0 vF1 vF2 vF3 vF3b vF4 vS hokS vB hokB hd1 hd2 hd3
      (fun t tpc tcode _ _ tx2 tx3 tx4 tx8 tx9 tx18 tx19 tx20 tx21 tx22 tx23 tx24 tx25 tx26 tx27 tU tS =>
        hk t tpc
          (CalleeSaved.intro (tx2.trans hsp.symm) (tx3.trans vx3) (tx4.trans vx4) tx8 tx9 tx18 tx19 tx20 tx21 tx22 tx23 tx24 tx25 tx26 tx27)
          (tcode.trans vcode) (vU.trans tU) tS)
  have hk2 : ∀ v, v.pc = 0x780381c4#64 → v.code = s.code → CodeAt F_780361e0.base F_780361e0.prog v → CodeWithin Ro.layout.textLo Ro.layout.textHi v →
      v.getReg .x2 = sp + 18446744073709550704#64 → v.getReg .x3 = s.getReg .x3 → v.getReg .x4 = s.getReg .x4 →
      Unchanged [(sp - 0x390#64, 114), (st, 4)] s v →
      Region (sp - 0x390#64) [st] v → (∃ J, J.length = 64 ∧ Region (sp - 0x388#64) J v) →
      Region (sp - 0x188#64) [blk + 64#64] v → (∃ J, J.length = 34 ∧ Region (sp - 0x180#64) J v) →
      Region (sp - 0x70#64) [blk] v → Region (sp - 0x68#64) [s.getReg .x27, s.getReg .x26, s.getReg .x25, s.getReg .x24, s.getReg .x23, s.getReg .x22, s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18, s.getReg .x9, s.getReg .x8, ra] v →
      (∃ S', S'.length = 4 ∧ Region st S' v) → (∃ B', B'.length = 8 ∧ Region blk B' v) → Safe P v := by
    intro v vpc vcode vcA vcw vx2 vx3 vx4 vU vF0 ⟨J1, hJ1, vF1⟩ vF2 ⟨J3, hJ3, vF3⟩ vF3b vF4 ⟨S', hS', vS⟩ ⟨B', hB', vB⟩
    exact compress256_seg2 v ra sp st blk (s.getReg .x8) (s.getReg .x9) (s.getReg .x18) (s.getReg .x19) (s.getReg .x20) (s.getReg .x21) (s.getReg .x22) (s.getReg .x23) (s.getReg .x24) (s.getReg .x25) (s.getReg .x26) (s.getReg .x27) J1 J3 S' B' hJ1 hJ3 hS' hB'
      vpc vcA vcw (vx2.trans (by bv_omega)) hstk vF0 vF1 vF2 vF3 vF3b vF4 vS hokS vB hokB hd1 hd2 hd3
      (fun t tpc tcode tcA tcw tx2 tx3 tx4 tU tF0 tF1 tF2 tF3 tF3b tF4 tS tB =>
        hk3 t tpc (tcode.trans vcode) tcA tcw tx2 (tx3.trans vx3) (tx4.trans vx4) (vU.trans tU) tF0 tF1 tF2 tF3 tF3b tF4 tS tB)
  have hk1 : ∀ v, v.pc = 0x78037204#64 → v.code = s.code → CodeAt F_780361e0.base F_780361e0.prog v → CodeWithin Ro.layout.textLo Ro.layout.textHi v →
      v.getReg .x2 = sp + 18446744073709550704#64 → v.getReg .x3 = s.getReg .x3 → v.getReg .x4 = s.getReg .x4 →
      Unchanged [(sp - 0x390#64, 114), (st, 4)] s v →
      Region (sp - 0x390#64) [st] v → (∃ J, J.length = 64 ∧ Region (sp - 0x388#64) J v) →
      Region (sp - 0x188#64) [blk + 64#64] v → (∃ J, J.length = 34 ∧ Region (sp - 0x180#64) J v) →
      Region (sp - 0x70#64) [blk] v → Region (sp - 0x68#64) [s.getReg .x27, s.getReg .x26, s.getReg .x25, s.getReg .x24, s.getReg .x23, s.getReg .x22, s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18, s.getReg .x9, s.getReg .x8, ra] v →
      (∃ S', S'.length = 4 ∧ Region st S' v) → (∃ B', B'.length = 8 ∧ Region blk B' v) → Safe P v := by
    intro v vpc vcode vcA vcw vx2 vx3 vx4 vU vF0 ⟨J1, hJ1, vF1⟩ vF2 ⟨J3, hJ3, vF3⟩ vF3b vF4 ⟨S', hS', vS⟩ ⟨B', hB', vB⟩
    exact compress256_seg1 v ra sp st blk (s.getReg .x8) (s.getReg .x9) (s.getReg .x18) (s.getReg .x19) (s.getReg .x20) (s.getReg .x21) (s.getReg .x22) (s.getReg .x23) (s.getReg .x24) (s.getReg .x25) (s.getReg .x26) (s.getReg .x27) J1 J3 S' B' hJ1 hJ3 hS' hB'
      vpc vcA vcw (vx2.trans (by bv_omega)) hstk vF0 vF1 vF2 vF3 vF3b vF4 vS hokS vB hokB hd1 hd2 hd3
      (fun t tpc tcode tcA tcw tx2 tx3 tx4 tU tF0 tF1 tF2 tF3 tF3b tF4 tS tB =>
        hk2 t tpc (tcode.trans vcode) tcA tcw tx2 (tx3.trans vx3) (tx4.trans vx4) (vU.trans tU) tF0 tF1 tF2 tF3 tF3b tF4 tS tB)
  sym_exec stop [0x78037204]
  sym_close hk1

end Cases.Zip2005
