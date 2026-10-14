import Cases.Zip2005.Runtime.MemcpyMis
import Cases.Zip2005.Kit.ByteShiftAll
import Cases.Zip2005.Runtime.And7
import Cases.Zip2005.Image.Ro

/-! `memcpy(dst, src, 18)` with `dst ≡ 5`, `src ≡ 0` (mod 8). -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
theorem memcpy_d5s0_18_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 3) (hSl : S.length = 3)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 18#64)
    (hD : Region (dst - 5#64) D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi (dst - 5#64) 3)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 3)
    (hdj : Disjoint (dst - 5#64) 3 src 3)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst - 5#64, 3)] s t →
      Region (dst - 5#64) (mcpyW D S 5 0 18 3) t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst - 5#64, 3)] s
  have hm : dst &&& 7#64 = 5#64 := and7_of_sub5' hokD.aligned
  have hm2 : src &&& 7#64 = 0#64 := hokS.and7
  rw [AsmVerif.RiscV.Sym.List.eq_map_range D hDl] at hD
  rw [AsmVerif.RiscV.Sym.List.eq_map_range S hSl] at hS
  sym_exec
  have e : [v21, v38, v58] = mcpyW D S 5 0 18 3 := by
    sym_subst
    simp only [mcpyW, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_⟩ <;>
    · apply word_ext
      intro k hk
      interval_cases k <;> simp (disch := decide) only [byte_simp]
  rw [e] at hR0
  sym_close hk

end Cases.Zip2005
