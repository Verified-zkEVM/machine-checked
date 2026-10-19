import Cases.Zip2005.Runtime.MemcpyMis
import Cases.Zip2005.Kit.ByteShiftAll
import Cases.Zip2005.Runtime.And7
import Cases.Zip2005.Image.Ro

/-! `memcpy(dst, src, 1010)` with `dst ≡ 6`, `src ≡ 0` (mod 8). -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
theorem memcpy_d6s0_1010_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 127) (hSl : S.length = 127)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 1010#64)
    (hD : Region (dst - 6#64) D s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi (dst - 6#64) 127)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 127)
    (hdj : Disjoint (dst - 6#64) 127 src 127)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst - 6#64, 127)] s t →
      Region (dst - 6#64) (mcpyW D S 6 0 1010 127) t → SafeN G n P t) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(dst - 6#64, 127)] s
  have hm : dst &&& 7#64 = 6#64 := and7_of_sub6' hokD.aligned
  have hm2 : src &&& 7#64 = 0#64 := hokS.and7
  rw [MachineChecked.RiscV.Sym.List.eq_map_range D hDl] at hD
  rw [MachineChecked.RiscV.Sym.List.eq_map_range S hSl] at hS
  sym_exec
  have e : [v18, v29, v32, v35, v37, v53, v56, v59, v61, v77, v80, v83, v85, v101, v104, v107, v109, v125, v128, v131, v133, v149, v152, v155, v157, v173, v176, v179, v181, v197, v200, v203, v205, v221, v224, v227, v229, v245, v248, v251, v253, v269, v272, v275, v277, v293, v296, v299, v301, v317, v320, v323, v325, v341, v344, v347, v349, v365, v368, v371, v373, v389, v392, v395, v397, v413, v416, v419, v421, v437, v440, v443, v445, v461, v464, v467, v469, v485, v488, v491, v493, v509, v512, v515, v517, v533, v536, v539, v541, v557, v560, v563, v565, v581, v584, v587, v589, v605, v608, v611, v613, v629, v632, v635, v637, v653, v656, v659, v661, v677, v680, v683, v685, v701, v704, v707, v709, v725, v728, v731, v733, v749, v752, v755, v757, v790, v804] = mcpyW D S 6 0 1010 127 := by
    sym_subst
    simp only [mcpyW, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · apply word_ext
      intro k hk
      interval_cases k <;> simp (disch := decide) only [byte_simp]
  rw [e] at hR0
  sym_close hk

end Cases.Zip2005
