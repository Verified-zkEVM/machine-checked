import Cases.Zip2005.Runtime.MemcpyMis
import Cases.Zip2005.Kit.ByteShift
import Cases.Zip2005.Image.Ro

/-! `memcpy(dst, src, 1009)` with `dst ≡ 1`, `src ≡ 0` (mod 8). -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
theorem memcpy_d1s0_1009_spec {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 127) (hSl : S.length = 127)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 1009#64)
    (hD : Region (dst - 1#64) D s) (hokD : RegionOk Ro.layout.roBase Ro.layout.textHi (dst - 1#64) 127)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 127)
    (hdj : Disjoint (dst - 1#64) 127 src 127)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst - 1#64, 127)] s t →
      Region (dst - 1#64) (mcpyW D S 1 0 1009 127) t → Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl [(dst - 1#64, 127)] s
  have hm : dst &&& 7#64 = 1#64 := and7_of_sub1 hokD.aligned
  have hm2 : src &&& 7#64 = 0#64 := hokS.and7
  rw [AsmVerif.RiscV.Sym.List.eq_map_range D hDl] at hD
  rw [AsmVerif.RiscV.Sym.List.eq_map_range S hSl] at hS
  sym_exec
  have e : [v28, v39, v42, v45, v47, v63, v66, v69, v71, v87, v90, v93, v95, v111, v114, v117, v119, v135, v138, v141, v143, v159, v162, v165, v167, v183, v186, v189, v191, v207, v210, v213, v215, v231, v234, v237, v239, v255, v258, v261, v263, v279, v282, v285, v287, v303, v306, v309, v311, v327, v330, v333, v335, v351, v354, v357, v359, v375, v378, v381, v383, v399, v402, v405, v407, v423, v426, v429, v431, v447, v450, v453, v455, v471, v474, v477, v479, v495, v498, v501, v503, v519, v522, v525, v527, v543, v546, v549, v551, v567, v570, v573, v575, v591, v594, v597, v599, v615, v618, v621, v623, v639, v642, v645, v647, v663, v666, v669, v671, v687, v690, v693, v695, v711, v714, v717, v719, v735, v738, v741, v743, v759, v762, v765, v767, v800, v811] = mcpyW D S 1 0 1009 127 := by
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
