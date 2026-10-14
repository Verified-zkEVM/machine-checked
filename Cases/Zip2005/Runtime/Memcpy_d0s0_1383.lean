import Cases.Zip2005.Kit.ByteSext
import Cases.Zip2005.Runtime.MemcpyMis
import Cases.Zip2005.Kit.ByteShiftAll
import Cases.Zip2005.Runtime.And7
import Cases.Zip2005.Image.Ro

/-! `memcpy(dst, src, 1383)` with `dst ≡ 0`, `src ≡ 0` (mod 8). -/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 4000000000 in
set_option maxRecDepth 400000 in
theorem memcpy_d0s0_1383_spec {P : Prop} (s : MachineState) (ra dst src : Word) (D S : List Word)
    (hDl : D.length = 173) (hSl : S.length = 173)
    (hpc : s.pc = 0x7801b4d8#64) (hcode : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = dst) (ha1 : s.getReg .x11 = src) (ha2 : s.getReg .x12 = 1383#64)
    (hD : Region dst D s) (hokD : RegionOk Ro.layout.textLo Ro.layout.textHi dst 173)
    (hS : Region src S s) (hokS : RegionOk Ro.layout.textLo Ro.layout.textHi src 173)
    (hdj : Disjoint dst 173 src 173)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(dst, 173)] s t →
      Region dst (mcpyW D S 0 0 1383 173) t → Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl [(dst, 173)] s
  have hm : dst &&& 7#64 = 0#64 := hokD.and7
  have hm2 : src &&& 7#64 = 0#64 := hokS.and7
  rw [AsmVerif.RiscV.Sym.List.eq_map_range D hDl] at hD
  rw [AsmVerif.RiscV.Sym.List.eq_map_range S hSl] at hS
  sym_exec
  have e : [v8, v9, v10, v11, v20, v21, v22, v23, v32, v33, v34, v35, v44, v45, v46, v47, v56, v57, v58, v59, v68, v69, v70, v71, v80, v81, v82, v83, v92, v93, v94, v95, v104, v105, v106, v107, v116, v117, v118, v119, v128, v129, v130, v131, v140, v141, v142, v143, v152, v153, v154, v155, v164, v165, v166, v167, v176, v177, v178, v179, v188, v189, v190, v191, v200, v201, v202, v203, v212, v213, v214, v215, v224, v225, v226, v227, v236, v237, v238, v239, v248, v249, v250, v251, v260, v261, v262, v263, v272, v273, v274, v275, v284, v285, v286, v287, v296, v297, v298, v299, v308, v309, v310, v311, v320, v321, v322, v323, v332, v333, v334, v335, v344, v345, v346, v347, v356, v357, v358, v359, v368, v369, v370, v371, v380, v381, v382, v383, v392, v393, v394, v395, v404, v405, v406, v407, v416, v417, v418, v419, v428, v429, v430, v431, v440, v441, v442, v443, v452, v453, v454, v455, v464, v465, v466, v467, v476, v477, v478, v479, v488, v489, v490, v491, v500, v501, v502, v503, v512, v513, v514, v515, v547] = mcpyW D S 0 0 1383 173 := by
    sym_subst
    simp only [mcpyW, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · apply word_ext
      intro k hk
      interval_cases k <;> simp (disch := decide) only [byte_simp]
  rw [e] at hR0
  sym_close hk

end Cases.Zip2005
