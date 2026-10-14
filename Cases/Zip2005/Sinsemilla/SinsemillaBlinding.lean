import Cases.Zip2005.Curve.EpMulFq
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Runtime.Memcmp
import Cases.Zip2005.Image.F_78023594
import Cases.Zip2005.Image.Ro

/-!
# `CommitDomain::blinding` (sinsemilla)

`self.R * r`: the domain's second point (at offset `0x60`) copied into the frame and
multiplied by the scalar; the result is `ep_mul_fq_spec`'s (`mulW`, `mulFacts`).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

theorem fold12 {xs : List Word} (h : xs.length = 12) :
    [xs[0]!, xs[1]!, xs[2]!, xs[3]!, xs[4]!, xs[5]!, xs[6]!, xs[7]!, xs[8]!, xs[9]!, xs[10]!, xs[11]!] = xs := by
  match xs, h with
  | [_, _, _, _, _, _, _, _, _, _, _, _], _ => rfl

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem sinsemilla_blinding_spec {P : Prop} (s : MachineState) (ra sp a0 a1 a2 : Word)
    (pt k O : List Word) (hptl : pt.length = 12) (hkl : k.length = 4) (hOl : O.length = 12)
    (hpanic : ∀ u : MachineState, u.pc = 0x7803de40#64 → u.code = s.code → Safe P u)
    (hpc : s.pc = 0x78023594#64) (hcode : CodeAt F_78023594.base F_78023594.prog s)
    (hcodeW : CodeAt F_7802827c.base F_7802827c.prog s)
    (hcodeMul : CodeAt F_78031be8.base F_78031be8.prog s)
    (hcodeBB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeMS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeC : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeRp : CodeAt F_78029468.base F_78029468.prog s)
    (hcodeRq : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    (hcodeA : CodeAt F_78035fe0.base F_78035fe0.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hcodeCpy : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcodeD : CodeAt F_780360c8.base F_780360c8.prog s)
    (hcodeL : CodeAt F_780360e0.base F_780360e0.prog s)
    (hcodeAF : CodeAt F_7803a110.base F_7803a110.prog s)
    (hcodeAFI : CodeAt F_7803dd28.base F_7803dd28.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x520 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1) (ha2 : s.getReg .x12 = a2)
    (hp : Region (a1 + 0x60#64) pt s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi (a1 + 0x60#64) 12)
    (hkk : Region a2 k s) (hok2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 4)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 12)
    (hd0 : Disjoint (sp - 0x520#64) 164 a0 12) (hd1 : Disjoint (sp - 0x520#64) 164 (a1 + 0x60#64) 12)
    (hd2 : Disjoint (sp - 0x520#64) 164 a2 4)
    (hd01 : Disjoint a0 12 (a1 + 0x60#64) 12) (hd02 : Disjoint a0 12 a2 4)
    (hk' : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x520#64, 164), (a0, 12)] s t → (mulW pt k).length = 12 →
      Region a0 (mulW pt k) t → mulFacts pt k → Safe P t) :
    Safe P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x520#64) 164 := hstk.frame 164 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x80#64) 16 := hokW.sub' 148 16 (by decide) (by bv_omega)
  -- the frame: [8, 0x68) the copied point, saved registers
  have hokP : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x78#64) 12 := hokF.sub' 1 12 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x18#64) 3 := hokF.sub' 13 3 (by decide) (by bv_omega)
  obtain ⟨FP, hFP, hFPl⟩ := Region.exists_junk (sp - 0x78#64) 12 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x18#64) 3 s
  have hu := Unchanged.refl [(sp - 0x520#64, 164), (a0, 12)] s
  have hlo := hstk.lo
  sym_exec [memcpy96_spec, ep_mul_fq_spec, hpanic]
  have e1 : [pt[0]!, pt[1]!, pt[2]!, pt[3]!, pt[4]!, pt[5]!, pt[6]!, pt[7]!, pt[8]!, pt[9]!, pt[10]!, pt[11]!] = pt :=
    fold12 hptl
  have e2 : [k[0]!, k[1]!, k[2]!, k[3]!] = k := fold4 hkl
  sym_close hk'
  all_goals first
    | exact length_mulW pt k
    | (rw [← e1, ← e2]; assumption)
    | (rw [← e1, ← e2, acc17_0_def]
       exact @fold12 acc17_0 (by rw [← acc17_0_def, e1, e2]; exact length_mulW pt k))

end Cases.Zip2005
