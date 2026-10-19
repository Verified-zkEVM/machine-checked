import Cases.Zip2005.Curve.EpAddMain
import Cases.Zip2005.Curve.EpAddKit
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Runtime.MemsetSpec
import Cases.Zip2005.Image.Ro

/-!
# `Ep::add`

Jacobian addition on Pallas (`add-2007-bl`) as `Fp.addJ`: an identity operand copies the other
operand (`memcpy`), equal `x`s double (`Ep::double`) or give the identity (`memset`), otherwise
the general case (`Cases.Zip2005.ep_add_main_spec`, entered at `0x780273e0` through a cut). The six
products `z1z1, z2z2, u1, u2, s1, s2` are computed before the branches and read back from the
frame.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem ep_add_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 a2 : Word)
    (x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 : Word) (u0 u1 u2 u3 e0 e1 e2 e3 w0 w1 w2 w3 : Word)
    (O : List Word) (hOl : O.length = 12)
    (hpc : s.pc = 0x78026b44#64) (hcode : CodeAt F_78026b44.base F_78026b44.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeB : CodeAt F_7803a0fc.base F_7803a0fc.prog s)
    (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeD : CodeAt F_7802413c.base F_7802413c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x430 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1) (ha2 : s.getReg .x12 = a2)
    (hp : Region a1 [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] s) (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hq : Region a2 [u0, u1, u2, u3, e0, e1, e2, e3, w0, w1, w2, w3] s) (hok2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 12)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 12)
    (hd0 : Disjoint (sp - 0x430#64) 134 a0 12) (hd1 : Disjoint (sp - 0x430#64) 134 a1 12)
    (hd2 : Disjoint (sp - 0x430#64) 134 a2 12)
    (he1 : Disjoint a0 12 a1 12) (he2 : Disjoint a0 12 a2 12)
    (hX : leLimbsToNat [x0, x1, x2, x3] < Fp.p) (hZ : leLimbsToNat [z0, z1, z2, z3] < Fp.p) (hW : leLimbsToNat [w0, w1, w2, w3] < Fp.p)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x430#64, 134), (a0, 12)] s t →
      Region a0 (natToLeLimbs 4 (Fp.addJ (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [u0, u1, u2, u3]) (leLimbsToNat [e0, e1, e2, e3]) (leLimbsToNat [w0, w1, w2, w3])).1 ++ natToLeLimbs 4 (Fp.addJ (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [u0, u1, u2, u3]) (leLimbsToNat [e0, e1, e2, e3]) (leLimbsToNat [w0, w1, w2, w3])).2.1 ++
        natToLeLimbs 4 (Fp.addJ (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [u0, u1, u2, u3]) (leLimbsToNat [e0, e1, e2, e3]) (leLimbsToNat [w0, w1, w2, w3])).2.2) t → SafeN G n P t) :
    SafeN G n P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x430#64) 134 := hstk.frame 134 (by decide)
  have hokF : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x280#64) 67 := hokW.sub' 54 67 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 13 := hokW.sub' 121 13 (by decide) (by bv_omega)
  obtain ⟨F, hF, hFl⟩ := Region.exists_junk (sp - 0x280#64) 67 s
  obtain ⟨FS, hFS, hFSl⟩ := Region.exists_junk (sp - 0x68#64) 13 s
  have hu := Unchanged.refl [(sp - 0x430#64, 134), (a0, 12)] s
  have hlo := hstk.lo
  -- the general case, from the cut at `0x780273e0`
  have hk' : ∀ (u : MachineState) (k0 k1 k2 k3 l0 l1 l2 l3 m0 m1 m2 m3 n0 n1 n2 n3 p0 p1 p2 p3 q0 q1 q2 q3 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 : Word),
      u.pc = 0x780273e0#64 → u.code = s.code →
      CodeAt F_78026b44.base F_78026b44.prog u → CodeAt F_7801bf5c.base F_7801bf5c.prog u →
      CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      Unchanged [(sp - 0x430#64, 134), (a0, 12)] s u →
      Region a1 [x0, x1, x2, x3, y0, y1, y2, y3, z0, z1, z2, z3] u →
      Region a2 [u0, u1, u2, u3, e0, e1, e2, e3, w0, w1, w2, w3] u →
      Region a0 [O[0]!, O[1]!, O[2]!, O[3]!, O[4]!, O[5]!, O[6]!, O[7]!, O[8]!, O[9]!, O[10]!, O[11]!] u →
      Region (sp - 0x280#64) [g0, g1, g2, g3, g4, g5, g6, 4611686018427387904#64, l1, l2, w0, z0, n1, n2, q0, m3, m2, q1, n3, q2, p1, p2, q3, p3, p0, m0, m1, 8127635680764926565#64, n0, 2445952672640170197#64, l0, l3, 14933811601259063721#64, 12438865661331504215#64, k0, k1, k2, k3, a0, g7, g8, g9, g10, m0, m1, m2, m3, p0, p1, p2, p3, g11, g12, g13, g14, g15, g16, g17, g18, 14933811601259063721#64, 12438865661331504215#64, 8127635680764926565#64, 2445952672640170197#64, 11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64] u →
      Region (sp - 0x68#64) [s.getReg .x27, s.getReg .x26, s.getReg .x25, s.getReg .x24, s.getReg .x23, s.getReg .x22, s.getReg .x21, s.getReg .x20, s.getReg .x19, s.getReg .x18, s.getReg .x9, s.getReg .x8, ra] u →
      u.getReg .x2 = sp + 18446744073709550976#64 →
      u.getReg .x3 = s.getReg .x3 → u.getReg .x4 = s.getReg .x4 →
      u.getReg .x8 = m0 → u.getReg .x9 = a1 → u.getReg .x10 = g19 → u.getReg .x11 = 1#64 →
      u.getReg .x18 = a2 → u.getReg .x19 = 1#64 → u.getReg .x20 = 11037532056220336129#64 →
      u.getReg .x21 = 2469829653914515739#64 → u.getReg .x22 = n1 → u.getReg .x23 = m3 →
      u.getReg .x24 = m2 → u.getReg .x25 = n3 → u.getReg .x26 = m1 → u.getReg .x27 = n2 →
      leLimbsToNat [k0, k1, k2, k3] = Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3]) →
      leLimbsToNat [l0, l1, l2, l3] = Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3]) →
      leLimbsToNat [m0, m1, m2, m3] = Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3])) →
      leLimbsToNat [n0, n1, n2, n3] = Fp.mul (leLimbsToNat [u0, u1, u2, u3]) (Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3])) →
      leLimbsToNat [p0, p1, p2, p3] = Fp.mul (Fp.mul (leLimbsToNat [y0, y1, y2, y3]) (Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3]))) (leLimbsToNat [w0, w1, w2, w3]) →
      leLimbsToNat [q0, q1, q2, q3] = Fp.mul (Fp.mul (leLimbsToNat [e0, e1, e2, e3]) (Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3]))) (leLimbsToNat [z0, z1, z2, z3]) →
      leLimbsToNat [z0, z1, z2, z3] ≠ 0 → leLimbsToNat [w0, w1, w2, w3] ≠ 0 → leLimbsToNat [n0, n1, n2, n3] ≠ leLimbsToNat [m0, m1, m2, m3] →
      SafeN G n P u := by
    intro u k0 k1 k2 k3 l0 l1 l2 l3 m0 m1 m2 m3 n0 n1 n2 n3 p0 p1 p2 p3 q0 q1 q2 q3 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 upc ucode ucA ucM ucw uU uP uQ uO uF uS rx2 rx3 rx4 rx8 rx9 rx10 rx11 rx18 rx19 rx20
      rx21 rx22 rx23 rx24 rx25 rx26 rx27 fK fL fM fN fP fQ fz1 fz2 fne
    have hne : Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3])) ≠ Fp.mul (leLimbsToNat [u0, u1, u2, u3]) (Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3])) := by
      rw [← fM, ← fN]; exact fun h => fne h.symm
    have uro : RoImage Ro.layout u := RoImage.of_unchanged hro uU (roW_cons
      (by
        show (sp - 0x430#64).toNat + 8 * 134 ≤ Ro.layout.roBase ∨ Ro.layout.roBase + Ro.layout.roBytes ≤ (sp - 0x430#64).toNat
        have h1 := hstk.lo; have h2 := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
        simp only [Ro.layout_roBase, Ro.layout_roBytes]; left; bv_omega)
      (roW_cons (Or.imp_right (fun h => Nat.le_trans (by decide) h) hok0.offCode) (roW_nil Ro.layout)))
    have e := Fp.addJ_general (Y1 := leLimbsToNat [y0, y1, y2, y3]) (Y2 := leLimbsToNat [e0, e1, e2, e3]) fz1 fz2 hne
    rw [← fM, ← fN, ← fP, ← fQ, ← fK, ← fL] at e
    exact ep_add_main_spec u ra sp a0 a1 a2 x0 x1 x2 x3 y0 y1 y2 y3 z0 z1 z2 z3 u0 u1 u2 u3 e0 e1 e2 e3
      w0 w1 w2 w3 k0 k1 k2 k3 l0 l1 l2 l3 m0 m1 m2 m3 n0 n1 n2 n3 p0 p1 p2 p3 q0 q1 q2 q3 g0 g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 g14 g15 g16 g17 g18 g19 (O[0]!) (O[1]!) (O[2]!) (O[3]!) (O[4]!) (O[5]!) (O[6]!) (O[7]!) (O[8]!) (O[9]!) (O[10]!) (O[11]!) (s.getReg .x8) (s.getReg .x9) (s.getReg .x18) (s.getReg .x19) (s.getReg .x20) (s.getReg .x21) (s.getReg .x22) (s.getReg .x23) (s.getReg .x24) (s.getReg .x25) (s.getReg .x26) (s.getReg .x27)
      upc ucA ucM ucw uro hra1 hstk (rx2.trans (by bv_omega : sp + 18446744073709550976#64 = sp - 0x280#64)) rx8 rx9 rx10 rx11 rx18 rx19 rx20 rx21 rx22 rx23
      rx24 rx25 rx26 rx27 uP hok1 uQ hok2 uO hok0 uF uS hd0 hd1 hd2 he1 he2 hZ hW
      (by rw [fK]; exact Fp.mul_lt _ _) (by rw [fL]; exact Fp.mul_lt _ _) (by rw [fM]; exact Fp.mul_lt _ _)
      (by rw [fN]; exact Fp.mul_lt _ _) (by rw [fP]; exact Fp.mul_lt _ _) (by rw [fQ]; exact Fp.mul_lt _ _)
      (fun v vpc vcode vx2 vx3 vx4 vx8 vx9 vx18 vx19 vx20 vx21 vx22 vx23 vx24 vx25 vx26 vx27 vU vR =>
        hk v vpc
          (CalleeSaved.intro (vx2.trans hsp.symm) (vx3.trans rx3) (vx4.trans rx4) vx8 vx9 vx18 vx19 vx20
            vx21 vx22 vx23 vx24 vx25 vx26 vx27)
          (vcode.trans ucode) (uU.trans vU) (by rw [e]; exact vR))
  sym_exec [uint256_mulmod_spec, black_box_spec, memcpy96_spec, memset96_spec, ep_double_spec] stop [0x780273e0]
  · -- `u1 ≠ u2`: the general case
    have hKp : leLimbsToNat [v153, v155, v157, v159] = Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3]) := by
      rw [← v153_def, ← v155_def, ← v157_def, ← v159_def, cells_lt (acc_ltp acc152_0_def), mulpair acc131_0_def acc152_0_def]
    have hLp : leLimbsToNat [v199, v201, v202, v203] = Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3]) := by
      rw [← v199_def, ← v201_def, ← v202_def, ← v203_def, cells_lt (acc_ltp acc198_0_def), mulpair acc185_0_def acc198_0_def]
    have hMp : leLimbsToNat [v239, v241, v243, v245] = Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3])) := by
      rw [← v239_def, ← v241_def, ← v243_def, ← v245_def, cells_lt (acc_ltp acc238_0_def), mulpair acc225_0_def acc238_0_def, hLp]
    have hNp : leLimbsToNat [v289, v291, v293, v295] = Fp.mul (leLimbsToNat [u0, u1, u2, u3]) (Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3])) := by
      rw [← v289_def, ← v291_def, ← v293_def, ← v295_def, cells_lt (acc_ltp acc288_0_def), mulpair acc275_0_def acc288_0_def, hKp]
    have hYL : leLimbsToNat [v335, v336, v337, v338] = Fp.mul (leLimbsToNat [y0, y1, y2, y3]) (Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3])) := by
      rw [← v335_def, ← v336_def, ← v337_def, ← v338_def, cells_lt (acc_ltp acc334_0_def), mulpair acc321_0_def acc334_0_def, hLp]
    have hPp : leLimbsToNat [v374, v375, v376, v377] = Fp.mul (Fp.mul (leLimbsToNat [y0, y1, y2, y3]) (Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3]))) (leLimbsToNat [w0, w1, w2, w3]) := by
      rw [← v374_def, ← v375_def, ← v376_def, ← v377_def, cells_lt (acc_ltp acc373_0_def), mulpair acc359_0_def acc373_0_def, hYL]
    have hVK : leLimbsToNat [v424, v425, v426, v427] = Fp.mul (leLimbsToNat [e0, e1, e2, e3]) (Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3])) := by
      rw [← v424_def, ← v425_def, ← v426_def, ← v427_def, cells_lt (acc_ltp acc423_0_def), mulpair acc410_0_def acc423_0_def, hKp]
    have hQp : leLimbsToNat [v469, v471, v473, v475] = Fp.mul (Fp.mul (leLimbsToNat [e0, e1, e2, e3]) (Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3]))) (leLimbsToNat [z0, z1, z2, z3]) := by
      rw [← v469_def, ← v471_def, ← v473_def, ← v475_def, cells_lt (acc_ltp acc468_0_def), mulpair acc448_0_def acc468_0_def, hVK]
    have hz1 : leLimbsToNat [z0, z1, z2, z3] ≠ 0 := flag_ne_of_beq_zero (zero4_flag v18_def v23_def v24_def v28_def v29_def v34_def v35_def v39_def v40_def v45_def v46_def v50_def v51_def v55_def) hbr56
    have hz2 : leLimbsToNat [w0, w1, w2, w3] ≠ 0 := flag_ne_of_beq_zero (zero4_flag v58_def v63_def v64_def v68_def v69_def v74_def v75_def v79_def v80_def v85_def v86_def v90_def v91_def v95_def) hbr96
    have hun : leLimbsToNat [v289, v291, v293, v295] ≠ leLimbsToNat [v239, v241, v243, v245] :=
      flag_ne_of_bne_one (eq4_flag v480_def v481_def v485_def v490_def v491_def v495_def v496_def v500_def v503_def v504_def v508_def v509_def v513_def v516_def v517_def v521_def v522_def v526_def) hbr529
    sym_close hk' _ v153 v155 v157 v159 v199 v201 v202 v203 v239 v241 v243 v245 v289 v291 v293 v295 v374 v375 v376 v377 v469 v471 v473 v475 (F[0]!) (F[1]!) (F[2]!) (F[3]!) (F[4]!) (F[5]!) (F[6]!) (F[39]!) (F[40]!) (F[41]!) (F[42]!) (BitVec.ofNat 64 (acc423_0 >>> (64 * 0))) (BitVec.ofNat 64 (acc423_0 >>> (64 * 1))) (BitVec.ofNat 64 (acc423_0 >>> (64 * 2))) (BitVec.ofNat 64 (acc423_0 >>> (64 * 3))) (BitVec.ofNat 64 (acc468_0 >>> (64 * 0))) (BitVec.ofNat 64 (acc468_0 >>> (64 * 1))) (BitVec.ofNat 64 (acc468_0 >>> (64 * 2))) (BitVec.ofNat 64 (acc468_0 >>> (64 * 3))) v526
  · -- `u1 = u2`, `s1 ≠ s2`: the identity
    have hKp : leLimbsToNat [v153, v155, v157, v159] = Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3]) := by
      rw [← v153_def, ← v155_def, ← v157_def, ← v159_def, cells_lt (acc_ltp acc152_0_def), mulpair acc131_0_def acc152_0_def]
    have hLp : leLimbsToNat [v199, v201, v202, v203] = Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3]) := by
      rw [← v199_def, ← v201_def, ← v202_def, ← v203_def, cells_lt (acc_ltp acc198_0_def), mulpair acc185_0_def acc198_0_def]
    have hMp : leLimbsToNat [v239, v241, v243, v245] = Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3])) := by
      rw [← v239_def, ← v241_def, ← v243_def, ← v245_def, cells_lt (acc_ltp acc238_0_def), mulpair acc225_0_def acc238_0_def, hLp]
    have hNp : leLimbsToNat [v289, v291, v293, v295] = Fp.mul (leLimbsToNat [u0, u1, u2, u3]) (Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3])) := by
      rw [← v289_def, ← v291_def, ← v293_def, ← v295_def, cells_lt (acc_ltp acc288_0_def), mulpair acc275_0_def acc288_0_def, hKp]
    have hYL : leLimbsToNat [v335, v336, v337, v338] = Fp.mul (leLimbsToNat [y0, y1, y2, y3]) (Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3])) := by
      rw [← v335_def, ← v336_def, ← v337_def, ← v338_def, cells_lt (acc_ltp acc334_0_def), mulpair acc321_0_def acc334_0_def, hLp]
    have hPp : leLimbsToNat [v374, v375, v376, v377] = Fp.mul (Fp.mul (leLimbsToNat [y0, y1, y2, y3]) (Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3]))) (leLimbsToNat [w0, w1, w2, w3]) := by
      rw [← v374_def, ← v375_def, ← v376_def, ← v377_def, cells_lt (acc_ltp acc373_0_def), mulpair acc359_0_def acc373_0_def, hYL]
    have hVK : leLimbsToNat [v424, v425, v426, v427] = Fp.mul (leLimbsToNat [e0, e1, e2, e3]) (Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3])) := by
      rw [← v424_def, ← v425_def, ← v426_def, ← v427_def, cells_lt (acc_ltp acc423_0_def), mulpair acc410_0_def acc423_0_def, hKp]
    have hQp : leLimbsToNat [v469, v471, v473, v475] = Fp.mul (Fp.mul (leLimbsToNat [e0, e1, e2, e3]) (Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3]))) (leLimbsToNat [z0, z1, z2, z3]) := by
      rw [← v469_def, ← v471_def, ← v473_def, ← v475_def, cells_lt (acc_ltp acc468_0_def), mulpair acc448_0_def acc468_0_def, hVK]
    have hz1 : leLimbsToNat [z0, z1, z2, z3] ≠ 0 := flag_ne_of_beq_zero (zero4_flag v18_def v23_def v24_def v28_def v29_def v34_def v35_def v39_def v40_def v45_def v46_def v50_def v51_def v55_def) hbr56
    have hz2 : leLimbsToNat [w0, w1, w2, w3] ≠ 0 := flag_ne_of_beq_zero (zero4_flag v58_def v63_def v64_def v68_def v69_def v74_def v75_def v79_def v80_def v85_def v86_def v90_def v91_def v95_def) hbr96
    have hue : leLimbsToNat [v289, v291, v293, v295] = leLimbsToNat [v239, v241, v243, v245] :=
      flag_of_not_bne_one (eq4_flag v480_def v481_def v485_def v490_def v491_def v495_def v496_def v500_def v503_def v504_def v508_def v509_def v513_def v516_def v517_def v521_def v522_def v526_def) hbr529
    have hsn : leLimbsToNat [v469, v471, v473, v475] ≠ leLimbsToNat [v374, v375, v376, v377] :=
      flag_ne_of_bne_one (eq4_flag v532_def v533_def v537_def v540_def v541_def v545_def v546_def v550_def v553_def v554_def v558_def v559_def v563_def v566_def v567_def v571_def v572_def v576_def) hbr577
    sym_close hk
    rw [Fp.addJ_identity hz1 hz2 (hMp.symm.trans (hue.symm.trans hNp)) (fun h => hsn (hQp.trans (h.symm.trans hPp.symm))), zero_triple, replicate_cells acc583_0 acc583_0_def]
  · -- `u1 = u2`, `s1 = s2`: `Ep::double`
    have hKp : leLimbsToNat [v153, v155, v157, v159] = Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3]) := by
      rw [← v153_def, ← v155_def, ← v157_def, ← v159_def, cells_lt (acc_ltp acc152_0_def), mulpair acc131_0_def acc152_0_def]
    have hLp : leLimbsToNat [v199, v201, v202, v203] = Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3]) := by
      rw [← v199_def, ← v201_def, ← v202_def, ← v203_def, cells_lt (acc_ltp acc198_0_def), mulpair acc185_0_def acc198_0_def]
    have hMp : leLimbsToNat [v239, v241, v243, v245] = Fp.mul (leLimbsToNat [x0, x1, x2, x3]) (Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3])) := by
      rw [← v239_def, ← v241_def, ← v243_def, ← v245_def, cells_lt (acc_ltp acc238_0_def), mulpair acc225_0_def acc238_0_def, hLp]
    have hNp : leLimbsToNat [v289, v291, v293, v295] = Fp.mul (leLimbsToNat [u0, u1, u2, u3]) (Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3])) := by
      rw [← v289_def, ← v291_def, ← v293_def, ← v295_def, cells_lt (acc_ltp acc288_0_def), mulpair acc275_0_def acc288_0_def, hKp]
    have hYL : leLimbsToNat [v335, v336, v337, v338] = Fp.mul (leLimbsToNat [y0, y1, y2, y3]) (Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3])) := by
      rw [← v335_def, ← v336_def, ← v337_def, ← v338_def, cells_lt (acc_ltp acc334_0_def), mulpair acc321_0_def acc334_0_def, hLp]
    have hPp : leLimbsToNat [v374, v375, v376, v377] = Fp.mul (Fp.mul (leLimbsToNat [y0, y1, y2, y3]) (Fp.mul (leLimbsToNat [w0, w1, w2, w3]) (leLimbsToNat [w0, w1, w2, w3]))) (leLimbsToNat [w0, w1, w2, w3]) := by
      rw [← v374_def, ← v375_def, ← v376_def, ← v377_def, cells_lt (acc_ltp acc373_0_def), mulpair acc359_0_def acc373_0_def, hYL]
    have hVK : leLimbsToNat [v424, v425, v426, v427] = Fp.mul (leLimbsToNat [e0, e1, e2, e3]) (Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3])) := by
      rw [← v424_def, ← v425_def, ← v426_def, ← v427_def, cells_lt (acc_ltp acc423_0_def), mulpair acc410_0_def acc423_0_def, hKp]
    have hQp : leLimbsToNat [v469, v471, v473, v475] = Fp.mul (Fp.mul (leLimbsToNat [e0, e1, e2, e3]) (Fp.mul (leLimbsToNat [z0, z1, z2, z3]) (leLimbsToNat [z0, z1, z2, z3]))) (leLimbsToNat [z0, z1, z2, z3]) := by
      rw [← v469_def, ← v471_def, ← v473_def, ← v475_def, cells_lt (acc_ltp acc468_0_def), mulpair acc448_0_def acc468_0_def, hVK]
    have hz1 : leLimbsToNat [z0, z1, z2, z3] ≠ 0 := flag_ne_of_beq_zero (zero4_flag v18_def v23_def v24_def v28_def v29_def v34_def v35_def v39_def v40_def v45_def v46_def v50_def v51_def v55_def) hbr56
    have hz2 : leLimbsToNat [w0, w1, w2, w3] ≠ 0 := flag_ne_of_beq_zero (zero4_flag v58_def v63_def v64_def v68_def v69_def v74_def v75_def v79_def v80_def v85_def v86_def v90_def v91_def v95_def) hbr96
    have hue : leLimbsToNat [v289, v291, v293, v295] = leLimbsToNat [v239, v241, v243, v245] :=
      flag_of_not_bne_one (eq4_flag v480_def v481_def v485_def v490_def v491_def v495_def v496_def v500_def v503_def v504_def v508_def v509_def v513_def v516_def v517_def v521_def v522_def v526_def) hbr529
    have hse : leLimbsToNat [v469, v471, v473, v475] = leLimbsToNat [v374, v375, v376, v377] :=
      flag_of_not_bne_one (eq4_flag v532_def v533_def v537_def v540_def v541_def v545_def v546_def v550_def v553_def v554_def v558_def v559_def v563_def v566_def v567_def v571_def v572_def v576_def) hbr577
    sym_close hk
    rw [Fp.addJ_double hz1 hz2 (hMp.symm.trans (hue.symm.trans hNp)) (hPp.symm.trans (hse.symm.trans hQp))]
    generalize Fp.dblJ (leLimbsToNat [x0, x1, x2, x3]) (leLimbsToNat [y0, y1, y2, y3]) (leLimbsToNat [z0, z1, z2, z3]) = D
    rfl
  · -- `rhs` is the identity: copy `self`
    have hz1 : leLimbsToNat [z0, z1, z2, z3] ≠ 0 := flag_ne_of_beq_zero (zero4_flag v18_def v23_def v24_def v28_def v29_def v34_def v35_def v39_def v40_def v45_def v46_def v50_def v51_def v55_def) hbr56
    have hz2 : leLimbsToNat [w0, w1, w2, w3] = 0 := flag_of_not_beq_zero (zero4_flag v58_def v63_def v64_def v68_def v69_def v74_def v75_def v79_def v80_def v85_def v86_def v90_def v91_def v95_def) hbr96
    sym_close hk
    rw [Fp.addJ_z2_zero hz1 hz2, triple_limbs]
  · -- `self` is the identity: copy `rhs`
    have hz1 : leLimbsToNat [z0, z1, z2, z3] = 0 := flag_of_not_beq_zero (zero4_flag v18_def v23_def v24_def v28_def v29_def v34_def v35_def v39_def v40_def v45_def v46_def v50_def v51_def v55_def) hbr56
    sym_close hk
    rw [Fp.addJ_z1_zero hz1, triple_limbs]

end Cases.Zip2005
