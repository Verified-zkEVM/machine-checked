/-
  Cases.Zip2005.PowT

  `Fp::pow_by_t_minus1_over2` (`SqrtTableHelpers`): a fixed addition chain of
  squarings and products (`Fp.mul`, each two `UINT256_MULMOD` calls). Two of
  the repeated squarings are loops (`sqr(x, 129)`, `sqr(rg, 10)`).
-/

import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Field.BnKit
import Cases.Zip2005.Field.Fp
import Cases.Zip2005.Field.Limbs
import Cases.Zip2005.Image.F_78029d94
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

/-- One step of the chain after `ra = sqr(x, 129) · x`: `4` squares, `i < 4` multiplies by
    entry `i` of the table `[r11, r111, r1001, r1101]`. -/
def Fp.powStep (T : List Nat) (a o : Nat) : Nat := if o < 4 then Fp.mul a T[o]! else Fp.mul a a

def Fp.powRun (T : List Nat) (os : List Nat) (a : Nat) : Nat := os.foldl (Fp.powStep T) a

theorem Fp.powRun_nil (T : List Nat) (a : Nat) : Fp.powRun T [] a = a := rfl

theorem Fp.powRun_cons (T : List Nat) (o : Nat) (os : List Nat) (a : Nat) :
    Fp.powRun T (o :: os) a = Fp.powRun T os (Fp.powStep T a o) := rfl

theorem Fp.powRun_append (T l₁ l₂ : List Nat) (a : Nat) :
    Fp.powRun T (l₁ ++ l₂) a = Fp.powRun T l₂ (Fp.powRun T l₁ a) := List.foldl_append ..

theorem Fp.powStep_sq (T : List Nat) (a : Nat) : Fp.powStep T a 4 = Fp.mul a a := by
  unfold Fp.powStep; rw [if_neg (by decide)]

theorem Fp.powStep_tbl (T0 T1 T2 T3 a : Nat) :
    Fp.powStep [T0, T1, T2, T3] a 0 = Fp.mul a T0 ∧ Fp.powStep [T0, T1, T2, T3] a 1 = Fp.mul a T1 ∧
      Fp.powStep [T0, T1, T2, T3] a 2 = Fp.mul a T2 ∧ Fp.powStep [T0, T1, T2, T3] a 3 = Fp.mul a T3 := by
  unfold Fp.powStep
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [if_pos (by decide)] <;> rfl

theorem Fp.powRun_sqr (T : List Nat) (n : Nat) (os : List Nat) (a : Nat) :
    Fp.powRun T (List.replicate n 4 ++ os) a = Fp.powRun T os (Fp.sqrN a n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, Fp.powRun_cons, Fp.powStep_sq, ih, Fp.sqrN_succ]

def Fp.powR10 (x : Nat) : Nat := Fp.mul x x
def Fp.powR11 (x : Nat) : Nat := Fp.mul (Fp.powR10 x) x
def Fp.powR110 (x : Nat) : Nat := Fp.mul (Fp.powR11 x) (Fp.powR11 x)
def Fp.powR111 (x : Nat) : Nat := Fp.mul (Fp.powR110 x) x
def Fp.powR1001 (x : Nat) : Nat := Fp.mul (Fp.powR111 x) (Fp.powR10 x)
def Fp.powR1101 (x : Nat) : Nat := Fp.mul (Fp.powR111 x) (Fp.powR110 x)

/-- The table the chain multiplies by, in the guest's stack order. -/
def Fp.powTbl (x : Nat) : List Nat := [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x]

def Fp.powOps0 : List Nat := [4]

def Fp.powOps1 : List Nat := [4, 4, 4, 4, 4]

def Fp.powOps2 : List Nat := [4, 2, 4, 4, 4, 4]

def Fp.powOps3 : List Nat := [4, 4, 4, 3, 4, 4]

def Fp.powOps4 : List Nat := [4, 4, 0, 4, 4, 4]

def Fp.powOps5 : List Nat := [4, 4, 4, 1, 4, 4]

def Fp.powOps6 : List Nat := [4, 1, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 2, 4, 4]

def Fp.powOps7 : List Nat := [4, 4, 4, 2, 4, 4]

def Fp.powOps8 : List Nat := [4, 4, 2, 4, 4]

def Fp.powOps9 : List Nat := [4, 1, 4, 4, 4]

def Fp.powOps10 : List Nat := [4, 2, 4, 4, 4, 4]

def Fp.powOps11 : List Nat := [4, 0, 4, 4, 4]

def Fp.powOps12 : List Nat := [4, 1, 4, 4, 4]

def Fp.powOps13 : List Nat := [4, 0, 4, 4, 4, 4]

def Fp.powOps14 : List Nat := [4, 4, 2, 4, 4, 4]

def Fp.powOps15 : List Nat := [4, 4, 3, 4, 4, 4]

def Fp.powOps16 : List Nat := [4, 0, 4, 4, 4, 4]

def Fp.powOps17 : List Nat := [4, 4, 4, 1, 4, 4]

def Fp.powOps18 : List Nat := [4, 0, 4]

/-- `pow_by_t_minus1_over2` on Montgomery representatives (`Fp.mul`): the exponent is
    `(t - 1) / 2`, `p - 1 = 2^32 t`. The op lists are cut where the proof is. -/
def Fp.powT (x : Nat) : Nat :=
  Fp.powRun (Fp.powTbl x)
    (Fp.powOps0 ++ Fp.powOps1 ++ Fp.powOps2 ++ Fp.powOps3 ++ Fp.powOps4 ++ Fp.powOps5 ++ Fp.powOps6 ++ Fp.powOps7 ++ Fp.powOps8 ++ Fp.powOps9 ++ Fp.powOps10 ++ Fp.powOps11 ++ Fp.powOps12 ++ Fp.powOps13 ++ Fp.powOps14 ++ Fp.powOps15 ++ Fp.powOps16 ++ Fp.powOps17 ++ Fp.powOps18)
    (Fp.mul (Fp.sqrN x 129) x)

/-- `powT` as the segments compute it: one `powRun` per op slice. -/
theorem Fp.powT_eq (x : Nat) :
    Fp.powT x = Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps18
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps17
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps16
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps15
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps14
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps13
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps12
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps11
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps10
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps9
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps8
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps7
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps6
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps5
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps4
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps3
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps2
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps1
      (Fp.powRun [Fp.powR11 x, Fp.powR111 x, Fp.powR1001 x, Fp.powR1101 x] Fp.powOps0
      (Fp.mul (Fp.sqrN x 129) x))))))))))))))))))) := by
  simp only [Fp.powT, Fp.powTbl, Fp.powRun_append]

/-- Two `UINT256_MULMOD` calls, `x·y mod p` then `· R⁻¹ mod p`: one `Fp.mul`. -/
theorem mulpair {U V : List Word} {a b : Nat}
    (h1 : leLimbsToNat U * leLimbsToNat V %
      leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64] = a)
    (h2 : leLimbsToNat [BitVec.ofNat 64 (a >>> (64 * 0)), BitVec.ofNat 64 (a >>> (64 * 1)),
          BitVec.ofNat 64 (a >>> (64 * 2)), BitVec.ofNat 64 (a >>> (64 * 3))] *
        leLimbsToNat [14933811601259063721#64, 12438865661331504215#64, 8127635680764926565#64,
          2445952672640170197#64] %
      leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64, 4611686018427387904#64] = b) :
    b = Fp.mul (leLimbsToNat U) (leLimbsToNat V) := by
  subst h1 h2
  simp only [cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod]
  rfl

theorem acc_ltp {E c : Nat}
    (h : E % leLimbsToNat [11037532056220336129#64, 2469829653914515739#64, 0#64,
      4611686018427387904#64] = c) : c < Fp.p := by
  rw [← h, Fp.limbs_p]; exact Nat.mod_lt _ Fp.p_pos

/-- The limbs of a value below `2^256` read back. -/
theorem cells_lt {c : Nat} (h : c < Fp.p) :
    leLimbsToNat [BitVec.ofNat 64 (c >>> 0), BitVec.ofNat 64 (c >>> 64), BitVec.ofNat 64 (c >>> 128),
      BitVec.ofNat 64 (c >>> 192)] = c := by
  rw [cells4]; exact leLimbsToNat_natToLeLimbs 4 c (lt_trans h Fp.p_lt)

/-- The state at a cut (`late`: after the second loop, where `s7` holds `p₀` and `s9` is dead):
    the pending pair squares `A` (both operand blocks hold its limbs),
    the table `T0 … T3` sits in the frame, the callee-saved registers in the save area. -/
def PowCut (late : Bool) (s0 : MachineState) (sp a0 c : Word) (T0 T1 T2 T3 A : Nat) (t : MachineState) :
    Prop :=
  ∃ w0 w1 t00 t01 t02 t03 t10 t11 t12 t13 t20 t21 t22 t23 t30 t31 t32 t33 d0 d1 d2 d3 b0 b1 b2 b3 : Word,
    t.pc = c ∧ t.code = s0.code ∧ CodeAt F_78029d94.base F_78029d94.prog t ∧
    CodeAt F_7801bf5c.base F_7801bf5c.prog t ∧ CodeWithin Ro.layout.textLo Ro.layout.textHi t ∧
    RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 1104#64) 138 ∧ Unchanged [(sp - 1104#64, 138)] s0 t ∧
    t.getReg .x2 = sp - 1104#64 ∧ t.getReg .x3 = s0.getReg .x3 ∧ t.getReg .x4 = s0.getReg .x4 ∧
    t.getReg .x8 = a0 ∧ t.getReg .x9 = 4611686018427387904#64 ∧ t.getReg .x10 = sp - 224#64 ∧
    t.getReg .x11 = sp - 160#64 ∧
    t.getReg .x18 = 2469829653914515739#64 ∧ t.getReg .x19 = 2445952672640170197#64 ∧
    t.getReg .x20 = 8127635680764926565#64 ∧ t.getReg .x21 = 12438865661331504215#64 ∧
    t.getReg .x22 = 14933811601259063721#64 ∧
    t.getReg .x23 = (if late then 11037532056220336129#64 else sp - 128#64) ∧
    t.getReg .x24 = 11037532056220336129#64 ∧ (late = false → t.getReg .x25 = 4611686018427387904#64) ∧
    t.getReg .x27 = s0.getReg .x27 ∧
    Region (sp - 1104#64) [w0, w1, t00, t01, t02, t03, t10, t11, t12, t13, t20, t21, t22, t23, t30, t31, t32, t33] t ∧
    (∃ W : List Word, W.length = 4 ∧ Region (sp - 960#64) W t) ∧
    (∃ W : List Word, W.length = 20 ∧ Region (sp - 928#64) W t) ∧
    (∃ W : List Word, W.length = 4 ∧ Region (sp - 768#64) W t) ∧
    (∃ W : List Word, W.length = 56 ∧ Region (sp - 736#64) W t) ∧
    (∃ W : List Word, W.length = 8 ∧ Region (sp - 288#64) W t) ∧
    Region (sp - 224#64) [d0, d1, d2, d3] t ∧
    (∃ W : List Word, W.length = 4 ∧ Region (sp - 192#64) W t) ∧
    Region (sp - 160#64) [b0, b1, b2, b3, 11037532056220336129#64, 2469829653914515739#64, 0#64,
      4611686018427387904#64] t ∧
    Region (sp - 96#64) [s0.getReg .x26, s0.getReg .x25, s0.getReg .x24, s0.getReg .x23,
      s0.getReg .x22, s0.getReg .x21, s0.getReg .x20, s0.getReg .x19, s0.getReg .x18,
      s0.getReg .x9, s0.getReg .x8, s0.getReg .x1] t ∧
    leLimbsToNat [t00, t01, t02, t03] = T0 ∧ leLimbsToNat [t10, t11, t12, t13] = T1 ∧
    leLimbsToNat [t20, t21, t22, t23] = T2 ∧ leLimbsToNat [t30, t31, t32, t33] = T3 ∧
    leLimbsToNat [d0, d1, d2, d3] = A ∧ leLimbsToNat [b0, b1, b2, b3] = A

/-- `addiw c, c, -1` on a small positive counter. -/
theorem addiw_pred (n : Nat) (h1 : 1 ≤ n) (h2 : n < 2 ^ 31) :
    BitVec.signExtend 64 (BitVec.truncate 32 (BitVec.ofNat 64 n) +
      BitVec.truncate 32 18446744073709551615#64) = BitVec.ofNat 64 (n - 1) := by
  have e1 : BitVec.truncate 32 18446744073709551615#64 = 4294967295#32 := by decide
  have e2 : BitVec.truncate 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
    rw [BitVec.truncate_eq_setWidth, BitVec.setWidth_ofNat_of_le (by decide)]
  have e3 : BitVec.ofNat 32 n + 4294967295#32 = BitVec.ofNat 32 (n - 1) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [e1, e2, e3]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.signExtend_eq_setWidth_of_msb_false, BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  · omega
  · rw [BitVec.msb_eq_decide, BitVec.toNat_ofNat]; simp only [decide_eq_false_iff_not]; omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
/-- The `sqr(x, 129)` loop: `X := X²` while the counter `s10` runs down. -/
theorem sqr_loop1 {G : MachineState → Prop} {n : Nat} {P : Prop} (sp : Word) :
    ∀ m (t : MachineState) (W : List Word), W.length = 4 →
      t.pc = 0x7802a1d8#64 → CodeAt F_78029d94.base F_78029d94.prog t →
      CodeAt F_7801bf5c.base F_7801bf5c.prog t → CodeWithin Ro.layout.textLo Ro.layout.textHi t →
      t.getReg .x2 = sp →
      t.getReg .x18 = 2469829653914515739#64 → t.getReg .x19 = 2445952672640170197#64 →
      t.getReg .x20 = 8127635680764926565#64 → t.getReg .x21 = 12438865661331504215#64 →
      t.getReg .x22 = 14933811601259063721#64 → t.getReg .x23 = sp + 0x3d0#64 →
      t.getReg .x24 = 11037532056220336129#64 → t.getReg .x25 = 4611686018427387904#64 →
      t.getReg .x26 = BitVec.ofNat 64 (m + 1) → m + 1 < 2 ^ 31 →
      Region (sp + 0x90#64) W t → RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x90#64) 4 →
      (∃ W : List Word, W.length = 4 ∧ Region (sp + 0x370#64) W t) →
      RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x370#64) 4 →
      (∃ W : List Word, W.length = 4 ∧ Region (sp + 0x390#64) W t) →
      RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x390#64) 4 →
      (∃ W : List Word, W.length = 8 ∧ Region (sp + 0x3b0#64) W t) →
      RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x3b0#64) 8 →
      (∀ u, u.pc = 0x7802a280#64 → u.code = t.code →
        u.getReg .x2 = sp → u.getReg .x3 = t.getReg .x3 → u.getReg .x4 = t.getReg .x4 →
        u.getReg .x8 = t.getReg .x8 → u.getReg .x9 = t.getReg .x9 →
        u.getReg .x18 = 2469829653914515739#64 → u.getReg .x19 = 2445952672640170197#64 →
        u.getReg .x20 = 8127635680764926565#64 → u.getReg .x21 = 12438865661331504215#64 →
        u.getReg .x22 = 14933811601259063721#64 → u.getReg .x23 = sp + 0x3d0#64 →
        u.getReg .x24 = 11037532056220336129#64 → u.getReg .x25 = 4611686018427387904#64 →
        u.getReg .x27 = t.getReg .x27 →
        Unchanged [(sp + 0x90#64, 4), (sp + 0x370#64, 4), (sp + 0x3b0#64, 8)] t u →
        Region (sp + 0x90#64) (natToLeLimbs 4 (Fp.sqrN (leLimbsToNat W) (m + 1))) u →
        (∃ W : List Word, W.length = 4 ∧ Region (sp + 0x370#64) W u) →
        (∃ W : List Word, W.length = 4 ∧ Region (sp + 0x390#64) W u) →
        (∃ W : List Word, W.length = 8 ∧ Region (sp + 0x3b0#64) W u) →
        SafeN G n P u) →
      SafeN G n P t := by
  intro m
  induction m with
  | zero =>
    intro t W hWl hpc hcode hcodeM hcw hsp h18 h19 h20 h21 h22 h23 h24 h25 h26 hm hX hokX hW1 hokW1
      hW3 hokW3 hW2 hokW2 hk
    obtain ⟨W1, hW1l, hW1⟩ := hW1
    obtain ⟨W3, hW3l, hW3⟩ := hW3
    obtain ⟨W2, hW2l, hW2⟩ := hW2
    have hu := Unchanged.refl [(sp + 0x90#64, 4), (sp + 0x370#64, 4), (sp + 0x3b0#64, 8)] t
    rw [show (0 : Nat) + 1 = 1 from rfl] at h26
    rw [show Fp.sqrN (leLimbsToNat W) 1 = Fp.mul (leLimbsToNat W) (leLimbsToNat W) from rfl] at hk
    sym_exec [uint256_mulmod_spec] stop [0x7802a1d8, 0x7802a280]
    all_goals rw [addiw_pred 1 (by omega) (by omega)] at v38_def; subst v38_def
    · exact absurd hbr43 (by decide)
    · sym_close hk
      sym_subst
      rw [list4_eta hWl]
      simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod]; rfl
  | succ m ih =>
    intro t W hWl hpc hcode hcodeM hcw hsp h18 h19 h20 h21 h22 h23 h24 h25 h26 hm hX hokX hW1 hokW1
      hW3 hokW3 hW2 hokW2 hk
    obtain ⟨W1, hW1l, hW1⟩ := hW1
    obtain ⟨W3, hW3l, hW3⟩ := hW3
    obtain ⟨W2, hW2l, hW2⟩ := hW2
    have hu := Unchanged.refl [(sp + 0x90#64, 4), (sp + 0x370#64, 4), (sp + 0x3b0#64, 8)] t
    rw [Fp.sqrN_succ] at hk
    sym_exec [uint256_mulmod_spec] stop [0x7802a1d8, 0x7802a280]
    all_goals rw [addiw_pred (m + 1 + 1) (by omega) (by omega), show m + 1 + 1 - 1 = m + 1 from rfl]
      at v38_def; subst v38_def
    · sym_close ih
      · intro u hp hc r2 r3 r4 r8 r9 r18 r19 r20 r21 r22 r23 r24 r25 r27 hU hR hR1 hR2 hR3
        refine hk u hp (hc.trans hcode) r2 (r3.trans hx3) (r4.trans hx4) (r8.trans hx8) (r9.trans hx9)
          r18 r19 r20 r21 r22 r23 r24 r25 (r27.trans hx27) (hunch.trans hU) ?_ hR1 hR2 hR3
        convert hR using 4
        sym_subst
        rw [list4_eta hWl]
        simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod]
        rfl
      · rfl
    · exact absurd hbr43 (by rw [Bn.ne_lit (m + 1) 0 (by omega) (by omega)]; simp)


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
/-- The `sqr(rg, 10)` loop: as `sqr_loop1`, with the counter in `s9` and `p₃` in `s1`. -/
theorem sqr_loop2 {G : MachineState → Prop} {n : Nat} {P : Prop} (sp : Word) :
    ∀ m (t : MachineState) (W : List Word), W.length = 4 →
      t.pc = 0x7802b74c#64 → CodeAt F_78029d94.base F_78029d94.prog t →
      CodeAt F_7801bf5c.base F_7801bf5c.prog t → CodeWithin Ro.layout.textLo Ro.layout.textHi t →
      t.getReg .x2 = sp →
      t.getReg .x18 = 2469829653914515739#64 → t.getReg .x19 = 2445952672640170197#64 →
      t.getReg .x20 = 8127635680764926565#64 → t.getReg .x21 = 12438865661331504215#64 →
      t.getReg .x22 = 14933811601259063721#64 → t.getReg .x23 = sp + 0x3d0#64 →
      t.getReg .x24 = 11037532056220336129#64 → t.getReg .x9 = 4611686018427387904#64 →
      t.getReg .x25 = BitVec.ofNat 64 (m + 1) → m + 1 < 2 ^ 31 →
      Region (sp + 0x150#64) W t → RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x150#64) 4 →
      (∃ W : List Word, W.length = 4 ∧ Region (sp + 0x370#64) W t) →
      RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x370#64) 4 →
      (∃ W : List Word, W.length = 4 ∧ Region (sp + 0x390#64) W t) →
      RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x390#64) 4 →
      (∃ W : List Word, W.length = 8 ∧ Region (sp + 0x3b0#64) W t) →
      RegionOk Ro.layout.textLo Ro.layout.textHi (sp + 0x3b0#64) 8 →
      (∀ u, u.pc = 0x7802b7f4#64 → u.code = t.code →
        u.getReg .x2 = sp → u.getReg .x3 = t.getReg .x3 → u.getReg .x4 = t.getReg .x4 →
        u.getReg .x8 = t.getReg .x8 →
        u.getReg .x18 = 2469829653914515739#64 → u.getReg .x19 = 2445952672640170197#64 →
        u.getReg .x20 = 8127635680764926565#64 → u.getReg .x21 = 12438865661331504215#64 →
        u.getReg .x22 = 14933811601259063721#64 → u.getReg .x23 = sp + 0x3d0#64 →
        u.getReg .x24 = 11037532056220336129#64 → u.getReg .x9 = 4611686018427387904#64 →
        u.getReg .x26 = t.getReg .x26 → u.getReg .x27 = t.getReg .x27 →
        Unchanged [(sp + 0x150#64, 4), (sp + 0x370#64, 4), (sp + 0x3b0#64, 8)] t u →
        Region (sp + 0x150#64) (natToLeLimbs 4 (Fp.sqrN (leLimbsToNat W) (m + 1))) u →
        (∃ W : List Word, W.length = 4 ∧ Region (sp + 0x370#64) W u) →
        (∃ W : List Word, W.length = 4 ∧ Region (sp + 0x390#64) W u) →
        (∃ W : List Word, W.length = 8 ∧ Region (sp + 0x3b0#64) W u) →
        SafeN G n P u) →
      SafeN G n P t := by
  intro m
  induction m with
  | zero =>
    intro t W hWl hpc hcode hcodeM hcw hsp h18 h19 h20 h21 h22 h23 h24 h25 h26 hm hX hokX hW1 hokW1
      hW3 hokW3 hW2 hokW2 hk
    obtain ⟨W1, hW1l, hW1⟩ := hW1
    obtain ⟨W3, hW3l, hW3⟩ := hW3
    obtain ⟨W2, hW2l, hW2⟩ := hW2
    have hu := Unchanged.refl [(sp + 0x150#64, 4), (sp + 0x370#64, 4), (sp + 0x3b0#64, 8)] t
    rw [show (0 : Nat) + 1 = 1 from rfl] at h26
    rw [show Fp.sqrN (leLimbsToNat W) 1 = Fp.mul (leLimbsToNat W) (leLimbsToNat W) from rfl] at hk
    sym_exec [uint256_mulmod_spec] stop [0x7802b74c, 0x7802b7f4]
    all_goals rw [addiw_pred 1 (by omega) (by omega)] at v38_def; subst v38_def
    · exact absurd hbr43 (by decide)
    · sym_close hk
      sym_subst
      rw [list4_eta hWl]
      simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod]; rfl
  | succ m ih =>
    intro t W hWl hpc hcode hcodeM hcw hsp h18 h19 h20 h21 h22 h23 h24 h25 h26 hm hX hokX hW1 hokW1
      hW3 hokW3 hW2 hokW2 hk
    obtain ⟨W1, hW1l, hW1⟩ := hW1
    obtain ⟨W3, hW3l, hW3⟩ := hW3
    obtain ⟨W2, hW2l, hW2⟩ := hW2
    have hu := Unchanged.refl [(sp + 0x150#64, 4), (sp + 0x370#64, 4), (sp + 0x3b0#64, 8)] t
    rw [Fp.sqrN_succ] at hk
    sym_exec [uint256_mulmod_spec] stop [0x7802b74c, 0x7802b7f4]
    all_goals rw [addiw_pred (m + 1 + 1) (by omega) (by omega), show m + 1 + 1 - 1 = m + 1 from rfl]
      at v38_def; subst v38_def
    · sym_close ih
      · intro u hp hc r2 r3 r4 r8 r18 r19 r20 r21 r22 r23 r24 r9 r26 r27 hU hR hR1 hR2 hR3
        refine hk u hp (hc.trans hcode) r2 (r3.trans hx3) (r4.trans hx4) (r8.trans hx8)
          r18 r19 r20 r21 r22 r23 r24 r9 (r26.trans hx26) (r27.trans hx27) (hunch.trans hU) ?_ hR1 hR2 hR3
        convert hR using 4
        sym_subst
        rw [list4_eta hWl]
        simp only [cells4, cells4', Fp.limbs_p, Fp.limbs_rInv, Fp.limbs_mod]
        rfl
      · rfl
    · exact absurd hbr43 (by rw [Bn.ne_lit (m + 1) 0 (by omega) (by omega)]; simp)

set_option maxHeartbeats 100000000 in
set_option maxRecDepth 20000 in
theorem pow_seg8 {G : MachineState → Prop} {n : Nat} {P : Prop} (s0 : MachineState) (sp a0 : Word) (T0 T1 T2 T3 A : Nat) (t : MachineState)
    (hstk : StackOk Ro.layout 0x450 sp)
    (h : PowCut true s0 sp a0 0x7802be04#64 T0 T1 T2 T3 A t)
    (hk : ∀ u, PowCut true s0 sp a0 0x7802c124#64 T0 T1 T2 T3 (Fp.powRun [T0, T1, T2, T3] Fp.powOps8 A) u →
      SafeN G n P u) : SafeN G n P t := by
  obtain ⟨w0, w1, t00, t01, t02, t03, t10, t11, t12, t13, t20, t21, t22, t23, t30, t31, t32, t33, d0, d1, d2, d3, b0, b1, b2, b3, hpc, hcode, hcA, hcM, hcw, hok, hU0, hx2, hx3, hx4, hx8, hx9, hx10, hx11, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx27, hB0, hX1, hB1, hX2, hB2, hC, hD1, hD2, hE, hS, eT0, eT1, eT2, eT3, eA, eB⟩ := h
  rw [if_pos rfl] at hx23
  clear hx25
  obtain ⟨X1, hX1l, hX1⟩ := hX1
  obtain ⟨B1, hB1l, hB1⟩ := hB1
  obtain ⟨X2, hX2l, hX2⟩ := hX2
  obtain ⟨B2, hB2l, hB2⟩ := hB2
  obtain ⟨C, hCl, hC⟩ := hC
  obtain ⟨D2, hD2l, hD2⟩ := hD2
  have hokB0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 1104#64) 18 := hok.sub' 0 18 (by decide) (by bv_omega)
  have hokX1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 960#64) 4 := hok.sub' 18 4 (by decide) (by bv_omega)
  have hokB1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 928#64) 20 := hok.sub' 22 20 (by decide) (by bv_omega)
  have hokX2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 768#64) 4 := hok.sub' 42 4 (by decide) (by bv_omega)
  have hokB2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 736#64) 56 := hok.sub' 46 56 (by decide) (by bv_omega)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 288#64) 8 := hok.sub' 102 8 (by decide) (by bv_omega)
  have hokD1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 224#64) 4 := hok.sub' 110 4 (by decide) (by bv_omega)
  have hokD2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 192#64) 4 := hok.sub' 114 4 (by decide) (by bv_omega)
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 160#64) 8 := hok.sub' 118 8 (by decide) (by bv_omega)
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 96#64) 12 := hok.sub' 126 12 (by decide) (by bv_omega)
  have hu := Unchanged.refl [(sp - 1104#64, 138)] t
  have hk' : ∀ (u : MachineState) (w0' w1' t00' t01' t02' t03' t10' t11' t12' t13' t20' t21' t22' t23' t30' t31' t32' t33' d0' d1' d2' d3' b0' b1' b2' b3' : Word),
      u.pc = 0x7802c124#64 → u.code = t.code → CodeAt F_78029d94.base F_78029d94.prog u →
      CodeAt F_7801bf5c.base F_7801bf5c.prog u → CodeWithin Ro.layout.textLo Ro.layout.textHi u →
      u.getReg .x2 = sp - 1104#64 →
      u.getReg .x3 = t.getReg .x3 →
      u.getReg .x4 = t.getReg .x4 →
      u.getReg .x8 = a0 →
      u.getReg .x9 = 4611686018427387904#64 →
      u.getReg .x10 = sp - 224#64 →
      u.getReg .x11 = sp - 160#64 →
      u.getReg .x18 = 2469829653914515739#64 →
      u.getReg .x19 = 2445952672640170197#64 →
      u.getReg .x20 = 8127635680764926565#64 →
      u.getReg .x21 = 12438865661331504215#64 →
      u.getReg .x22 = 14933811601259063721#64 →
      u.getReg .x23 = 11037532056220336129#64 →
      u.getReg .x24 = 11037532056220336129#64 →
      u.getReg .x27 = t.getReg .x27 →
      Unchanged [(sp - 1104#64, 138)] t u →
      Region (sp - 1104#64) [w0', w1', t00', t01', t02', t03', t10', t11', t12', t13', t20', t21', t22', t23', t30', t31', t32', t33'] u →
      (∃ W : List Word, W.length = 4 ∧ Region (sp - 960#64) W u) →
      (∃ W : List Word, W.length = 20 ∧ Region (sp - 928#64) W u) →
      (∃ W : List Word, W.length = 4 ∧ Region (sp - 768#64) W u) →
      (∃ W : List Word, W.length = 56 ∧ Region (sp - 736#64) W u) →
      (∃ W : List Word, W.length = 8 ∧ Region (sp - 288#64) W u) →
      Region (sp - 224#64) [d0', d1', d2', d3'] u →
      (∃ W : List Word, W.length = 4 ∧ Region (sp - 192#64) W u) →
      Region (sp - 160#64) [b0', b1', b2', b3', 11037532056220336129#64, 2469829653914515739#64, 0#64,
        4611686018427387904#64] u →
      Region (sp - 96#64) [s0.getReg .x26, s0.getReg .x25, s0.getReg .x24, s0.getReg .x23,
      s0.getReg .x22, s0.getReg .x21, s0.getReg .x20, s0.getReg .x19, s0.getReg .x18,
      s0.getReg .x9, s0.getReg .x8, s0.getReg .x1] u →
      leLimbsToNat [t00', t01', t02', t03'] = T0 →
      leLimbsToNat [t10', t11', t12', t13'] = T1 →
      leLimbsToNat [t20', t21', t22', t23'] = T2 →
      leLimbsToNat [t30', t31', t32', t33'] = T3 →
      leLimbsToNat [d0', d1', d2', d3'] = Fp.powRun [T0, T1, T2, T3] Fp.powOps8 A →
      [b0', b1', b2', b3'] = [d0', d1', d2', d3'] →
      SafeN G n P u := by
    intro u w0' w1' t00' t01' t02' t03' t10' t11' t12' t13' t20' t21' t22' t23' t30' t31' t32' t33' d0' d1' d2' d3' b0' b1' b2' b3' upc ucode ucA ucM ucw rx2 rx3 rx4 rx8 rx9 rx10 rx11 rx18 rx19 rx20 rx21 rx22 rx23 rx24 rx27 uU uB0 uX1 uB1 uX2 uB2 uC uD1 uD2 uE uS f0 f1 f2 f3 fA hbd
    exact hk u ⟨w0', w1', t00', t01', t02', t03', t10', t11', t12', t13', t20', t21', t22', t23', t30', t31', t32', t33', d0', d1', d2', d3', b0', b1', b2', b3', upc, ucode.trans hcode, ucA, ucM, ucw, hok, hU0.trans uU, rx2, rx3.trans hx3, rx4.trans hx4, rx8, rx9, rx10, rx11, rx18, rx19, rx20, rx21, rx22, (by rw [if_pos rfl]; exact rx23), rx24, (fun h => absurd h (by decide)), rx27.trans hx27, uB0, uX1, uB1, uX2, uB2, uC, uD1, uD2, uE, uS, f0, f1, f2, f3, fA, by rw [hbd]; exact fA⟩
  sym_exec [uint256_mulmod_spec] stop [0x7802c124]
  sym_close hk' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have M_acc15_0 : acc15_0 = Fp.mul A A :=
    (mulpair acc2_0_def acc15_0_def).trans (congrArg₂ Fp.mul eA eB)
  have M_acc57_0 : acc57_0 = Fp.mul acc15_0 acc15_0 :=
    (mulpair acc44_0_def acc57_0_def).trans (congrArg₂ Fp.mul (by rw [← v16_def, ← v17_def, ← v18_def, ← v19_def]; exact cells_lt (acc_ltp acc15_0_def)) (by rw [← v16_def, ← v17_def, ← v18_def, ← v19_def]; exact cells_lt (acc_ltp acc15_0_def)))
  have M_acc99_0 : acc99_0 = Fp.mul acc57_0 T2 :=
    (mulpair acc86_0_def acc99_0_def).trans (congrArg₂ Fp.mul (by rw [← v58_def, ← v59_def, ← v60_def, ← v61_def]; exact cells_lt (acc_ltp acc57_0_def)) eT2)
  have M_acc141_0 : acc141_0 = Fp.mul acc99_0 acc99_0 :=
    (mulpair acc128_0_def acc141_0_def).trans (congrArg₂ Fp.mul (by rw [← v100_def, ← v101_def, ← v102_def, ← v103_def]; exact cells_lt (acc_ltp acc99_0_def)) (by rw [← v100_def, ← v101_def, ← v102_def, ← v103_def]; exact cells_lt (acc_ltp acc99_0_def)))
  have M_acc183_0 : acc183_0 = Fp.mul acc141_0 acc141_0 :=
    (mulpair acc170_0_def acc183_0_def).trans (congrArg₂ Fp.mul (by rw [← v142_def, ← v143_def, ← v144_def, ← v145_def]; exact cells_lt (acc_ltp acc141_0_def)) (by rw [← v142_def, ← v143_def, ← v144_def, ← v145_def]; exact cells_lt (acc_ltp acc141_0_def)))
  have hfin : acc183_0 = Fp.powRun [T0, T1, T2, T3] Fp.powOps8 A := by
    rw [show Fp.powOps8 = [4, 4, 2, 4, 4] from rfl]
    rw [Fp.powRun_cons, Fp.powStep_sq, ← M_acc15_0]
    rw [Fp.powRun_cons, Fp.powStep_sq, ← M_acc57_0]
    rw [Fp.powRun_cons, (Fp.powStep_tbl T0 T1 T2 T3 _).2.2.1, ← M_acc99_0]
    rw [Fp.powRun_cons, Fp.powStep_sq, ← M_acc141_0]
    rw [Fp.powRun_cons, Fp.powStep_sq, ← M_acc183_0]
    rfl
  rw [← v184_def, ← v185_def, ← v186_def, ← v187_def, cells_lt (acc_ltp acc183_0_def)]; exact hfin

end Cases.Zip2005
