import MachineChecked.RiscV.Lprog.Block

/-!
# Four-limb values in registers, for catcrypt-compiler's RV64 kernels

catcrypt-compiler's field kernels take their inputs in `a0..a3` and `a4..a7` (four 64-bit
limbs, little-endian) and leave the result in `a0..a3`. `limbs4` reads such a value as a
natural number, and `limbs4_eq_toNat` relates it to the 256-bit concatenation `bv_decide`
reasons about.

A kernel is stated as a correspondence (`MachineChecked.Ascent.Corres` over `stepSp1`)
between the machine and an abstract state that is either the entry (two values, at the
block's start) or the exit (one value, past the block): `KState`, `KSR`. It is proved through
the lift: the block runs at Lprog (`MachineChecked.RiscV.Lprog.corres_block`), and its effect
is the fold of `execInstrBr` over it.
-/

namespace Cases.CatCrypt

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.RiscV.Lprog
open MachineChecked.Ascent (Corres)

/-- The Curve25519 prime. -/
def p25519 : Nat := 2 ^ 255 - 19

/-- Four little-endian 64-bit limbs as a number. -/
def limbs4 (a0 a1 a2 a3 : Word) : Nat :=
  a0.toNat + 2 ^ 64 * a1.toNat + 2 ^ 128 * a2.toNat + 2 ^ 192 * a3.toNat

/-- The 256-bit concatenation, most significant limb first. -/
def cat4 (a0 a1 a2 a3 : Word) : BitVec 256 := a3 ++ a2 ++ a1 ++ a0

theorem limbs4_eq_toNat (a0 a1 a2 a3 : Word) : limbs4 a0 a1 a2 a3 = (cat4 a0 a1 a2 a3).toNat := by
  simp only [limbs4, cat4, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt a0.isLt, ← Nat.shiftLeft_add_eq_or_of_lt a1.isLt,
    ← Nat.shiftLeft_add_eq_or_of_lt a2.isLt]
  simp only [Nat.shiftLeft_eq]
  omega

/-- The value a state holds in `a0..a3`. -/
def regA (m : MachineState) : Nat := limbs4 (m.getReg .x10) (m.getReg .x11) (m.getReg .x12) (m.getReg .x13)

/-- The value a state holds in `a4..a7`. -/
def regB (m : MachineState) : Nat := limbs4 (m.getReg .x14) (m.getReg .x15) (m.getReg .x16) (m.getReg .x17)

/-- A kernel's abstract state: its two inputs at the entry, or its result past the block. -/
inductive KState where
  | entry (x y : Nat)
  | exit (z : Nat)

/-- The machine holds the kernel `prog` at `base`, and either the inputs in `a0..a7` at
    `base`, or the result in `a0..a3` past the block. -/
def KSR (base : Word) (prog : List Instr) (m : MachineState) : KState → Prop
  | .entry x y => CodeAt base (prog.map some) m ∧ m.pc = base ∧ regA m = x ∧ regB m = y
  | .exit z => CodeAt base (prog.map some) m ∧
      m.pc = base + BitVec.ofNat 64 (4 * prog.length) ∧ regA m = z

/-- At the entry, with inputs satisfying `pre`. -/
def KPre (pre : Nat → Nat → Prop) : KState → Prop
  | .entry x y => pre x y
  | .exit _ => False

/-- The kernel's specification `f` on the inputs. -/
def KSpec (f : Nat → Nat → Nat) : KState → KState
  | .entry x y => .exit (f x y)
  | .exit z => .exit z

/-- Registers agreeing, so do the values in `a0..a3`. -/
theorem regA_of_agree {t u : MachineState} (h : Agree t u) : regA t = regA u := by
  simp only [regA, h.regs]

/-- **A straight-line kernel.** A block of pure instructions whose fold takes the inputs in
    `a0..a7` to `f x y` in `a0..a3`, for inputs satisfying `pre`, corresponds to `f`. -/
theorem kernel_corres (base : Word) (prog : List Instr) (hall : prog.all isPure = true)
    (pre : Nat → Nat → Prop) (f : Nat → Nat → Nat)
    (h : ∀ m : MachineState, pre (regA m) (regB m) →
      regA (prog.foldl execInstrBr m) = f (regA m) (regB m)) :
    Corres stepSp1 (KSR base prog) (KPre pre) (KSpec f) := by
  apply corres_block base prog hall
  · rintro m (⟨x, y⟩ | z) hSR hP
    · exact ⟨hSR.1, hSR.2.1⟩
    · exact hP.elim
  · rintro m (⟨x, y⟩ | z) t hSR hP hag htpc htc
    · obtain ⟨-, -, hx, hy⟩ := hSR
      subst hx hy
      exact ⟨htc, htpc, (regA_of_agree hag).trans (h m hP)⟩
    · exact hP.elim

/-- The reduction the kernels' `bv_decide` facts give: a value below `p` that differs from `S`
    by a multiple of `p` is `S % p`. -/
theorem eq_mod_of_eq_add_mul {S R k p : Nat} (hR : R < p) (h : S = R + k * p) : R = S % p := by
  subst h; rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hR]

/-- The subtraction form: `x + c = y + r + k·p` with `r < p` gives `r = (x + c - y) % p`. -/
theorem eq_sub_mod_of_eq {x y r c k p : Nat} (hR : r < p) (h : x + c = y + r + k * p) :
    r = (x + c - y) % p :=
  eq_mod_of_eq_add_mul (S := x + c - y) (k := k) hR (by omega)

/-- The 258-bit identity `bv_decide` checks, read on numbers: no addition overflows. -/
theorem sum_of_zext {X Y R : BitVec 256} {c : Nat} (hc : c < 2 * 2 ^ 256)
    (h : X.zeroExtend 258 + Y.zeroExtend 258 = R.zeroExtend 258 + BitVec.ofNat 258 c) :
    X.toNat + Y.toNat = R.toNat + c := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  have := X.isLt; have := Y.isLt; have := R.isLt
  omega

/-- The same, with a third summand on the left: `X + c₁ = Y + R + c₂` with no overflow. -/
theorem sum3_of_zext {X Y R : BitVec 256} {c₁ c₂ : Nat} (hc₁ : c₁ < 2 ^ 256) (hc₂ : c₂ < 2 * 2 ^ 256)
    (h : X.zeroExtend 258 + BitVec.ofNat 258 c₁ =
      Y.zeroExtend 258 + R.zeroExtend 258 + BitVec.ofNat 258 c₂) :
    X.toNat + c₁ = Y.toNat + R.toNat + c₂ := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at this
  have := X.isLt; have := Y.isLt; have := R.isLt
  omega

/-- A bound on numbers, as the 258-bit comparison `bv_decide` takes. -/
theorem zext_le_add {X Y : BitVec 256} {c : Nat} (hc : c < 2 ^ 256) (h : Y.toNat ≤ X.toNat + c) :
    Y.zeroExtend 258 ≤ X.zeroExtend 258 + BitVec.ofNat 258 c := by
  rw [BitVec.le_def]
  simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have := X.isLt; have := Y.isLt
  omega

/-- `regA` of a state is the 256-bit value of its `a0..a3`. -/
theorem regA_eq (m : MachineState) :
    regA m = (cat4 (m.getReg .x10) (m.getReg .x11) (m.getReg .x12) (m.getReg .x13)).toNat :=
  limbs4_eq_toNat _ _ _ _

theorem regB_eq (m : MachineState) :
    regB m = (cat4 (m.getReg .x14) (m.getReg .x15) (m.getReg .x16) (m.getReg .x17)).toNat :=
  limbs4_eq_toNat _ _ _ _

end Cases.CatCrypt
