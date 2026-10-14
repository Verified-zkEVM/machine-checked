/-
  Cases.Zip2005.BnKit

  Multi-limb arithmetic as the executor leaves it: a chain of atoms `e = v`
  over 64-bit words (`add`, `mul`, `mulhu`, the `sltu` carry after an add,
  shifts). `bn_lin` states each as a linear `Nat` fact about `toNat`s, a
  quotient standing for each carry or high half:

    a + b = v              v + 2^64 * ((a + b) / 2^64) = a + b
    a * b = v              v + 2^64 * (a * b / 2^64)   = a * b
    mulhu a b = v          v = a * b / 2^64
    (a + w <ᵤ a ? 1 : 0)   v = (a + w) / 2^64          -- the carry of that add
    a >>> k = v            v = a / 2^k
    a <<< k = v            v + 2^64 * (a / 2^(64-k)) = a * 2^k

  Every multiplication the field code makes is by a constant limb, so the facts
  are linear in the atoms and `linarith` combines them into a limb identity.
-/

import Cases.Zip2005.Field.Limbs
import AsmVerif.RiscV.Sym
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Cases.Zip2005.Bn

open RiscvZkvm.Rv64

theorem add_fact {a b v : Word} (h : a + b = v) :
    v.toNat + 2 ^ 64 * ((a.toNat + b.toNat) / 2 ^ 64) = a.toNat + b.toNat := by
  subst h; rw [BitVec.toNat_add]; exact Nat.mod_add_div _ _

theorem mul_fact {a b v : Word} (h : a * b = v) :
    v.toNat + 2 ^ 64 * (a.toNat * b.toNat / 2 ^ 64) = a.toNat * b.toNat := by
  subst h; rw [BitVec.toNat_mul]; exact Nat.mod_add_div _ _

theorem mulhu_fact {a b v : Word} (h : rv64_mulhu a b = v) :
    v.toNat = a.toNat * b.toNat / 2 ^ 64 := by
  subst h
  have ha := a.isLt; have hb := b.isLt
  have hab : a.toNat * b.toNat < 2 ^ 128 := by
    calc a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 128 := by norm_num
  simp only [rv64_mulhu, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_mul, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega),
    Nat.mod_eq_of_lt hab]
  apply Nat.mod_eq_of_lt
  rw [Nat.div_lt_iff_lt_mul (by norm_num)]
  calc a.toNat * b.toNat < 2 ^ 128 := hab
    _ = 2 ^ 64 * 2 ^ 64 := by norm_num

/-- The carry of `b = a + w`, as `sltu b, a` computes it. -/
theorem carry_fact {a w b v : Word} (hb : a + w = b)
    (h : (if b.ult a = true then 1#64 else 0#64) = v) :
    v.toNat = (a.toNat + w.toNat) / 2 ^ 64 := by
  subst hb h
  have ha := a.isLt; have hw := w.isLt
  simp only [BitVec.ult, BitVec.toNat_add, decide_eq_true_eq]
  split <;> simp <;> omega

/-- The same carry, the add written the other way round. -/
theorem carry_fact' {a w b v : Word} (hb : w + a = b)
    (h : (if b.ult a = true then 1#64 else 0#64) = v) :
    v.toNat = (w.toNat + a.toNat) / 2 ^ 64 := by
  subst hb h
  have ha := a.isLt; have hw := w.isLt
  simp only [BitVec.ult, BitVec.toNat_add, decide_eq_true_eq]
  split <;> simp <;> omega

theorem shr_fact {a v : Word} {k : Nat} (h : a >>> k = v) : v.toNat = a.toNat / 2 ^ k := by
  subst h; rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- `BitVec.toNat_ofNat`, restated so that it is not a `rfl` lemma. `simp` closes
    goals with a `rfl` lemma by definitional unfolding, which the kernel then
    repeats; on a word literal of `2^63` or more that unfolding overflows its
    stack (E1 in `docs/LEDGER.md`). -/
theorem toNat_ofNat' {w : Nat} (x : Nat) : (BitVec.ofNat w x).toNat = x % 2 ^ w :=
  BitVec.toNat_ofNat x w

theorem shl_fact {a v : Word} {k : Nat} (hk : k ≤ 64) (h : a <<< k = v) :
    v.toNat + 2 ^ 64 * (a.toNat / 2 ^ (64 - k)) = a.toNat * 2 ^ k := by
  subst h
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have e : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_mod_mul_right, Nat.mul_comm (2 ^ (64 - k)) (2 ^ k), Nat.mul_assoc,
    Nat.mul_comm (a.toNat % _) (2 ^ k), ← Nat.mul_add, Nat.mod_add_div, Nat.mul_comm]

/-- The low limb of a Montgomery step vanishes: `m = x·n0`, and `m·p0 + x ≡ 0`
    when `n0 = -p0⁻¹ mod 2^64`. -/
theorem mont_low {n0 p0 : Nat} (hn : (n0 % 2 ^ 64 * (p0 % 2 ^ 64) + 1) % 2 ^ 64 = 0)
    {x m l s : Word} (hm : x * BitVec.ofNat 64 n0 = m) (hl : m * BitVec.ofNat 64 p0 = l)
    (hs : l + x = s) : s.toNat = 0 := by
  subst hm hl hs
  rw [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_mul, toNat_ofNat', toNat_ofNat',
    Nat.mod_mul_mod, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have e : x.toNat * (n0 % 2 ^ 64) * (p0 % 2 ^ 64) + x.toNat
      = x.toNat * (n0 % 2 ^ 64 * (p0 % 2 ^ 64) + 1) := by ring
  rw [e, Nat.mul_mod, hn, Nat.mul_zero, Nat.zero_mod]

/-! Upper bounds, to show that an add does not carry. -/

theorem word_le (x : Word) : x.toNat ≤ 18446744073709551615 := by
  have := x.isLt; omega

theorem lit_le (c : Nat) {b : Nat} (h : c % 2 ^ 64 ≤ b) : (BitVec.ofNat 64 c).toNat ≤ b := by
  rw [toNat_ofNat']; exact h

theorem carry_le {a b v : Word} (h : (if b.ult a = true then 1#64 else 0#64) = v) :
    v.toNat ≤ 1 := by
  subst h; split <;> simp

theorem mulhu_le {a v : Word} {c ba bv : Nat} (h : rv64_mulhu a (BitVec.ofNat 64 c) = v)
    (ha : a.toNat ≤ ba) (hb : ba * (c % 2 ^ 64) / 2 ^ 64 ≤ bv) : v.toNat ≤ bv := by
  have e := mulhu_fact h
  rw [toNat_ofNat'] at e
  rw [e]
  exact le_trans (Nat.div_le_div_right (Nat.mul_le_mul_right _ ha)) hb

theorem shr_le {a v : Word} {k ba bv : Nat} (h : a >>> k = v) (ha : a.toNat ≤ ba)
    (hb : ba / 2 ^ k ≤ bv) : v.toNat ≤ bv := by
  rw [shr_fact h]; exact le_trans (Nat.div_le_div_right ha) hb

theorem add_le {a b v : Word} {ba bb bv : Nat} (h : a + b = v) (ha : a.toNat ≤ ba)
    (hb : b.toNat ≤ bb) (hs : ba + bb ≤ bv) (hl : bv < 2 ^ 64) :
    (a.toNat + b.toNat) / 2 ^ 64 = 0 ∧ v.toNat ≤ bv := by
  have e := add_fact h
  have q : (a.toNat + b.toNat) / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  refine ⟨q, ?_⟩
  rw [q] at e
  omega

/-! Masks: `sra 63` of a word, and `and` with `b - 1` for a bit `b`. -/

theorem sar_fact {x v : Word} (h : x.sshiftRight 63 = v) :
    (x.toNat < 2 ^ 63 ∧ v.toNat = 0) ∨ (2 ^ 63 ≤ x.toNat ∧ v.toNat = 2 ^ 64 - 1) := by
  subst h
  have hx := x.isLt
  rw [BitVec.toNat_sshiftRight, BitVec.msb_eq_decide, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow]
  by_cases h : 2 ^ 63 ≤ x.toNat
  · right
    have h' : 2 ^ (64 - 1) ≤ x.toNat := h
    have : (2 ^ 64 - 1 - x.toNat) / 2 ^ 63 = 0 := Nat.div_eq_of_lt (by omega)
    rw [if_pos (by simpa using h'), this]
    omega
  · left
    have h' : ¬ 2 ^ (64 - 1) ≤ x.toNat := h
    simp only [h', decide_false, Bool.false_eq_true, if_false]
    have : x.toNat / 2 ^ 63 = 0 := Nat.div_eq_of_lt (by omega)
    omega

theorem mask_and {b c v : Word} (hb : b.toNat ≤ 1) (h : b + BitVec.ofNat 64 18446744073709551615 &&& c = v) :
    (b.toNat = 0 ∧ v.toNat = c.toNat) ∨ (b.toNat = 1 ∧ v.toNat = 0) := by
  subst h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with h0 | h1
  · left
    refine ⟨h0, ?_⟩
    have e : b + BitVec.ofNat 64 18446744073709551615 = BitVec.allOnes 64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, toNat_ofNat', BitVec.toNat_allOnes, h0]
      decide
    rw [e, BitVec.allOnes_and]
  · right
    refine ⟨h1, ?_⟩
    have e : b + BitVec.ofNat 64 18446744073709551615 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, toNat_ofNat', toNat_ofNat', h1]
      decide
    rw [e, BitVec.zero_and, toNat_ofNat']
    decide

end Cases.Zip2005.Bn

namespace Cases.Zip2005

open Lean Meta Elab Tactic

/-- The linear fact for one word expression `e` named `v` by `h : e = v`
    (`v` may be `e` itself, with `h := rfl`). `defOf` finds an atom's definition. -/
def bnFact (defOf : Std.HashMap FVarId (Expr × Expr)) (e h : Expr) : MetaM (Option Expr) := do
  -- words only: an accumulator the executor named over `Nat` is not a limb
  unless (← whnfR (← inferType e)).isAppOfArity ``BitVec 1 do return none
  if e.isAppOfArity ``HAdd.hAdd 6 then return some (← mkAppM ``Cases.Zip2005.Bn.add_fact #[h])
  if e.isAppOfArity ``HMul.hMul 6 then return some (← mkAppM ``Cases.Zip2005.Bn.mul_fact #[h])
  if e.isAppOfArity ``RiscvZkvm.Rv64.rv64_mulhu 2 then return some (← mkAppM ``Cases.Zip2005.Bn.mulhu_fact #[h])
  if e.isAppOfArity ``HShiftRight.hShiftRight 6 then return some (← mkAppM ``Cases.Zip2005.Bn.shr_fact #[h])
  if e.isAppOfArity ``HShiftLeft.hShiftLeft 6 then
    let k := e.appArg!
    let hk ← mkDecideProof (← mkAppM ``LE.le #[k, mkNatLit 64])
    return some (← mkAppM ``Cases.Zip2005.Bn.shl_fact #[hk, h])
  if e.isAppOfArity ``ite 5 then
    -- `if b.ult a = true then 1 else 0`, `b` an add of `a` (inline or an atom)
    let c := e.getAppArgs[1]!
    let some (_, ult, _) := c.eq? | return none
    unless ult.isAppOfArity ``BitVec.ult 3 do return none
    let b := ult.getAppArgs[1]!
    let a := ult.getAppArgs[2]!
    let (be, bh) ← if b.isFVar then
        match defOf[b.fvarId!]? with
        | some p => pure p
        | none => return none
      else pure (b, ← mkEqRefl b)
    unless be.isAppOfArity ``HAdd.hAdd 6 do return none
    if be.appFn!.appArg! == a then return some (← mkAppM ``Cases.Zip2005.Bn.carry_fact #[bh, h])
    if be.appArg! == a then return some (← mkAppM ``Cases.Zip2005.Bn.carry_fact' #[bh, h])
    return none
  return none

/-- The composite word subterms of `e` (below its head) that `bnFact` describes. -/
partial def bnSubterms (e : Expr) (acc : Array Expr := #[]) : Array Expr := Id.run do
  let mut acc := acc
  for a in e.getAppArgs do
    let isOp := a.isAppOfArity ``HAdd.hAdd 6 || a.isAppOfArity ``HMul.hMul 6 ||
      a.isAppOfArity ``HShiftRight.hShiftRight 6 || a.isAppOfArity ``HShiftLeft.hShiftLeft 6
    if isOp && !acc.contains a then acc := acc.push a
    acc := bnSubterms a acc
  return acc

/-- The value of a numeral `n` or `BitVec.ofNat 64 n`. -/
def natLit? (e : Expr) : Option Nat :=
  match e.nat? with
  | some n => some n
  | none => e.rawNatLit?

/-- An upper bound on `e.toNat`, with its proof, from the bounds known so far. -/
def bnBoundOf (bounds : Std.HashMap Expr (Nat × Expr)) (e : Expr) : MetaM (Nat × Expr) := do
  if let some b := bounds[e]? then return b
  if e.isAppOfArity ``BitVec.ofNat 2 then
    if let some c := natLit? e.appArg! then
      let b := c % 2 ^ 64
      -- `c % 2^64 ≤ b`, by evaluation
      let hb ← mkDecideProof (← mkAppM ``LE.le
        #[← mkAppM ``HMod.hMod #[e.appArg!, ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 64]],
          mkNatLit b])
      return (b, ← mkAppM ``Cases.Zip2005.Bn.lit_le #[e.appArg!, hb])
  return (2 ^ 64 - 1, ← mkAppM ``Cases.Zip2005.Bn.word_le #[e])

/-- A bound for `v` named by `h : e = v`, and, for an add that cannot carry, the
    proof that its quotient is zero. -/
def bnBound (bounds : Std.HashMap Expr (Nat × Expr)) (e h : Expr) :
    MetaM (Option (Nat × Expr) × Option Expr) := do
  unless (← whnfR (← inferType e)).isAppOfArity ``BitVec 1 do return (none, none)
  let dle (a b : Expr) := do mkDecideProof (← mkAppM ``LE.le #[a, b])
  let two64 ← mkAppM ``HPow.hPow #[mkNatLit 2, mkNatLit 64]
  if e.isAppOfArity ``ite 5 then
    if let some _ := (e.getAppArgs[1]!).eq? then
      return (some (1, ← mkAppM ``Cases.Zip2005.Bn.carry_le #[h]), none)
  if e.isAppOfArity ``RiscvZkvm.Rv64.rv64_mulhu 2 then
    let c := e.appArg!
    if c.isAppOfArity ``BitVec.ofNat 2 then
      if let some cn := natLit? c.appArg! then
        let (ba, ha) ← bnBoundOf bounds e.appFn!.appArg!
        let bv := ba * (cn % 2 ^ 64) / 2 ^ 64
        let hb ← dle (← mkAppM ``HDiv.hDiv #[← mkAppM ``HMul.hMul #[mkNatLit ba,
          ← mkAppM ``HMod.hMod #[c.appArg!, two64]], two64]) (mkNatLit bv)
        return (some (bv, ← mkAppM ``Cases.Zip2005.Bn.mulhu_le #[h, ha, hb]), none)
  if e.isAppOfArity ``HShiftRight.hShiftRight 6 then
    if let some k := natLit? e.appArg! then
      let (ba, ha) ← bnBoundOf bounds e.appFn!.appArg!
      let bv := ba / 2 ^ k
      let hb ← dle (← mkAppM ``HDiv.hDiv #[mkNatLit ba,
        ← mkAppM ``HPow.hPow #[mkNatLit 2, e.appArg!]]) (mkNatLit bv)
      return (some (bv, ← mkAppM ``Cases.Zip2005.Bn.shr_le #[h, ha, hb]), none)
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let (ba, ha) ← bnBoundOf bounds e.appFn!.appArg!
    let (bb, hb) ← bnBoundOf bounds e.appArg!
    let bv := ba + bb
    if bv < 2 ^ 64 then
      let hs ← dle (← mkAppM ``HAdd.hAdd #[mkNatLit ba, mkNatLit bb]) (mkNatLit bv)
      let hl ← mkDecideProof (← mkAppM ``LT.lt #[mkNatLit bv, two64])
      let pf ← mkAppM ``Cases.Zip2005.Bn.add_le #[h, ha, hb, hs, hl]
      return (some (bv, ← mkAppM ``And.right #[pf]), some (← mkAppM ``And.left #[pf]))
  return (none, none)

/-- State every atom definition `e = v` in the context as a linear `Nat` fact
    `hn_v` (see `Cases.Zip2005.Bn`), and every composite operand inside them as a fact of
    its own. Definitions of other shapes are skipped. -/
elab "bn_lin" : tactic => withMainContext do
  let lctx ← getLCtx
  let mut defOf : Std.HashMap FVarId (Expr × Expr) := {}
  let mut defs : Array (Expr × Expr × Name) := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    if !d.userName.toString.endsWith "_def" then continue
    let ty ← instantiateMVars d.type
    if let some (_, e, v) := ty.eq? then
      if v.isFVar then
        defOf := defOf.insert v.fvarId! (e, d.toExpr)
        defs := defs.push (e, d.toExpr, ← v.fvarId!.getUserName)
  let mut facts : Array (Name × Expr) := #[]
  let mut seen : Array Expr := #[]
  let mut bounds : Std.HashMap Expr (Nat × Expr) := {}
  let mut k := 0
  let mut z := 0
  for (e, h, vn) in defs do
    for sub in (bnSubterms e).reverse do
      if seen.contains sub then continue
      seen := seen.push sub
      let hr ← mkEqRefl sub
      if let some pf ← bnFact defOf sub hr then
        facts := facts.push (Name.mkSimple s!"hs_{k}", pf)
        k := k + 1
      let (b?, z?) ← bnBound bounds sub hr
      if let some b := b? then bounds := bounds.insert sub b
      if let some pz := z? then
        facts := facts.push (Name.mkSimple s!"hz_{z}", pz)
        z := z + 1
    if let some pf ← bnFact defOf e h then facts := facts.push (Name.mkSimple s!"hn_{vn}", pf)
    let v := (← instantiateMVars (← inferType h)).appArg!
    let (b?, z?) ← bnBound bounds e h
    if let some b := b? then
      bounds := bounds.insert v b
      facts := facts.push (Name.mkSimple s!"hb_{vn}", b.2)
    if let some pz := z? then
      facts := facts.push (Name.mkSimple s!"hz_{z}", pz)
      z := z + 1
  let g ← getMainGoal
  let mut g := g
  for (nm, pf) in facts do
    let ty ← g.withContext (inferType pf)
    -- constants as numerals
    let r ← g.withContext (AsmVerif.RiscV.Sym.Meta.simpWith ty #[] #[``Cases.Zip2005.Bn.toNat_ofNat'])
    let (ty, pf) ← g.withContext do
      if r.expr == ty then pure (ty, pf) else pure (r.expr, ← mkEqMP (← r.getProof) pf)
    let (_, g') ← (← g.assert nm ty pf).intro1P
    g := g'
  replaceMainGoal [g]

end Cases.Zip2005

namespace Cases.Zip2005.Bn

open RiscvZkvm.Rv64

/-- `(e >> (j - 2)) & 1 == 0`, as `srl`/`andi` compute it with the shift
    amount `j + (-2)`: the exponent bit `j - 2` is clear. -/
theorem bit_test (e : Nat) (he : e < 2 ^ 64) (j : Nat) (hj : 2 ≤ j) (hj' : j ≤ 65) :
    ((BitVec.ofNat 64 e >>> ((BitVec.ofNat 64 j + BitVec.ofNat 64 18446744073709551614).toNat % 64)
      &&& BitVec.ofNat 64 1) == BitVec.ofNat 64 0) = !(e.testBit (j - 2)) := by
  have hk : (BitVec.ofNat 64 j + BitVec.ofNat 64 18446744073709551614).toNat % 64 = j - 2 := by
    rw [BitVec.toNat_add, toNat_ofNat', toNat_ofNat']; omega
  rw [hk]
  have h : ((BitVec.ofNat 64 e >>> (j - 2)) &&& BitVec.ofNat 64 1).toNat = e >>> (j - 2) % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, toNat_ofNat', toNat_ofNat',
      Nat.mod_eq_of_lt he, Nat.mod_eq_of_lt (by norm_num : 1 < 2 ^ 64), Nat.and_one_is_mod]
  have ht := Nat.testBit_eq_decide_div_mod_eq (x := e) (i := j - 2)
  rw [← Nat.shiftRight_eq_div_pow] at ht
  generalize e >>> (j - 2) = y at h ht
  cases hb : e.testBit (j - 2)
  · rw [hb] at ht
    have h0 : y % 2 = 0 := by
      have : ¬ y % 2 = 1 := fun h' => by rw [h'] at ht; exact absurd ht (by decide)
      omega
    simp only [Bool.not_false, beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [h, h0, toNat_ofNat', Nat.zero_mod]
  · rw [hb] at ht
    have h1 : y % 2 = 1 := of_decide_eq_true ht.symm
    simp only [Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    intro heq
    have := congrArg BitVec.toNat heq
    rw [h, h1, toNat_ofNat'] at this
    exact absurd this (by norm_num)

/-- The loop test `bgeu 1, j - 1`: another iteration when `j - 1 > 1`. -/
theorem ult_dec (j : Nat) (hj : 2 ≤ j) (hj' : j ≤ 65) :
    (BitVec.ofNat 64 1).ult (BitVec.ofNat 64 j + BitVec.ofNat 64 18446744073709551615) =
      decide (2 < j) := by
  rw [BitVec.ult_eq_decide, BitVec.toNat_add, toNat_ofNat', toNat_ofNat', toNat_ofNat']
  congr 1
  apply propext
  omega

theorem ofNat_pred (j : Nat) (hj : 1 ≤ j) (hj' : j ≤ 65) :
    BitVec.ofNat 64 j + BitVec.ofNat 64 18446744073709551615 = BitVec.ofNat 64 (j - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, toNat_ofNat', toNat_ofNat', toNat_ofNat']
  omega

theorem ne_lit (j c : Nat) (hj : j < 2 ^ 64) (hc : c < 2 ^ 64) :
    (BitVec.ofNat 64 j != BitVec.ofNat 64 c) = decide (j ≠ c) := by
  by_cases h : j = c
  · subst h; simp
  · have hne : BitVec.ofNat 64 j ≠ BitVec.ofNat 64 c := fun e => h (by
      have := congrArg BitVec.toNat e
      rwa [toNat_ofNat', toNat_ofNat', Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hc] at this)
    simp [hne, h]

end Cases.Zip2005.Bn
