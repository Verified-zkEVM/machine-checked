/-
  AsmVerif.RiscV.Check.Fact

  Facts and certificates (phase E2).

  A *fact* is what the checker may know about values it does not know exactly: a linear
  inequality over ℕ between terms with nonnegative coefficients (`le`), the exact result of
  a machine operation (`op`: `x = u + v` as 64-bit words, say), or a model's atom
  (`atom`: a heap block is live). Values are abstract (`α`); a valuation gives them words,
  and an inequality is read on their `toNat`.

  A *certificate* (`Proof`) derives new facts from old: a nonnegative combination of
  inequalities compared coefficientwise (Farkas), a case split on an inequality, a built-in
  consequence of an operation (an addition that did not wrap is a sum), or an instance of a
  model rule. The kernel checks certificates; it never searches. `runAll_sound` is the one
  theorem the checker relies on.
-/

import RiscvZkvm.Rv64

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64

/-! ## Linear terms -/

/-- `Σ c·x + k`, with nonnegative integer coefficients. -/
structure LinTerm (α : Type) where
  coeffs : List (α × Nat) := []
  const : Nat := 0
  deriving DecidableEq, Repr, Inhabited

namespace LinTerm

variable {α β : Type}

def eval (ν : α → Nat) (t : LinTerm α) : Nat :=
  t.const + (t.coeffs.map fun p => p.2 * ν p.1).sum

def var (x : α) : LinTerm α := ⟨[(x, 1)], 0⟩
def ofNat (k : Nat) : LinTerm α := ⟨[], k⟩
def add (s t : LinTerm α) : LinTerm α := ⟨s.coeffs ++ t.coeffs, s.const + t.const⟩
def smul (c : Nat) (t : LinTerm α) : LinTerm α :=
  ⟨t.coeffs.map fun p => (p.1, c * p.2), c * t.const⟩
def map (f : α → β) (t : LinTerm α) : LinTerm β := ⟨t.coeffs.map fun p => (f p.1, p.2), t.const⟩

instance : Add (LinTerm α) := ⟨add⟩

def mentions [DecidableEq α] (t : LinTerm α) (x : α) : Bool := t.coeffs.any (·.1 == x)

/-- The total coefficient of `x`. -/
def coeff [DecidableEq α] (t : LinTerm α) (x : α) : Nat :=
  ((t.coeffs.filter fun p => p.1 == x).map (·.2)).sum

/-- The entries of other variables. -/
def without [DecidableEq α] (t : LinTerm α) (x : α) : LinTerm α :=
  ⟨t.coeffs.filter fun p => p.1 != x, t.const⟩

/-- `s ≤ t` coefficientwise: every variable's coefficient, and the constant. -/
def leq [DecidableEq α] (s t : LinTerm α) : Bool :=
  s.const ≤ t.const && s.coeffs.all fun p => s.coeff p.1 ≤ t.coeff p.1

theorem eval_add (ν : α → Nat) (s t : LinTerm α) : (s + t).eval ν = s.eval ν + t.eval ν := by
  show (add s t).eval ν = _
  simp only [add, eval, List.map_append, List.sum_append]; omega

theorem eval_smul (ν : α → Nat) (c : Nat) (t : LinTerm α) : (t.smul c).eval ν = c * t.eval ν := by
  simp only [smul, eval, List.map_map, Nat.mul_add]
  congr 1
  induction t.coeffs with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp, ih, Nat.mul_add, Nat.mul_assoc]

theorem eval_map (ν : β → Nat) (f : α → β) (t : LinTerm α) :
    (t.map f).eval ν = t.eval (ν ∘ f) := by
  simp only [map, eval, List.map_map, Function.comp_def]

theorem eval_var (ν : α → Nat) (x : α) : (var x).eval ν = ν x := by simp [var, eval]
theorem eval_ofNat (ν : α → Nat) (k : Nat) : (ofNat k : LinTerm α).eval ν = k := by simp [ofNat, eval]

section Leq

variable [DecidableEq α]

/-- The sum over the coefficient list splits into `x`'s entries and the rest. -/
theorem sum_split (ν : α → Nat) (l : List (α × Nat)) (x : α) :
    (l.map fun p => p.2 * ν p.1).sum =
      ((l.filter fun p => p.1 == x).map (·.2)).sum * ν x +
      ((l.filter fun p => p.1 != x).map fun p => p.2 * ν p.1).sum := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    by_cases h : p.1 = x
    · subst h
      simp only [List.map_cons, List.sum_cons, List.filter_cons, beq_self_eq_true, bne_self_eq_false,
        Bool.false_eq_true, ↓reduceIte, ih, Nat.add_mul]
      omega
    · simp only [List.map_cons, List.sum_cons, List.filter_cons, beq_iff_eq, h, ↓reduceIte,
        bne_iff_ne, ne_eq, not_false_eq_true, ih]
      omega

theorem eval_eq_coeff (ν : α → Nat) (t : LinTerm α) (x : α) :
    t.eval ν = t.coeff x * ν x + (t.without x).eval ν := by
  simp only [eval, coeff, without]
  rw [sum_split ν t.coeffs x]; omega

theorem coeff_without (t : LinTerm α) {x y : α} (h : y ≠ x) : (t.without x).coeff y = t.coeff y := by
  unfold coeff without
  rw [List.filter_filter]
  congr 2
  apply List.filter_congr
  intro p _
  by_cases hpy : p.1 = y
  · simp [hpy, h]
  · simp [hpy]

theorem without_length_lt (t : LinTerm α) {x : α} (h : t.mentions x = true) :
    (t.without x).coeffs.length < t.coeffs.length := by
  simp only [mentions, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨p, hp, hpx⟩ := h
  simp only [without]
  exact List.length_filter_lt_length_iff_exists.mpr ⟨p, hp, by simp [hpx]⟩

theorem leq_iff (s t : LinTerm α) :
    leq s t = true ↔ s.const ≤ t.const ∧ ∀ p ∈ s.coeffs, s.coeff p.1 ≤ t.coeff p.1 := by
  simp [leq]

/-- Coefficientwise order is semantic order, under any valuation. -/
theorem leq_sound (ν : α → Nat) : ∀ (s t : LinTerm α), leq s t = true → s.eval ν ≤ t.eval ν
  | s, t, h => by
    rw [leq_iff] at h
    cases hc : s.coeffs with
    | nil => simp [eval, hc]; omega
    | cons p ps =>
      have hx : s.mentions p.1 = true := by simp [mentions, hc]
      have hlt := without_length_lt s hx
      have ih := leq_sound ν (s.without p.1) (t.without p.1)
      rw [eval_eq_coeff ν s p.1, eval_eq_coeff ν t p.1]
      have h1 : s.coeff p.1 ≤ t.coeff p.1 := h.2 p (by rw [hc]; simp)
      have h2 : (s.without p.1).eval ν ≤ (t.without p.1).eval ν := by
        apply ih
        rw [leq_iff]
        refine ⟨h.1, fun q hq => ?_⟩
        have hq' := List.mem_filter.mp hq
        have hne : q.1 ≠ p.1 := by simpa using hq'.2
        rw [coeff_without s hne, coeff_without t hne]
        exact h.2 q hq'.1
      exact Nat.add_le_add (Nat.mul_le_mul_right _ h1) h2
termination_by s _ _ => s.coeffs.length

end Leq

end LinTerm

/-! ## Operations -/

/-- A machine operation whose exact result a fact may record. -/
inductive Op where
  | add | sub | and | or | xor | sltu | slt | mul | mulhu
  | shl (c : Nat) | shr (c : Nat) | sra (c : Nat)
  /-- The 32-bit operations, sign-extended. -/
  | addw | subw | shlw (c : Nat) | shrw (c : Nat)
  deriving DecidableEq, Repr

def Op.eval : Op → List Word → Word
  | .add, [u, v] => u + v
  | .sub, [u, v] => u - v
  | .and, [u, v] => u &&& v
  | .or, [u, v] => u ||| v
  | .xor, [u, v] => u ^^^ v
  | .sltu, [u, v] => if u < v then 1 else 0
  | .slt, [u, v] => if u.toInt < v.toInt then 1 else 0
  | .mul, [u, v] => u * v
  | .mulhu, [u, v] => BitVec.ofNat 64 ((u.toNat * v.toNat) / 2 ^ 64)
  | .shl c, [u] => u <<< c
  | .shr c, [u] => u >>> c
  | .sra c, [u] => u.sshiftRight c
  | .addw, [u, v] => ((u + v).truncate 32).signExtend 64
  | .subw, [u, v] => ((u - v).truncate 32).signExtend 64
  | .shlw c, [u] => ((u <<< c).truncate 32).signExtend 64
  | .shrw c, [u] => ((u.truncate 32) >>> c).signExtend 64
  | _, _ => 0

/-! ## Facts -/

inductive Fact (α : Type) where
  | le (l r : LinTerm α)
  | op (o : Op) (x : α) (args : List α)
  | atom (i : Nat) (args : List α)
  deriving DecidableEq, Repr, Inhabited

namespace Fact

variable {α β : Type}

def map (f : α → β) : Fact α → Fact β
  | .le l r => .le (l.map f) (r.map f)
  | .op o x args => .op o (f x) (args.map f)
  | .atom i args => .atom i (args.map f)

def mentions [DecidableEq α] (x : α) : Fact α → Bool
  | .le l r => l.mentions x || r.mentions x
  | .op _ y args => y == x || args.contains x
  | .atom _ args => args.contains x

/-- The valuation of a term, in ℕ. -/
def nat (ν : α → Word) : α → Nat := fun x => (ν x).toNat

/-- A fact holds under a valuation, with the atoms' meaning `A`. -/
def Holds (A : Nat → List Word → Prop) (ν : α → Word) : Fact α → Prop
  | .le l r => l.eval (nat ν) ≤ r.eval (nat ν)
  | .op o x args => ν x = o.eval (args.map ν)
  | .atom i args => A i (args.map ν)

theorem holds_map (A : Nat → List Word → Prop) (ν : β → Word) (f : α → β) (φ : Fact α) :
    (φ.map f).Holds A ν ↔ φ.Holds A (ν ∘ f) := by
  cases φ <;> simp only [map, Holds, LinTerm.eval_map, List.map_map, Function.comp_def] <;> exact Iff.rfl

/-- The negation of an inequality, as an inequality. -/
def neg : Fact α → Fact α
  | .le l r => .le (r + LinTerm.ofNat 1) l
  | f => f

theorem holds_neg_le (A : Nat → List Word → Prop) (ν : α → Word) (l r : LinTerm α)
    (h : ¬ (Fact.le l r).Holds A ν) : (Fact.le l r).neg.Holds A ν := by
  simp only [Holds, neg, LinTerm.eval_add, LinTerm.eval_ofNat] at h ⊢; omega

end Fact

/-! ## Model rules -/

/-- A rule over variables `0, 1, …`: its premises entail its conclusions, whatever the
    variables stand for. A model supplies rules about its atoms. -/
structure Rule where
  prems : List (Fact Nat)
  concls : List (Fact Nat)
  deriving Repr

def Rule.Sound (A : Nat → List Word → Prop) (r : Rule) : Prop :=
  ∀ ν : Nat → Word, (∀ f ∈ r.prems, f.Holds A ν) → ∀ f ∈ r.concls, f.Holds A ν

/-! ## Certificates -/

/-- A reference to a fact the certificate uses: a hypothesis by index, or the upper bound of
    a value (`x ≤ 2^64 - 1`). -/
inductive Ref (α : Type) where
  | hyp (i : Nat)
  | ub (x : α)
  deriving DecidableEq, Repr

/-- The built-in consequences of operations. -/
inductive Builtin where
  /-- `x = u + v` and `u + v ≤ 2^64 - 1`: `x` is the sum. -/
  | addNoWrap
  /-- `x = u + v` and `u ≤ x`: `x` is the sum. -/
  | addLow
  /-- `x = u - v` and `v ≤ u`: `x + v = u`. -/
  | subNoWrap
  /-- `x = u << c` and `u·2^c ≤ 2^64 - 1`: `x = u·2^c`. -/
  | shlNoWrap
  /-- `x = u >> c`: `x·2^c ≤ u`. -/
  | shrBound
  /-- `x = sltu u v`: `x ≤ 1`. -/
  | sltuLe
  /-- `x = sltu u v` and `u + 1 ≤ v`: `1 ≤ x`. -/
  | sltuTrue
  /-- `x = sltu u v` and `v ≤ u`: `x ≤ 0`. -/
  | sltuFalse
  /-- `x = u & v`: `x ≤ u` and `x ≤ v`. -/
  | andBound
  /-- Two applications of the same operation to the same arguments: equal results. -/
  | det
  deriving DecidableEq, Repr

inductive Proof (α : Type) where
  /-- `l ≤ r` from the combination `Σ mᵢ·refᵢ`. -/
  | farkas (l r : LinTerm α) (ms : List (Ref α × Nat))
  /-- `goal` under `l ≤ r` (by `p1`) and under `r + 1 ≤ l` (by `p2`). -/
  | split (l r : LinTerm α) (p1 p2 : List (Proof α)) (goal : Fact α)
  /-- A built-in consequence of the referenced facts. -/
  | builtin (b : Builtin) (refs : List (Ref α))
  /-- Rule `i` of the model, with its variables standing for `subst`, its premises the
      referenced facts. -/
  | rule (i : Nat) (subst : List α) (prems : List (Ref α))
  deriving Repr

variable {α : Type} [DecidableEq α] [Inhabited α]

def ubFact (x : α) : Fact α := .le (LinTerm.var x) (LinTerm.ofNat (2 ^ 64 - 1))

def Ref.get (facts : List (Fact α)) : Ref α → Option (Fact α)
  | .hyp i => facts[i]?
  | .ub x => some (ubFact x)

/-- The combination `Σ m·(l, r)` of inequalities. -/
def combine (facts : List (Fact α)) : List (Ref α × Nat) → Option (LinTerm α × LinTerm α)
  | [] => some (LinTerm.ofNat 0, LinTerm.ofNat 0)
  | (rf, m) :: rest => do
    let (a, b) ← combine facts rest
    match rf.get facts with
    | some (.le l r) => some (a + l.smul m, b + r.smul m)
    | _ => none

/-- A built-in step on the fetched facts. -/
def Builtin.runOn (b : Builtin) (gs : List (Option (Fact α))) : Option (List (Fact α)) :=
  let v := LinTerm.var (α := α)
  let n := LinTerm.ofNat (α := α)
  match b, gs with
  | .addNoWrap, [some (.op .add x [u, w]), some (.le l r)] =>
    if l == v u + v w && r == n (2 ^ 64 - 1) then some [.le (v x) (v u + v w), .le (v u + v w) (v x)]
    else none
  | .addLow, [some (.op .add x [u, w]), some (.le l r)] =>
    if l == v u && r == v x then some [.le (v x) (v u + v w), .le (v u + v w) (v x)] else none
  | .subNoWrap, [some (.op .sub x [u, w]), some (.le l r)] =>
    if l == v w && r == v u then some [.le (v x + v w) (v u), .le (v u) (v x + v w)] else none
  | .shlNoWrap, [some (.op (.shl c) x [u]), some (.le l r)] =>
    if l == (v u).smul (2 ^ c) && r == n (2 ^ 64 - 1) then
      some [.le (v x) ((v u).smul (2 ^ c)), .le ((v u).smul (2 ^ c)) (v x)]
    else none
  | .shrBound, [some (.op (.shr c) x [u])] => some [.le ((v x).smul (2 ^ c)) (v u)]
  | .sltuLe, [some (.op .sltu x [_, _])] => some [.le (v x) (n 1)]
  | .sltuTrue, [some (.op .sltu x [u, w]), some (.le l r)] =>
    if l == v u + n 1 && r == v w then some [.le (n 1) (v x)] else none
  | .sltuFalse, [some (.op .sltu x [u, w]), some (.le l r)] =>
    if l == v w && r == v u then some [.le (v x) (n 0)] else none
  | .andBound, [some (.op .and x [u, w])] => some [.le (v x) (v u), .le (v x) (v w)]
  | .det, [some (.op o x args), some (.op o' y args')] =>
    if o == o' && args == args' then some [.le (v x) (v y), .le (v y) (v x)] else none
  | _, _ => none

def Builtin.run (facts : List (Fact α)) (b : Builtin) (refs : List (Ref α)) :
    Option (List (Fact α)) :=
  b.runOn (refs.map (·.get facts))

mutual

/-- Run a certificate: the facts it adds. -/
def Proof.run (rules : List Rule) (facts : List (Fact α)) : Proof α → Option (List (Fact α))
  | .farkas l r ms => do
    let (a, b) ← combine facts ms
    if (l + b).leq (r + a) then some [.le l r] else none
  | .split l r p1 p2 goal => do
    let f1 ← Proof.runAll rules (facts ++ [.le l r]) p1
    let f2 ← Proof.runAll rules (facts ++ [(Fact.le l r).neg]) p2
    if f1.contains goal && f2.contains goal then some [goal] else none
  | .builtin b refs => b.run facts refs
  | .rule i subst prems => do
    let r ← rules[i]?
    let sub : Nat → α := fun j => subst.getD j default
    if prems.map (·.get facts) == r.prems.map (fun f => some (f.map sub)) then
      some (r.concls.map (·.map sub))
    else none

/-- Run certificates in order, each seeing what the earlier ones added. -/
def Proof.runAll (rules : List Rule) (facts : List (Fact α)) :
    List (Proof α) → Option (List (Fact α))
  | [] => some facts
  | p :: ps => do
    let new ← p.run rules facts
    Proof.runAll rules (facts ++ new) ps

end

/-- `goal` follows from `facts` by the certificate. -/
def entails (rules : List Rule) (facts : List (Fact α)) (pfs : List (Proof α)) (goal : Fact α) :
    Bool :=
  match Proof.runAll rules facts pfs with
  | some facts' => facts'.contains goal
  | none => false

/-- The facts are contradictory, by the certificate. -/
def refutes (rules : List Rule) (facts : List (Fact α)) (pfs : List (Proof α)) : Bool :=
  entails rules facts pfs (.le (LinTerm.ofNat 1) (LinTerm.ofNat 0))

/-! ## Soundness -/

section Sound

variable {A : Nat → List Word → Prop} {ν : α → Word}

omit [DecidableEq α] [Inhabited α] in
theorem ubFact_holds (x : α) : (ubFact x).Holds A ν := by
  simp only [ubFact, Fact.Holds, LinTerm.eval_var, LinTerm.eval_ofNat, Fact.nat]
  have := (ν x).isLt; omega

omit [DecidableEq α] [Inhabited α] in
theorem Ref.get_holds {facts : List (Fact α)} (hf : ∀ f ∈ facts, f.Holds A ν) {rf : Ref α}
    {f : Fact α} (h : rf.get facts = some f) : f.Holds A ν := by
  cases rf with
  | hyp i => exact hf f (List.mem_of_getElem? h)
  | ub x => simp only [Ref.get, Option.some.injEq] at h; rw [← h]; exact ubFact_holds x

omit [DecidableEq α] [Inhabited α] in
theorem combine_sound {facts : List (Fact α)} (hf : ∀ f ∈ facts, f.Holds A ν) :
    ∀ {ms : List (Ref α × Nat)} {a b : LinTerm α}, combine facts ms = some (a, b) →
      a.eval (Fact.nat ν) ≤ b.eval (Fact.nat ν)
  | [], a, b, h => by
    simp only [combine, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp
  | (rf, m) :: rest, a, b, h => by
    simp only [combine, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨a', b'⟩, hrest, h⟩ := h
    have ih := combine_sound hf hrest
    split at h
    · rename_i l r hget
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hl := Ref.get_holds hf hget
      simp only [Fact.Holds] at hl
      simp only [LinTerm.eval_add, LinTerm.eval_smul]
      exact Nat.add_le_add ih (Nat.mul_le_mul_left _ hl)
    · exact absurd h (by simp)

/-- The fetched facts hold. -/
def GsOk (A : Nat → List Word → Prop) (ν : α → Word) (gs : List (Option (Fact α))) : Prop :=
  ∀ g ∈ gs, ∀ f, g = some f → f.Holds A ν

/-- The evaluation of the facts a built-in step matches and produces. -/
macro "bsimp" : tactic => `(tactic| simp only [Fact.Holds, Op.eval, List.map_cons, List.map_nil,
  LinTerm.eval_add, LinTerm.eval_var, LinTerm.eval_ofNat, LinTerm.eval_smul, Fact.nat] at *)

omit [Inhabited α] in
theorem Builtin.runOn_sound {gs : List (Option (Fact α))} (hg : GsOk A ν gs) {b : Builtin}
    {new : List (Fact α)} (h : b.runOn gs = some new) : ∀ f ∈ new, f.Holds A ν := by
  unfold Builtin.runOn at h
  simp only at h
  split at h
  · rename_i x u w l r
    split at h
    · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at h; subst h
      have h1 := hg _ (List.mem_cons_self ..) _ rfl
      have h2 := hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ rfl
      bsimp
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;> bsimp <;> rw [h1] <;> bv_omega
    · simp only [reduceCtorEq] at h
  · rename_i x u w l r
    split at h
    · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at h; subst h
      have h1 := hg _ (List.mem_cons_self ..) _ rfl
      have h2 := hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ rfl
      bsimp
      rw [h1] at h2
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;> bsimp <;> rw [h1] <;> bv_omega
    · simp only [reduceCtorEq] at h
  · rename_i x u w l r
    split at h
    · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at h; subst h
      have h1 := hg _ (List.mem_cons_self ..) _ rfl
      have h2 := hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ rfl
      bsimp
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;> bsimp <;> rw [h1] <;> bv_omega
    · simp only [reduceCtorEq] at h
  · rename_i c x u l r
    split at h
    · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at h; subst h
      have h1 := hg _ (List.mem_cons_self ..) _ rfl
      have h2 := hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ rfl
      bsimp
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rw [Nat.mul_comm] at h2
      rcases hf with rfl | rfl <;> bsimp <;>
        rw [h1, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega), Nat.mul_comm] <;>
        exact Nat.le_refl _
    · simp only [reduceCtorEq] at h
  · rename_i c x u
    simp only [Option.some.injEq] at h; subst h
    have h1 := hg _ (List.mem_cons_self ..) _ rfl
    bsimp
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    bsimp
    rw [h1, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  · rename_i x u w
    simp only [Option.some.injEq] at h; subst h
    have h1 := hg _ (List.mem_cons_self ..) _ rfl
    bsimp
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    bsimp
    rw [h1]; split <;> simp
  · rename_i x u w l r
    split at h
    · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at h; subst h
      have h1 := hg _ (List.mem_cons_self ..) _ rfl
      have h2 := hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ rfl
      bsimp
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf
      bsimp
      rw [h1]; split
      · simp
      · rename_i hlt; rw [BitVec.lt_def] at hlt; omega
    · simp only [reduceCtorEq] at h
  · rename_i x u w l r
    split at h
    · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at h; subst h
      have h1 := hg _ (List.mem_cons_self ..) _ rfl
      have h2 := hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ rfl
      bsimp
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      subst hf
      bsimp
      rw [h1]; split
      · rename_i hlt; rw [BitVec.lt_def] at hlt; omega
      · simp
    · simp only [reduceCtorEq] at h
  · rename_i x u w
    simp only [Option.some.injEq] at h; subst h
    have h1 := hg _ (List.mem_cons_self ..) _ rfl
    bsimp
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;> bsimp <;> rw [h1, BitVec.toNat_and]
    · exact Nat.and_le_left
    · exact Nat.and_le_right
  · rename_i o x args o' y args'
    split at h
    · rename_i hc; simp only [Bool.and_eq_true, beq_iff_eq] at hc; obtain ⟨rfl, rfl⟩ := hc
      simp only [Option.some.injEq] at h; subst h
      have h1 := hg _ (List.mem_cons_self ..) _ rfl
      have h2 := hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ rfl
      simp only [Fact.Holds] at h1 h2
      intro f hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl <;> bsimp <;> rw [h1, h2] <;> exact Nat.le_refl _
    · simp only [reduceCtorEq] at h
  · simp only [reduceCtorEq] at h

omit [Inhabited α] in
theorem Builtin.run_sound {facts : List (Fact α)} (hf : ∀ f ∈ facts, f.Holds A ν) {b : Builtin}
    {refs : List (Ref α)} {new : List (Fact α)} (h : b.run facts refs = some new) :
    ∀ f ∈ new, f.Holds A ν :=
  Builtin.runOn_sound (fun g hg f hgf => by
    simp only [List.mem_map] at hg
    obtain ⟨rf, _, rfl⟩ := hg
    exact Ref.get_holds hf hgf) h

theorem rule_sound {rules : List Rule} (hr : ∀ r ∈ rules, r.Sound A) {facts : List (Fact α)}
    (hf : ∀ f ∈ facts, f.Holds A ν) {i : Nat} {subst : List α} {prems : List (Ref α)}
    {new : List (Fact α)} (h : Proof.run rules facts (.rule i subst prems) = some new) :
    ∀ f ∈ new, f.Holds A ν := by
  simp only [Proof.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨r, hri, h⟩ := h
  split at h
  · rename_i hp
    simp only [Option.some.injEq] at h
    subst h
    have hrs := hr r (List.mem_of_getElem? hri) (fun j => ν (subst.getD j default))
    simp only [beq_iff_eq] at hp
    intro f hf'
    simp only [List.mem_map] at hf'
    obtain ⟨c, hc, rfl⟩ := hf'
    rw [Fact.holds_map]
    refine hrs (fun p hp' => ?_) c hc
    refine (Fact.holds_map A ν (fun j => subst.getD j default) p).mp ?_
    have : some (p.map fun j => subst.getD j default) ∈ prems.map (·.get facts) := by
      rw [hp]; exact List.mem_map.mpr ⟨p, hp', rfl⟩
    obtain ⟨rf, _, hrf⟩ := List.mem_map.mp this
    exact Ref.get_holds hf hrf
  · exact absurd h (by simp)

mutual

theorem Proof.run_sound {rules : List Rule} (hr : ∀ r ∈ rules, r.Sound A) {facts : List (Fact α)}
    (hf : ∀ f ∈ facts, f.Holds A ν) :
    ∀ {p : Proof α} {new : List (Fact α)}, p.run rules facts = some new → ∀ f ∈ new, f.Holds A ν
  | .farkas l r ms, new, h => by
    simp only [Proof.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨a, b⟩, hc, h⟩ := h
    split at h
    · rename_i hleq
      simp only [Option.some.injEq] at h
      subst h
      intro f hf'
      simp only [List.mem_singleton] at hf'
      subst hf'
      have h1 := combine_sound hf hc
      have h2 := LinTerm.leq_sound (Fact.nat ν) _ _ hleq
      simp only [LinTerm.eval_add] at h2
      simp only [Fact.Holds]; omega
    · exact absurd h (by simp)
  | .split l r p1 p2 goal, new, h => by
    simp only [Proof.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨f1, h1, f2, h2, h⟩ := h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, List.contains_iff_mem] at hc
      simp only [Option.some.injEq] at h
      subst h
      intro f hf'
      simp only [List.mem_singleton] at hf'
      subst hf'
      by_cases hle : (Fact.le l r).Holds A ν
      · have hf1 : ∀ f ∈ facts ++ [Fact.le l r], f.Holds A ν := fun f hf' => by
          simp only [List.mem_append, List.mem_singleton] at hf'
          rcases hf' with hf' | rfl
          · exact hf f hf'
          · exact hle
        exact Proof.runAll_sound hr hf1 h1 _ hc.1
      · have hf2 : ∀ f ∈ facts ++ [(Fact.le l r).neg], f.Holds A ν := fun f hf' => by
          simp only [List.mem_append, List.mem_singleton] at hf'
          rcases hf' with hf' | rfl
          · exact hf f hf'
          · exact Fact.holds_neg_le A ν l r hle
        exact Proof.runAll_sound hr hf2 h2 _ hc.2
    · exact absurd h (by simp)
  | .builtin b refs, new, h => Builtin.run_sound hf h
  | .rule i subst prems, new, h => rule_sound hr hf h

theorem Proof.runAll_sound {rules : List Rule} (hr : ∀ r ∈ rules, r.Sound A)
    {facts : List (Fact α)} (hf : ∀ f ∈ facts, f.Holds A ν) :
    ∀ {ps : List (Proof α)} {facts' : List (Fact α)}, Proof.runAll rules facts ps = some facts' →
      ∀ f ∈ facts', f.Holds A ν
  | [], facts', h => by
    simp only [Proof.runAll, Option.some.injEq] at h; subst h; exact hf
  | p :: ps, facts', h => by
    simp only [Proof.runAll, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨new, hnew, h⟩ := h
    have hn := Proof.run_sound hr hf hnew
    have hf' : ∀ f ∈ facts ++ new, f.Holds A ν := fun f hf' => by
      rcases List.mem_append.mp hf' with hf' | hf'
      · exact hf f hf'
      · exact hn f hf'
    exact Proof.runAll_sound hr hf' h

end

theorem entails_sound {rules : List Rule} (hr : ∀ r ∈ rules, r.Sound A) {facts : List (Fact α)}
    (hf : ∀ f ∈ facts, f.Holds A ν) {pfs : List (Proof α)} {goal : Fact α}
    (h : entails rules facts pfs goal = true) : goal.Holds A ν := by
  unfold entails at h
  split at h
  · rename_i facts' hrun
    exact Proof.runAll_sound hr hf hrun goal (List.contains_iff_mem.mp h)
  · exact absurd h (by simp)

theorem refutes_sound {rules : List Rule} (hr : ∀ r ∈ rules, r.Sound A) {facts : List (Fact α)}
    (hf : ∀ f ∈ facts, f.Holds A ν) {pfs : List (Proof α)}
    (h : refutes rules facts pfs = true) : False := by
  have := entails_sound hr hf h
  simp [Fact.Holds, LinTerm.eval_ofNat] at this

end Sound

end AsmVerif.RiscV.Check
