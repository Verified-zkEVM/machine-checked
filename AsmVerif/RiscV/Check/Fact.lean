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

/-- A machine operation whose exact result a fact may record. Each case evaluates as
    `execInstr` computes the instruction it stands for. -/
inductive Op where
  | add | sub | and | or | xor | sltu | slt | mul | mulhu | divu | remu
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
  | .sltu, [u, v] => if BitVec.ult u v then 1 else 0
  | .slt, [u, v] => if BitVec.slt u v then 1 else 0
  | .mul, [u, v] => u * v
  | .mulhu, [u, v] => rv64_mulhu u v
  | .divu, [u, v] => rv64_divu u v
  | .remu, [u, v] => rv64_remu u v
  | .shl c, [u] => u <<< c
  | .shr c, [u] => u >>> c
  | .sra c, [u] => u.sshiftRight c
  | .addw, [u, v] => (u.truncate 32 + v.truncate 32).signExtend 64
  | .subw, [u, v] => (u.truncate 32 - v.truncate 32).signExtend 64
  | .shlw c, [u] => (u.truncate 32 <<< c).signExtend 64
  | .shrw c, [u] => (u.truncate 32 >>> c).signExtend 64
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

/-- Rename the variables, if every one has a name. -/
def mapM (f : α → Option β) : Fact α → Option (Fact β)
  | .le l r => do
    let lc ← l.coeffs.mapM fun p => (f p.1).map fun y => (y, p.2)
    let rc ← r.coeffs.mapM fun p => (f p.1).map fun y => (y, p.2)
    pure (.le ⟨lc, l.const⟩ ⟨rc, r.const⟩)
  | .op o x args => do pure (.op o (← f x) (← args.mapM f))
  | .atom i args => do pure (.atom i (← args.mapM f))

/-- Some variable satisfies `p`. -/
def any (p : α → Bool) : Fact α → Bool
  | .le l r => l.coeffs.any (p ·.1) || r.coeffs.any (p ·.1)
  | .op _ y args => p y || args.any p
  | .atom _ args => args.any p

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

/-- Mapping over a list that `mapM` succeeded on, with a function that agrees across it. -/
theorem mapM_map_eq {f : α → Option β} {g : α → γ} {g' : β → γ}
    (hg : ∀ a b, f a = some b → g a = g' b) :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l.map g = l'.map g'
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | a :: l, l', h => by
    cases hb : f a with
    | none => rw [List.mapM_cons, hb] at h; simp at h
    | some b =>
      cases hl : l.mapM f with
      | none => rw [List.mapM_cons, hb, hl] at h; simp at h
      | some l'' =>
        rw [List.mapM_cons, hb, hl] at h
        simp at h
        subst h
        simp only [List.map_cons]
        rw [hg _ _ hb, mapM_map_eq hg hl]

/-- A fact whose variables are renamed, each to one with the same value, holds iff it did. -/
theorem holds_mapM (A : Nat → List Word → Prop) {ν : α → Word} {ν' : β → Word} {f : α → Option β}
    (hf : ∀ x y, f x = some y → ν' y = ν x) {φ : Fact α} {ψ : Fact β} (h : φ.mapM f = some ψ)
    (hψ : ψ.Holds A ν') : φ.Holds A ν := by
  have hterm : ∀ (t : LinTerm α) (tc : List (β × Nat)),
      t.coeffs.mapM (fun p => (f p.1).map fun y => (y, p.2)) = some tc →
      (LinTerm.mk tc t.const).eval (nat ν') = t.eval (nat ν) := by
    intro t tc htc
    simp only [LinTerm.eval]
    congr 1
    rw [mapM_map_eq (fun p q hpq => ?_) htc]
    simp only [Option.map_eq_some_iff] at hpq
    obtain ⟨y, hy, rfl⟩ := hpq
    simp [nat, hf _ _ hy]
  cases φ with
  | le l r =>
    cases hlc : l.coeffs.mapM (fun p => (f p.1).map fun y => (y, p.2)) with
    | none => simp [mapM, hlc] at h
    | some lc =>
    cases hrc : r.coeffs.mapM (fun p => (f p.1).map fun y => (y, p.2)) with
    | none => simp [mapM, hlc, hrc] at h
    | some rc =>
    simp [mapM, hlc, hrc] at h
    subst h
    simp only [Holds] at hψ ⊢
    rw [← hterm l lc hlc, ← hterm r rc hrc]; exact hψ
  | op o x args =>
    cases hx' : f x with
    | none => simp [mapM, hx'] at h
    | some x' =>
    cases hargs' : args.mapM f with
    | none => simp [mapM, hx', hargs'] at h
    | some args' =>
    simp [mapM, hx', hargs'] at h
    subst h
    simp only [Holds] at hψ ⊢
    rw [← hf _ _ hx', mapM_map_eq (fun a b hab => (hf a b hab).symm) hargs']
    exact hψ
  | atom i args =>
    cases hargs' : args.mapM f with
    | none => simp [mapM, hargs'] at h
    | some args' =>
    simp [mapM, hargs'] at h
    subst h
    simp only [Holds] at hψ ⊢
    rw [mapM_map_eq (fun a b hab => (hf a b hab).symm) hargs']
    exact hψ

theorem any_map (p : β → Bool) (f : α → β) (φ : Fact α) : (φ.map f).any p = φ.any (p ∘ f) := by
  cases φ <;> simp [map, any, LinTerm.map, List.any_map, Function.comp_def]

/-- Two valuations that agree on the variables of a fact give it the same truth. -/
theorem holds_congr (A : Nat → List Word → Prop) {ν ν' : α → Word} (p : α → Bool)
    (hν : ∀ x, p x = false → ν x = ν' x) {φ : Fact α} (hφ : φ.any p = false) :
    φ.Holds A ν ↔ φ.Holds A ν' := by
  have hterm : ∀ t : LinTerm α, t.coeffs.any (p ·.1) = false → t.eval (nat ν) = t.eval (nat ν') := by
    intro t ht
    simp only [LinTerm.eval, nat]
    congr 2
    apply List.map_congr_left
    intro q hq
    have : p q.1 = false := by
      simp only [List.any_eq_false] at ht
      simpa using ht q hq
    rw [hν q.1 this]
  have hargs : ∀ args : List α, args.any p = false → args.map ν = args.map ν' := by
    intro args ha
    apply List.map_congr_left
    intro x hx
    simp only [List.any_eq_false] at ha
    exact hν x (by simpa using ha x hx)
  cases φ with
  | le l r =>
    simp only [any, Bool.or_eq_false_iff] at hφ
    simp only [Holds, hterm l hφ.1, hterm r hφ.2]
  | op o x args =>
    simp only [any, Bool.or_eq_false_iff] at hφ
    simp only [Holds, hν x hφ.1, hargs args hφ.2]
  | atom i args =>
    simp only [any] at hφ
    simp only [Holds, hargs args hφ]

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

/-- A reference to a fact the certificate uses: a hypothesis by index, the upper bound of
    a value (`x ≤ 2^64 - 1`), or an axiom of the instance (`Thy.ax`: what the values
    themselves say, a constant's value or an offset). -/
inductive Ref (α : Type) where
  | hyp (i : Nat)
  | ub (x : α)
  | ax (f : Fact α)
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
  /-- `x = u / w`, `w ≤ c` and `c ≤ w` with `c ≠ 0`: `c·x ≤ u`. -/
  | divBound
  /-- `x = u % w`, `w ≤ c` and `c ≤ w` with `c ≠ 0`: `x + 1 ≤ c` and `x ≤ u`. -/
  | remBound
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
  /-- Rule `i` of the theory, with its variables standing for `subst`, its premises the
      referenced facts. -/
  | rule (i : Nat) (subst : List α) (prems : List (Ref α))
  deriving Repr

/-- What certificates may use besides the facts: a model's rules, and the instance's
    axioms (facts true of the values by what they are). -/
structure Thy (α : Type) where
  rules : List Rule := []
  ax : Fact α → Bool := fun _ => false

variable {α : Type} [DecidableEq α] [Inhabited α]

def ubFact (x : α) : Fact α := .le (LinTerm.var x) (LinTerm.ofNat (2 ^ 64 - 1))

def Ref.get (T : Thy α) (facts : List (Fact α)) : Ref α → Option (Fact α)
  | .hyp i => facts[i]?
  | .ub x => some (ubFact x)
  | .ax f => if T.ax f then some f else none

/-- The combination `Σ m·(l, r)` of inequalities. -/
def combine (T : Thy α) (facts : List (Fact α)) : List (Ref α × Nat) → Option (LinTerm α × LinTerm α)
  | [] => some (LinTerm.ofNat 0, LinTerm.ofNat 0)
  | (rf, m) :: rest => do
    let (a, b) ← combine T facts rest
    match rf.get T facts with
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
  | .divBound, [some (.op .divu x [u, w]), some (.le l1 r1), some (.le l2 r2)] =>
    match r1.coeffs, l2.coeffs with
    | [], [] =>
      if l1 == v w && r2 == v w && r1.const == l2.const && r1.const != 0 then
        some [.le ((v x).smul r1.const) (v u)]
      else none
    | _, _ => none
  | .remBound, [some (.op .remu x [u, w]), some (.le l1 r1), some (.le l2 r2)] =>
    match r1.coeffs, l2.coeffs with
    | [], [] =>
      if l1 == v w && r2 == v w && r1.const == l2.const && r1.const != 0 then
        some [.le (v x + n 1) (n r1.const), .le (v x) (v u)]
      else none
    | _, _ => none
  | .sltuLe, [some (.op .sltu x [_, _])] => some [.le (v x) (n 1)]
  | .sltuTrue, [some (.op .sltu x [u, w]), some (.le l r)] =>
    if l == v u + n 1 && r == v w then some [.le (n 1) (v x)] else none
  | .sltuFalse, [some (.op .sltu x [u, w]), some (.le l r)] =>
    if l == v w && r == v u then some [.le (v x) (n 0)] else none
  | .andBound, [some (.op .and x [u, w])] => some [.le (v x) (v u), .le (v x) (v w)]
  | .det, [some (.op o x args), some (.op o' y args')] =>
    if o == o' && args == args' then some [.le (v x) (v y), .le (v y) (v x)] else none
  | _, _ => none

def Builtin.run (T : Thy α) (facts : List (Fact α)) (b : Builtin) (refs : List (Ref α)) :
    Option (List (Fact α)) :=
  b.runOn (refs.map (·.get T facts))

mutual

/-- Run a certificate: the facts it adds, or `none` if it does not apply. -/
def Proof.run (T : Thy α) (facts : List (Fact α)) : Proof α → Option (List (Fact α))
  | .farkas l r ms => do
    let (a, b) ← combine T facts ms
    if (l + b).leq (r + a) then some [.le l r] else none
  | .split l r p1 p2 goal =>
    let f1 := Proof.runAll T (facts ++ [.le l r]) p1
    let f2 := Proof.runAll T (facts ++ [(Fact.le l r).neg]) p2
    if f1.contains goal && f2.contains goal then some [goal] else none
  | .builtin b refs => b.run T facts refs
  | .rule i subst prems => do
    let r ← T.rules[i]?
    let sub : Nat → α := fun j => subst.getD j default
    if prems.map (·.get T facts) == r.prems.map (fun f => some (f.map sub)) then
      some (r.concls.map (·.map sub))
    else none

/-- Run certificates in order, each seeing what the earlier ones added; one that does not
    apply adds nothing. -/
def Proof.runAll (T : Thy α) (facts : List (Fact α)) : List (Proof α) → List (Fact α)
  | [] => facts
  | p :: ps => Proof.runAll T (facts ++ (p.run T facts).getD []) ps

end

/-- `goal` follows from `facts` by the certificate. -/
def entails (T : Thy α) (facts : List (Fact α)) (pfs : List (Proof α)) (goal : Fact α) : Bool :=
  (Proof.runAll T facts pfs).contains goal

/-- The false fact: a state whose facts contain it is unreachable. -/
def falseFact : Fact α := .le (LinTerm.ofNat 1) (LinTerm.ofNat 0)

/-- The facts are contradictory, by the certificate. -/
def refutes (T : Thy α) (facts : List (Fact α)) (pfs : List (Proof α)) : Bool :=
  entails T facts pfs falseFact

/-! ## Soundness -/

/-- The theory is sound for the atoms' meaning and the valuation. -/
def Thy.Sound (A : Nat → List Word → Prop) (ν : α → Word) (T : Thy α) : Prop :=
  (∀ r ∈ T.rules, r.Sound A) ∧ ∀ f, T.ax f = true → f.Holds A ν

section Sound

variable {A : Nat → List Word → Prop} {ν : α → Word} {T : Thy α}

omit [DecidableEq α] [Inhabited α] in
theorem ubFact_holds (x : α) : (ubFact x).Holds A ν := by
  simp only [ubFact, Fact.Holds, LinTerm.eval_var, LinTerm.eval_ofNat, Fact.nat]
  have := (ν x).isLt; omega

omit [DecidableEq α] [Inhabited α] in
theorem Ref.get_holds (hT : T.Sound A ν) {facts : List (Fact α)} (hf : ∀ f ∈ facts, f.Holds A ν)
    {rf : Ref α} {f : Fact α} (h : rf.get T facts = some f) : f.Holds A ν := by
  cases rf with
  | hyp i => exact hf f (List.mem_of_getElem? h)
  | ub x => simp only [Ref.get, Option.some.injEq] at h; rw [← h]; exact ubFact_holds x
  | ax g =>
    simp only [Ref.get] at h
    split at h
    · rename_i hax; simp only [Option.some.injEq] at h; rw [← h]; exact hT.2 g hax
    · cases h

omit [DecidableEq α] [Inhabited α] in
theorem combine_sound (hT : T.Sound A ν) {facts : List (Fact α)} (hf : ∀ f ∈ facts, f.Holds A ν) :
    ∀ {ms : List (Ref α × Nat)} {a b : LinTerm α}, combine T facts ms = some (a, b) →
      a.eval (Fact.nat ν) ≤ b.eval (Fact.nat ν)
  | [], a, b, h => by
    simp only [combine, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp
  | (rf, m) :: rest, a, b, h => by
    simp only [combine, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨a', b'⟩, hrest, h⟩ := h
    have ih := combine_sound hT hf hrest
    split at h
    · rename_i l r hget
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hl := Ref.get_holds hT hf hget
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

omit [DecidableEq α] [Inhabited α] in
theorem const_eval {t : LinTerm α} (h : t.coeffs = []) (μ : α → Nat) : t.eval μ = t.const := by
  simp [LinTerm.eval, h]

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
  · rename_i x u w l1 r1 l2 r2
    split at h
    · rename_i hr1 hl2
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
        obtain ⟨⟨⟨rfl, rfl⟩, hcc⟩, hc0⟩ := hc
        simp only [Option.some.injEq] at h; subst h
        have h1 := hg _ (List.mem_cons_self ..) _ rfl
        have h2 := hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ rfl
        have h3 := hg _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _ rfl
        bsimp
        rw [const_eval hr1] at h2; rw [const_eval hl2, ← hcc] at h3
        intro f hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        subst hf
        bsimp
        have hw : (ν w).toNat = r1.const := by omega
        rw [h1, rv64_divu, if_neg (by simp [BitVec.toNat_eq] at hc0 ⊢; omega),
          BitVec.toNat_udiv, hw, Nat.mul_comm]
        exact Nat.div_mul_le_self _ _
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  · rename_i x u w l1 r1 l2 r2
    split at h
    · rename_i hr1 hl2
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
        obtain ⟨⟨⟨rfl, rfl⟩, hcc⟩, hc0⟩ := hc
        simp only [Option.some.injEq] at h; subst h
        have h1 := hg _ (List.mem_cons_self ..) _ rfl
        have h2 := hg _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ rfl
        have h3 := hg _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) _ rfl
        bsimp
        rw [const_eval hr1] at h2; rw [const_eval hl2, ← hcc] at h3
        have hw : (ν w).toNat = r1.const := by omega
        have hne : ¬ (ν w == 0#64) = true := by
          simp only [beq_iff_eq, BitVec.toNat_eq, BitVec.toNat_ofNat, Nat.zero_mod]; omega
        intro f hf
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl <;> bsimp <;> rw [h1, rv64_remu, if_neg hne, BitVec.toNat_umod, hw]
        · have := Nat.mod_lt (ν u).toNat (Nat.pos_of_ne_zero hc0); omega
        · exact Nat.mod_le _ _
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
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
      · rename_i hlt; rw [BitVec.ult_iff_lt, BitVec.lt_def] at hlt; omega
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
      · rename_i hlt; rw [BitVec.ult_iff_lt, BitVec.lt_def] at hlt; omega
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
theorem Builtin.run_sound (hT : T.Sound A ν) {facts : List (Fact α)} (hf : ∀ f ∈ facts, f.Holds A ν)
    {b : Builtin} {refs : List (Ref α)} {new : List (Fact α)} (h : b.run T facts refs = some new) :
    ∀ f ∈ new, f.Holds A ν :=
  Builtin.runOn_sound (fun g hg f hgf => by
    simp only [List.mem_map] at hg
    obtain ⟨rf, _, rfl⟩ := hg
    exact Ref.get_holds hT hf hgf) h

theorem rule_sound (hT : T.Sound A ν) {facts : List (Fact α)}
    (hf : ∀ f ∈ facts, f.Holds A ν) {i : Nat} {subst : List α} {prems : List (Ref α)}
    {new : List (Fact α)} (h : Proof.run T facts (.rule i subst prems) = some new) :
    ∀ f ∈ new, f.Holds A ν := by
  simp only [Proof.run, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨r, hri, h⟩ := h
  split at h
  · rename_i hp
    simp only [Option.some.injEq] at h
    subst h
    have hrs := hT.1 r (List.mem_of_getElem? hri) (fun j => ν (subst.getD j default))
    simp only [beq_iff_eq] at hp
    intro f hf'
    simp only [List.mem_map] at hf'
    obtain ⟨c, hc, rfl⟩ := hf'
    rw [Fact.holds_map]
    refine hrs (fun p hp' => ?_) c hc
    refine (Fact.holds_map A ν (fun j => subst.getD j default) p).mp ?_
    have : some (p.map fun j => subst.getD j default) ∈ prems.map (·.get T facts) := by
      rw [hp]; exact List.mem_map.mpr ⟨p, hp', rfl⟩
    obtain ⟨rf, _, hrf⟩ := List.mem_map.mp this
    exact Ref.get_holds hT hf hrf
  · exact absurd h (by simp)

mutual

theorem Proof.run_sound (hT : T.Sound A ν) {facts : List (Fact α)}
    (hf : ∀ f ∈ facts, f.Holds A ν) :
    ∀ {p : Proof α} {new : List (Fact α)}, p.run T facts = some new → ∀ f ∈ new, f.Holds A ν
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
      have h1 := combine_sound hT hf hc
      have h2 := LinTerm.leq_sound (Fact.nat ν) _ _ hleq
      simp only [LinTerm.eval_add] at h2
      simp only [Fact.Holds]; omega
    · exact absurd h (by simp)
  | .split l r p1 p2 goal, new, h => by
    simp only [Proof.run] at h
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
        exact Proof.runAll_sound hT hf1 (ps := p1) _ hc.1
      · have hf2 : ∀ f ∈ facts ++ [(Fact.le l r).neg], f.Holds A ν := fun f hf' => by
          simp only [List.mem_append, List.mem_singleton] at hf'
          rcases hf' with hf' | rfl
          · exact hf f hf'
          · exact Fact.holds_neg_le A ν l r hle
        exact Proof.runAll_sound hT hf2 (ps := p2) _ hc.2
    · exact absurd h (by simp)
  | .builtin b refs, new, h => Builtin.run_sound hT hf h
  | .rule i subst prems, new, h => rule_sound hT hf h

theorem Proof.runAll_sound (hT : T.Sound A ν) {facts : List (Fact α)}
    (hf : ∀ f ∈ facts, f.Holds A ν) :
    ∀ {ps : List (Proof α)}, ∀ f ∈ Proof.runAll T facts ps, f.Holds A ν
  | [] => by simp only [Proof.runAll]; exact hf
  | p :: ps => by
    simp only [Proof.runAll]
    have hf' : ∀ f ∈ facts ++ (p.run T facts).getD [], f.Holds A ν := fun f hf' => by
      rcases List.mem_append.mp hf' with hf' | hf'
      · exact hf f hf'
      · cases hrun : p.run T facts with
        | none => rw [hrun] at hf'; simp at hf'
        | some new => rw [hrun] at hf'; exact Proof.run_sound hT hf hrun f hf'
    exact Proof.runAll_sound hT hf'

end

theorem entails_sound (hT : T.Sound A ν) {facts : List (Fact α)}
    (hf : ∀ f ∈ facts, f.Holds A ν) {pfs : List (Proof α)} {goal : Fact α}
    (h : entails T facts pfs goal = true) : goal.Holds A ν :=
  Proof.runAll_sound hT hf goal (List.contains_iff_mem.mp h)

omit [DecidableEq α] [Inhabited α] in
theorem falseFact_false : ¬ (falseFact (α := α)).Holds A ν := by
  simp [falseFact, Fact.Holds, LinTerm.eval_ofNat]

theorem refutes_sound (hT : T.Sound A ν) {facts : List (Fact α)}
    (hf : ∀ f ∈ facts, f.Holds A ν) {pfs : List (Proof α)}
    (h : refutes T facts pfs = true) : False :=
  falseFact_false (entails_sound hT hf h)

end Sound

end AsmVerif.RiscV.Check
