/-
  AsmVerif.RiscV.Check.Model

  Typed resources. A program's `Env` may name a `Model` of *writers*: memory objects a
  function is handed by pointer (`p`) whose *kind* (`k`, a vtable address) determines a
  typing predicate over memory, `writerOk k p m`. An interface lists the writers it is
  lent (`Iface.strs`); its precondition asks that they be well-typed, its postcondition
  gives them back well-typed. What the checker needs of a model is abstract:

    * `hit k p m`: the keys the writer's typing may depend on and that a function it is
      lent may rewrite (a `String`'s header and the heap it lives in; a `Cursor`'s buffer).
      The precondition says a lent writer's `hit` keys are none the function writes itself,
      so its own stores keep every writer well-typed (`writerOk_congr`).
    * `stable k p m`: `hit` keys no function changes (a wrapper's pointer to the writer it
      wraps). A callee gives them back unchanged, so the caller's abstract values loaded
      through them stay valid across the call.
    * `sub k`: for a *structural* kind, the sub-writer it wraps, found by following paths
      of loads from `p`; `writerOk` is then exactly the sub-writer's typing (`sub_elim`/
      `sub_intro`), and `hit`/`stable` add the paths' keys (`hit_struct`/`stable_struct`).
      A checked function can thus build a wrapper around a writer it was lent, in its own
      frame, and lend the wrapper on; and a wrapper's own code reaches the writer it wraps.

  Everything is stated for arbitrary memories; a model's lemmas are its author's burden.
  `Model.trivial` has no writers and is the default.
-/

import AsmVerif.RiscV.Frame.Domain

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame

def Aligned (a : Word) : Prop := a &&& 7#64 = 0

/-- Follow a path of loads in memory `m` from `a`: each `k` loads the doubleword at `· + k`. -/
def derefM (m : Word → Word) : Word → List Word → Word
  | a, [] => a
  | a, k :: ks => derefM m (m (a + k)) ks

/-- The keys a path of loads reads. -/
def pathKeys (m : Word → Word) : Word → List Word → List Word
  | _, [] => []
  | a, k :: ks => (a + k) :: pathKeys m (m (a + k)) ks

theorem Ent.deref_eq (E : Ent) (a : Word) (ks : List Word) : E.deref a ks = derefM E.mem a ks := by
  induction ks generalizing a with
  | nil => rfl
  | cons k ks ih => simp [Ent.deref, derefM, ih]

theorem derefM_append (m : Word → Word) (a : Word) (ks : List Word) (k : Word) :
    derefM m a (ks ++ [k]) = m (derefM m a ks + k) := by
  induction ks generalizing a with
  | nil => rfl
  | cons k' ks ih => simp [derefM, ih]

theorem derefM_congr {m m' : Word → Word} :
    ∀ {a : Word} {ks : List Word}, (∀ b ∈ pathKeys m a ks, m' b = m b) → derefM m' a ks = derefM m a ks
  | _, [], _ => rfl
  | a, k :: ks, h => by
    simp only [derefM]
    rw [h (a + k) (by simp [pathKeys])]
    exact derefM_congr fun b hb => h b (by simp [pathKeys, hb])

theorem pathKeys_congr {m m' : Word → Word} :
    ∀ {a : Word} {ks : List Word}, (∀ b ∈ pathKeys m a ks, m' b = m b) → pathKeys m' a ks = pathKeys m a ks
  | _, [], _ => rfl
  | a, k :: ks, h => by
    simp only [pathKeys]
    rw [h (a + k) (by simp [pathKeys])]
    exact congrArg _ (pathKeys_congr fun b hb => h b (by simp [pathKeys, hb]))

/-- The sub-writer of a structural kind: from the writer's pointer, the path to the
    sub-writer's pointer, the path to its kind, and the kinds it may have. -/
structure Sub where
  dp : List Word
  kp : List Word
  kinds : List Word
  deriving DecidableEq, Repr

/-- The keys of a sub-writer's two paths. -/
def Sub.keys (s : Sub) (m : Word → Word) (p : Word) : List Word :=
  pathKeys m p s.dp ++ pathKeys m p s.kp

/-- The sub-writer `s` of the writer at `p` is well-typed, of one of its kinds, and its
    paths avoid it. -/
def SubOk (writerOk : Word → Word → (Word → Word) → Prop)
    (hit : Word → Word → (Word → Word) → Word → Prop) (p : Word) (m : Word → Word) (s : Sub) :
    Prop :=
  writerOk (derefM m p s.kp) (derefM m p s.dp) m ∧ derefM m p s.kp ∈ s.kinds ∧
  ∀ a ∈ s.keys m p, Aligned a ∧ ¬ hit (derefM m p s.kp) (derefM m p s.dp) m a

structure Model where
  writerOk : Word → Word → (Word → Word) → Prop
  hit : Word → Word → (Word → Word) → Word → Prop
  stable : Word → Word → (Word → Word) → Word → Prop
  sub : Word → Option Sub
  hit_aligned : ∀ {k p m a}, hit k p m a → Aligned a
  stable_hit : ∀ {k p m a}, stable k p m a → hit k p m a
  hit_congr : ∀ {k p m m'}, (∀ a, hit k p m a → m' a = m a) → ∀ a, hit k p m' a → hit k p m a
  stable_congr : ∀ {k p m m'}, (∀ a, stable k p m a → m' a = m a) →
    ∀ a, stable k p m' a ↔ stable k p m a
  writerOk_congr : ∀ {k p m m'}, writerOk k p m → (∀ a, hit k p m a → m' a = m a) →
    writerOk k p m'
  sub_elim : ∀ {k p m s}, sub k = some s → writerOk k p m → SubOk writerOk hit p m s
  sub_intro : ∀ {k p m s}, sub k = some s → SubOk writerOk hit p m s → writerOk k p m
  hit_struct : ∀ {k p m s}, sub k = some s → ∀ a,
    hit k p m a ↔ a ∈ s.keys m p ∨ hit (derefM m p s.kp) (derefM m p s.dp) m a
  stable_struct : ∀ {k p m s}, sub k = some s → ∀ a,
    stable k p m a ↔ a ∈ s.keys m p ∨ stable (derefM m p s.kp) (derefM m p s.dp) m a

/-- No writers. -/
def Model.trivial : Model where
  writerOk _ _ _ := True
  hit _ _ _ _ := False
  stable _ _ _ _ := False
  sub _ := none
  hit_aligned h := h.elim
  stable_hit h := h
  hit_congr _ _ h := h
  stable_congr _ _ := Iff.rfl
  writerOk_congr _ _ := True.intro
  sub_elim h := nomatch h
  sub_intro h := nomatch h
  hit_struct h := nomatch h
  stable_struct h := nomatch h

namespace Model

variable {M : Model}

/-- What a function gives back about a writer it was lent, or did not touch: well-typed,
    its keys no more than before, its stable keys as they were. -/
def Keeps (M : Model) (k p : Word) (m m' : Word → Word) : Prop :=
  M.writerOk k p m' ∧ (∀ a, M.hit k p m' a → M.hit k p m a) ∧
  ∀ a, M.stable k p m a → m' a = m a

theorem Keeps.refl {k p : Word} {m : Word → Word} (h : M.writerOk k p m) : M.Keeps k p m m :=
  ⟨h, fun _ h => h, fun _ _ => rfl⟩

theorem Keeps.stable_iff {k p : Word} {m m' : Word → Word} (h : M.Keeps k p m m') (a : Word) :
    M.stable k p m' a ↔ M.stable k p m a :=
  M.stable_congr h.2.2 a

theorem Keeps.trans {k p : Word} {m m' m'' : Word → Word} (h1 : M.Keeps k p m m')
    (h2 : M.Keeps k p m' m'') : M.Keeps k p m m'' :=
  ⟨h2.1, fun a ha => h1.2.1 a (h2.2.1 a ha),
   fun a ha => (h2.2.2 a ((h1.stable_iff a).mpr ha)).trans (h1.2.2 a ha)⟩

/-- A memory that agrees with `m` on the writer's keys keeps it. -/
theorem Keeps.of_congr {k p : Word} {m m' : Word → Word} (hw : M.writerOk k p m)
    (h : ∀ a, M.hit k p m a → m' a = m a) : M.Keeps k p m m' :=
  ⟨M.writerOk_congr hw h, M.hit_congr h, fun a ha => h a (M.stable_hit ha)⟩

/-- Keeping, then changing nothing on the writer's keys, keeps. -/
theorem Keeps.congr {k p : Word} {m m' m'' : Word → Word} (h : M.Keeps k p m m')
    (hc : ∀ a, M.hit k p m a → m'' a = m' a) : M.Keeps k p m m'' :=
  h.trans (Keeps.of_congr h.1 fun a ha => hc a (h.2.1 a ha))

end Model

end AsmVerif.RiscV.Check
