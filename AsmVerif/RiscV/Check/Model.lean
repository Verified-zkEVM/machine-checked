/-
  AsmVerif.RiscV.Check.Model

  Typed resources. A program's `Env` may name a `Model` of *writers*: memory objects a
  function is handed by pointer (`p`) whose *kind* (`k`, a vtable address or a tag)
  determines a typing predicate over memory, `writerOk k p m`. An interface lists the
  writers it is lent (`Iface.strs`); its precondition asks that they be well-typed, its
  postcondition gives them back well-typed.

  A model is a table of kinds (`Model.kinds`). A kind declares its doubleword *fields*
  (offsets from `p`), which of them are *stable* (no function lent the writer changes
  them), an *invariant* (facts over the pointer and the fields' values, with the model's
  atoms: a `String`'s length is at most its capacity and its buffer is a live heap block),
  whether its typing depends on the *heap* (then the allocator's keys are among its keys),
  and, for a *structural* kind, the writer it wraps (`Sub`: the paths from `p` to the
  wrapped writer's pointer and kind).

  From the table the checker's three predicates are defined, inductively through wrappers:
    * `hit k p m`: the keys the writer's typing may depend on and that a function it is
      lent may rewrite: its fields, the heap if it is heap-typed, its paths' keys, and the
      keys of what it wraps. The precondition says a lent writer's `hit` keys are none the
      function writes itself, so its own stores keep every writer well-typed.
    * `stable k p m`: the `hit` keys no function changes: the stable fields, the paths'
      keys, and the wrapped writer's stable keys. A callee gives them back unchanged.
    * `writerOk k p m`: the invariant holds, and what it wraps is a well-typed writer of
      one of the listed kinds, reached through aligned keys that are not its own.
  A path's keys count only up to the first unaligned one (`alKeys`): unaligned keys are
  no doubleword, and what lies past them is nobody's. The lemmas about the predicates that
  the soundness proof uses (`hit_aligned`, `hit_congr`, …) are proved here once, for every
  model. `Model.trivial` has no kinds and is the default.
-/

import Std.Tactic.BVDecide
import AsmVerif.RiscV.Frame.Domain
import AsmVerif.RiscV.Check.Fact

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame

def Aligned (a : Word) : Prop := a &&& 7#64 = 0

instance (a : Word) : Decidable (Aligned a) := inferInstanceAs (Decidable (a &&& 7#64 = 0))

/-- Follow a path of loads in memory `m` from `a`: each `k` loads the doubleword at `· + k`. -/
def derefM (m : Word → Word) : Word → List Word → Word
  | a, [] => a
  | a, k :: ks => derefM m (m (a + k)) ks

/-- The keys a path of loads reads. -/
def pathKeys (m : Word → Word) : Word → List Word → List Word
  | _, [] => []
  | a, k :: ks => (a + k) :: pathKeys m (m (a + k)) ks

/-- The keys a path reads, up to the first unaligned one. -/
def alPath (m : Word → Word) : Word → List Word → List Word
  | _, [] => []
  | a, k :: ks => if Aligned (a + k) then (a + k) :: alPath m (m (a + k)) ks else []

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

theorem alPath_aligned {m : Word → Word} :
    ∀ {a : Word} {ks : List Word} {b : Word}, b ∈ alPath m a ks → Aligned b
  | _, [], _, h => by simp [alPath] at h
  | a, k :: ks, b, h => by
    simp only [alPath] at h
    split at h
    · rename_i hal
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact hal
      · exact alPath_aligned h
    · simp at h

theorem alPath_sub {m : Word → Word} :
    ∀ {a : Word} {ks : List Word} {b : Word}, b ∈ alPath m a ks → b ∈ pathKeys m a ks
  | _, [], _, h => by simp [alPath] at h
  | a, k :: ks, b, h => by
    simp only [alPath] at h
    split at h
    · simp only [List.mem_cons, pathKeys] at h ⊢
      rcases h with rfl | h
      · exact Or.inl rfl
      · exact Or.inr (alPath_sub h)
    · simp at h

/-- A path all of whose keys are aligned has them all. -/
theorem alPath_eq {m : Word → Word} :
    ∀ {a : Word} {ks : List Word}, (∀ b ∈ pathKeys m a ks, Aligned b) → alPath m a ks = pathKeys m a ks
  | _, [], _ => rfl
  | a, k :: ks, h => by
    have h1 : Aligned (a + k) := h _ (by simp [pathKeys])
    have h2 := alPath_eq (m := m) (a := m (a + k)) (ks := ks) fun b hb => h b (by simp [pathKeys, hb])
    simp only [alPath, pathKeys, h1, ↓reduceIte, h2]

/-- A memory that agrees with `m` on the aligned keys of a path has the same aligned keys. -/
theorem alPath_congr {m m' : Word → Word} :
    ∀ {a : Word} {ks : List Word}, (∀ b ∈ alPath m a ks, m' b = m b) → alPath m' a ks = alPath m a ks
  | _, [], _ => rfl
  | a, k :: ks, h => by
    simp only [alPath]
    split
    · rename_i hal
      rw [h (a + k) (by simp [alPath, hal])]
      exact congrArg _ (alPath_congr fun b hb => h b (by simp [alPath, hal, hb]))
    · rfl

/-- …and, if the path is wholly aligned, the same path. -/
theorem path_congr {m m' : Word → Word} {a : Word} {ks : List Word}
    (hal : ∀ b ∈ pathKeys m a ks, Aligned b) (h : ∀ b ∈ alPath m a ks, m' b = m b) :
    pathKeys m' a ks = pathKeys m a ks ∧ derefM m' a ks = derefM m a ks := by
  rw [alPath_eq hal] at h
  exact ⟨pathKeys_congr h, derefM_congr h⟩

/-! ## Kinds -/

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

/-- …up to the first unaligned one. -/
def Sub.alKeys (s : Sub) (m : Word → Word) (p : Word) : List Word :=
  alPath m p s.dp ++ alPath m p s.kp

theorem Sub.alKeys_eq {s : Sub} {m : Word → Word} {p : Word} (h : ∀ b ∈ s.keys m p, Aligned b) :
    s.alKeys m p = s.keys m p := by
  simp only [Sub.alKeys, Sub.keys] at h ⊢
  rw [alPath_eq fun b hb => h b (List.mem_append_left _ hb),
    alPath_eq fun b hb => h b (List.mem_append_right _ hb)]

theorem Sub.alKeys_sub {s : Sub} {m : Word → Word} {p : Word} {b : Word} (h : b ∈ s.alKeys m p) :
    b ∈ s.keys m p := by
  simp only [Sub.alKeys, Sub.keys, List.mem_append] at h ⊢
  rcases h with h | h
  · exact Or.inl (alPath_sub h)
  · exact Or.inr (alPath_sub h)

theorem Sub.alKeys_aligned {s : Sub} {m : Word → Word} {p : Word} {b : Word} (h : b ∈ s.alKeys m p) :
    Aligned b := by
  simp only [Sub.alKeys, List.mem_append] at h
  rcases h with h | h <;> exact alPath_aligned h

theorem Sub.alKeys_congr {s : Sub} {m m' : Word → Word} {p : Word}
    (h : ∀ b ∈ s.alKeys m p, m' b = m b) : s.alKeys m' p = s.alKeys m p := by
  simp only [Sub.alKeys] at h ⊢
  rw [alPath_congr fun b hb => h b (List.mem_append_left _ hb),
    alPath_congr fun b hb => h b (List.mem_append_right _ hb)]

theorem Sub.congr {s : Sub} {m m' : Word → Word} {p : Word} (hal : ∀ b ∈ s.keys m p, Aligned b)
    (h : ∀ b ∈ s.alKeys m p, m' b = m b) :
    s.keys m' p = s.keys m p ∧ derefM m' p s.dp = derefM m p s.dp ∧ derefM m' p s.kp = derefM m p s.kp := by
  simp only [Sub.keys, Sub.alKeys] at hal h ⊢
  have h1 := path_congr (fun b hb => hal b (List.mem_append_left _ hb))
    (fun b hb => h b (List.mem_append_left _ hb))
  have h2 := path_congr (fun b hb => hal b (List.mem_append_right _ hb))
    (fun b hb => h b (List.mem_append_right _ hb))
  rw [h1.1, h2.1]
  exact ⟨rfl, h1.2, h2.2⟩

/-- A kind of writer. Its invariant's variable `0` is the pointer, `i + 1` the value of
    field `i`. -/
structure Kind where
  fields : List Word := []
  stable : List Word := []
  inv : List (Fact Nat) := []
  /-- The typing depends on the heap; the allocator's keys are the writer's. -/
  heap : Bool := false
  /-- A buffer: the fields holding its pointer and its capacity. -/
  buf : Option (Nat × Nat) := none
  sub : Option Sub := none
  deriving Repr

/-- The pointer and the fields' values, as the invariant's variables. -/
def Kind.val (kd : Kind) (p : Word) (m : Word → Word) : Nat → Word
  | 0 => p
  | i + 1 => match kd.fields[i]? with
    | some off => m (p + off)
    | none => 0

def Kind.fieldKeys (kd : Kind) (p : Word) : List Word := kd.fields.map (p + ·)

/-- A kind with no fields, no invariant and no heap: a pure wrapper, or a unit. -/
def Kind.pure (kd : Kind) : Bool := kd.fields.isEmpty && kd.inv.isEmpty && !kd.heap
def Kind.stableKeys (kd : Kind) (p : Word) : List Word := kd.stable.map (p + ·)

def Fact.isAtom : Fact Nat → Bool
  | .atom _ _ => true
  | _ => false

/-! ## Models -/

structure Model where
  kinds : Word → Option Kind
  /-- The allocator's keys: everything the heap's structure or contents live in. -/
  heap : Word → Prop
  /-- The heap keys inside allocated blocks, in a memory: the keys a buffer store may
      rewrite without changing the heap's structure. -/
  payload : (Word → Word) → Word → Prop
  /-- The atoms' meaning, in a memory. -/
  atom : Nat → List Word → (Word → Word) → Prop
  /-- Rules about the atoms, for certificates. -/
  rules : List Rule
  /-- The atoms that do not depend on memory at all. -/
  fixed : Nat → Bool := fun _ => false
  heap_aligned : ∀ a, heap a → Aligned a
  payload_heap : ∀ m a, payload m a → heap a
  /-- A memory that changes heap keys only inside allocated blocks has the same blocks. -/
  payload_keep : ∀ m m', (∀ a, heap a → m' a = m a ∨ payload m a) → ∀ a, payload m' a ↔ payload m a
  /-- …and the same atoms. -/
  atom_keep : ∀ i args m m', (∀ a, heap a → m' a = m a ∨ payload m a) → atom i args m → atom i args m'
  rules_sound : ∀ m, ∀ r ∈ rules, r.Sound (fun i args => atom i args m)
  fixed_sound : ∀ i args m m', fixed i = true → atom i args m → atom i args m'
  /-- A well-typed buffer's bytes `[ptr, ptr + cap)` lie in allocated blocks, away from
      the writer's fields. -/
  buf_sound : ∀ k kd p m, kinds k = some kd → ∀ pi ci, kd.buf = some (pi, ci) →
    (∀ f ∈ kd.inv, f.Holds (fun i args => atom i args m) (kd.val p m)) →
    ∀ a, (kd.val p m (pi + 1)).toNat ≤ a.toNat →
      a.toNat + 1 ≤ (kd.val p m (pi + 1)).toNat + (kd.val p m (ci + 1)).toNat →
      payload m (alignToDword a) ∧ alignToDword a ∉ kd.fieldKeys p
  /-- Fields are aligned; stable fields are fields; a kind with a buffer, or whose invariant
      has an atom, is heap-typed; a kind with a buffer wraps nothing. -/
  kinds_wf : ∀ k kd, kinds k = some kd →
    (∀ off ∈ kd.fields, Aligned off) ∧ (∀ off ∈ kd.stable, off ∈ kd.fields) ∧
    (kd.buf.isSome → kd.heap = true) ∧ (∀ f ∈ kd.inv, f.isAtom = true → kd.heap = true) ∧
    (∀ s, kd.sub = some s → s.dp ≠ [] ∧ ∀ off ∈ s.dp ++ s.kp, Aligned off) ∧
    (kd.buf.isSome → kd.sub = none)

namespace Model

variable (M : Model)

/-- The atoms' meaning in memory `m`. -/
def atomIn (m : Word → Word) : Nat → List Word → Prop := fun i args => M.atom i args m

def sub (k : Word) : Option Sub := (M.kinds k).bind Kind.sub

/-- A writer's own keys: its fields, the heap if heap-typed, its paths' keys. -/
def Own (kd : Kind) (p : Word) (m : Word → Word) (a : Word) : Prop :=
  (a ∈ kd.fieldKeys p ∧ Aligned a) ∨ (kd.heap = true ∧ M.heap a) ∨
  (∃ s, kd.sub = some s ∧ a ∈ s.alKeys m p)

/-- A writer's own stable keys: its stable fields, its paths' keys. -/
def OwnStable (kd : Kind) (p : Word) (m : Word → Word) (a : Word) : Prop :=
  (a ∈ kd.stableKeys p ∧ Aligned a) ∨ (∃ s, kd.sub = some s ∧ a ∈ s.alKeys m p)

/-- The keys a function lent the writer may rewrite. -/
inductive Hit : Word → Word → (Word → Word) → Word → Prop where
  | own {k p m a kd} (hk : M.kinds k = some kd) (h : M.Own kd p m a) : Hit k p m a
  | sub {k p m a kd s} (hk : M.kinds k = some kd) (hs : kd.sub = some s)
      (hal : ∀ b ∈ s.keys m p, Aligned b)
      (h : Hit (derefM m p s.kp) (derefM m p s.dp) m a) : Hit k p m a

/-- The keys every function keeps. -/
inductive Stable : Word → Word → (Word → Word) → Word → Prop where
  | own {k p m a kd} (hk : M.kinds k = some kd) (h : OwnStable kd p m a) : Stable k p m a
  | sub {k p m a kd s} (hk : M.kinds k = some kd) (hs : kd.sub = some s)
      (hal : ∀ b ∈ s.keys m p, Aligned b)
      (h : Stable (derefM m p s.kp) (derefM m p s.dp) m a) : Stable k p m a

/-- The field keys of the writer and of what it wraps. -/
inductive Fields : Word → Word → (Word → Word) → Word → Prop where
  | own {k p m a kd} (hk : M.kinds k = some kd) (h : a ∈ kd.fieldKeys p) (hal : Aligned a) :
      Fields k p m a
  | sub {k p m a kd s} (hk : M.kinds k = some kd) (hs : kd.sub = some s)
      (hal : ∀ b ∈ s.keys m p, Aligned b)
      (h : Fields (derefM m p s.kp) (derefM m p s.dp) m a) : Fields k p m a

/-- Well-typed: the invariant holds, and what the writer wraps is a well-typed writer of
    one of the listed kinds, reached through aligned keys that are not its own. -/
inductive WriterOk : Word → Word → (Word → Word) → Prop where
  | mk {k p m kd} (hk : M.kinds k = some kd) (hal : Aligned p)
      (hinv : ∀ f ∈ kd.inv, f.Holds (M.atomIn m) (kd.val p m))
      (hsub : ∀ s, kd.sub = some s → WriterOk (derefM m p s.kp) (derefM m p s.dp) m)
      (hkind : ∀ s, kd.sub = some s → derefM m p s.kp ∈ s.kinds)
      (hkeys : ∀ s, kd.sub = some s → ∀ a ∈ s.keys m p,
        Aligned a ∧ ¬ M.Hit (derefM m p s.kp) (derefM m p s.dp) m a) :
      WriterOk k p m

abbrev hit := M.Hit
abbrev stable := M.Stable
abbrev writerOk := M.WriterOk
abbrev fields := M.Fields

/-- A field key is a hit key. -/
theorem fields_hit {M : Model} {k p : Word} {m : Word → Word} {a : Word} (h : M.Fields k p m a) :
    M.Hit k p m a := by
  induction h with
  | own hk h hal => exact .own hk (Or.inl ⟨h, hal⟩)
  | sub hk hs hal _ ih => exact .sub hk hs hal ih

/-- A hit key is a field key, a stable key, or a heap key. -/
theorem hit_fields_stable_heap {M : Model} {k p : Word} {m : Word → Word} {a : Word}
    (h : M.Hit k p m a) : M.Fields k p m a ∨ M.Stable k p m a ∨ M.heap a := by
  induction h with
  | own hk ho =>
    rcases ho with ⟨h, hal⟩ | ⟨_, hh⟩ | ⟨s, hs, h⟩
    · exact Or.inl (.own hk h hal)
    · exact Or.inr (Or.inr hh)
    · exact Or.inr (Or.inl (.own hk (Or.inr ⟨s, hs, h⟩)))
  | sub hk hs hal _ ih =>
    rcases ih with ih | ih | ih
    · exact Or.inl (.sub hk hs hal ih)
    · exact Or.inr (Or.inl (.sub hk hs hal ih))
    · exact Or.inr (Or.inr ih)

/-- An atom depends on the heap's keys only. -/
theorem atom_congr (i : Nat) (args : List Word) (m m' : Word → Word)
    (h : ∀ a, M.heap a → m' a = m a) (ha : M.atom i args m) : M.atom i args m' :=
  M.atom_keep i args m m' (fun a ha => Or.inl (h a ha)) ha

/-- The sub-writer `s` of the writer at `p` is well-typed, of one of its kinds, and its
    paths avoid it. -/
def SubOk (p : Word) (m : Word → Word) (s : Sub) : Prop :=
  M.writerOk (derefM m p s.kp) (derefM m p s.dp) m ∧ derefM m p s.kp ∈ s.kinds ∧
  ∀ a ∈ s.keys m p, Aligned a ∧ ¬ M.hit (derefM m p s.kp) (derefM m p s.dp) m a

/-! ### The lemmas the checker's soundness uses -/

variable {M}

theorem own_aligned {kd : Kind} {p : Word} {m : Word → Word} {a : Word} (h : M.Own kd p m a) :
    Aligned a := by
  rcases h with ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩
  · exact h
  · exact M.heap_aligned a h
  · exact Sub.alKeys_aligned h

theorem ownStable_own {k : Word} {kd : Kind} (hk : M.kinds k = some kd) {p : Word} {m : Word → Word}
    {a : Word} (h : OwnStable kd p m a) : M.Own kd p m a := by
  rcases h with ⟨h, hal⟩ | h
  · refine Or.inl ⟨?_, hal⟩
    simp only [Kind.stableKeys, List.mem_map] at h
    obtain ⟨off, hoff, rfl⟩ := h
    exact List.mem_map.mpr ⟨off, (M.kinds_wf k kd hk).2.1 off hoff, rfl⟩
  · exact Or.inr (Or.inr h)

theorem hit_aligned {k p : Word} {m : Word → Word} {a : Word} (h : M.hit k p m a) : Aligned a := by
  induction h with
  | own _ h => exact own_aligned h
  | sub _ _ _ _ ih => exact ih

theorem stable_hit {k p : Word} {m : Word → Word} {a : Word} (h : M.stable k p m a) :
    M.hit k p m a := by
  induction h with
  | own hk h => exact .own hk (ownStable_own hk h)
  | sub hk hs hal _ ih => exact .sub hk hs hal ih

/-- The keys of a wholly aligned path are hit keys. -/
theorem hit_of_keys {k : Word} {kd : Kind} (hk : M.kinds k = some kd) {s : Sub} (hs : kd.sub = some s)
    {p : Word} {m : Word → Word} (hal : ∀ b ∈ s.keys m p, Aligned b) {a : Word}
    (ha : a ∈ s.keys m p) : M.hit k p m a :=
  .own hk (Or.inr (Or.inr ⟨s, hs, by rw [Sub.alKeys_eq hal]; exact ha⟩))

theorem stable_of_keys {k : Word} {kd : Kind} (hk : M.kinds k = some kd) {s : Sub}
    (hs : kd.sub = some s) {p : Word} {m : Word → Word} (hal : ∀ b ∈ s.keys m p, Aligned b)
    {a : Word} (ha : a ∈ s.keys m p) : M.stable k p m a :=
  .own hk (Or.inr ⟨s, hs, by rw [Sub.alKeys_eq hal]; exact ha⟩)

theorem field_aligned {k : Word} {kd : Kind} (hk : M.kinds k = some kd) {p : Word} (hal : Aligned p)
    {off : Word} (hoff : off ∈ kd.fields) : Aligned (p + off) := by
  have h1 := (M.kinds_wf k kd hk).1 off hoff
  unfold Aligned at *
  bv_decide

theorem hit_of_field {k : Word} {kd : Kind} (hk : M.kinds k = some kd) {p : Word} {m : Word → Word}
    {off : Word} (hoff : off ∈ kd.fields) (hal : Aligned p) : M.hit k p m (p + off) :=
  .own hk (Or.inl ⟨List.mem_map.mpr ⟨off, hoff, rfl⟩, field_aligned hk hal hoff⟩)

theorem stable_of_field {k : Word} {kd : Kind} (hk : M.kinds k = some kd) {p : Word}
    {m : Word → Word} {off : Word} (hoff : off ∈ kd.stable) (hal : Aligned p) :
    M.stable k p m (p + off) :=
  .own hk (Or.inl ⟨List.mem_map.mpr ⟨off, hoff, rfl⟩,
    field_aligned hk hal ((M.kinds_wf k kd hk).2.1 off hoff)⟩)

theorem hit_of_heap {k : Word} {kd : Kind} (hk : M.kinds k = some kd) (hh : kd.heap = true)
    {p : Word} {m : Word → Word} {a : Word} (ha : M.heap a) : M.hit k p m a :=
  .own hk (Or.inr (Or.inl ⟨hh, ha⟩))

theorem hit_of_sub {k : Word} {kd : Kind} (hk : M.kinds k = some kd) {s : Sub} (hs : kd.sub = some s)
    {p : Word} {m : Word → Word} (hal : ∀ b ∈ s.keys m p, Aligned b) {a : Word}
    (ha : M.hit (derefM m p s.kp) (derefM m p s.dp) m a) : M.hit k p m a :=
  .sub hk hs hal ha

theorem stable_of_sub {k : Word} {kd : Kind} (hk : M.kinds k = some kd) {s : Sub}
    (hs : kd.sub = some s) {p : Word} {m : Word → Word} (hal : ∀ b ∈ s.keys m p, Aligned b)
    {a : Word} (ha : M.stable (derefM m p s.kp) (derefM m p s.dp) m a) : M.stable k p m a :=
  .sub hk hs hal ha

/-- A hit key is an own key or a key of what the writer wraps. -/
theorem hit_cases {k : Word} {kd : Kind} (hk : M.kinds k = some kd) {p : Word} {m : Word → Word}
    {a : Word} (ha : M.hit k p m a) :
    M.Own kd p m a ∨ ∃ s, kd.sub = some s ∧ (∀ b ∈ s.keys m p, Aligned b) ∧
      M.hit (derefM m p s.kp) (derefM m p s.dp) m a := by
  cases ha with
  | own hk' h => rw [hk] at hk'; cases hk'; exact Or.inl h
  | sub hk' hs hal h => rw [hk] at hk'; cases hk'; exact Or.inr ⟨_, hs, hal, h⟩

theorem stable_cases {k : Word} {kd : Kind} (hk : M.kinds k = some kd) {p : Word} {m : Word → Word}
    {a : Word} (ha : M.stable k p m a) :
    OwnStable kd p m a ∨ ∃ s, kd.sub = some s ∧ (∀ b ∈ s.keys m p, Aligned b) ∧
      M.stable (derefM m p s.kp) (derefM m p s.dp) m a := by
  cases ha with
  | own hk' h => rw [hk] at hk'; cases hk'; exact Or.inl h
  | sub hk' hs hal h => rw [hk] at hk'; cases hk'; exact Or.inr ⟨_, hs, hal, h⟩

/-- Own keys of `m'` are own keys of `m`, when the two agree on `m`'s own keys. -/
theorem own_congr {kd : Kind} {p : Word} {m m' : Word → Word}
    (h : ∀ a, M.Own kd p m a → m' a = m a) : ∀ a, M.Own kd p m' a → M.Own kd p m a := by
  intro a ha
  rcases ha with ha | ha | ⟨s, hs, ha⟩
  · exact Or.inl ha
  · exact Or.inr (Or.inl ha)
  · refine Or.inr (Or.inr ⟨s, hs, ?_⟩)
    rw [Sub.alKeys_congr fun b hb => h b (Or.inr (Or.inr ⟨s, hs, hb⟩))] at ha
    exact ha

theorem ownStable_congr {kd : Kind} {p : Word} {m m' : Word → Word}
    (h : ∀ a, OwnStable kd p m a → m' a = m a) :
    ∀ a, OwnStable kd p m' a ↔ OwnStable kd p m a := by
  intro a
  have hk : ∀ s, kd.sub = some s → s.alKeys m' p = s.alKeys m p := fun s hs =>
    Sub.alKeys_congr fun b hb => h b (Or.inr ⟨s, hs, hb⟩)
  constructor
  · rintro (ha | ⟨s, hs, ha⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨s, hs, by rw [hk s hs] at ha; exact ha⟩
  · rintro (ha | ⟨s, hs, ha⟩)
    · exact Or.inl ha
    · exact Or.inr ⟨s, hs, by rw [hk s hs]; exact ha⟩

theorem hit_congr {k p : Word} {m m' : Word → Word} (h : ∀ a, M.hit k p m a → m' a = m a) :
    ∀ a, M.hit k p m' a → M.hit k p m a := by
  intro a ha
  induction ha with
  | own hk ho => exact .own hk (own_congr (fun b hb => h b (.own hk hb)) _ ho)
  | sub hk hs hal _ ih =>
    -- The paths are wholly aligned in `m'`, so their keys are the same in `m`.
    rename_i k p m' a kd s hh
    have hpre : ∀ b ∈ s.alKeys m p, m' b = m b := fun b hb =>
      h b (.own hk (Or.inr (Or.inr ⟨s, hs, hb⟩)))
    -- First from `m'` to `m`: the aligned prefix in `m'` is the whole path.
    have hpre' : ∀ b ∈ s.alKeys m' p, m' b = m b := by
      intro b hb
      rw [Sub.alKeys_congr hpre] at hb
      exact hpre b hb
    have hc := Sub.congr hal (fun b hb => (hpre' b hb).symm)
    obtain ⟨hkeys, hdp, hkp⟩ := hc
    rw [← hdp, ← hkp] at ih
    refine .sub hk hs (by rw [hkeys]; exact hal) (ih fun b hb => h b (.sub hk hs ?_ hb))
    rw [hkeys]; exact hal

/-- The same, from agreement on the stable keys alone: the hit keys depend on memory
    only through the paths, which are stable. -/
theorem hit_congr_stable {k p : Word} {m m' : Word → Word}
    (h : ∀ a, M.stable k p m a → m' a = m a) : ∀ a, M.hit k p m' a → M.hit k p m a := by
  intro a ha
  induction ha with
  | own hk ho =>
    rename_i k p m' a kd
    refine .own hk ?_
    rcases ho with ho | ho | ⟨s, hs, ho⟩
    · exact Or.inl ho
    · exact Or.inr (Or.inl ho)
    · refine Or.inr (Or.inr ⟨s, hs, ?_⟩)
      rw [Sub.alKeys_congr fun b hb => h b (.own hk (Or.inr ⟨s, hs, hb⟩))] at ho
      exact ho
  | sub hk hs hal _ ih =>
    rename_i k p m' a kd s hh
    have hpre : ∀ b ∈ s.alKeys m p, m' b = m b := fun b hb =>
      h b (.own hk (Or.inr ⟨s, hs, hb⟩))
    have hpre' : ∀ b ∈ s.alKeys m' p, m' b = m b := by
      intro b hb
      rw [Sub.alKeys_congr hpre] at hb
      exact hpre b hb
    have hc := Sub.congr hal (fun b hb => (hpre' b hb).symm)
    obtain ⟨hkeys, hdp, hkp⟩ := hc
    rw [← hdp, ← hkp] at ih
    refine .sub hk hs (by rw [hkeys]; exact hal) (ih fun b hb => h b (.sub hk hs ?_ hb))
    rw [hkeys]; exact hal

/-- Field keys of `m'` are field keys of `m`, when the two agree on the stable keys. -/
theorem fields_congr_stable {k p : Word} {m m' : Word → Word}
    (h : ∀ a, M.stable k p m a → m' a = m a) : ∀ a, M.fields k p m' a → M.fields k p m a := by
  intro a ha
  induction ha with
  | own hk ho hal => exact .own hk ho hal
  | sub hk hs hal _ ih =>
    rename_i k p m' a kd s hh
    have hpre : ∀ b ∈ s.alKeys m p, m' b = m b := fun b hb =>
      h b (.own hk (Or.inr ⟨s, hs, hb⟩))
    have hpre' : ∀ b ∈ s.alKeys m' p, m' b = m b := by
      intro b hb
      rw [Sub.alKeys_congr hpre] at hb
      exact hpre b hb
    have hc := Sub.congr hal (fun b hb => (hpre' b hb).symm)
    obtain ⟨hkeys, hdp, hkp⟩ := hc
    rw [← hdp, ← hkp] at ih
    refine .sub hk hs (by rw [hkeys]; exact hal) (ih fun b hb => h b (.sub hk hs ?_ hb))
    rw [hkeys]; exact hal

theorem stable_congr {k p : Word} {m m' : Word → Word}
    (h : ∀ a, M.stable k p m a → m' a = m a) : ∀ a, M.stable k p m' a ↔ M.stable k p m a := by
  intro a
  constructor
  · intro ha
    induction ha with
    | own hk ho => exact .own hk ((ownStable_congr (fun b hb => h b (.own hk hb)) _).mp ho)
    | sub hk hs hal _ ih =>
      rename_i k p m' a kd s hh
      have hpre : ∀ b ∈ s.alKeys m p, m' b = m b := fun b hb =>
        h b (.own hk (Or.inr ⟨s, hs, hb⟩))
      have hpre' : ∀ b ∈ s.alKeys m' p, m' b = m b := by
        intro b hb
        rw [Sub.alKeys_congr hpre] at hb
        exact hpre b hb
      obtain ⟨hkeys, hdp, hkp⟩ := Sub.congr hal (fun b hb => (hpre' b hb).symm)
      rw [← hdp, ← hkp] at ih
      refine .sub hk hs (by rw [hkeys]; exact hal) (ih fun b hb => h b (.sub hk hs ?_ hb))
      rw [hkeys]; exact hal
  · intro ha
    induction ha with
    | own hk ho => exact .own hk ((ownStable_congr (fun b hb => h b (.own hk hb)) _).mpr ho)
    | sub hk hs hal _ ih =>
      rename_i k p m a kd s hh
      have hpre : ∀ b ∈ s.alKeys m p, m' b = m b := fun b hb =>
        h b (.own hk (Or.inr ⟨s, hs, hb⟩))
      obtain ⟨hkeys, hdp, hkp⟩ := Sub.congr hal hpre
      refine .sub hk hs (by rw [hkeys]; exact hal) ?_
      rw [hdp, hkp]
      exact ih fun b hb => h b (.sub hk hs hal hb)

/-- A kind's field values and atoms are as in a memory agreeing on its own keys. -/
theorem val_congr {k : Word} {kd : Kind} (hk : M.kinds k = some kd) {p : Word} (hal : Aligned p)
    {m m' : Word → Word} (h : ∀ a, M.Own kd p m a → m' a = m a) : kd.val p m' = kd.val p m := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    simp only [Kind.val]
    cases hoff : kd.fields[i]? with
    | none => rfl
    | some off =>
      have hmem : off ∈ kd.fields := List.mem_of_getElem? hoff
      exact h _ (Or.inl ⟨List.mem_map.mpr ⟨_, hmem, rfl⟩, field_aligned hk hal hmem⟩)

theorem writerOk_congr {k p : Word} {m m' : Word → Word} (hw : M.writerOk k p m)
    (h : ∀ a, M.hit k p m a → m' a = m a) : M.writerOk k p m' := by
  induction hw with
  | mk hk hal hinv hsub hkind hkeys ihsub =>
    rename_i k p m kd
    have hown : ∀ a, M.Own kd p m a → m' a = m a := fun a ha => h a (.own hk ha)
    refine .mk hk hal ?_ ?_ ?_ ?_
    · intro f hf
      have hf' := hinv f hf
      rw [val_congr hk hal hown]
      cases f with
      | atom i args =>
        have hh := (M.kinds_wf k kd hk).2.2.2.1 _ hf rfl
        exact M.atom_congr _ _ m m' (fun a ha => hown a (Or.inr (Or.inl ⟨hh, ha⟩))) hf'
      | le l r => exact hf'
      | op o x args => exact hf'
    · intro s hs
      have hk' := hkeys s hs
      obtain ⟨hkeys', hdp, hkp⟩ := Sub.congr (fun b hb => (hk' b hb).1)
        (fun b hb => hown b (Or.inr (Or.inr ⟨s, hs, hb⟩)))
      rw [hdp, hkp]
      exact ihsub s hs fun a ha => h a (.sub hk hs (fun b hb => (hk' b hb).1) ha)
    · intro s hs
      have hk' := hkeys s hs
      obtain ⟨-, -, hkp⟩ := Sub.congr (fun b hb => (hk' b hb).1)
        (fun b hb => hown b (Or.inr (Or.inr ⟨s, hs, hb⟩)))
      rw [hkp]; exact hkind s hs
    · intro s hs a ha
      have hk' := hkeys s hs
      obtain ⟨hkeys', hdp, hkp⟩ := Sub.congr (fun b hb => (hk' b hb).1)
        (fun b hb => hown b (Or.inr (Or.inr ⟨s, hs, hb⟩)))
      rw [hkeys'] at ha
      rw [hdp, hkp]
      refine ⟨(hk' a ha).1, fun hh => (hk' a ha).2 ?_⟩
      exact hit_congr (fun b hb => h b (.sub hk hs (fun b hb => (hk' b hb).1) hb)) a hh

theorem sub_elim {k p : Word} {m : Word → Word} {kd : Kind} (hk : M.kinds k = some kd) {s : Sub}
    (hs : kd.sub = some s) (hw : M.writerOk k p m) : M.SubOk p m s := by
  cases hw with
  | mk hk' _ _ hsub hkind hkeys =>
    rw [hk] at hk'; cases hk'
    exact ⟨hsub s hs, hkind s hs, hkeys s hs⟩

theorem sub_intro {k p : Word} {m : Word → Word} {kd : Kind} (hk : M.kinds k = some kd) {s : Sub}
    (hs : kd.sub = some s) (hal : Aligned p)
    (hinv : ∀ f ∈ kd.inv, f.Holds (M.atomIn m) (kd.val p m)) (h : M.SubOk p m s) :
    M.writerOk k p m :=
  .mk hk hal hinv (fun s' hs' => by rw [hs] at hs'; cases hs'; exact h.1)
    (fun s' hs' => by rw [hs] at hs'; cases hs'; exact h.2.1)
    (fun s' hs' => by rw [hs] at hs'; cases hs'; exact h.2.2)

theorem writerOk_kind {k p : Word} {m : Word → Word} (hw : M.writerOk k p m) :
    ∃ kd, M.kinds k = some kd ∧ Aligned p ∧ ∀ f ∈ kd.inv, f.Holds (M.atomIn m) (kd.val p m) := by
  cases hw with
  | mk hk hal hinv _ _ _ => exact ⟨_, hk, hal, hinv⟩

theorem sub_eq {k : Word} {kd : Kind} (hk : M.kinds k = some kd) : M.sub k = kd.sub := by
  simp [Model.sub, hk]

theorem sub_some {K : Word} {s : Sub} (h : M.sub K = some s) :
    ∃ kd, M.kinds K = some kd ∧ kd.sub = some s := by
  simp only [Model.sub, Option.bind_eq_some_iff] at h; exact h

theorem pure_iff {kd : Kind} : kd.pure = true ↔ kd.fields = [] ∧ kd.inv = [] ∧ kd.heap = false := by
  simp [Kind.pure, List.isEmpty_iff, and_assoc]

/-! ### Pure kinds -/

theorem pure_own {kd : Kind} (hp : kd.pure = true) {s : Sub} (hs : kd.sub = some s) {p : Word}
    {m : Word → Word} (hal : ∀ b ∈ s.keys m p, Aligned b) (a : Word) :
    M.Own kd p m a ↔ a ∈ s.keys m p := by
  rw [pure_iff] at hp
  constructor
  · rintro (⟨h, _⟩ | ⟨h, _⟩ | ⟨s', hs', h⟩)
    · simp [Kind.fieldKeys, hp.1] at h
    · rw [hp.2.2] at h; cases h
    · rw [hs] at hs'; cases hs'; rw [Sub.alKeys_eq hal] at h; exact h
  · intro h; exact Or.inr (Or.inr ⟨s, hs, by rw [Sub.alKeys_eq hal]; exact h⟩)

theorem pure_ownStable {k : Word} {kd : Kind} (hk : M.kinds k = some kd) (hp : kd.pure = true)
    {s : Sub} (hs : kd.sub = some s) {p : Word} {m : Word → Word}
    (hal : ∀ b ∈ s.keys m p, Aligned b) (a : Word) : OwnStable kd p m a ↔ a ∈ s.keys m p := by
  have hst : kd.stable = [] := by
    rw [pure_iff] at hp
    cases h : kd.stable with
    | nil => rfl
    | cons x xs =>
      have := (M.kinds_wf k kd hk).2.1 x (by rw [h]; exact List.mem_cons_self ..)
      rw [hp.1] at this; cases this
  constructor
  · rintro (⟨h, _⟩ | ⟨s', hs', h⟩)
    · simp [Kind.stableKeys, hst] at h
    · rw [hs] at hs'; cases hs'; rw [Sub.alKeys_eq hal] at h; exact h
  · intro h; exact Or.inr ⟨s, hs, by rw [Sub.alKeys_eq hal]; exact h⟩

/-- For a pure structural kind, the old shape: a hit key is a path key or the wrapped
    writer's. -/
theorem hit_struct_pure {k : Word} {kd : Kind} (hk : M.kinds k = some kd) (hp : kd.pure = true)
    {s : Sub} (hs : kd.sub = some s) {p : Word} {m : Word → Word}
    (hal : ∀ b ∈ s.keys m p, Aligned b) (a : Word) :
    M.hit k p m a ↔ a ∈ s.keys m p ∨ M.hit (derefM m p s.kp) (derefM m p s.dp) m a := by
  constructor
  · intro ha
    rcases hit_cases hk ha with ha | ⟨s', hs', _, ha⟩
    · exact Or.inl ((pure_own hp hs hal a).mp ha)
    · rw [hs] at hs'; cases hs'; exact Or.inr ha
  · rintro (ha | ha)
    · exact hit_of_keys hk hs hal ha
    · exact hit_of_sub hk hs hal ha

theorem stable_struct_pure {k : Word} {kd : Kind} (hk : M.kinds k = some kd) (hp : kd.pure = true)
    {s : Sub} (hs : kd.sub = some s) {p : Word} {m : Word → Word}
    (hal : ∀ b ∈ s.keys m p, Aligned b) (a : Word) :
    M.stable k p m a ↔ a ∈ s.keys m p ∨ M.stable (derefM m p s.kp) (derefM m p s.dp) m a := by
  constructor
  · intro ha
    rcases stable_cases hk ha with ha | ⟨s', hs', _, ha⟩
    · exact Or.inl ((pure_ownStable hk hp hs hal a).mp ha)
    · rw [hs] at hs'; cases hs'; exact Or.inr ha
  · rintro (ha | ha)
    · exact stable_of_keys hk hs hal ha
    · exact stable_of_sub hk hs hal ha

/-- A field key of a pure structural writer is one of the writer it wraps. -/
theorem fields_struct_pure {M : Model} {k : Word} {kd : Kind} (hk : M.kinds k = some kd)
    (hp : kd.pure = true) {s : Sub} (hs : kd.sub = some s) {p : Word} {m : Word → Word}
    {a : Word} (h : M.Fields k p m a) : M.Fields (derefM m p s.kp) (derefM m p s.dp) m a := by
  cases h with
  | own hk' h _ =>
    rw [hk] at hk'; cases hk'
    rw [pure_iff] at hp
    simp [Kind.fieldKeys, hp.1] at h
  | sub hk' hs' _ h =>
    rw [hk] at hk'; cases hk'
    rw [hs] at hs'; cases hs'
    exact h

/-- A pure unit kind (no wrapper) has no keys. -/
theorem unit_no_hit {k : Word} {kd : Kind} (hk : M.kinds k = some kd) (hp : kd.pure = true)
    (hs : kd.sub = none) {p : Word} {m : Word → Word} {a : Word} : ¬ M.hit k p m a := by
  intro ha
  rcases hit_cases hk ha with ha | ⟨s', hs', _, _⟩
  · rw [pure_iff] at hp
    rcases ha with ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, hs', _⟩
    · simp [Kind.fieldKeys, hp.1] at h
    · rw [hp.2.2] at h; cases h
    · rw [hs] at hs'; cases hs'
  · rw [hs] at hs'; cases hs'

theorem unit_writerOk {k : Word} {kd : Kind} (hk : M.kinds k = some kd) (hp : kd.pure = true)
    (hs : kd.sub = none) {p : Word} {m : Word → Word} (hal : Aligned p) : M.writerOk k p m := by
  rw [pure_iff] at hp
  exact .mk hk hal (fun f hf => by rw [hp.2.1] at hf; cases hf)
    (fun s hs' => by rw [hs] at hs'; cases hs') (fun s hs' => by rw [hs] at hs'; cases hs')
    (fun s hs' => by rw [hs] at hs'; cases hs')

theorem sub_intro_pure {k : Word} {kd : Kind} (hk : M.kinds k = some kd) (hp : kd.pure = true)
    {s : Sub} (hs : kd.sub = some s) {p : Word} {m : Word → Word} (hal : Aligned p)
    (h : M.SubOk p m s) : M.writerOk k p m := by
  rw [pure_iff] at hp
  exact sub_intro hk hs hal (fun f hf => by rw [hp.2.1] at hf; cases hf) h

/-- The pointer of a structural writer is aligned when its paths' keys are. -/
theorem aligned_of_sub {k : Word} {kd : Kind} (hk : M.kinds k = some kd) {s : Sub}
    (hs : kd.sub = some s) {p : Word} {m : Word → Word} (hal : ∀ b ∈ s.keys m p, Aligned b) :
    Aligned p := by
  obtain ⟨hne, hoff⟩ := (M.kinds_wf k kd hk).2.2.2.2.1 s hs
  cases hdp : s.dp with
  | nil => exact absurd hdp hne
  | cons d rest =>
    have h1 : Aligned (p + d) := hal _ (by simp [Sub.keys, hdp, pathKeys])
    have h2 : Aligned d := hoff d (by simp [hdp])
    unfold Aligned at *
    bv_decide

/-! ### Keeping -/

/-- What a function gives back about a writer it was lent, or did not touch: well-typed,
    its keys no more than before, its stable keys as they were. -/
def Keeps (M : Model) (k p : Word) (m m' : Word → Word) : Prop :=
  M.writerOk k p m' ∧ (∀ a, M.hit k p m' a → M.hit k p m a) ∧
  ∀ a, M.stable k p m a → m' a = m a

theorem Keeps.refl {k p : Word} {m : Word → Word} (h : M.writerOk k p m) : M.Keeps k p m m :=
  ⟨h, fun _ h => h, fun _ _ => rfl⟩

theorem Keeps.stable_iff {k p : Word} {m m' : Word → Word} (h : M.Keeps k p m m') (a : Word) :
    M.stable k p m' a ↔ M.stable k p m a :=
  stable_congr h.2.2 a

theorem Keeps.trans {k p : Word} {m m' m'' : Word → Word} (h1 : M.Keeps k p m m')
    (h2 : M.Keeps k p m' m'') : M.Keeps k p m m'' :=
  ⟨h2.1, fun a ha => h1.2.1 a (h2.2.1 a ha),
   fun a ha => (h2.2.2 a ((h1.stable_iff a).mpr ha)).trans (h1.2.2 a ha)⟩

/-- Keeping from a memory whose stable keys are `m`'s keeps from `m`. -/
theorem Keeps.of_stable {k p : Word} {m m' m'' : Word → Word}
    (hst : ∀ a, M.stable k p m a → m' a = m a) (h : M.Keeps k p m' m'') : M.Keeps k p m m'' :=
  ⟨h.1, fun a ha => hit_congr_stable hst a (h.2.1 a ha),
   fun a ha => (h.2.2 a ((stable_congr hst a).mpr ha)).trans (hst a ha)⟩

/-- A memory that agrees with `m` on the writer's keys keeps it. -/
theorem Keeps.of_congr {k p : Word} {m m' : Word → Word} (hw : M.writerOk k p m)
    (h : ∀ a, M.hit k p m a → m' a = m a) : M.Keeps k p m m' :=
  ⟨writerOk_congr hw h, hit_congr h, fun a ha => h a (stable_hit ha)⟩

/-- Keeping, then changing nothing on the writer's keys, keeps. -/
theorem Keeps.congr {k p : Word} {m m' m'' : Word → Word} (h : M.Keeps k p m m')
    (hc : ∀ a, M.hit k p m a → m'' a = m' a) : M.Keeps k p m m'' :=
  h.trans (Keeps.of_congr h.1 fun a ha => hc a (h.2.1 a ha))

/-- A stable key is a field key. -/
theorem stable_fields {k p : Word} {m : Word → Word} {a : Word} (h : M.stable k p m a) :
    M.fields k p m a ∨ ∃ k' p' s kd, M.kinds k' = some kd ∧ kd.sub = some s ∧ a ∈ s.alKeys m p' := by
  induction h with
  | own hk h =>
    rename_i k p m a kd
    rcases h with ⟨h, hal⟩ | ⟨s, hs, h⟩
    · left
      refine .own hk ?_ hal
      simp only [Kind.stableKeys, List.mem_map] at h
      obtain ⟨off, hoff, rfl⟩ := h
      exact List.mem_map.mpr ⟨off, (M.kinds_wf k kd hk).2.1 off hoff, rfl⟩
    · exact Or.inr ⟨k, p, s, kd, hk, hs, h⟩
  | sub hk hs hal _ ih =>
    rcases ih with ih | ih
    · exact Or.inl (.sub hk hs hal ih)
    · exact Or.inr ih

/-- The heap keys a well-typed writer owns change only inside allocated blocks, and its
    fields and stable keys are not heap keys: it is kept. -/
theorem Keeps.of_keep {k p : Word} {m m' : Word → Word} (hw : M.writerOk k p m)
    (h : ∀ a, M.hit k p m a → m' a = m a ∨ (M.heap a ∧ M.payload m a))
    (hf : ∀ a, M.fields k p m a → ¬ M.heap a) (hs : ∀ a, M.stable k p m a → ¬ M.heap a) :
    M.Keeps k p m m' := by
  have hst : ∀ a, M.stable k p m a → m' a = m a := fun a ha =>
    (h a (stable_hit ha)).resolve_right fun hh => hs a ha hh.1
  refine ⟨?_, hit_congr_stable hst, hst⟩
  induction hw with
  | mk hk hal hinv hsub hkind hkeys ihsub =>
    rename_i k p m kd
    have hfld : ∀ a, a ∈ kd.fieldKeys p → m' a = m a := fun a ha => by
      obtain ⟨off, hoff, rfl⟩ := List.mem_map.mp ha
      exact (h _ (.own hk (Or.inl ⟨ha, field_aligned hk hal hoff⟩))).resolve_right
        fun hh => hf _ (.own hk ha (field_aligned hk hal hoff)) hh.1
    have hval : kd.val p m' = kd.val p m := by
      funext i
      cases i with
      | zero => rfl
      | succ i =>
        simp only [Kind.val]
        split
        · rename_i off hoff
          exact hfld _ (List.mem_map.mpr ⟨off, List.mem_of_getElem? hoff, rfl⟩)
        · rfl
    refine .mk hk hal ?_ ?_ ?_ ?_
    · intro f hf'
      have hf'' := hinv f hf'
      rw [hval]
      cases f with
      | atom i args =>
        have hh := (M.kinds_wf k kd hk).2.2.2.1 _ hf' rfl
        refine M.atom_keep _ _ m m' (fun a ha => ?_) hf''
        rcases h a (.own hk (Or.inr (Or.inl ⟨hh, ha⟩))) with h1 | ⟨_, h1⟩
        · exact Or.inl h1
        · exact Or.inr h1
      | le l r => exact hf''
      | op o x args => exact hf''
    · intro s hs'
      have hk' := hkeys s hs'
      have hpath : ∀ b ∈ s.alKeys m p, m' b = m b := fun b hb =>
        hst b (.own hk (Or.inr ⟨s, hs', hb⟩))
      obtain ⟨hkeys', hdp, hkp⟩ := Sub.congr (fun b hb => (hk' b hb).1) hpath
      rw [hdp, hkp]
      refine ihsub s hs' (fun a ha => h a (.sub hk hs' (fun b hb => (hk' b hb).1) ha))
        (fun a ha => hf a (.sub hk hs' (fun b hb => (hk' b hb).1) ha))
        (fun a ha => hs a (.sub hk hs' (fun b hb => (hk' b hb).1) ha))
        (fun a ha => hst a (.sub hk hs' (fun b hb => (hk' b hb).1) ha))
    · intro s hs'
      have hk' := hkeys s hs'
      obtain ⟨-, -, hkp⟩ := Sub.congr (fun b hb => (hk' b hb).1)
        (fun b hb => hst b (.own hk (Or.inr ⟨s, hs', hb⟩)))
      rw [hkp]; exact hkind s hs'
    · intro s hs' a ha
      have hk' := hkeys s hs'
      obtain ⟨hkeys', hdp, hkp⟩ := Sub.congr (fun b hb => (hk' b hb).1)
        (fun b hb => hst b (.own hk (Or.inr ⟨s, hs', hb⟩)))
      rw [hkeys'] at ha
      rw [hdp, hkp]
      refine ⟨(hk' a ha).1, fun hh => (hk' a ha).2 ?_⟩
      exact hit_congr_stable (fun b hb => hst b (.sub hk hs' (fun b hb => (hk' b hb).1) hb)) a hh

/-- The bytes of a writer's buffer: `[ptr, ptr + cap)`, from its fields. -/
def BufKey (k p : Word) (m : Word → Word) (a : Word) : Prop :=
  ∃ kd pi ci, M.kinds k = some kd ∧ kd.buf = some (pi, ci) ∧
    (kd.val p m (pi + 1)).toNat ≤ a.toNat ∧
    a.toNat + 1 ≤ (kd.val p m (pi + 1)).toNat + (kd.val p m (ci + 1)).toNat

/-- The doubleword of a buffer byte is a payload key the writer may rewrite. -/
theorem bufKey_payload {k p : Word} {m : Word → Word} (hw : M.writerOk k p m) {a : Word}
    (hb : M.BufKey k p m a) :
    M.payload m (alignToDword a) ∧ M.hit k p m (alignToDword a) ∧
    ∀ kd, M.kinds k = some kd → alignToDword a ∉ kd.fieldKeys p := by
  obtain ⟨kd, pi, ci, hk, hbuf, h1, h2⟩ := hb
  obtain ⟨kd', hk', _, hinv⟩ := writerOk_kind hw
  rw [hk] at hk'; cases hk'
  obtain ⟨hp, hnf⟩ := M.buf_sound k kd p m hk pi ci hbuf hinv a h1 h2
  have hh := (M.kinds_wf k kd hk).2.2.1 (by simp [hbuf])
  refine ⟨hp, .own hk (Or.inr (Or.inl ⟨hh, M.payload_heap m _ hp⟩)), fun kd' hk' => ?_⟩
  rw [hk] at hk'; cases hk'; exact hnf

end Model

/-- No writers. -/
def Model.trivial : Model where
  kinds _ := none
  heap _ := False
  atom _ _ _ := False
  payload _ _ := False
  rules := []
  heap_aligned _ h := h.elim
  payload_heap _ _ h := h.elim
  payload_keep _ _ _ _ := Iff.rfl
  atom_keep _ _ _ _ _ h := h.elim
  rules_sound _ _ h := by simp at h
  fixed_sound _ _ _ _ _ h := h.elim
  buf_sound _ _ _ _ h := nomatch h
  kinds_wf _ _ h := nomatch h

theorem Model.trivial_hit {k p : Word} {m : Word → Word} {a : Word} : ¬ Model.trivial.hit k p m a := by
  intro h; cases h with
  | own hk _ => cases hk
  | sub hk _ _ _ => cases hk

theorem Model.trivial_writerOk {k p : Word} {m : Word → Word} : ¬ Model.trivial.writerOk k p m := by
  intro h; cases h with
  | mk hk _ _ _ _ _ => cases hk

end AsmVerif.RiscV.Check
