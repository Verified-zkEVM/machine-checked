/-
  MachineChecked.RiscV.Check.Sound.Core

  The checker's soundness, part 1: the facts of an activation, its invariant (`St`) at
  each state, the cells and candidates, and the symbols: killing, substituting and joining.
-/

import MachineChecked.RiscV.Check.Arith
import MachineChecked.RiscV.Check.Ecall

namespace MachineChecked.RiscV.Check

open RiscvZkvm.Rv64 MachineChecked.RiscV.Frame

/-- The function's words, and its fragments' instructions, are what the code map holds. -/
def CodeAt (f : Fn) (C : Word → Option Instr) : Prop :=
  (∀ j oi, f.prog[j]? = some oi → C (f.pcOf j) = oi) ∧
  ∀ fb fp, f.frags.lookup fb = some fp →
    ∀ m ins, fp[m]? = some (some ins) → C (fb + BitVec.ofNat 64 (4 * m)) = some ins

/-- The cell premises, at the activation's entry `E`. -/
def CellsOk (σ : Iface) (E : Ent) : Prop :=
  ∀ c ∈ σ.cells, Aligned (c.addr E) ∧ ¬ Written σ E (c.addr E) ∧
    ∀ cs, c.vals = some cs → E.mem (c.addr E) ∈ cs

/-- The cells are not owned statics: no call changes them. -/
def CellsOwnFree (env : Env) (σ : Iface) (E : Ent) : Prop :=
  ∀ c ∈ σ.cells, ¬ env.InOwn (c.addr E)

/-- What `A` says about a memory `M`: its slots hold there, and the cells still hold their
    entry contents. -/
def MemOk (σ : Iface) (E : Ent) (A : AState) (M : Word → Word) : Prop :=
  (∀ p ∈ A.slots, p.2.Holds E (M (E .x2 + p.1))) ∧
  ∀ c ∈ σ.cells, M (c.addr E) = E.mem (c.addr E)

theorem Ent.deref_append (E : Ent) (a : Word) (ks : List Word) (k : Word) :
    E.deref a (ks ++ [k]) = E.mem (E.deref a ks + k) := by
  induction ks generalizing a with
  | nil => rfl
  | cons k' ks ih => simp [Ent.deref, ih]

theorem derefM_append' (m : Word → Word) (x : Word) (l1 l2 : List Word) :
    derefM m x (l1 ++ l2) = derefM m (derefM m x l1) l2 := by
  induction l1 generalizing x with
  | nil => rfl
  | cons y l ih => simp [derefM, ih]

theorem cellVal_some {σ : Iface} {r : Reg} {ks : List Word} {k : Word} {v : AVal}
    (h : cellVal σ r ks k = some v) :
    (∃ c ∈ σ.cells, c.r = r ∧ c.ks = ks ∧ c.k = k) ∧ v = .cell r (ks ++ [k]) 0 := by
  unfold cellVal at h
  split at h
  · rename_i hany
    simp only [Option.some.injEq] at h
    simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hany
    obtain ⟨c, hc, ⟨hr, hks⟩, hk⟩ := hany
    exact ⟨⟨c, hc, hr, hks, hk⟩, h.symm⟩
  · cases h

/-- A value's concretization is determined, unless it is `top` or a set. -/
theorem holds_det {E : Ent} {v : AVal} (hv : v.isPtr = true) {w w' : Word} (h : v.Holds E w)
    (h' : v.Holds E w') : w = w' := by
  cases v with
  | lin r k => simp only [AVal.Holds] at h h'; rw [h, h']
  | const c => simp only [AVal.Holds] at h h'; rw [h, h']
  | cell r ks d => simp only [AVal.Holds] at h h'; rw [h, h']
  | sym i j k => simp only [AVal.Holds] at h h'; rw [h, h']
  | top => simp [AVal.isPtr] at hv
  | oneOf _ => simp [AVal.isPtr] at hv

theorem holds_self {E : Ent} {v : AVal} (hv : v.isPtr = true) : v.Holds E (v.eval E) := by
  cases v <;> simp_all [AVal.Holds, AVal.eval, AVal.isPtr]

theorem holds_iff_eval {E : Ent} {v : AVal} (hv : v.isPtr = true) {w : Word} :
    v.Holds E w ↔ w = v.eval E :=
  ⟨fun h => holds_eval h hv ▸ rfl, fun h => h ▸ holds_self hv⟩

@[simp] theorem getMem_setReg' (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).getMem = s.getMem := funext fun _ => by simp [MachineState.getMem_setReg]

@[simp] theorem getMem_setPC' (s : MachineState) (v : Word) : (s.setPC v).getMem = s.getMem :=
  funext fun _ => by simp [MachineState.getMem, MachineState.setPC]

theorem cellOf_holds {E : Ent} {b : AVal} {a : Word} (hb : b.Holds E a) {v : AVal}
    (h : b.cellOf = some v) : v.Holds E (E.mem a) := by
  cases b with
  | lin r k =>
    simp only [AVal.cellOf, Option.some.injEq] at h; subst h
    simp only [AVal.Holds] at hb; subst hb
    simp [AVal.Holds, Ent.deref]
  | cell r ks d =>
    simp only [AVal.cellOf, Option.some.injEq] at h; subst h
    simp only [AVal.Holds] at hb; subst hb
    simp [AVal.Holds, Ent.deref_append]
  | const => simp [AVal.cellOf] at h
  | top => simp [AVal.cellOf] at h
  | oneOf => simp [AVal.cellOf] at h
  | sym => simp [AVal.cellOf] at h

theorem path_holds {E : Ent} {b : AVal} {a : Word} (hb : b.Holds E a) :
    ∀ {ks : List Word} {v : AVal}, b.path ks = some v → v.Holds E (E.deref a ks)
  | [], v, h => by simp only [AVal.path, Option.some.injEq] at h; subst h; exact hb
  | k :: ks, v, h => by
    cases b with
    | lin r k0 =>
      simp only [AVal.path, Option.some.injEq] at h; subst h
      simp only [AVal.Holds] at hb; subst hb
      simp [AVal.Holds, Ent.deref, BitVec.add_assoc]
    | cell r ks0 d =>
      simp only [AVal.path, Option.some.injEq] at h; subst h
      simp only [AVal.Holds] at hb; subst hb
      simp only [AVal.Holds]
      rw [Ent.deref_eq, Ent.deref_eq, Ent.deref_eq, derefM_append']
      simp [derefM, BitVec.add_assoc]
    | const => simp [AVal.path] at h
    | top => simp [AVal.path] at h
    | oneOf => simp [AVal.path] at h
    | sym => simp [AVal.path] at h

section Cells

variable {σ : Iface} {E : Ent} {M : Word → Word}

theorem cellVal_holds (hm : ∀ c ∈ σ.cells, M (c.addr E) = E.mem (c.addr E))
    {r : Reg} {ks : List Word} {k : Word} {v : AVal} (h : cellVal σ r ks k = some v) :
    v.Holds E (M (E.deref (E r) ks + k)) := by
  obtain ⟨⟨c, hc', rfl, rfl, rfl⟩, rfl⟩ := cellVal_some h
  have ha : E.deref (E c.r) c.ks + c.k = c.addr E := rfl
  rw [ha, hm c hc']
  simp [AVal.Holds, Ent.deref_append, Cell.addr]

theorem cellAt_addr {b : AVal} {a : Word} (hb : b.Holds E a) {v : AVal}
    (h : cellAt σ b = some v) : ∃ c ∈ σ.cells, c.addr E = a := by
  cases b with
  | lin r k =>
    simp only [AVal.Holds] at hb; subst hb
    obtain ⟨⟨c, hc', hr, hks, hk⟩, _⟩ := cellVal_some h
    exact ⟨c, hc', by simp [Cell.addr, hr, hks, hk, Ent.deref]⟩
  | cell r ks d =>
    simp only [AVal.Holds] at hb; subst hb
    obtain ⟨⟨c, hc', rfl, rfl, rfl⟩, _⟩ := cellVal_some h
    exact ⟨c, hc', rfl⟩
  | const => simp [cellAt] at h
  | top => simp [cellAt] at h
  | oneOf => simp [cellAt] at h
  | sym => simp [cellAt] at h

theorem cellAt_holds (hm : ∀ c ∈ σ.cells, M (c.addr E) = E.mem (c.addr E))
    {b : AVal} {a : Word} (hb : b.Holds E a) {v : AVal} (h : cellAt σ b = some v) :
    v.Holds E (M a) := by
  cases b with
  | lin r k =>
    simp only [AVal.Holds] at hb; subst hb
    exact cellVal_holds (ks := []) hm h
  | cell r ks d =>
    simp only [AVal.Holds] at hb; subst hb
    exact cellVal_holds hm h
  | const => simp [cellAt] at h
  | top => simp [cellAt] at h
  | oneOf => simp [cellAt] at h
  | sym => simp [cellAt] at h

/-- The stable doublewords of a knowledge hold their contents in `M`. -/
def KnCells (E : Ent) (M : Word → Word) (kn : Kn) : Prop :=
  ∀ p ∈ kn.cells, ∀ w, p.1.Holds E w → p.2.Holds E (M w)

/-- The kinds of a knowledge are among their candidates. -/
def KnRoots (E : Ent) (kn : Kn) : Prop :=
  ∀ p ∈ kn.roots, ∀ w, p.1.Holds E w → w ∈ p.2

theorem knCells_empty : KnCells E M {} := fun _ h => by simp at h
theorem knRoots_empty : KnRoots E ({} : Kn) := fun _ h => by simp at h

/-- The tracked fields of a state hold their contents in `M`. -/
def WmemOk (E : Ent) (A : AState) (M : Word → Word) : Prop :=
  ∀ p ∈ A.wmem, p.1.isPtr = true ∧ p.2.Holds E (M (p.1.eval E))

theorem contentAt_holds {A : AState} {kn : Kn} (hm : MemOk σ E A M) (hk : KnCells E M kn)
    (hw : WmemOk E A M) {a : AVal} {w : Word} (ha : a.Holds E w) {v : AVal}
    (h : contentAt σ kn A a = some v) : v.Holds E (M w) := by
  unfold contentAt at h
  cases hf : a.frameOff? with
  | some f =>
    rw [hf] at h
    simp only at h
    rw [AVal.frameOff?_some hf] at ha
    simp only [AVal.Holds] at ha
    subst ha
    exact hm.1 _ (lookup_mem h)
  | none =>
    rw [hf] at h
    cases hc : cellAt σ a with
    | some u =>
      rw [hc] at h; simp only [Option.some.injEq] at h; subst h
      exact cellAt_holds hm.2 ha hc
    | none =>
      rw [hc] at h
      cases hkc : kn.cells.lookup a with
      | some u =>
        rw [hkc] at h; simp only [Option.some.injEq] at h; subst h
        exact hk _ (lookup_mem hkc) w ha
      | none =>
        rw [hkc] at h
        obtain ⟨hp, hv⟩ := hw _ (lookup_mem h)
        rw [← holds_eval ha hp]; exact hv

theorem instPath_holds {A : AState} {kn : Kn} {E' : Ent} (hm : MemOk σ E A E'.mem)
    (hk : KnCells E E'.mem kn) (hw : WmemOk E A E'.mem) :
    ∀ {ks : List Word} {v v' : AVal} {w : Word}, v.Holds E w → instPath σ kn A v ks = some v' →
      v'.Holds E (E'.deref w ks)
  | [], _, _, _, hv, h => by
    simp only [instPath, Option.some.injEq] at h; subst h; exact hv
  | k :: ks, v, v', w, hv, h => by
    simp only [instPath] at h
    cases hct : contentAt σ kn A (v.addK k) with
    | none => rw [hct] at h; cases h
    | some u =>
      rw [hct] at h
      simp only [Option.bind_some] at h
      exact instPath_holds (ks := ks) hm hk hw (contentAt_holds hm hk hw (AVal.holds_addK hv) hct) h

end Cells

/-! ## The facts of an activation -/

structure Facts (env : Env) (σ : Iface) (E : Ent) (s0 : MachineState) : Prop where
  wf : env.wf = true
  ok : env.Ok
  depth : σ.depth ≤ (E .x2).toNat
  top : (E .x2).toNat ≤ env.stackTop
  al : Aligned (E .x2)
  prot : ∀ a, Aligned a → env.InProt a → s0.getMem a = env.init a
  foot : ∀ it ∈ σ.foot, ∀ a, Aligned a → it.Hits E a →
    ¬ InWin (E .x2) σ.depth a ∧ ¬ env.InProt a ∧ ¬ env.InOwn a
  nz : ∀ v ∈ σ.nz, v.eval E ≠ 0
  vals : ∀ p ∈ σ.vals, E p.1 ∈ p.2
  cells : CellsOk σ E
  cellsOwn : CellsOwnFree env σ E
  inv : env.Inv s0.getMem
  strs : StrsPre env σ E s0.getMem
  strsPtr : ∀ e ∈ σ.strs, e.1.isPtr = true ∧ e.2.isPtr = true
  symFree : σ.symFree = true
  pre : ∀ f ∈ σ.pre, f.Holds (env.model.atomIn s0.getMem) (AVal.eval E)
  emem : ∀ a, E.mem a = s0.getMem a

theorem Facts.of_pre {env : Env} {C} {σ : Iface} {s0 : MachineState} (hwf : env.wf = true)
    (hok : env.Ok) (hptr : ∀ e ∈ σ.strs, e.1.isPtr = true ∧ e.2.isPtr = true)
    (hsf : σ.symFree = true) (h : Pre env C σ s0) : Facts env σ (regsOf s0) s0 :=
  ⟨hwf, hok, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1,
    fun c hc => let hc' := h.2.2.2.2.2.2.2.2.1 c hc; ⟨hc'.1, hc'.2.1, hc'.2.2.2⟩,
    fun c hc => (h.2.2.2.2.2.2.2.2.1 c hc).2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.1, hptr, hsf, h.2.2.2.2.2.2.2.2.2.2.2, fun _ => rfl⟩

/-- The writers at a state: their stable keys are as at entry, and, if the function leaves
    the heap's structure alone, the writers it was not lent are kept. -/
def StrsInv (env : Env) (σ : Iface) (E : Ent) (m m' : Word → Word) : Prop :=
  (∀ e ∈ σ.strs, ∀ a, env.model.stable (e.2.eval E) (e.1.eval E) m a → m' a = m a) ∧
  (σ.heap = false → ∀ k p, env.model.writerOk k p m →
    (∀ a, env.model.hit k p m a → ¬ Written σ E a ∧ ¬ StrHit env σ E m a) →
    (∀ a, env.model.fields k p m a → ¬ env.InOwn a) →
    (∀ a, env.model.stable k p m a → ¬ env.InOwn a) →
    env.model.Keeps k p m m')

/-- A field key of one of the function's writers. -/
def FieldKey (env : Env) (σ : Iface) (E : Ent) (m : Word → Word) (a : Word) : Prop :=
  ∃ e ∈ σ.strs, env.model.fields (e.2.eval E) (e.1.eval E) m a

/-- The checker's invariant at a state `x` of the activation, with abstract state `A`. -/
structure St (env : Env) (σ : Iface) (C : Word → Option Instr) (E : Ent) (s0 : MachineState)
    (A : AState) (x : MachineState) : Prop where
  holds : A.Holds E x
  code : x.code = C
  mem : ∀ a, Aligned a → ¬ Written σ E a → ¬ env.InOwn a → ¬ StrHit env σ E s0.getMem a →
    x.getMem a = s0.getMem a
  heap : σ.heap = false → ∀ a, env.model.heap a → ¬ env.model.payload s0.getMem a →
    x.getMem a = s0.getMem a
  inv : env.Inv x.getMem
  slots : ∀ p ∈ A.slots, 8 ≤ negOff p.1 ∧ negOff p.1 ≤ σ.depth ∧ negOff p.1 % 8 = 0
  facts : ∀ f ∈ A.facts, f.Holds (env.model.atomIn x.getMem) (AVal.eval E)
  wmem : ∀ p ∈ A.wmem, p.1.isPtr = true ∧ FieldKey env σ E s0.getMem (p.1.eval E) ∧
    p.2.Holds E (x.getMem (p.1.eval E))
  strs : StrsInv env σ E s0.getMem x.getMem

section Facts

variable {env : Env} {σ : Iface} {E : Ent} {s0 : MachineState}

theorem aligned_sub {e : Word} {m : Nat} (he : Aligned e) (hm : m % 8 = 0) :
    Aligned (e - BitVec.ofNat 64 m) := by
  rw [aligned_iff] at he ⊢
  have := e.isLt
  bv_omega

/-- A slot's key: aligned, and in the window. -/
theorem slot_facts (hF : Facts env σ E s0) {k : Word}
    (hk : 8 ≤ negOff k ∧ negOff k ≤ σ.depth ∧ negOff k % 8 = 0) :
    Aligned (E .x2 + k) ∧ InWin (E .x2) σ.depth (E .x2 + k) := by
  rw [add_frame]
  exact ⟨aligned_sub hF.al hk.2.2,
    inWin_slot hF.depth hk.1 hk.2.1⟩

/-- A writer's key is nothing the activation writes, and not protected. -/
theorem Facts.strHit (hF : Facts env σ E s0) {a : Word} (h : StrHit env σ E s0.getMem a) :
    ¬ Written σ E a ∧ ¬ env.InProt a := by
  obtain ⟨e, he, hh⟩ := h
  exact (hF.strs.1 e he).2.1 a hh

/-- A field key: aligned, not owned, a writer's key. -/
theorem Facts.fieldKey (hF : Facts env σ E s0) {a : Word} (h : FieldKey env σ E s0.getMem a) :
    Aligned a ∧ ¬ env.InOwn a ∧ StrHit env σ E s0.getMem a := by
  obtain ⟨e, he, hh⟩ := h
  refine ⟨((hF.strs.1 e he).2.2.2 a hh).1, ((hF.strs.1 e he).2.2.2 a hh).2, e, he, ?_⟩
  exact Model.fields_hit hh

theorem St.wmemOk {C} {A : AState} {x : MachineState} (h : St env σ C E s0 A x) :
    WmemOk E A x.getMem := fun p hp => ⟨(h.wmem p hp).1, (h.wmem p hp).2.2⟩

/-- The slots and cells describe the memory of every state of the activation. -/
theorem St.memOk {C} {A : AState} {x : MachineState} (hF : Facts env σ E s0)
    (h : St env σ C E s0 A x) : MemOk σ E A x.getMem :=
  ⟨h.holds.2, fun c hc => by
    have := hF.cells c hc
    rw [h.mem _ this.1 this.2.1 (hF.cellsOwn c hc) (hF.strs.2 c hc), hF.emem]⟩

/-- What the activation may write is not owned. -/
theorem Facts.not_own (hF : Facts env σ E s0) {a : Word} (ha : Aligned a)
    (hw : Written σ E a) : ¬ env.InOwn a := by
  rcases hw with hw | ⟨it, hit, hh⟩
  · exact not_own_of_inWin hF.wf hF.top hF.depth hw
  · exact (hF.foot it hit a ha hh).2.2

/-- What the activation may write is not a heap key. -/
theorem Facts.not_heap (hF : Facts env σ E s0) {a : Word} (ha : Aligned a)
    (hw : Written σ E a) : ¬ env.model.heap a := fun hh => hF.not_own ha hw (hF.ok.1 a hh)

/-- The protected regions hold their contents at every state of the activation. -/
theorem St.prot {C} {A : AState} {x : MachineState} (hF : Facts env σ E s0)
    (h : St env σ C E s0 A x) {a : Word} (ha : Aligned a) (hp : env.InProt a) :
    x.getMem a = env.init a := by
  rw [h.mem a ha ?_ (not_own_of_prot hF.wf hp) (fun hs => (hF.strHit hs).2 hp), hF.prot a ha hp]
  rintro (hw | ⟨it, hit, hh⟩)
  · exact not_prot_of_inWin hF.wf hF.top hF.depth hw hp
  · exact (hF.foot it hit a ha hh).2.1 hp

/-- A store at a key that is not owned keeps the invariant. -/
theorem Env.Inv_setMem_not_own {x : MachineState} (h : env.Inv x.getMem) {k v : Word}
    (hk : ¬ env.InOwn k) : env.Inv (x.setMem k v).getMem :=
  Env.Inv_congr (fun a _ ho => by rw [getMem_setMem, if_neg]; rintro rfl; exact hk ho) h

/-- A store the activation may make keeps the invariant. -/
theorem St.inv_setMem {C} {A : AState} {x : MachineState} (hF : Facts env σ E s0)
    (h : St env σ C E s0 A x) {k v : Word} (hk : Aligned k → Written σ E k) :
    env.Inv (x.setMem k v).getMem :=
  Env.Inv_congr (fun a ha ho => by
    rw [getMem_setMem, if_neg]
    rintro rfl
    exact hF.not_own ha (hk ha) ho) h.inv

/-- A memory that differs from one the writers survive only on keys that are no writer's
    stable key and nothing the activation may write still has them survive. -/
theorem StrsInv.congr (hF : Facts env σ E s0) {m m' : Word → Word}
    (h : StrsInv env σ E s0.getMem m) (hc : ∀ a, ¬ Written σ E a → m' a = m a) :
    StrsInv env σ E s0.getMem m' :=
  ⟨fun e he a ha => by
    rw [hc a ((hF.strs.1 e he).2.1 a (Model.stable_hit ha)).1]
    exact h.1 e he a ha,
   fun hh k p hw hhit hf hs => (h.2 hh k p hw hhit hf hs).congr fun a ha => hc a (hhit a ha).1⟩

/-- A store the activation may make keeps the writers. -/
theorem St.strs_setMem {C} {A : AState} {x : MachineState} (hF : Facts env σ E s0)
    (h : St env σ C E s0 A x) {k v : Word} (hk : Written σ E k) :
    StrsInv env σ E s0.getMem (x.setMem k v).getMem :=
  StrsInv.congr hF h.strs fun a ha => by
    rw [getMem_setMem, if_neg]; rintro rfl; exact ha hk

/-- The facts of a state survive a store at a key that is not a heap key. -/
theorem St.facts_setMem {C} {A : AState} {x : MachineState} (h : St env σ C E s0 A x) {k v : Word}
    (hk : ¬ env.model.heap k) :
    ∀ f ∈ A.facts, f.Holds (env.model.atomIn (x.setMem k v).getMem) (AVal.eval E) := by
  intro f hf
  have := h.facts f hf
  cases f with
  | le l r => exact this
  | op o x args => exact this
  | atom i args =>
    simp only [Fact.Holds, Model.atomIn] at this ⊢
    refine env.model.atom_congr i _ _ _ (fun a ha => ?_) this
    rw [getMem_setMem, if_neg]; rintro rfl; exact hk ha

/-- The tracked fields survive a store at a key the activation may write, or that is owned. -/
theorem St.wmem_setMem {C} {A : AState} {x : MachineState} (hF : Facts env σ E s0)
    (h : St env σ C E s0 A x) {k v : Word} (hk : Written σ E k ∨ env.InOwn k) :
    ∀ p ∈ A.wmem, p.1.isPtr = true ∧ FieldKey env σ E s0.getMem (p.1.eval E) ∧
      p.2.Holds E ((x.setMem k v).getMem (p.1.eval E)) := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := h.wmem p hp
  refine ⟨h1, h2, ?_⟩
  rw [getMem_setMem, if_neg]
  · exact h3
  · intro he
    obtain ⟨_, hno, hsh⟩ := hF.fieldKey h2
    rcases hk with hk | hk
    · exact (hF.strHit hsh).1 (he ▸ hk)
    · exact hno (he ▸ hk)

/-- Facts that hold may be added. -/
theorem St.addFacts {C} {A : AState} {x : MachineState} (h : St env σ C E s0 A x)
    {fs : List (Fact AVal)} (hfs : ∀ f ∈ fs, f.Holds (env.model.atomIn x.getMem) (AVal.eval E)) :
    St env σ C E s0 (A.addFacts fs) x :=
  ⟨h.holds, h.code, h.mem, h.heap, h.inv, h.slots, fun f hf => by
    rcases List.mem_append.mp hf with hf | hf
    · exact h.facts f hf
    · exact hfs f hf, h.wmem, h.strs⟩

/-- Fewer facts. -/
theorem St.gc {C} {A : AState} {x : MachineState} (h : St env σ C E s0 A x) :
    St env σ C E s0 A.gc x :=
  ⟨h.holds, h.code, h.mem, h.heap, h.inv, h.slots,
    fun f hf => h.facts f (List.mem_filter.mp hf).1, h.wmem, h.strs⟩

theorem St.gcIf {C} {A : AState} {x : MachineState} (h : St env σ C E s0 A x) :
    St env σ C E s0 A.gcIf x := by
  unfold AState.gcIf
  split
  · exact h.gc
  · exact h

/-- The frame writers are not part of the invariant: the check of them is separate. -/
theorem St.setFw {C} {A : AState} {x : MachineState} (h : St env σ C E s0 A x)
    (fw : List (AVal × AVal)) : St env σ C E s0 { A with fw := fw } x :=
  ⟨h.holds, h.code, h.mem, h.heap, h.inv, h.slots, h.facts, h.wmem, h.strs⟩

theorem St.setPC {C} {A : AState} {x : MachineState} {v : Word}
    (h : St env σ C E s0 A x) : St env σ C E s0 A (x.setPC v) :=
  ⟨AState.holds_setPC h.holds, by simp [h.code],
    fun a ha hnw hno hns => by simpa using h.mem a ha hnw hno hns,
    fun hh a hha hnp => by simpa using h.heap hh a hha hnp,
    Env.Inv_congr (fun _ _ _ => by simp) h.inv, h.slots, by simpa using h.facts,
    by simpa using h.wmem, by simpa using h.strs⟩

theorem St.setReg {C} {A : AState} {x : MachineState} {r : Reg} {v : AVal} {w : Word}
    (h : St env σ C E s0 A x) (hv : v.Holds E w) : St env σ C E s0 (A.set r v) (x.setReg r w) :=
  ⟨AState.holds_set h.holds hv, by simp [h.code],
    fun a ha hnw hno hns => by simpa using h.mem a ha hnw hno hns,
    fun hh a hha hnp => by simpa using h.heap hh a hha hnp,
    Env.Inv_congr (fun _ _ _ => by simp) h.inv, by
      intro p hp
      exact h.slots p (by simpa [AState.set] using hp),
    by simpa [AState.set] using h.facts, by simpa [AState.set] using h.wmem, by simpa using h.strs⟩

/-- A store the activation may write: everything but the slots as it was. -/
theorem St.setMem_written {C} {A : AState} {x : MachineState} (hF : Facts env σ E s0)
    (h : St env σ C E s0 A x) {k v : Word} (hk : Written σ E k)
    (hsl : ∀ p ∈ A.slots, p.2.Holds E ((x.setMem k v).getMem (E .x2 + p.1))) :
    St env σ C E s0 A (x.setMem k v) := by
  have hnh : ¬ env.model.heap k := fun hh =>
    hF.not_heap (env.model.heap_aligned _ hh) hk hh
  refine ⟨⟨fun r => by rw [getReg_setMem]; exact h.holds.1 r, hsl⟩, by simp [h.code],
    fun a ha hnw hno hns => ?_, fun hh a hha hnp => ?_, St.inv_setMem hF h (fun _ => hk), h.slots,
    St.facts_setMem h hnh, St.wmem_setMem hF h (Or.inl hk), St.strs_setMem hF h hk⟩
  · rw [getMem_setMem, if_neg]
    · exact h.mem a ha hnw hno hns
    · rintro rfl; exact hnw hk
  · rw [getMem_setMem, if_neg]
    · exact h.heap hh a hha hnp
    · rintro rfl; exact hnh hha

end Facts
/-! ## Candidates -/

section Cands

variable {env : Env} {σ : Iface} {E : Ent} {s0 : MachineState}

theorem protKey_inProt {env : Env} {a : Word} (h : env.protKey a = true) :
    Aligned a ∧ env.InProt a := by
  simp only [Env.protKey, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  obtain ⟨hal, ⟨b, l⟩, hR, hb, hl⟩ := h
  refine ⟨(aligned_iff a).mpr hal, ⟨b, l⟩, hR, Or.inl ?_⟩
  simp only
  have := a.isLt; have := b.isLt
  bv_omega

/-- A protected key holds its load-time contents at entry. -/
theorem Facts.protKey (hF : Facts env σ E s0) {a : Word} (h : env.protKey a = true) :
    E.mem a = env.init a := by
  obtain ⟨hal, hp⟩ := protKey_inProt h
  rw [hF.emem, hF.prot a hal hp]

theorem derefProt_sound (hF : Facts env σ E s0) :
    ∀ {a : Word} {ks : List Word} {t : Word}, derefProt env a ks = some t → t = E.deref a ks
  | _, [], _, h => by simp only [derefProt, Option.some.injEq] at h; subst h; rfl
  | a, k :: ks, t, h => by
    simp only [derefProt] at h
    split at h
    · rename_i hp
      rw [derefProt_sound hF h, Ent.deref, hF.protKey hp]
    · cases h

/-- Under a refinement that holds, a value it determines is what the refinement says. -/
theorem refineVal_sound (hF : Facts env σ E s0) {rf : AVal × Word} (hrf : rf.1.Holds E rf.2)
    {v : AVal} {w : Word} (hv : v.Holds E w) (heq : v = rf.1 → w = rf.2) {t : Word}
    (h : refineVal env rf v = some t) : t = w := by
  obtain ⟨root, c⟩ := rf
  simp only at hrf heq
  by_cases hveq : v = root
  · subst hveq
    simp only [refineVal, if_true, Option.some.injEq] at h; subst h
    exact (heq rfl).symm
  · unfold refineVal at h
    dsimp only at h
    rw [if_neg hveq] at h
    cases root with
    | lin r k0 =>
      simp only at h
      split at h
      · rename_i hk0; subst hk0
        cases v with
        | lin r' k =>
          simp only at h
          split at h
          · rename_i hr; subst hr
            simp only [Option.some.injEq] at h; subst h
            simp only [AVal.Holds] at hrf hv
            rw [hv, hrf]; simp
          · cases h
        | cell r' ks d =>
          simp only at h
          split at h
          · rename_i hr; subst hr
            cases hd : derefProt env c ks with
            | none => rw [hd] at h; cases h
            | some u =>
              rw [hd] at h
              simp only [Option.map_some, Option.some.injEq] at h; subst h
              simp only [AVal.Holds] at hrf hv
              rw [hv, derefProt_sound hF hd, hrf]; simp
          · cases h
        | const _ => cases h
        | top => cases h
        | oneOf _ => cases h
        | sym _ _ _ => cases h
      · cases h
    | cell r ks0 d0 =>
      simp only at h
      split at h
      · rename_i hd0; subst hd0
        cases v with
        | cell r' ks d =>
          simp only at h
          split at h
          · rename_i hr
            obtain ⟨rfl, hpre⟩ := hr
            cases hd : derefProt env c (ks.drop ks0.length) with
            | none => rw [hd] at h; cases h
            | some u =>
              rw [hd] at h
              simp only [Option.map_some, Option.some.injEq] at h; subst h
              simp only [AVal.Holds] at hrf hv
              rw [hv, derefProt_sound hF hd, hrf]
              obtain ⟨rest, hrest⟩ := List.isPrefixOf_iff_prefix.mp hpre
              rw [← hrest, List.drop_left, Ent.deref_eq, Ent.deref_eq, Ent.deref_eq, derefM_append']
              simp
          · cases h
        | lin _ _ => cases h
        | const _ => cases h
        | top => cases h
        | oneOf _ => cases h
        | sym _ _ _ => cases h
      · cases h
    | const _ => cases h
    | top => cases h
    | oneOf _ => cases h
    | sym _ _ _ => cases h

/-- A root's candidates: one of them holds, the one the value is when they coincide. -/
theorem rootGo_sound (hF : Facts env σ E s0) {r : Reg} {w : Word} :
    ∀ {pre ks : List Word} {best : Option (AVal × List Word)} {root : AVal} {cs : List Word},
    (∀ b cs', best = some (b, cs') → ∃ c ∈ cs', b.Holds E c ∧
      (b = .cell r (pre ++ ks) w → c = E.deref (E r) (pre ++ ks) + w)) →
    rootGo σ r pre best ks = some (root, cs) →
    ∃ c ∈ cs, root.Holds E c ∧ (root = .cell r (pre ++ ks) w → c = E.deref (E r) (pre ++ ks) + w)
  | _, [], best, root, cs, hb, h => by
    simp only [rootGo] at h
    simpa using hb root cs h
  | pre, k :: ks, best, root, cs, hb, h => by
    simp only [rootGo] at h
    rw [show pre ++ k :: ks = pre ++ [k] ++ ks by simp]
    refine rootGo_sound hF (pre := pre ++ [k]) (ks := ks) ?_ h
    intro b cs' hb'
    rw [List.append_assoc, List.singleton_append]
    split at hb'
    · rename_i cs'' hcc
      simp only [Option.some.injEq, Prod.mk.injEq] at hb'
      obtain ⟨rfl, rfl⟩ := hb'
      simp only [cellCands] at hcc
      cases hf : σ.cells.find? (fun c => c.r == r && c.ks == pre && c.k == k) with
      | none => rw [hf] at hcc; cases hcc
      | some c =>
        rw [hf] at hcc
        have hp := List.find?_some hf
        simp only [Bool.and_eq_true, beq_iff_eq] at hp
        obtain ⟨⟨hr, hks⟩, hk⟩ := hp
        have hmem := List.mem_of_find?_eq_some hf
        have := (hF.cells c hmem).2.2 _ hcc
        refine ⟨_, this, ?_, fun heq => ?_⟩
        · simp [AVal.Holds, Ent.deref_append, Cell.addr, hr, hks, hk]
        · simp only [AVal.cell.injEq] at heq
          obtain ⟨_, hks', hw⟩ := heq
          have hks'' : ks = [] := (List.cons.inj (List.append_cancel_left hks')).2.symm
          subst hks''
          subst hw
          simp [Ent.deref_append, Cell.addr, hr, hks, hk]
    · exact hb b cs' hb'

theorem root_sound (hF : Facts env σ E s0) {kn : Kn} (hk : KnRoots E kn) {v : AVal} {w : Word}
    (hv : v.Holds E w) {root : AVal} {cs : List Word} (h : rootK σ kn v = some (root, cs)) :
    ∃ c ∈ cs, root.Holds E c ∧ (v = root → c = w) := by
  unfold rootK at h
  cases hl : kn.roots.lookup v with
  | some cs' =>
    rw [hl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨w, hk _ (lookup_mem hl) w hv, hv, fun _ => rfl⟩
  | none =>
    rw [hl] at h
    cases v with
    | lin r k =>
      simp only [root?] at h
      cases hl' : σ.vals.lookup r with
      | none => rw [hl'] at h; cases h
      | some cs' =>
        rw [hl'] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨E r, hF.vals _ (lookup_mem hl'), by simp [AVal.Holds], fun heq => ?_⟩
        simp only [AVal.lin.injEq] at heq
        simp only [AVal.Holds] at hv
        obtain ⟨_, rfl⟩ := heq
        simp [hv]
    | cell r ks d =>
      simp only [root?] at h
      have hb : ∀ b cs', ((σ.vals.lookup r).map fun cs => ((.lin r 0 : AVal), cs)) = some (b, cs') →
          ∃ c ∈ cs', b.Holds E c ∧ (b = .cell r ([] ++ ks) d → c = E.deref (E r) ([] ++ ks) + d) := by
        intro b cs' hb
        cases hl' : σ.vals.lookup r with
        | none => rw [hl'] at hb; cases hb
        | some cs'' =>
          rw [hl'] at hb
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
          obtain ⟨rfl, rfl⟩ := hb
          exact ⟨E r, hF.vals _ (lookup_mem hl'), by simp [AVal.Holds], fun h => by cases h⟩
      obtain ⟨c, hc, hroot, heq⟩ := rootGo_sound hF (pre := []) (ks := ks) (w := d) hb h
      refine ⟨c, hc, hroot, fun hveq => ?_⟩
      simp only [AVal.Holds] at hv
      rw [hv, heq hveq.symm]; rfl
    | const c =>
      simp only [root?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [AVal.Holds] at hv
      exact ⟨c, by simp, rfl, fun _ => hv.symm⟩
    | oneOf cs' =>
      simp only [root?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨w, hv, hv, fun _ => rfl⟩
    | top => simp [root?] at h
    | sym _ _ _ => simp [root?] at h

theorem mapM_some_mem' {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ x ∈ l, ∃ y ∈ l', f x = some y
  | [], _, _, x, hx => by simp at hx
  | a :: l, l', h, x, hx => by
    cases hb : f a with
    | none => rw [List.mapM_cons, hb] at h; simp at h
    | some b =>
      cases hl : l.mapM f with
      | none => rw [List.mapM_cons, hb, hl] at h; simp at h
      | some l'' =>
        rw [List.mapM_cons, hb, hl] at h
        simp at h
        subst h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨b, List.mem_cons_self .., hb⟩
        · obtain ⟨y, hy, hfy⟩ := mapM_some_mem' hl x hx
          exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

/-- A value is among its candidates. -/
theorem cands_mem (hF : Facts env σ E s0) {kn : Kn} (hk : KnRoots E kn) {v : AVal} {w : Word}
    (hv : v.Holds E w) {cs : List Word} (h : cands env σ kn v = some cs) : w ∈ cs := by
  unfold cands at h
  cases hr : rootK σ kn v with
  | none => rw [hr] at h; cases h
  | some rc =>
    obtain ⟨root, cs0⟩ := rc
    rw [hr] at h
    simp only [Option.bind_some] at h
    obtain ⟨c, hc, hroot, heq⟩ := root_sound hF hk hv hr
    obtain ⟨t, ht, hrv⟩ := mapM_some_mem' h c hc
    rw [refineVal_sound hF hroot hv (fun hveq => (heq hveq).symm) hrv] at ht
    exact ht

theorem inCands_sound (hF : Facts env σ E s0) {kn : Kn} (hk : KnRoots E kn) {v : AVal} {w : Word}
    (hv : v.Holds E w) {cs : List Word} (h : inCands env σ kn v cs = true) : w ∈ cs := by
  unfold inCands at h
  cases hc : cands env σ kn v with
  | none => rw [hc] at h; cases h
  | some ws =>
    rw [hc] at h
    simp only [List.all_eq_true] at h
    exact List.contains_iff_mem.mp (h w (cands_mem hF hk hv hc))

/-- The root of a value's candidates mentions no symbol. -/
theorem root?_symFree {v : AVal} {root : AVal} {cs : List Word}
    (h : root? σ v = some (root, cs)) : root.symFree = true := by
  cases v with
  | lin r k =>
    simp only [root?, Option.map_eq_some_iff] at h
    obtain ⟨_, _, h⟩ := h
    simp only [Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | cell r ks d =>
    simp only [root?] at h
    have : ∀ (pre : List Word) (best : Option (AVal × List Word)) (ks : List Word),
        (∀ b, best = some b → b.1.symFree = true) →
        ∀ root cs, rootGo σ r pre best ks = some (root, cs) → root.symFree = true := by
      intro pre best ks
      induction ks generalizing pre best with
      | nil => intro hb root cs h; exact hb _ h
      | cons k ks ih =>
        intro hb root cs h
        simp only [rootGo] at h
        refine ih _ _ (fun b hb' => ?_) root cs h
        split at hb'
        · simp only [Option.some.injEq] at hb'; rw [← hb']; rfl
        · exact hb b hb'
    refine this [] _ ks (fun b hb => ?_) root cs h
    simp only [Option.map_eq_some_iff] at hb
    obtain ⟨_, _, hb⟩ := hb
    rw [← hb]; rfl
  | const c => simp only [root?, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; rfl
  | oneOf cs' => simp only [root?, Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]; rfl
  | top => simp [root?] at h
  | sym _ _ _ => simp [root?] at h

/-- The refinement a fan-out branch runs under: one candidate of the root, the one the
    value is. -/
theorem fanOut_sound (hF : Facts env σ E s0) {v : AVal} {w : Word} (hv : v.Holds E w)
    {off : BitVec 12} {k : Option (AVal × Word) → Word → Option (List Edge)} {es : List Edge}
    (h : fanOut env σ v off k = some es) :
    ∃ root c es', root.Holds E c ∧ root.symFree = true ∧
      k (some (root, c)) ((w + signExtend12 off) &&& ~~~1#64) = some es' ∧ ∀ e ∈ es', e ∈ es := by
  unfold fanOut at h
  cases hr : root? σ v with
  | none => rw [hr] at h; cases h
  | some rc =>
    obtain ⟨root, cs⟩ := rc
    rw [hr] at h
    simp only at h
    cases hm : cs.mapM (fun c => (refineVal env (root, c) v).bind fun t =>
        k (some (root, c)) ((t + signExtend12 off) &&& ~~~1#64)) with
    | none => rw [hm] at h; cases h
    | some l =>
      rw [hm] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have hr' : rootK σ {} v = some (root, cs) := by simp [rootK, hr]
      obtain ⟨c, hc, hroot, heq⟩ := root_sound hF knRoots_empty hv hr'
      obtain ⟨es', hes', hfc⟩ := mapM_some_mem' hm c hc
      cases hrv : refineVal env (root, c) v with
      | none => rw [hrv] at hfc; cases hfc
      | some t =>
        rw [hrv] at hfc
        simp only [Option.bind_some] at hfc
        rw [refineVal_sound hF hroot hv (fun hveq => (heq hveq).symm) hrv] at hfc
        exact ⟨root, c, es', hroot, root?_symFree hr, hfc,
          fun e he => List.mem_flatten.mpr ⟨es', hes', he⟩⟩

end Cands

/-! ## Symbols

A symbol's value is whatever the entry valuation's `sym` says; the activation argument
chooses it when the symbol is made. Everything that does not mention a symbol is
indifferent to its value. -/

def _root_.MachineChecked.RiscV.Frame.Ent.withSym (E : Ent) (V : Nat → Nat → Word) : Ent :=
  { E with sym := V }

theorem Ent.eq_withSym {E E' : Ent} (hr : E'.reg = E.reg) (hm : E'.mem = E.mem) :
    E' = E.withSym E'.sym := by
  cases E'; cases E; simp only [Ent.withSym] at *; simp [hr, hm]

section Sym

variable {E : Ent} {V : Nat → Nat → Word}

@[simp] theorem Ent.withSym_reg : (E.withSym V).reg = E.reg := rfl
@[simp] theorem Ent.withSym_mem : (E.withSym V).mem = E.mem := rfl
@[simp] theorem Ent.withSym_sym : (E.withSym V).sym = V := rfl
@[simp] theorem Ent.withSym_apply (r : Reg) : (E.withSym V) r = E r := rfl
@[simp] theorem Ent.withSym_withSym (V' : Nat → Nat → Word) :
    (E.withSym V).withSym V' = E.withSym V' := rfl

theorem Ent.deref_congr {E E' : Ent} (h : E'.mem = E.mem) (a : Word) (ks : List Word) :
    E'.deref a ks = E.deref a ks := by
  induction ks generalizing a with
  | nil => rfl
  | cons k ks ih => simp [Ent.deref, h, ih]

@[simp] theorem Ent.deref_withSym (a : Word) (ks : List Word) :
    (E.withSym V).deref a ks = E.deref a ks := Ent.deref_congr (E := E) (E' := E.withSym V) rfl a ks

theorem AVal.holds_withSym {v : AVal} (h : v.symFree = true) {w : Word} :
    v.Holds (E.withSym V) w ↔ v.Holds E w := by
  cases v <;> simp [AVal.symFree, AVal.Holds] at h ⊢

theorem AVal.eval_withSym {v : AVal} (h : v.symFree = true) : v.eval (E.withSym V) = v.eval E := by
  cases v <;> simp [AVal.symFree, AVal.eval] at h ⊢

theorem Len.eval_withSym (l : Len) : l.eval (E.withSym V) = l.eval E := by
  cases l <;> rfl

theorem Cell.addr_withSym (c : Cell) : c.addr (E.withSym V) = c.addr E := by
  simp [Cell.addr]

theorem Fact.holds_withSym {f : Fact AVal} (h : f.symFree = true) {A : Nat → List Word → Prop} :
    f.Holds A (AVal.eval (E.withSym V)) ↔ f.Holds A (AVal.eval E) := by
  simp only [Fact.symFree, Bool.not_eq_true'] at h
  exact Fact.holds_congr A (fun v => !v.symFree)
    (fun v hv => AVal.eval_withSym (by simpa using hv)) h

variable {env : Env} {σ : Iface} (hsf : σ.symFree = true)
include hsf

theorem Iface.symFree_parts :
    (∀ it ∈ σ.foot, it.base.symFree = true) ∧ (∀ v ∈ σ.nz, v.symFree = true) ∧
    (∀ e ∈ σ.strs, e.1.symFree = true ∧ e.2.symFree = true) ∧ (∀ f ∈ σ.pre, f.symFree = true) := by
  simp only [Iface.symFree, Bool.and_eq_true, List.all_eq_true] at hsf
  exact ⟨hsf.1.1.1, hsf.1.1.2, hsf.1.2, hsf.2⟩

theorem Item.hits_withSym {it : Item} (hit : it ∈ σ.foot) (a : Word) :
    it.Hits (E.withSym V) a ↔ it.Hits E a := by
  simp only [Item.Hits, AVal.eval_withSym ((Iface.symFree_parts hsf).1 it hit), Len.eval_withSym]

theorem Written_withSym (a : Word) : Written σ (E.withSym V) a ↔ Written σ E a := by
  simp only [Written, Ent.withSym]
  constructor <;> rintro (h | ⟨it, hit, hh⟩)
  · exact Or.inl h
  · exact Or.inr ⟨it, hit, (Item.hits_withSym hsf hit a).mp hh⟩
  · exact Or.inl h
  · exact Or.inr ⟨it, hit, (Item.hits_withSym hsf hit a).mpr hh⟩

theorem StrHit_withSym (m : Word → Word) (a : Word) :
    StrHit env σ (E.withSym V) m a ↔ StrHit env σ E m a := by
  simp only [StrHit]
  constructor <;> rintro ⟨e, he, hh⟩ <;> refine ⟨e, he, ?_⟩ <;>
    simp only [AVal.eval_withSym ((Iface.symFree_parts hsf).2.2.1 e he).1,
      AVal.eval_withSym ((Iface.symFree_parts hsf).2.2.1 e he).2] at hh ⊢ <;> exact hh

theorem FieldKey_withSym (m : Word → Word) (a : Word) :
    FieldKey env σ (E.withSym V) m a ↔ FieldKey env σ E m a := by
  simp only [FieldKey]
  constructor <;> rintro ⟨e, he, hh⟩ <;> refine ⟨e, he, ?_⟩ <;>
    simp only [AVal.eval_withSym ((Iface.symFree_parts hsf).2.2.1 e he).1,
      AVal.eval_withSym ((Iface.symFree_parts hsf).2.2.1 e he).2] at hh ⊢ <;> exact hh

theorem StrsPre_withSym (m : Word → Word) :
    StrsPre env σ (E.withSym V) m ↔ StrsPre env σ E m := by
  have hs := (Iface.symFree_parts hsf).2.2.1
  simp only [StrsPre, Written_withSym hsf, StrHit_withSym hsf, Cell.addr_withSym]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨fun e he => ?_, h2⟩ <;> have := h1 e he <;>
    simp only [AVal.eval_withSym (hs e he).1, AVal.eval_withSym (hs e he).2] at this ⊢ <;> exact this

theorem StrsPost_withSym (m m' : Word → Word) :
    StrsPost env σ (E.withSym V) m m' ↔ StrsPost env σ E m m' := by
  have hs := (Iface.symFree_parts hsf).2.2.1
  simp only [StrsPost, Written_withSym hsf, StrHit_withSym hsf]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨fun e he => ?_, h2⟩ <;> have := h1 e he <;>
    simp only [AVal.eval_withSym (hs e he).1, AVal.eval_withSym (hs e he).2] at this ⊢ <;> exact this

theorem StrsInv_withSym (m m' : Word → Word) :
    StrsInv env σ (E.withSym V) m m' ↔ StrsInv env σ E m m' := by
  have hs := (Iface.symFree_parts hsf).2.2.1
  simp only [StrsInv, Written_withSym hsf, StrHit_withSym hsf]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨fun e he => ?_, h2⟩ <;> have := h1 e he <;>
    simp only [AVal.eval_withSym (hs e he).1, AVal.eval_withSym (hs e he).2] at this ⊢ <;> exact this

/-- The facts of an activation do not depend on the symbols' values. -/
theorem Facts.withSym {s0 : MachineState} (hF : Facts env σ E s0) :
    Facts env σ (E.withSym V) s0 := by
  have hp := Iface.symFree_parts hsf
  refine ⟨hF.wf, hF.ok, hF.depth, hF.top, hF.al, hF.prot, fun it hit a ha hh => ?_,
    fun v hv => ?_, hF.vals, fun c hc => ?_, fun c hc => ?_, hF.inv, ?_, hF.strsPtr, hF.symFree,
    fun f hf => ?_, hF.emem⟩
  · exact hF.foot it hit a ha ((Item.hits_withSym hsf hit a).mp hh)
  · rw [AVal.eval_withSym (hp.2.1 v hv)]; exact hF.nz v hv
  · simp only [Cell.addr_withSym, Written_withSym hsf]
    have := hF.cells c hc
    simpa [Cell.addr] using this
  · simp only [Cell.addr_withSym]
    exact hF.cellsOwn c hc
  · exact (StrsPre_withSym hsf _).mpr hF.strs
  · rw [Fact.holds_withSym (hp.2.2.2 f hf)]; exact hF.pre f hf

omit hsf in
/-- A register of a state nothing of which mentions the symbol. -/
theorem AState.get_not_mentions (A : AState) {i j : Nat} (hm : ¬ A.mentionsSym i j = true)
    (r : Reg) : (A.get r).mentions i j = false := by
  simp only [AState.mentionsSym, Bool.or_eq_true, List.any_eq_true, not_or] at hm
  by_cases h0 : r = .x0
  · subst h0; simp [AState.get, AVal.mentions]
  · simp only [AState.get, h0, if_false]
    cases hv : A.regs[regIdx r]? with
    | none => simp [List.getD_eq_getElem?_getD, hv, AVal.mentions]
    | some v =>
      rw [List.getD_eq_getElem?_getD, hv, Option.getD_some]
      exact Bool.eq_false_iff.mpr fun h => hm.1.1.1 ⟨v, List.mem_of_getElem? hv, h⟩

omit hsf in
theorem AState.get_kill (A : AState) (i j : Nat) (r : Reg) :
    (A.kill i j).get r = if (A.get r).mentions i j then .top else A.get r := by
  unfold AState.kill
  split
  · by_cases h0 : r = .x0
    · subst h0; simp [AState.get, AVal.mentions]
    · simp only [AState.get, h0, if_false, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases A.regs[regIdx r]? with
      | none => simp [AVal.mentions]
      | some v => simp
  · rename_i hm
    rw [AState.get_not_mentions A hm r]; rfl

omit hsf in
theorem AState.kill_slots {A : AState} {i j : Nat} {p : Word × AVal} (hp : p ∈ (A.kill i j).slots) :
    p ∈ A.slots ∧ p.2.mentions i j = false := by
  unfold AState.kill at hp
  split at hp
  · have := List.mem_filter.mp hp
    simpa using this
  · rename_i hm
    simp only [AState.mentionsSym, Bool.or_eq_true, List.any_eq_true, not_or] at hm
    exact ⟨hp, Bool.eq_false_iff.mpr fun h => hm.1.1.2 ⟨p, hp, h⟩⟩

omit hsf in
theorem AState.kill_facts {A : AState} {i j : Nat} {f : Fact AVal} (hf : f ∈ (A.kill i j).facts) :
    f ∈ A.facts ∧ f.mentionsSym i j = false := by
  unfold AState.kill at hf
  split at hf
  · have := List.mem_filter.mp hf
    simpa using this
  · rename_i hm
    simp only [AState.mentionsSym, Bool.or_eq_true, List.any_eq_true, not_or] at hm
    exact ⟨hf, Bool.eq_false_iff.mpr fun h => hm.1.2 ⟨f, hf, h⟩⟩

omit hsf in
theorem AState.kill_wmem {A : AState} {i j : Nat} {p : AVal × AVal} (hp : p ∈ (A.kill i j).wmem) :
    p ∈ A.wmem ∧ (p.1.mentions i j || p.2.mentions i j) = false := by
  unfold AState.kill at hp
  split at hp
  · have := List.mem_filter.mp hp
    simpa using this
  · rename_i hm
    simp only [AState.mentionsSym, Bool.or_eq_true, List.any_eq_true, not_or] at hm
    exact ⟨hp, Bool.eq_false_iff.mpr fun h => hm.2 ⟨p, hp, by simpa using h⟩⟩

omit hsf in
theorem AState.kill_fw (A : AState) (i j : Nat) : (A.kill i j).fw = A.fw := by
  unfold AState.kill; split <;> rfl

omit hsf in
/-- Forgetting what mentions a symbol keeps the invariant. -/
theorem St.kill {C : Word → Option Instr} {s0 : MachineState} {A : AState} {x : MachineState}
    (h : St env σ C E s0 A x) (i j : Nat) : St env σ C E s0 (A.kill i j) x := by
  refine ⟨⟨fun r => ?_, fun p hp => ?_⟩, h.code, h.mem, h.heap, h.inv, fun p hp => ?_,
    fun f hf => ?_, fun p hp => ?_, h.strs⟩
  · rw [AState.get_kill]; split
    · trivial
    · exact h.holds.1 r
  · exact h.holds.2 p (AState.kill_slots hp).1
  · exact h.slots p (AState.kill_slots hp).1
  · exact h.facts f (AState.kill_facts hf).1
  · exact h.wmem p (AState.kill_wmem hp).1

omit hsf in
theorem AVal.holds_agree {V' : Nat → Nat → Word} {i j : Nat}
    (hV : ∀ i' j', (i' = i ∧ j' = j) ∨ V' i' j' = E.sym i' j') {v : AVal}
    (hv : v.mentions i j = false) {w : Word} : v.Holds (E.withSym V') w ↔ v.Holds E w := by
  cases v with
  | sym i' j' k =>
    simp only [AVal.mentions, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hv
    simp only [AVal.Holds, Ent.withSym_sym]
    rcases hV i' j' with ⟨rfl, rfl⟩ | h
    · rcases hv with hv | hv <;> exact absurd rfl hv
    · rw [h]
  | _ => simp [AVal.Holds]

omit hsf in
theorem AVal.eval_agree {V' : Nat → Nat → Word} {i j : Nat}
    (hV : ∀ i' j', (i' = i ∧ j' = j) ∨ V' i' j' = E.sym i' j') {v : AVal}
    (hv : v.mentions i j = false) : v.eval (E.withSym V') = v.eval E := by
  cases v with
  | sym i' j' k =>
    simp only [AVal.mentions, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq] at hv
    simp only [AVal.eval, Ent.withSym_sym]
    rcases hV i' j' with ⟨rfl, rfl⟩ | h
    · rcases hv with hv | hv <;> exact absurd rfl hv
    · rw [h]
  | _ => simp [AVal.eval]

/-- After a symbol is killed, its value may change. -/
theorem St.resym {C : Word → Option Instr} {s0 : MachineState} {A : AState} {x : MachineState}
    (h : St env σ C E s0 (A.kill i j) x) {V' : Nat → Nat → Word}
    (hV : ∀ i' j', (i' = i ∧ j' = j) ∨ V' i' j' = E.sym i' j') :
    St env σ C (E.withSym V') s0 (A.kill i j) x := by
  refine ⟨⟨fun r => ?_, fun p hp => ?_⟩, h.code, ?_, h.heap, h.inv, h.slots, fun f hf => ?_,
    fun p hp => ?_, ?_⟩
  · rw [AState.get_kill]
    have := h.holds.1 r
    rw [AState.get_kill] at this
    split at this
    · rename_i hm; rw [if_pos hm]; trivial
    · rename_i hm; rw [if_neg hm]; rw [AVal.holds_agree hV (by simpa using hm)]; exact this
  · have hp' := (AState.kill_slots hp).2
    rw [show (E.withSym V') .x2 = E .x2 from rfl, AVal.holds_agree hV hp']
    exact h.holds.2 p hp
  · intro a ha hnw hno hns
    rw [Written_withSym hsf] at hnw
    rw [StrHit_withSym hsf] at hns
    exact h.mem a ha hnw hno hns
  · have hf' := (AState.kill_facts hf).2
    simp only [Fact.mentionsSym] at hf'
    rw [← Fact.holds_congr _ (fun v : AVal => v.mentions i j) (fun v hv => (AVal.eval_agree hV hv).symm) hf']
    exact h.facts f hf
  · have hp' := (AState.kill_wmem hp).2
    simp only [Bool.or_eq_false_iff] at hp'
    obtain ⟨h1, h2, h3⟩ := h.wmem p hp
    rw [AVal.eval_agree hV hp'.1, FieldKey_withSym hsf, AVal.holds_agree hV hp'.2]
    exact ⟨h1, h2, h3⟩
  · rw [StrsInv_withSym hsf]; exact h.strs

/-! ### Forgetting an instruction's symbols -/

omit hsf in
theorem AState.get_not_mentionsAt (A : AState) {i : Nat} (hm : ¬ A.mentionsAt i = true)
    (r : Reg) : (A.get r).mentionsAt i = false := by
  simp only [AState.mentionsAt, Bool.or_eq_true, List.any_eq_true, not_or] at hm
  by_cases h0 : r = .x0
  · subst h0; simp [AState.get, AVal.mentionsAt]
  · simp only [AState.get, h0, if_false]
    cases hv : A.regs[regIdx r]? with
    | none => simp [List.getD_eq_getElem?_getD, hv, AVal.mentionsAt]
    | some v =>
      rw [List.getD_eq_getElem?_getD, hv, Option.getD_some]
      exact Bool.eq_false_iff.mpr fun h => hm.1.1.1 ⟨v, List.mem_of_getElem? hv, h⟩

omit hsf in
theorem AState.get_killAll (A : AState) (i : Nat) (r : Reg) :
    (A.killAll i).get r = if (A.get r).mentionsAt i then .top else A.get r := by
  unfold AState.killAll
  split
  · by_cases h0 : r = .x0
    · subst h0; simp [AState.get, AVal.mentionsAt]
    · simp only [AState.get, h0, if_false, List.getD_eq_getElem?_getD, List.getElem?_map]
      cases A.regs[regIdx r]? with
      | none => simp [AVal.mentionsAt]
      | some v => simp
  · rename_i hm
    rw [AState.get_not_mentionsAt A hm r]; rfl

omit hsf in
theorem AState.killAll_slots {A : AState} {i : Nat} {p : Word × AVal} (hp : p ∈ (A.killAll i).slots) :
    p ∈ A.slots ∧ p.2.mentionsAt i = false := by
  unfold AState.killAll at hp
  split at hp
  · have := List.mem_filter.mp hp
    simpa using this
  · rename_i hm
    simp only [AState.mentionsAt, Bool.or_eq_true, List.any_eq_true, not_or] at hm
    exact ⟨hp, Bool.eq_false_iff.mpr fun h => hm.1.1.2 ⟨p, hp, h⟩⟩

omit hsf in
theorem AState.killAll_facts {A : AState} {i : Nat} {f : Fact AVal} (hf : f ∈ (A.killAll i).facts) :
    f ∈ A.facts ∧ f.mentionsAt i = false := by
  unfold AState.killAll at hf
  split at hf
  · have := List.mem_filter.mp hf
    simpa using this
  · rename_i hm
    simp only [AState.mentionsAt, Bool.or_eq_true, List.any_eq_true, not_or] at hm
    exact ⟨hf, Bool.eq_false_iff.mpr fun h => hm.1.2 ⟨f, hf, h⟩⟩

omit hsf in
theorem AState.killAll_wmem {A : AState} {i : Nat} {p : AVal × AVal} (hp : p ∈ (A.killAll i).wmem) :
    p ∈ A.wmem ∧ (p.1.mentionsAt i || p.2.mentionsAt i) = false := by
  unfold AState.killAll at hp
  split at hp
  · have := List.mem_filter.mp hp
    simpa using this
  · rename_i hm
    simp only [AState.mentionsAt, Bool.or_eq_true, List.any_eq_true, not_or] at hm
    exact ⟨hp, Bool.eq_false_iff.mpr fun h => hm.2 ⟨p, hp, by simpa using h⟩⟩

omit hsf in
theorem AState.killAll_fw (A : AState) (i : Nat) : (A.killAll i).fw = A.fw := by
  unfold AState.killAll; split <;> rfl

omit hsf in
theorem St.killAll {C : Word → Option Instr} {s0 : MachineState} {A : AState} {x : MachineState}
    (h : St env σ C E s0 A x) (i : Nat) : St env σ C E s0 (A.killAll i) x := by
  refine ⟨⟨fun r => ?_, fun p hp => ?_⟩, h.code, h.mem, h.heap, h.inv, fun p hp => ?_,
    fun f hf => ?_, fun p hp => ?_, h.strs⟩
  · rw [AState.get_killAll]; split
    · trivial
    · exact h.holds.1 r
  · exact h.holds.2 p (AState.killAll_slots hp).1
  · exact h.slots p (AState.killAll_slots hp).1
  · exact h.facts f (AState.killAll_facts hf).1
  · exact h.wmem p (AState.killAll_wmem hp).1

omit hsf in
theorem AVal.holds_agreeAt {V' : Nat → Nat → Word} {i : Nat}
    (hV : ∀ i' j', i' = i ∨ V' i' j' = E.sym i' j') {v : AVal}
    (hv : v.mentionsAt i = false) {w : Word} : v.Holds (E.withSym V') w ↔ v.Holds E w := by
  cases v with
  | sym i' j' k =>
    simp only [AVal.mentionsAt, beq_eq_false_iff_ne, ne_eq] at hv
    simp only [AVal.Holds, Ent.withSym_sym]
    rcases hV i' j' with rfl | h
    · exact absurd rfl hv
    · rw [h]
  | _ => simp [AVal.Holds]

omit hsf in
theorem AVal.eval_agreeAt {V' : Nat → Nat → Word} {i : Nat}
    (hV : ∀ i' j', i' = i ∨ V' i' j' = E.sym i' j') {v : AVal}
    (hv : v.mentionsAt i = false) : v.eval (E.withSym V') = v.eval E := by
  cases v with
  | sym i' j' k =>
    simp only [AVal.mentionsAt, beq_eq_false_iff_ne, ne_eq] at hv
    simp only [AVal.eval, Ent.withSym_sym]
    rcases hV i' j' with rfl | h
    · exact absurd rfl hv
    · rw [h]
  | _ => simp [AVal.eval]

/-- After an instruction's symbols are forgotten, their values may change. -/
theorem St.resymAll {C : Word → Option Instr} {s0 : MachineState} {A : AState} {x : MachineState}
    {i : Nat} (h : St env σ C E s0 (A.killAll i) x) {V' : Nat → Nat → Word}
    (hV : ∀ i' j', i' = i ∨ V' i' j' = E.sym i' j') :
    St env σ C (E.withSym V') s0 (A.killAll i) x := by
  refine ⟨⟨fun r => ?_, fun p hp => ?_⟩, h.code, ?_, h.heap, h.inv, h.slots, fun f hf => ?_,
    fun p hp => ?_, ?_⟩
  · rw [AState.get_killAll]
    have := h.holds.1 r
    rw [AState.get_killAll] at this
    split at this
    · rename_i hm; rw [if_pos hm]; trivial
    · rename_i hm; rw [if_neg hm]; rw [AVal.holds_agreeAt hV (by simpa using hm)]; exact this
  · have hp' := (AState.killAll_slots hp).2
    rw [show (E.withSym V') .x2 = E .x2 from rfl, AVal.holds_agreeAt hV hp']
    exact h.holds.2 p hp
  · intro a ha hnw hno hns
    rw [Written_withSym hsf] at hnw
    rw [StrHit_withSym hsf] at hns
    exact h.mem a ha hnw hno hns
  · have hf' := (AState.killAll_facts hf).2
    simp only [Fact.mentionsAt] at hf'
    rw [← Fact.holds_congr _ (fun v : AVal => v.mentionsAt i)
      (fun v hv => (AVal.eval_agreeAt hV hv).symm) hf']
    exact h.facts f hf
  · have hp' := (AState.killAll_wmem hp).2
    simp only [Bool.or_eq_false_iff] at hp'
    obtain ⟨h1, h2, h3⟩ := h.wmem p hp
    rw [AVal.eval_agreeAt hV hp'.1, FieldKey_withSym hsf, AVal.holds_agreeAt hV hp'.2]
    exact ⟨h1, h2, h3⟩
  · rw [StrsInv_withSym hsf]; exact h.strs

omit hsf in
/-- A symbol-free value does not mention any symbol. -/
theorem AVal.mentionsAt_of_symFree {v : AVal} (h : v.symFree = true) (i : Nat) :
    v.mentionsAt i = false := by
  cases v <;> simp_all [AVal.symFree, AVal.mentionsAt]

/-- Making a symbol: its value is the register's, and whatever facts hold of it. -/
theorem St.mkSym {C : Word → Option Instr} {s0 : MachineState} {A : AState} {x : MachineState}
    (h : St env σ C E s0 A x) (i j : Nat) (r : Reg) (w : Word) {fs : List (Fact AVal)}
    (hfs : ∀ f ∈ fs, f.Holds (env.model.atomIn x.getMem)
      (AVal.eval (E.withSym fun i' j' => if i' = i ∧ j' = j then w else E.sym i' j'))) :
    St env σ C (E.withSym fun i' j' => if i' = i ∧ j' = j then w else E.sym i' j') s0
      (((A.kill i j).set r (.sym i j 0)).addFacts fs) (x.setReg r w) := by
  have hV : ∀ i' j', (i' = i ∧ j' = j) ∨
      (if i' = i ∧ j' = j then w else E.sym i' j') = E.sym i' j' := by
    intro i' j'
    by_cases hc : i' = i ∧ j' = j
    · exact Or.inl hc
    · exact Or.inr (if_neg hc)
  have h1 := St.resym hsf (h.kill i j) hV
  have h2 : St env σ C (E.withSym fun i' j' => if i' = i ∧ j' = j then w else E.sym i' j') s0
      ((A.kill i j).set r (.sym i j 0)) (x.setReg r w) := by
    refine ⟨AState.holds_set h1.holds (by simp [AVal.Holds]), by simp [h1.code],
      fun a ha hnw hno hns => by simpa using h1.mem a ha hnw hno hns,
      fun hh a hha hnp => by simpa using h1.heap hh a hha hnp,
      Env.Inv_congr (fun _ _ _ => by simp) h1.inv, fun p hp => h1.slots p (by simpa [AState.set] using hp),
      fun f hf => by simpa [AState.set] using h1.facts f hf,
      fun p hp => by simpa [AState.set] using h1.wmem p hp, by simpa using h1.strs⟩
  refine ⟨h2.holds, h2.code, h2.mem, h2.heap, h2.inv, fun p hp => h2.slots p hp, fun f hf => ?_,
    h2.wmem, h2.strs⟩
  simp only [AState.addFacts, List.mem_append] at hf
  rcases hf with hf | hf
  · exact h2.facts f hf
  · simpa using hfs f hf

/-! ### Joining: the target's symbols stand for the source's values -/

/-- The symbol values after a jump to `j`: what `θ` says, where it says anything. -/
def phiSym (E : Ent) (j : Nat) (θ : List (Nat × AVal)) : Nat → Nat → Word := fun i k =>
  if i = j then
    match θ.lookup k with
    | some v => v.eval E
    | none => E.sym i k
  else E.sym i k

omit hsf in
theorem AVal.eval_addK_ptr {v : AVal} (hv : v.isPtr = true) (d : Word) :
    (v.addK d).eval E = v.eval E + d := by
  cases v <;> simp [AVal.isPtr, AVal.addK, AVal.eval, BitVec.add_assoc] at hv ⊢

omit hsf in
theorem AVal.isPtr_addK {v : AVal} (hv : v.isPtr = true) (d : Word) : (v.addK d).isPtr = true := by
  cases v <;> simp [AVal.isPtr, AVal.addK] at hv ⊢

omit hsf in
theorem AVal.eval_substSym {j : Nat} {θ : List (Nat × AVal)} (hθ : ∀ q ∈ θ, q.2.isPtr = true)
    (v : AVal) : (v.substSym j θ).eval E = v.eval (E.withSym (phiSym E j θ)) := by
  cases v with
  | sym i k off =>
    by_cases hij : i = j
    · subst hij
      cases hl : θ.lookup k with
      | none => simp [AVal.substSym, AVal.eval, phiSym, hl]
      | some u =>
        simp only [AVal.substSym, if_true, hl]
        rw [AVal.eval_addK_ptr (hθ _ (lookup_mem hl))]
        simp [AVal.eval, phiSym, hl]
    · simp [AVal.substSym, AVal.eval, phiSym, hij]
  | _ => simp [AVal.substSym, AVal.eval]

omit hsf in
theorem AVal.holds_substSym {j : Nat} {θ : List (Nat × AVal)} (hθ : ∀ q ∈ θ, q.2.isPtr = true)
    (v : AVal) (w : Word) : (v.substSym j θ).Holds E w ↔ v.Holds (E.withSym (phiSym E j θ)) w := by
  cases v with
  | sym i k off =>
    by_cases hij : i = j
    · subst hij
      cases hl : θ.lookup k with
      | none => simp [AVal.substSym, AVal.Holds, phiSym, hl]
      | some u =>
        have hp := hθ _ (lookup_mem hl)
        simp only [AVal.substSym, if_true, hl]
        rw [holds_iff_eval (AVal.isPtr_addK hp off), AVal.eval_addK_ptr hp]
        simp [AVal.Holds, phiSym, hl]
    · simp [AVal.substSym, AVal.Holds, phiSym, hij]
  | _ => simp [AVal.substSym, AVal.Holds]

omit hsf in
theorem AState.get_subst (A : AState) (j : Nat) (θ : List (Nat × AVal)) (r : Reg) :
    (A.subst j θ).get r = (A.get r).substSym j θ := by
  by_cases h0 : r = .x0
  · subst h0; simp [AState.get, AVal.substSym]
  · simp only [AState.get, h0, if_false, AState.subst, List.getD_eq_getElem?_getD, List.getElem?_map]
    cases A.regs[regIdx r]? with
    | none => simp [AVal.substSym]
    | some v => simp

omit hsf in
theorem phiOf_isPtr (j : Nat) (B C : AState) : ∀ q ∈ phiOf j B C, q.2.isPtr = true := by
  intro q hq
  simp only [phiOf, List.mem_append, List.mem_filterMap] at hq
  rcases hq with ⟨r, _, hr⟩ | ⟨p, _, hp⟩
  · split at hr
    · split at hr
      · rename_i hc; simp only [Option.some.injEq] at hr; subst hr
        exact AVal.isPtr_addK hc.2 _
      · cases hr
    · cases hr
  · split at hp
    · split at hp
      · simp only [Option.bind_eq_some_iff] at hp
        obtain ⟨v, _, hv⟩ := hp
        split at hv
        · rename_i hc; simp only [Option.some.injEq] at hv; subst hv
          exact AVal.isPtr_addK hc _
        · cases hv
      · cases hp
    · cases hp

/-- The invariant of the substituted target state is the target's, with the symbols as the
    substitution says. -/
theorem St.unsubst {C : Word → Option Instr} {s0 : MachineState} {A : AState} {x : MachineState}
    {j : Nat} {θ : List (Nat × AVal)} (hθ : ∀ q ∈ θ, q.2.isPtr = true)
    (h : St env σ C E s0 (A.subst j θ) x) : St env σ C (E.withSym (phiSym E j θ)) s0 A x := by
  refine ⟨⟨fun r => ?_, fun p hp => ?_⟩, h.code, ?_, h.heap, h.inv, fun p hp => ?_,
    fun f hf => ?_, fun p hp => ?_, ?_⟩
  · have := h.holds.1 r
    rw [AState.get_subst, AVal.holds_substSym hθ] at this
    exact this
  · have := h.holds.2 (p.1, p.2.substSym j θ) (by
      simp only [AState.subst, List.mem_map]; exact ⟨p, hp, rfl⟩)
    simp only at this
    rw [AVal.holds_substSym hθ] at this
    exact this
  · intro a ha hnw hno hns
    rw [Written_withSym hsf] at hnw
    rw [StrHit_withSym hsf] at hns
    exact h.mem a ha hnw hno hns
  · exact h.slots (p.1, p.2.substSym j θ) (by simp only [AState.subst, List.mem_map]; exact ⟨p, hp, rfl⟩)
  · have := h.facts (f.substSym j θ) (by simp only [AState.subst, List.mem_map]; exact ⟨f, hf, rfl⟩)
    simp only [Fact.substSym] at this
    rw [Fact.holds_map] at this
    have he : AVal.eval E ∘ AVal.substSym j θ = AVal.eval (E.withSym (phiSym E j θ)) := by
      funext v; simp [Function.comp, AVal.eval_substSym hθ]
    rw [he] at this
    exact this
  · obtain ⟨h1, h2, h3⟩ := h.wmem (p.1.substSym j θ, p.2.substSym j θ)
      (by simp only [AState.subst, List.mem_map]; exact ⟨p, hp, rfl⟩)
    simp only at h1 h2 h3
    rw [AVal.eval_substSym hθ] at h2 h3
    rw [AVal.holds_substSym hθ] at h3
    refine ⟨?_, (FieldKey_withSym hsf _ _).mpr h2, h3⟩
    cases hp1 : p.1 <;> simp [AVal.substSym, AVal.isPtr] at h1 ⊢ <;> (try split at h1) <;> simp_all [AVal.isPtr]
  · rw [StrsInv_withSym hsf]; exact h.strs

/-- The target of a jump the check accepts: its invariant, with its own symbols standing for
    what the source has. -/
theorem St.ofLeAt {C : Word → Option Instr} {s0 : MachineState} {B D : AState} {x : MachineState}
    {j : Nat} (h : St env σ C E s0 B x) (hle : Check.leAt j B D = true) :
    St env σ C (E.withSym (phiSym E j (phiOf j B D))) s0 D x := by
  refine St.unsubst hsf (phiOf_isPtr j B D) ?_
  unfold Check.leAt at hle
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, List.any_eq_true,
    beq_iff_eq] at hle
  obtain ⟨⟨⟨⟨hregs, hslots⟩, hfacts⟩, hwmem⟩, _⟩ := hle
  refine ⟨⟨fun r => AVal.holds_of_le (hregs r (mem_allRegs r)) (h.holds.1 r),
    fun p hp => h.holds.2 p (hslots p hp)⟩, h.code, h.mem, h.heap, h.inv,
    fun p hp => h.slots p (hslots p hp), fun f hf => h.facts f (hfacts f hf), fun p hp => ?_, h.strs⟩
  obtain ⟨q, hq, hq1, hq2⟩ := hwmem p hp
  obtain ⟨h1, h2, h3⟩ := h.wmem q hq
  rw [hq1] at h1 h2 h3
  exact ⟨h1, h2, AVal.holds_of_le hq2 h3⟩

end Sym

end MachineChecked.RiscV.Check
