/-
  AsmVerif.RiscV.Check.Sound

  The checker is sound: if `Ctx.valid` accepts a function's annotation, and every callee
  in the table meets its interface for smaller budgets, the function meets its own.
-/

import AsmVerif.RiscV.Check.Arith
import AsmVerif.RiscV.Check.Ecall

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame

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
  | top => simp [AVal.isPtr] at hv
  | oneOf _ => simp [AVal.isPtr] at hv

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

/-- The stable doublewords of a knowledge hold their contents in `M`. -/
def KnCells (E : Ent) (M : Word → Word) (kn : Kn) : Prop :=
  ∀ p ∈ kn.cells, ∀ w, p.1.Holds E w → p.2.Holds E (M w)

/-- The kinds of a knowledge are among their candidates. -/
def KnRoots (E : Ent) (kn : Kn) : Prop :=
  ∀ p ∈ kn.roots, ∀ w, p.1.Holds E w → w ∈ p.2

theorem knCells_empty : KnCells E M {} := fun _ h => by simp at h
theorem knRoots_empty : KnRoots E ({} : Kn) := fun _ h => by simp at h

theorem contentAt_holds {A : AState} {kn : Kn} (hm : MemOk σ E A M) (hk : KnCells E M kn)
    {a : AVal} {w : Word} (ha : a.Holds E w) {v : AVal} (h : contentAt σ kn A a = some v) :
    v.Holds E (M w) := by
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
      exact hk _ (lookup_mem h) w ha

theorem instPath_holds {A : AState} {kn : Kn} {E' : Ent} (hm : MemOk σ E A E'.mem)
    (hk : KnCells E E'.mem kn) :
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
      exact instPath_holds (ks := ks) hm hk (contentAt_holds hm hk (AVal.holds_addK hv) hct) h

end Cells

/-! ## The facts of an activation -/

structure Facts (env : Env) (σ : Iface) (E : Ent) (s0 : MachineState) : Prop where
  wf : env.wf = true
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
  emem : ∀ a, E.mem a = s0.getMem a

theorem Facts.of_pre {env : Env} {C} {σ : Iface} {s0 : MachineState} (hwf : env.wf = true)
    (hptr : ∀ e ∈ σ.strs, e.1.isPtr = true ∧ e.2.isPtr = true) (h : Pre env C σ s0) :
    Facts env σ (regsOf s0) s0 :=
  ⟨hwf, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1,
    fun c hc => let hc' := h.2.2.2.2.2.2.2.2.1 c hc; ⟨hc'.1, hc'.2.1, hc'.2.2.2⟩,
    fun c hc => (h.2.2.2.2.2.2.2.2.1 c hc).2.2.1, h.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2, hptr, fun _ => rfl⟩

/-- The checker's invariant at a state `x` of the activation, with abstract state `A`. -/
structure St (env : Env) (σ : Iface) (C : Word → Option Instr) (E : Ent) (s0 : MachineState)
    (A : AState) (x : MachineState) : Prop where
  holds : A.Holds E x
  code : x.code = C
  mem : ∀ a, Aligned a → ¬ Written σ E a → ¬ env.InOwn a → ¬ StrHit env σ E s0.getMem a →
    x.getMem a = s0.getMem a
  inv : env.Inv x.getMem
  slots : ∀ p ∈ A.slots, 8 ≤ negOff p.1 ∧ negOff p.1 ≤ σ.depth ∧ negOff p.1 % 8 = 0
  strs : StrsPost env σ E s0.getMem x.getMem

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

/-- The protected regions hold their contents at every state of the activation. -/
theorem St.prot {C} {A : AState} {x : MachineState} (hF : Facts env σ E s0)
    (h : St env σ C E s0 A x) {a : Word} (ha : Aligned a) (hp : env.InProt a) :
    x.getMem a = env.init a := by
  rw [h.mem a ha ?_ (not_own_of_prot hF.wf hp) (fun hs => (hF.strHit hs).2 hp), hF.prot a ha hp]
  rintro (hw | ⟨it, hit, hh⟩)
  · exact not_prot_of_inWin hF.wf hF.top hF.depth hw hp
  · exact (hF.foot it hit a ha hh).2.1 hp

/-- A store the activation may make keeps the invariant. -/
theorem St.inv_setMem {C} {A : AState} {x : MachineState} (hF : Facts env σ E s0)
    (h : St env σ C E s0 A x) {k v : Word} (hk : Aligned k → Written σ E k) :
    env.Inv (x.setMem k v).getMem :=
  Env.Inv_congr (fun a ha ho => by
    rw [getMem_setMem, if_neg]
    rintro rfl
    exact hF.not_own ha (hk ha) ho) h.inv

/-- A memory that differs from one the writers survive only on keys the activation may
    write still has them survive. -/
theorem StrsPost.congr (hF : Facts env σ E s0) {m m' : Word → Word}
    (h : StrsPost env σ E s0.getMem m)
    (hc : ∀ a, ¬ Written σ E a → m' a = m a) : StrsPost env σ E s0.getMem m' :=
  ⟨fun e he => (h.1 e he).congr fun a ha => hc a ((hF.strs.1 e he).2.1 a ha).1,
    fun k p hw hh => (h.2 k p hw hh).congr fun a ha => hc a (hh a ha).1⟩

/-- A store the activation may make keeps the writers. -/
theorem St.strs_setMem {C} {A : AState} {x : MachineState} (hF : Facts env σ E s0)
    (h : St env σ C E s0 A x) {k v : Word} (hk : Written σ E k) :
    StrsPost env σ E s0.getMem (x.setMem k v).getMem :=
  StrsPost.congr hF h.strs fun a ha => by
    rw [getMem_setMem, if_neg]; rintro rfl; exact ha hk

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
      · cases h
    | const _ => cases h
    | top => cases h
    | oneOf _ => cases h

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

/-- The refinement a fan-out branch runs under: one candidate of the root, the one the
    value is. -/
theorem fanOut_sound (hF : Facts env σ E s0) {v : AVal} {w : Word} (hv : v.Holds E w)
    {off : BitVec 12} {k : Option (AVal × Word) → Word → Option (List Edge)} {es : List Edge}
    (h : fanOut env σ v off k = some es) :
    ∃ root c es', root.Holds E c ∧
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
        exact ⟨root, c, es', hroot, hfc, fun e he => List.mem_flatten.mpr ⟨es', hes', he⟩⟩

end Cands

/-! ## Straight-line instructions -/

section Plain

variable {env : Env} {σ : Iface} {C : Word → Option Instr} {E : Ent} {s0 : MachineState}

theorem loadVal_sound (hF : Facts env σ E s0) {kn : Kn} {A : AState} {x : MachineState}
    {b : AVal} {addr : Word} (h : St env σ C E s0 A x) (hk : KnCells E x.getMem kn)
    (hkr : KnRoots E kn) (hb : b.Holds E addr) :
    (loadVal env σ kn A b true).Holds E (x.getMem addr) := by
  unfold loadVal
  simp only [if_true]
  split
  · rename_i k hk
    rw [AVal.frameOff?_some hk] at hb
    simp only [AVal.Holds] at hb
    cases hlk : A.slots.lookup k with
    | none => trivial
    | some v' => simp only [Option.getD_some]; rw [hb]; exact h.holds.2 _ (lookup_mem hlk)
  · split
    · rename_i c
      simp only [AVal.Holds] at hb
      subst hb
      split
      · rename_i hk
        obtain ⟨hal, hp⟩ := protKey_inProt hk
        simp only [AVal.Holds]
        exact St.prot hF h hal hp
      · trivial
    · rename_i cs
      simp only [AVal.Holds] at hb
      split
      · rename_i hall
        obtain ⟨hal, hp⟩ := protKey_inProt (List.all_eq_true.mp hall addr hb)
        simp only [AVal.Holds]
        rw [St.prot hF h hal hp]
        exact List.mem_map_of_mem hb
      · trivial
    · cases hc : cellAt σ b with
      | some v => exact cellAt_holds (St.memOk hF h).2 hb hc
      | none =>
      cases hkc : kn.cells.lookup b with
      | some v => exact hk _ (lookup_mem hkc) addr hb
      | none =>
        cases hcs : cands env σ kn b with
        | none => trivial
        | some cs =>
          simp only
          split
          · rename_i hall
            have hmem := cands_mem hF hkr hb hcs
            obtain ⟨hal, hp⟩ := protKey_inProt (List.all_eq_true.mp hall addr hmem)
            cases hco : b.cellOf with
            | none => trivial
            | some v =>
              simp only [Option.getD_some]
              rw [St.prot hF h hal hp, ← hF.prot addr hal hp, ← hF.emem]
              exact cellOf_holds hb hco
          · trivial

@[simp] theorem getMem_setReg' (s : MachineState) (r : Reg) (v : Word) :
    (s.setReg r v).getMem = s.getMem := funext fun _ => by simp [MachineState.getMem_setReg]

@[simp] theorem getMem_setPC' (s : MachineState) (v : Word) : (s.setPC v).getMem = s.getMem :=
  funext fun _ => by simp [MachineState.getMem, MachineState.setPC]

theorem storeStep_sound (hF : Facts env σ E s0) {A B : AState} {x : MachineState}
    {rs1 rs2 : Reg} {off : BitVec 12} {w : Width} {v : Word}
    (h : St env σ C E s0 A x) (hv : w = .d → v = x.getReg rs2)
    (hs : storeStep σ A rs1 rs2 off w = some B) :
    St env σ C E s0 B (x.setMem (w.target (x.getReg rs1 + signExtend12 off)) v) := by
  have hb := AVal.holds_addK (d := signExtend12 off) (h.holds.1 rs1)
  have hregs : ∀ a, ∀ r, (A.get r).Holds E ((x.setMem a v).getReg r) := fun a r => by
    rw [getReg_setMem]; exact h.holds.1 r
  unfold storeStep at hs
  generalize (A.get rs1).addK (signExtend12 off) = b at hb hs
  generalize hkey : w.target (x.getReg rs1 + signExtend12 off) = key
  cases hk : b.frameOff? with
  | some k =>
    simp only [hk] at hs
    split at hs
    · rename_i hwin
      cases hs
      simp only [winOk, Bool.and_eq_true, decide_eq_true_eq] at hwin
      rw [AVal.frameOff?_some hk] at hb
      simp only [AVal.Holds] at hb
      rw [hb, add_frame] at hkey
      have hkw : InWin (E .x2) σ.depth key := by
        rw [← hkey]; exact inWin_store hF.depth hwin.1 hwin.2
      have hkeyF : w.target (E .x2 + k) = key := by rw [add_frame]; exact hkey
      refine ⟨⟨hregs _, fun p hp => ?_⟩, by simp [h.code], fun a ha hnw hno hns => ?_,
        St.inv_setMem hF h (fun _ => Or.inl hkw), fun p hp => ?_, St.strs_setMem hF h (Or.inl hkw)⟩
      · have keep : ∀ p ∈ A.slots.filter (fun p => !mayHit w k p.1),
            p.2.Holds E ((x.setMem key v).getMem (E .x2 + p.1)) := by
          intro p hp
          simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
          rw [← hkeyF, frame_keep hp.2]; exact h.holds.2 p hp.1
        cases w with
        | sub => exact keep p hp
        | d =>
          simp only at hp
          cases hr2 : A.get rs2 with
          | top => simp only [hr2] at hp; exact keep p hp
          | lin r j =>
            simp only [hr2] at hp
            split at hp
            · rcases List.mem_cons.mp hp with rfl | hp
              · rw [← hkeyF, getMem_setMem, if_pos (by simp [Width.target]), hv rfl, ← hr2]
                exact h.holds.1 rs2
              · exact keep p hp
            · exact keep p hp
          | const c =>
            simp only [hr2] at hp
            split at hp
            · rcases List.mem_cons.mp hp with rfl | hp
              · rw [← hkeyF, getMem_setMem, if_pos (by simp [Width.target]), hv rfl, ← hr2]
                exact h.holds.1 rs2
              · exact keep p hp
            · exact keep p hp
          | oneOf cs =>
            simp only [hr2] at hp
            split at hp
            · rcases List.mem_cons.mp hp with rfl | hp
              · rw [← hkeyF, getMem_setMem, if_pos (by simp [Width.target]), hv rfl, ← hr2]
                exact h.holds.1 rs2
              · exact keep p hp
            · exact keep p hp
          | cell r ks j =>
            simp only [hr2] at hp
            split at hp
            · rcases List.mem_cons.mp hp with rfl | hp
              · rw [← hkeyF, getMem_setMem, if_pos (by simp [Width.target]), hv rfl, ← hr2]
                exact h.holds.1 rs2
              · exact keep p hp
            · exact keep p hp
      · rw [getMem_setMem, if_neg (fun he => hnw (Or.inl (by rw [he]; exact hkw)))]
        exact h.mem a ha hnw hno hns
      · have sub : ∀ p ∈ A.slots.filter (fun p => !mayHit w k p.1), p ∈ A.slots :=
          fun p hp => (List.mem_filter.mp hp).1
        cases w with
        | sub => exact h.slots p (sub p hp)
        | d =>
          simp only at hp
          cases hr2 : A.get rs2 with
          | top => simp only [hr2] at hp; exact h.slots p (sub p hp)
          | lin r j =>
            simp only [hr2] at hp
            split at hp
            · rename_i h8
              rcases List.mem_cons.mp hp with rfl | hp
              · exact ⟨hwin.1, hwin.2, h8⟩
              · exact h.slots p (sub p hp)
            · exact h.slots p (sub p hp)
          | const c =>
            simp only [hr2] at hp
            split at hp
            · rename_i h8
              rcases List.mem_cons.mp hp with rfl | hp
              · exact ⟨hwin.1, hwin.2, h8⟩
              · exact h.slots p (sub p hp)
            · exact h.slots p (sub p hp)
          | oneOf cs =>
            simp only [hr2] at hp
            split at hp
            · rename_i h8
              rcases List.mem_cons.mp hp with rfl | hp
              · exact ⟨hwin.1, hwin.2, h8⟩
              · exact h.slots p (sub p hp)
            · exact h.slots p (sub p hp)
          | cell r ks j =>
            simp only [hr2] at hp
            split at hp
            · rename_i h8
              rcases List.mem_cons.mp hp with rfl | hp
              · exact ⟨hwin.1, hwin.2, h8⟩
              · exact h.slots p (sub p hp)
            · exact h.slots p (sub p hp)
    · cases hs
  | none =>
    simp only [hk] at hs
    split at hs
    · cases hs
    · rename_i hnt
      split at hs
      · rename_i hcov
        cases hs
        obtain ⟨d, hd, hwd⟩ := List.any_eq_true.mp hcov
        -- The key is hit by the store's bytes, so by `d`.
        have hhit : d.Hits E key := by
          apply within_hits hwd
          unfold Item.Hits
          have : b.eval E = x.getReg rs1 + signExtend12 off := by
            cases b with
            | lin r k => simp only [AVal.Holds] at hb; simp [AVal.eval, hb]
            | const c => simp only [AVal.Holds] at hb; simp [AVal.eval, hb]
            | top => simp [AVal.isPtr] at hnt
            | oneOf _ => simp [AVal.isPtr] at hnt
            | cell r ks d => simp only [AVal.Holds] at hb; simp [AVal.eval, hb]
          simp only [this, Len.eval]
          rw [← hkey]; exact hits_target w _
        refine ⟨⟨hregs _, fun p hp => ?_⟩, by simp [h.code], fun a ha hnw hno hns => ?_,
          St.inv_setMem hF h (fun _ => Or.inr ⟨d, hd, hhit⟩), h.slots,
          St.strs_setMem hF h (Or.inr ⟨d, hd, hhit⟩)⟩
        · have hsl := slot_facts hF (h.slots p hp)
          have hne : E .x2 + p.1 ≠ key := by
            intro he
            rw [← he] at hhit
            exact (hF.foot d hd _ hsl.1 hhit).1 hsl.2
          rw [getMem_setMem, if_neg hne]; exact h.holds.2 p hp
        · have hne : a ≠ key := fun he => hnw (Or.inr ⟨d, hd, he ▸ hhit⟩)
          rw [getMem_setMem, if_neg hne]; exact h.mem a ha hnw hno hns
      · cases hs

theorem plainStep_sound (hF : Facts env σ E s0) {kn : Kn} {A B : AState} {x : MachineState}
    {pc : Word} {i : Instr} (hpc : x.pc = pc) (h : St env σ C E s0 A x)
    (hk : KnCells E x.getMem kn) (hkr : KnRoots E kn) (hs : plainStep env σ kn pc A i = some B) :
    St env σ C E s0 B (execInstrBr x i) ∧ (execInstrBr x i).pc = x.pc + 4 := by
  unfold plainStep at hs
  split at hs
  · rename_i rd v hr
    cases hs
    obtain ⟨w, he, hw⟩ := aluResult_sound hpc h.holds hr
    rw [he]
    exact ⟨⟨AState.holds_setPC (AState.holds_set h.holds hw), by simp [h.code],
      fun a ha hnw hno hns => by simpa using h.mem a ha hnw hno hns,
      Env.Inv_congr (fun _ _ _ => by simp) h.inv, h.slots, by simpa using h.strs⟩, rfl⟩
  · split at hs
    · rename_i rd rs off isD hl
      cases hs
      obtain ⟨w, he, hw⟩ := loadOf_shape (s := x) hl
      rw [he]
      refine ⟨⟨AState.holds_setPC (AState.holds_set h.holds ?_), by simp [h.code],
        fun a ha hnw hno hns => by simpa using h.mem a ha hnw hno hns,
        Env.Inv_congr (fun _ _ _ => by simp) h.inv, h.slots, by simpa using h.strs⟩, rfl⟩
      cases isD with
      | false => simp [loadVal, AVal.Holds]
      | true =>
        rw [hw rfl]
        exact loadVal_sound hF h hk hkr (AVal.holds_addK (h.holds.1 rs))
    · split at hs
      · rename_i rs1 rs2 off w hst
        obtain ⟨v, he, hv⟩ := storeOf_shape (s := x) hst
        rw [he]
        have := storeStep_sound hF h hv hs
        exact ⟨⟨AState.holds_setPC this.holds, by simpa using this.code,
          fun a ha hnw hno hns => by simpa using this.mem a ha hnw hno hns,
          Env.Inv_congr (fun _ _ _ => by simp) this.inv, this.slots, by simpa using this.strs⟩, rfl⟩
      · split at hs
        · cases hs
          exact ⟨⟨AState.holds_setPC h.holds, by simp [execInstrBr, h.code],
            fun a ha hnw hno hns => by simpa [execInstrBr] using h.mem a ha hnw hno hns,
            Env.Inv_congr (fun _ _ _ => by simp [execInstrBr]) h.inv, h.slots,
            by simpa [execInstrBr] using h.strs⟩, rfl⟩
        · cases hs
          exact ⟨⟨AState.holds_setPC h.holds, by simp [execInstrBr, h.code],
            fun a ha hnw hno hns => by simpa [execInstrBr] using h.mem a ha hnw hno hns,
            Env.Inv_congr (fun _ _ _ => by simp [execInstrBr]) h.inv, h.slots,
            by simpa [execInstrBr] using h.strs⟩, rfl⟩
        · cases hs

end Plain

/-! ## Instantiating a callee's interface -/

section Inst

variable {E : Ent} {A : AState} {y : MachineState}

/-- `A` describes the registers of `y`. -/
def RegsHold (E : Ent) (A : AState) (y : MachineState) : Prop :=
  ∀ r, (A.get r).Holds E (y.getReg r)

theorem holds_self {v : AVal} (hv : v.isPtr = true) : v.Holds E (v.eval E) := by
  cases v <;> simp_all [AVal.Holds, AVal.eval, AVal.isPtr]

/-- An entry-relative, loaded or constant value, instantiated in a state `A` describes. -/
theorem instVal_holds {σ : Iface} {kn : Kn} (h : RegsHold E A y) (hm : MemOk σ E A y.getMem)
    (hk : KnCells E y.getMem kn) {v : AVal} (hv : v.isPtr = true) :
    (instVal σ kn A v).Holds E (v.eval (regsOf y)) := by
  cases v with
  | lin r k => exact AVal.holds_addK (h r)
  | const c => simp [instVal, AVal.Holds, AVal.eval]
  | top => simp [AVal.isPtr] at hv
  | oneOf _ => simp [AVal.isPtr] at hv
  | cell r ks d =>
    simp only [instVal]
    cases hp : instPath σ kn A (A.get r) ks with
    | none => simp [AVal.Holds]
    | some v' =>
      simp only [Option.map_some, Option.getD_some]
      exact AVal.holds_addK (instPath_holds (E' := regsOf y) hm hk (h r) hp)

theorem instVal_eval {σ : Iface} {kn : Kn} (h : RegsHold E A y) (hm : MemOk σ E A y.getMem)
    (hk : KnCells E y.getMem kn) {v : AVal} (hv : (instVal σ kn A v).isPtr = true) :
    (instVal σ kn A v).eval E = v.eval (regsOf y) := by
  have hv' : v.isPtr = true := by
    cases v <;> first | rfl | simp [instVal, AVal.isPtr] at hv
  exact holds_eval (instVal_holds h hm hk hv') hv

theorem instLen_eval (h : RegsHold E A y) {l l' : Len} (hl : instLen A l = some l') :
    l'.eval E = l.eval (regsOf y) := by
  cases l with
  | n k => simp only [instLen, Option.some.injEq] at hl; subst hl; rfl
  | reg r =>
    simp only [instLen] at hl
    have hr := h r
    cases hA : A.get r with
    | const c =>
      rw [hA] at hl hr; simp only [Option.some.injEq] at hl; subst hl
      simp only [AVal.Holds] at hr
      simp [Len.eval, regsOf, hr]
    | lin r' k =>
      rw [hA] at hl hr
      simp only at hl
      split at hl
      · rename_i hk; subst hk
        simp only [Option.some.injEq] at hl; subst hl
        simp only [AVal.Holds] at hr
        simp [Len.eval, regsOf, hr]
      · cases hl
    | top => rw [hA] at hl; cases hl
    | oneOf _ => rw [hA] at hl; cases hl
    | cell _ _ _ => rw [hA] at hl; cases hl
  | regPlus r c =>
    simp only [instLen] at hl
    have hr := h r
    cases hA : A.get r with
    | const v =>
      rw [hA] at hl hr; simp only [Option.some.injEq] at hl; subst hl
      simp only [AVal.Holds] at hr
      simp [Len.eval, regsOf, hr]
    | lin r' k =>
      rw [hA] at hl hr
      simp only at hl
      split at hl
      · rename_i hk; subst hk
        simp only [Option.some.injEq] at hl; subst hl
        simp only [AVal.Holds] at hr
        simp [Len.eval, regsOf, hr]
      · cases hl
    | top => rw [hA] at hl; cases hl
    | oneOf _ => rw [hA] at hl; cases hl
    | cell _ _ _ => rw [hA] at hl; cases hl

theorem instItem_hits {σ : Iface} {kn : Kn} (h : RegsHold E A y) (hm : MemOk σ E A y.getMem)
    (hk : KnCells E y.getMem kn) {it it' : Item} (hi : instItem σ kn A it = some it')
    (hnt : it'.base.isPtr = true) {a : Word} (ha : it.Hits (regsOf y) a) : it'.Hits E a := by
  unfold instItem at hi
  cases hl : instLen A it.len with
  | none => rw [hl] at hi; cases hi
  | some l =>
    rw [hl] at hi
    simp only [Option.map_some, Option.some.injEq] at hi
    subst hi
    unfold Item.Hits at ha ⊢
    simp only at hnt ⊢
    rw [instVal_eval h hm hk hnt, instLen_eval h hl]
    exact ha

theorem nzOk_sound {σ : Iface} {kn : Kn} (hnz : ∀ v ∈ σ.nz, v.eval E ≠ 0) (h : RegsHold E A y)
    (hm : MemOk σ E A y.getMem) (hk : KnCells E y.getMem kn) {v : AVal}
    (hok : nzOk σ kn A v = true) : v.eval (regsOf y) ≠ 0 := by
  unfold nzOk at hok
  simp only [Bool.and_eq_true] at hok
  exact nzVal_holds hnz (instVal_holds h hm hk hok.1) hok.2

end Inst

theorem valOk_sound {env : Env} {σ : Iface} {E : Ent} {s0 : MachineState} (hF : Facts env σ E s0)
    {kn : Kn} (hk : KnRoots E kn) {A : AState} {y : MachineState} (h : RegsHold E A y)
    {p : Reg × List Word} (hok : valOk env σ kn A p = true) : y.getReg p.1 ∈ p.2 :=
  inCands_sound hF hk (h p.1) hok

/-! ## Knowledge

What `closure` computes holds at every state of the activation: the function's writers
are well-typed there, the writers they wrap too, and the paths to those are stable. -/

section Kn

variable {env : Env} {σ : Iface} {E : Ent} {s0 : MachineState}

/-- The refinement holds. -/
def RefOk (E : Ent) (ref : Option (AVal × Word)) : Prop :=
  ∀ rf, ref = some rf → rf.1.Holds E rf.2

theorem refOk_none : RefOk E none := fun _ h => by cases h

theorem kindConst_eval (hF : Facts env σ E s0) {ref : Option (AVal × Word)} (hrf : RefOk E ref)
    {k : AVal} (hk : k.isPtr = true) {K : Word} (h : kindConst env ref k = some K) :
    k.eval E = K := by
  unfold kindConst at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · cases ref with
    | none => simp at h
    | some rf =>
      simp only [Option.bind_some] at h
      have hr := hrf rf rfl
      exact (refineVal_sound hF hr (holds_self hk)
        (fun hveq => holds_det hk (holds_self hk) (by rw [hveq]; exact hr)) h).symm

theorem path_isPtr {b : AVal} (hb : b.isPtr = true) {ks : List Word} {u : AVal}
    (h : b.path ks = some u) : u.isPtr = true := by
  cases ks with
  | nil => simp only [AVal.path, Option.some.injEq] at h; subst h; exact hb
  | cons k ks =>
    cases b with
    | lin r k0 => simp only [AVal.path, Option.some.injEq] at h; subst h; rfl
    | cell r ks0 d => simp only [AVal.path, Option.some.injEq] at h; subst h; rfl
    | const _ => simp [AVal.path] at h
    | top => simp [AVal.path] at h
    | oneOf _ => simp [AVal.path] at h

/-- A writer the function has, as of a memory `M` of its activation: well-typed; its keys
    nothing the function writes, not protected, among its writers' keys at entry; its
    stable keys aligned, not owned, and as at entry. -/
def EntryOk (env : Env) (σ : Iface) (E : Ent) (s0 : MachineState) (M : Word → Word)
    (e : AVal × AVal) : Prop :=
  e.1.isPtr = true ∧ e.2.isPtr = true ∧
  env.model.writerOk (e.2.eval E) (e.1.eval E) M ∧
  (∀ a, env.model.hit (e.2.eval E) (e.1.eval E) M a →
    ¬ Written σ E a ∧ ¬ env.InProt a ∧ StrHit env σ E s0.getMem a) ∧
  (∀ a, env.model.stable (e.2.eval E) (e.1.eval E) M a →
    Aligned a ∧ ¬ env.InOwn a ∧ M a = s0.getMem a)

/-- A wrapped writer, in terms of the writer wrapping it. -/
def IsSub (env : Env) (ref : Option (AVal × Word)) (e' e : AVal × AVal) : Prop :=
  ∃ s, subEntry env ref e = some (s, e'.1, e'.2)

theorem subEntry_some {env : Env} {ref : Option (AVal × Word)} {e : AVal × AVal} {s : Sub}
    {d' k' : AVal} (h : subEntry env ref e = some (s, d', k')) :
    ∃ K, kindConst env ref e.2 = some K ∧ env.model.sub K = some s ∧
      e.1.path s.dp = some d' ∧ e.1.path s.kp = some k' := by
  unfold subEntry at h
  cases hks : (kindConst env ref e.2).bind env.model.sub with
  | none => rw [hks] at h; cases h
  | some s' =>
    rw [hks] at h
    simp only at h
    obtain ⟨K, hK, hs⟩ := Option.bind_eq_some_iff.mp hks
    cases hd : e.1.path s'.dp with
    | none => rw [hd] at h; cases h
    | some d'' =>
      cases hk : e.1.path s'.kp with
      | none => rw [hd, hk] at h; cases h
      | some k'' =>
        rw [hd, hk] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨K, hK, hs, hd, hk⟩

structure KnOk (env : Env) (σ : Iface) (E : Ent) (s0 : MachineState) (M : Word → Word)
    (ref : Option (AVal × Word)) (kn : Kn) : Prop where
  cells : KnCells E M kn
  roots : KnRoots E kn
  strs : ∀ e ∈ kn.strs, EntryOk env σ E s0 M e
  subs : ∀ q ∈ kn.subs, q.2 ∈ kn.strs ∧ IsSub env ref q.1 q.2

theorem knOk_empty {M : Word → Word} {ref : Option (AVal × Word)} :
    KnOk env σ E s0 M ref {} :=
  ⟨knCells_empty, knRoots_empty, fun _ h => by simp at h, fun _ h => by simp at h⟩

/-- The function's writers, at any state of the activation. -/
theorem St.entryOk (hF : Facts env σ E s0) {C} {A : AState} {x : MachineState}
    (hx : St env σ C E s0 A x) {e : AVal × AVal} (he : e ∈ σ.strs) :
    EntryOk env σ E s0 x.getMem e := by
  obtain ⟨hp1, hp2⟩ := hF.strsPtr e he
  have hk := hx.strs.1 e he
  have hpre := hF.strs.1 e he
  refine ⟨hp1, hp2, hk.1, fun a ha => ?_, fun a ha => ?_⟩
  · have ha0 := hk.2.1 a ha
    exact ⟨(hpre.2.1 a ha0).1, (hpre.2.1 a ha0).2, e, he, ha0⟩
  · have ha0 := (hk.stable_iff a).mp ha
    exact ⟨(hpre.2.2 a ha0).1, (hpre.2.2 a ha0).2, hk.2.2 a ha0⟩

/-- What a structural writer wraps, as of `M`: a writer too; its pointer and kind are the
    paths' contents, which are stable keys, and the paths' keys are not its own. -/
theorem sub_entryOk (hF : Facts env σ E s0) {M : Word → Word} {ref : Option (AVal × Word)}
    (hrf : RefOk E ref) {e : AVal × AVal} (he : EntryOk env σ E s0 M e) {K : Word} {s : Sub}
    (hK : kindConst env ref e.2 = some K) (hs : env.model.sub K = some s) {d' k' : AVal}
    (hd : e.1.path s.dp = some d') (hk : e.1.path s.kp = some k') :
    pathKeys M (e.1.eval E) s.dp = pathKeys E.mem (e.1.eval E) s.dp ∧
    pathKeys M (e.1.eval E) s.kp = pathKeys E.mem (e.1.eval E) s.kp ∧
    d'.eval E = derefM M (e.1.eval E) s.dp ∧ k'.eval E = derefM M (e.1.eval E) s.kp ∧
    EntryOk env σ E s0 M (d', k') ∧ (∀ w, k'.Holds E w → w ∈ s.kinds) ∧
    (∀ a ∈ s.keys M (e.1.eval E), Aligned a ∧ ¬ Written σ E a ∧ ¬ env.InOwn a ∧
      M a = s0.getMem a ∧ ¬ env.model.hit (k'.eval E) (d'.eval E) M a) := by
  obtain ⟨hp1, hp2, hw, hhit, hst⟩ := he
  have hK' := kindConst_eval hF hrf hp2 hK
  rw [hK'] at hw hhit hst
  have hsub := env.model.sub_elim hs hw
  obtain ⟨hw', hkind, hkeys⟩ := hsub
  -- The paths' keys are stable, hence as at entry.
  have hkey : ∀ a ∈ s.keys M (e.1.eval E), Aligned a ∧ ¬ Written σ E a ∧ ¬ env.InOwn a ∧
      M a = s0.getMem a := by
    intro a ha
    have hst' := hst a ((env.model.stable_struct hs a).mpr (Or.inl ha))
    exact ⟨(hkeys a ha).1, (hhit a (env.model.stable_hit ((env.model.stable_struct hs a).mpr (Or.inl ha)))).1,
      hst'.2.1, hst'.2.2⟩
  have hdp : ∀ b ∈ pathKeys M (e.1.eval E) s.dp, E.mem b = M b := fun b hb => by
    rw [hF.emem, (hkey b (by simp [Sub.keys, hb])).2.2.2]
  have hkp : ∀ b ∈ pathKeys M (e.1.eval E) s.kp, E.mem b = M b := fun b hb => by
    rw [hF.emem, (hkey b (by simp [Sub.keys, hb])).2.2.2]
  have hpd := pathKeys_congr hdp
  have hpk := pathKeys_congr hkp
  have hdd := derefM_congr hdp
  have hdk := derefM_congr hkp
  have hd'h : d'.Holds E (derefM M (e.1.eval E) s.dp) := by
    rw [← hdd, ← Ent.deref_eq]; exact path_holds (holds_self hp1) hd
  have hk'h : k'.Holds E (derefM M (e.1.eval E) s.kp) := by
    rw [← hdk, ← Ent.deref_eq]; exact path_holds (holds_self hp1) hk
  have hd'p := path_isPtr hp1 hd
  have hk'p := path_isPtr hp1 hk
  have hd'e := holds_eval hd'h hd'p
  have hk'e := holds_eval hk'h hk'p
  refine ⟨hpd.symm, hpk.symm, hd'e, hk'e, ⟨hd'p, hk'p, ?_, fun a ha => ?_, fun a ha => ?_⟩,
    fun w hw => ?_, fun a ha => ?_⟩
  · rw [hd'e, hk'e]; exact hw'
  · rw [hd'e, hk'e] at ha
    exact hhit a ((env.model.hit_struct hs a).mpr (Or.inr ha))
  · rw [hd'e, hk'e] at ha
    exact hst a ((env.model.stable_struct hs a).mpr (Or.inr ha))
  · rw [holds_det hk'p hw hk'h]; exact hkind
  · refine ⟨(hkey a ha).1, (hkey a ha).2.1, (hkey a ha).2.2.1, (hkey a ha).2.2.2, ?_⟩
    rw [hd'e, hk'e]; exact (hkeys a ha).2

theorem addK_det {b : AVal} {k : Word} {u : AVal} (hu : b.path [k] = some u) {p w : Word}
    (hb : b.Holds E p) (hw : (b.addK k).Holds E w) : w = p + k := by
  cases b with
  | lin r k0 => simp only [AVal.Holds, AVal.addK] at hb hw; rw [hw, hb, BitVec.add_assoc]
  | cell r ks d => simp only [AVal.Holds, AVal.addK] at hb hw; rw [hw, hb, BitVec.add_assoc]
  | const _ => simp [AVal.path] at hu
  | top => simp [AVal.path] at hu
  | oneOf _ => simp [AVal.path] at hu

/-- The doublewords along a path whose keys hold their entry contents. -/
theorem pathCells_sound {M : Word → Word} {b : AVal} {p : Word} (hb : b.Holds E p) :
    ∀ {ks : List Word}, (∀ a ∈ pathKeys E.mem p ks, M a = E.mem a) →
      ∀ q ∈ pathCells b ks, ∀ w, q.1.Holds E w → q.2.Holds E (M w)
  | [], _, q, hq => by simp [pathCells] at hq
  | k :: ks, hkeys, q, hq => by
    simp only [pathCells] at hq
    cases hu : b.path [k] with
    | none => rw [hu] at hq; simp at hq
    | some u =>
      rw [hu] at hq
      have hu' : u.Holds E (E.mem (p + k)) := by
        have := path_holds hb hu
        simpa [Ent.deref] using this
      rcases List.mem_cons.mp hq with rfl | hq
      · intro w hw
        rw [addK_det hu hb hw, hkeys (p + k) (by simp [pathKeys])]
        exact hu'
      · exact pathCells_sound hu' (fun a ha => hkeys a (by simp [pathKeys, ha])) q hq

/-- A writer added, and nothing else. -/
theorem knOk_cons {M : Word → Word} {ref : Option (AVal × Word)} {kn : Kn}
    (hkn : KnOk env σ E s0 M ref kn) {e : AVal × AVal} (he : EntryOk env σ E s0 M e) :
    KnOk env σ E s0 M ref { kn with strs := e :: kn.strs } :=
  ⟨hkn.cells, hkn.roots,
    fun e' he' => by
      rcases List.mem_cons.mp he' with rfl | he'
      · exact he
      · exact hkn.strs e' he',
    fun q hq => ⟨List.mem_cons_of_mem _ (hkn.subs q hq).1, (hkn.subs q hq).2⟩⟩

theorem addEntry_ok (hF : Facts env σ E s0) {M : Word → Word} {ref : Option (AVal × Word)}
    (hrf : RefOk E ref) {kn : Kn} (hkn : KnOk env σ E s0 M ref kn) {e : AVal × AVal}
    (he : EntryOk env σ E s0 M e) : KnOk env σ E s0 M ref (addEntry env ref kn e) := by
  unfold addEntry
  cases hse : subEntry env ref e with
  | none => exact knOk_cons hkn he
  | some x =>
    obtain ⟨s, d', k'⟩ := x
    obtain ⟨K, hK, hs, hd, hk⟩ := subEntry_some hse
    simp only
    obtain ⟨hpd, hpk, hd'e, hk'e, he', hkinds, hkeys⟩ := sub_entryOk hF hrf he hK hs hd hk
    have hp : e.1.Holds E (e.1.eval E) := holds_self he.1
    have hcd : ∀ a ∈ pathKeys E.mem (e.1.eval E) s.dp, M a = E.mem a := fun a ha => by
      rw [← hpd] at ha
      rw [hF.emem]; exact (hkeys a (by simp [Sub.keys, ha])).2.2.2.1
    have hck : ∀ a ∈ pathKeys E.mem (e.1.eval E) s.kp, M a = E.mem a := fun a ha => by
      rw [← hpk] at ha
      rw [hF.emem]; exact (hkeys a (by simp [Sub.keys, ha])).2.2.2.1
    refine ⟨fun q hq => ?_, fun q hq => ?_, fun e' he'' => ?_, fun q hq => ?_⟩
    · simp only [List.append_assoc, List.mem_append] at hq
      rcases hq with hq | hq | hq
      · exact hkn.cells q hq
      · exact pathCells_sound hp hcd q hq
      · exact pathCells_sound hp hck q hq
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact hkinds
      · exact hkn.roots q hq
    · rcases List.mem_cons.mp he'' with rfl | he''
      · exact he'
      · rcases List.mem_cons.mp he'' with rfl | he''
        · exact he
        · exact hkn.strs e' he''
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨List.mem_cons_of_mem _ (List.mem_cons_self ..), s, hse⟩
      · exact ⟨List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hkn.subs q hq).1), (hkn.subs q hq).2⟩

theorem closure_ok (hF : Facts env σ E s0) {C} {A : AState} {x : MachineState}
    (hx : St env σ C E s0 A x) {ref : Option (AVal × Word)} (hrf : RefOk E ref) :
    KnOk env σ E s0 x.getMem ref (closure env σ ref) := by
  unfold closure
  have : ∀ (l : List (AVal × AVal)), (∀ e ∈ l, e ∈ σ.strs) → ∀ kn, KnOk env σ E s0 x.getMem ref kn →
      KnOk env σ E s0 x.getMem ref (l.foldl (addEntry env ref) kn) := by
    intro l
    induction l with
    | nil => intro _ kn hkn; exact hkn
    | cons e l ih =>
      intro hl kn hkn
      simp only [List.foldl_cons]
      exact ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) _
        (addEntry_ok hF hrf hkn (St.entryOk hF hx (hl e (List.mem_cons_self ..))))
  exact this σ.strs (fun _ h => h) {} knOk_empty

/-- Two writers that match denote the same writer. -/
theorem matchEntry_eval (hF : Facts env σ E s0) {ref : Option (AVal × Word)} (hrf : RefOk E ref)
    {e e' : AVal × AVal} (he : e.1.isPtr = true ∧ e.2.isPtr = true)
    (h : matchEntry env ref e e' = true) :
    e'.1 = e.1 ∧ e'.2.isPtr = true ∧ e'.2.eval E = e.2.eval E := by
  simp only [matchEntry, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1.symm, ?_, ?_⟩
  · rcases h2 with h2 | h2
    · rw [← h2]; exact he.2
    · split at h2
      · simp only [beq_iff_eq] at h2; rw [h2]; rfl
      · cases h2
  · rcases h2 with h2 | h2
    · rw [h2]
    · split at h2
      · rename_i K hK
        simp only [beq_iff_eq] at h2
        rw [h2, kindConst_eval hF hrf he.2 hK]; rfl
      · cases h2

end Kn

/-! ## Calls, tail calls, returns -/

theorem mapM_some_mem {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ x ∈ l, ∃ y ∈ l', f x = some y :=
  mapM_some_mem'

/-- A candidate's edges are among all candidates' edges. -/
theorem allEdges_mem {f : Word → Option (List Edge)} {ts : List Word} {es : List Edge}
    (h : allEdges f ts = some es) {t : Word} (ht : t ∈ ts) :
    ∃ es', f t = some es' ∧ ∀ e ∈ es', e ∈ es := by
  unfold allEdges at h
  cases hm : ts.mapM f with
  | none => rw [hm] at h; cases h
  | some l =>
    rw [hm] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    obtain ⟨y, hy, hfy⟩ := mapM_some_mem hm t ht
    exact ⟨y, hfy, fun e he => List.mem_flatten.mpr ⟨y, hy, he⟩⟩

theorem afterCall_get (A : AState) (m : Nat) (its : List Item) (r : Reg) :
    (afterCall A m its).get r =
      if r = .x0 then .const 0 else if savedRegs.contains r then A.get r else .top := by
  by_cases h0 : r = .x0
  · subst h0; simp [AState.get]
  · simp only [AState.get, h0, if_false, afterCall, getD_map_allRegs]

theorem x1_not_saved : savedRegs.contains .x1 = false := by decide

theorem okExit_regs {A : AState} {E : Ent} {x : MachineState} (hx : okExit A = true)
    (h : RegsHold E A x) : x.getReg .x1 = E .x1 ∧ ∀ r ∈ savedRegs, x.getReg r = E r := by
  simp only [okExit, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hx
  refine ⟨?_, fun r hr => ?_⟩
  · have := h .x1; rw [hx.1] at this; simpa [AVal.Holds] using this
  · have := h r; rw [hx.2 r hr] at this; simpa [AVal.Holds] using this

section Call

variable {env : Env} {σ : Iface} {C : Word → Option Instr} {E : Ent} {s0 : MachineState}

theorem spOff_sound {A : AState} {x : MachineState} {m : Nat} (h : RegsHold E A x)
    (hm : spOff A = some m) : x.getReg .x2 = E .x2 - BitVec.ofNat 64 m ∧ m % 8 = 0 := by
  unfold spOff at hm
  cases hk : (A.get .x2).frameOff? with
  | none => rw [hk] at hm; cases hm
  | some k =>
    rw [hk] at hm
    simp only at hm
    split at hm
    · rename_i h8
      cases hm
      have := h .x2
      rw [AVal.frameOff?_some hk] at this
      simp only [AVal.Holds] at this
      exact ⟨by rw [this, add_frame], h8⟩
    · cases hm

/-- At a call, the slots and cells describe the callee's entry memory. -/
theorem memOk_call (hF : Facts env σ E s0) {A A1 : AState} {x y : MachineState}
    (hx : St env σ C E s0 A x) (hA1 : A1.slots = A.slots) (hmem : y.mem = x.mem) :
    MemOk σ E A1 y.getMem := by
  have h := St.memOk hF hx
  have hg : y.getMem = x.getMem := by funext a; simp [MachineState.getMem, hmem]
  rw [hg, MemOk, hA1]; exact h

section Callee

variable (hF : Facts env σ E s0) {kn : Kn} {A1 : AState} {y : MachineState} {g : Iface} {m : Nat}
  {its : List Item} (hy1 : RegsHold E A1 y) (hm1 : MemOk σ E A1 y.getMem)
  (hk : KnCells E y.getMem kn)
  (hsp : y.getReg .x2 = E .x2 - BitVec.ofNat 64 m) (hm8 : m % 8 = 0)
  (hdep : m + g.depth ≤ σ.depth) (hits : g.foot.mapM (instItem σ kn A1) = some its)
  (hall : ∀ it ∈ its, itemOk σ m it = true)
include hF hy1 hm1 hk hsp hm8 hdep hits hall

/-- Everything a checked callee may write, the caller may write. -/
theorem callee_written : ∀ a, Aligned a → Written g (regsOf y) a → Written σ E a := by
  intro a ha hw
  rcases hw with hw | ⟨it, hit, hh⟩
  · left
    rw [show (regsOf y) .x2 = y.getReg .x2 from rfl, hsp] at hw
    exact inWin_callee hF.al hm8 hdep ha hw
  · obtain ⟨it', hit', hinst⟩ := mapM_some_mem hits it hit
    have hio := hall it' hit'
    unfold itemOk at hio
    cases hfo : it'.base.frameOff? with
    | some k =>
      rw [hfo] at hio
      cases hl : it'.len with
      | reg _ => rw [hl] at hio; cases hio
      | regPlus _ _ => rw [hl] at hio; cases hio
      | n l =>
        rw [hl] at hio
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hio
        have hb := AVal.frameOff?_some hfo
        have hh' := instItem_hits hy1 hm1 hk hinst (by simp [hb, AVal.isPtr]) hh
        unfold Item.Hits at hh'
        rw [hb, hl] at hh'
        simp only [AVal.eval, Len.eval] at hh'
        rw [add_frame] at hh'
        exact Or.inl
          (frameItem_keys (Dg := g.depth) hF.depth hF.al hm8 hdep hio.1.1 hio.1.2 ha hh').2
    | none =>
      rw [hfo] at hio
      simp only [Bool.and_eq_true, List.any_eq_true] at hio
      obtain ⟨hnt, d, hd, hwd⟩ := hio
      exact Or.inr ⟨d, hd, within_hits hwd (instItem_hits hy1 hm1 hk hinst hnt hh)⟩

/-- A caller slot at or above the callee's stack pointer that `slotClear` keeps clear of the
    callee's items is not something the callee may write. -/
theorem slot_callee {f : Word} (hsl : 8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0)
    (hpm : negOff f ≤ m) (hclr : ∀ it ∈ its, slotClear f it = true) :
    ¬ Written g (regsOf y) (E .x2 + f) := by
  have hkey := slot_facts hF hsl
  rintro (hw | ⟨it, hit, hh⟩)
  · rw [show (regsOf y) .x2 = y.getReg .x2 from rfl, hsp, add_frame] at hw
    exact not_inWin_callee_slot hF.depth hF.al hm8 hdep hsl.2.2 hpm hw
  · obtain ⟨it', hit', hinst⟩ := mapM_some_mem hits it hit
    have hio := hall it' hit'
    have hc := hclr it' hit'
    unfold itemOk at hio
    unfold slotClear at hc
    cases hfo : it'.base.frameOff? with
    | some k =>
      rw [hfo] at hio hc
      cases hl : it'.len with
      | reg _ => rw [hl] at hio; cases hio
      | regPlus _ _ => rw [hl] at hio; cases hio
      | n l =>
        rw [hl] at hio hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hio
        simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
        have hb := AVal.frameOff?_some hfo
        have hh' := instItem_hits hy1 hm1 hk hinst (by simp [hb, AVal.isPtr]) hh
        unfold Item.Hits at hh'
        rw [hb, hl] at hh'
        simp only [AVal.eval, Len.eval] at hh'
        rw [add_frame, add_frame] at hh'
        have := hF.depth
        exact slot_not_hits (by omega) (by omega) hsl.1 hio.1.1 hc hh'
    | none =>
      rw [hfo] at hio
      simp only [Bool.and_eq_true, List.any_eq_true] at hio
      obtain ⟨hnt, d, hd, hwd⟩ := hio
      have := within_hits hwd (instItem_hits hy1 hm1 hk hinst hnt hh)
      exact (hF.foot d hd _ hkey.1 this).1 hkey.2

end Callee

/-- A callee's cell premise, discharged by `cellOk`: given that the callee writes only what
    the caller may (`hW`), and leaves the caller's slots that `slotClear` keeps (`hslot`).
    The cell's key is a slot not among `fs`, or one of the caller's cells. -/
theorem cellOk_sound (hF : Facts env σ E s0) {kn : Kn} {fs : List Word} {A : AState}
    {y : MachineState} {g : Iface} {mo : Option Nat} {its : List Item} {c : Cell}
    (hy : RegsHold E A y) (hm : MemOk σ E A y.getMem) (hk : KnCells E y.getMem kn)
    (hkr : KnRoots E kn)
    (hsl : ∀ p ∈ A.slots, 8 ≤ negOff p.1 ∧ negOff p.1 ≤ σ.depth ∧ negOff p.1 % 8 = 0)
    (hW : ∀ a, Aligned a → Written g (regsOf y) a → Written σ E a)
    (hslot : ∀ m f, mo = some m → (8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0) →
      negOff f ≤ m → (∀ it ∈ its, slotClear f it = true) → ¬ Written g (regsOf y) (E .x2 + f))
    (hok : cellOk env σ kn fs A mo its c = true) :
    (Aligned (c.addr (regsOf y)) ∧ ¬ Written g (regsOf y) (c.addr (regsOf y)) ∧
      ¬ env.InOwn (c.addr (regsOf y)) ∧
      ∀ cs, c.vals = some cs → y.getMem (c.addr (regsOf y)) ∈ cs) ∧
    ((∃ f, f ∉ fs ∧ (8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0) ∧
        c.addr (regsOf y) = E .x2 + f) ∨
      ∃ c' ∈ σ.cells, c'.addr E = c.addr (regsOf y)) := by
  unfold cellOk at hok
  cases hp : instPath σ kn A (A.get c.r) c.ks with
  | none => rw [hp] at hok; cases hok
  | some v =>
  rw [hp] at hok
  simp only [Bool.and_eq_true] at hok
  obtain ⟨hfs, hok⟩ := hok
  have hva : (v.addK c.k).Holds E (c.addr (regsOf y)) :=
    AVal.holds_addK (instPath_holds (E' := regsOf y) hm hk (hy c.r) hp)
  cases hs : stableAt σ A mo its (v.addK c.k) with
  | none => rw [hs] at hok; cases hok
  | some w =>
  rw [hs] at hok
  simp only at hok
  -- The contents, and the address stays put.
  have hw : w.Holds E (y.getMem (c.addr (regsOf y))) ∧ Aligned (c.addr (regsOf y)) ∧
      ¬ Written g (regsOf y) (c.addr (regsOf y)) ∧ ¬ env.InOwn (c.addr (regsOf y)) ∧
      ((∃ f, f ∉ fs ∧ (8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0) ∧
          c.addr (regsOf y) = E .x2 + f) ∨
        ∃ c' ∈ σ.cells, c'.addr E = c.addr (regsOf y)) := by
    unfold stableAt at hs
    cases hf : (v.addK c.k).frameOff? with
    | some f =>
      rw [hf] at hs hfs
      simp only at hfs
      rw [AVal.frameOff?_some hf] at hva
      simp only [AVal.Holds] at hva
      rw [hva]
      cases mo with
      | none => simp at hs
      | some m =>
        simp only at hs
        split at hs
        · rename_i hc
          simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
          have hp' := lookup_mem hs
          have hsl' := hsl _ hp'
          have hfs' : f ∉ fs := by
            intro hmem
            rw [List.contains_iff_mem.mpr hmem] at hfs
            simp at hfs
          exact ⟨hm.1 _ hp', (slot_facts hF hsl').1, hslot m f rfl hsl' hc.1 hc.2,
            not_own_of_inWin hF.wf hF.top hF.depth (slot_facts hF hsl').2,
            Or.inl ⟨f, hfs', hsl', rfl⟩⟩
        · cases hs
    | none =>
      rw [hf] at hs
      obtain ⟨c', hc', ha⟩ := cellAt_addr hva hs
      have hcf := hF.cells c' hc'
      rw [← ha]
      exact ⟨by rw [ha]; exact cellAt_holds hm.2 hva hs, hcf.1,
        fun hw => hcf.2.1 (hW _ hcf.1 hw), hF.cellsOwn c' hc', Or.inr ⟨c', hc', rfl⟩⟩
  refine ⟨⟨hw.2.1, hw.2.2.1, hw.2.2.2.1, fun cs hcs => ?_⟩, hw.2.2.2.2⟩
  rw [hcs] at hok
  exact inCands_sound hF hkr hw.1 hok

/-- Following a path through the caller's frame: the content, and the slots read. -/
theorem framePath_sound {A : AState} {y : MachineState} (hy : RegsHold E A y)
    (hm : MemOk σ E A y.getMem)
    (hsl : ∀ p ∈ A.slots, 8 ≤ negOff p.1 ∧ negOff p.1 ≤ σ.depth ∧ negOff p.1 % 8 = 0)
    {m : Nat} {its : List Item} :
    ∀ {v : AVal} {ks : List Word} {q : Word} {w : AVal} {fs : List Word},
    v.Holds E q → framePath A m its v ks = some (w, fs) →
    w.Holds E (derefM y.getMem q ks) ∧
    (∀ a ∈ pathKeys y.getMem q ks, ∃ f ∈ fs, a = E .x2 + f) ∧
    (∀ f ∈ fs, (8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0) ∧ negOff f ≤ m ∧
      ∀ it ∈ its, slotClear f it = true)
  | v, [], q, w, fs, hv, h => by
    simp only [framePath, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hv, fun a ha => by simp [pathKeys] at ha, fun f hf => by simp at hf⟩
  | v, k :: ks, q, w, fs, hv, h => by
    simp only [framePath] at h
    cases hf : (v.addK k).frameOff? with
    | none => rw [hf] at h; cases h
    | some f =>
      rw [hf] at h
      simp only at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
        cases hl : A.slots.lookup f with
        | none => rw [hl] at h; cases h
        | some u =>
          rw [hl] at h
          simp only at h
          cases hr : framePath A m its u ks with
          | none => rw [hr] at h; cases h
          | some wf =>
            obtain ⟨w', fs'⟩ := wf
            rw [hr] at h
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hqk : q + k = E .x2 + f := by
              have := AVal.holds_addK (d := k) hv
              rw [AVal.frameOff?_some hf] at this
              simpa [AVal.Holds] using this
            have hu : u.Holds E (y.getMem (q + k)) := by rw [hqk]; exact hm.1 _ (lookup_mem hl)
            obtain ⟨h1, h2, h3⟩ := framePath_sound hy hm hsl hu hr
            refine ⟨by simpa [derefM] using h1, fun a ha => ?_, fun f' hf' => ?_⟩
            · simp only [pathKeys, List.mem_cons] at ha
              rcases ha with rfl | ha
              · exact ⟨f, by simp, hqk⟩
              · obtain ⟨f', hf', ha'⟩ := h2 a ha
                exact ⟨f', by simp [hf'], ha'⟩
            · rcases List.mem_cons.mp hf' with rfl | hf'
              · exact ⟨hsl _ (lookup_mem hl), hc.1, hc.2⟩
              · exact h3 f' hf'
      · cases h

/-- What passing a callee writer establishes: it is one the caller has, or a structural
    writer built in the caller's frame around one the caller has. -/
theorem passEntry_sound (hF : Facts env σ E s0) {ref : Option (AVal × Word)} (hrf : RefOk E ref)
    {kn : Kn} {A1 : AState} {y : MachineState} (hkn : KnOk env σ E s0 y.getMem ref kn)
    (hy1 : RegsHold E A1 y) (hm1 : MemOk σ E A1 y.getMem)
    (hsl : ∀ p ∈ A1.slots, 8 ≤ negOff p.1 ∧ negOff p.1 ≤ σ.depth ∧ negOff p.1 % 8 = 0)
    {mo : Option Nat} {its : List Item} {d' k' : AVal} {es : List (AVal × AVal)} {fs : List Word}
    (h : passEntry env σ kn ref A1 mo its d' k' = some (es, fs)) :
    d'.isPtr = true ∧ k'.isPtr = true ∧
    ((∃ e ∈ kn.strs, es = [e] ∧ fs = [] ∧ e.1 = d' ∧ e.2.eval E = k'.eval E) ∨
     (∃ e ∈ kn.strs, ∃ m K s, mo = some m ∧ es = [e] ∧ k' = .const K ∧ env.model.sub K = some s ∧
        e.1.eval E = derefM y.getMem (d'.eval E) s.dp ∧
        e.2.eval E = derefM y.getMem (d'.eval E) s.kp ∧
        (∀ a ∈ s.keys y.getMem (d'.eval E), ∃ f ∈ fs, a = E .x2 + f) ∧
        (∀ f ∈ fs, (8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0) ∧ negOff f ≤ m ∧
          ∀ it ∈ its, slotClear f it = true) ∧
        SubOk env.model.writerOk env.model.hit (d'.eval E) y.getMem s)) := by
  unfold passEntry at h
  cases hfind : kn.strs.find? (matchEntry env ref · (d', k')) with
  | some e =>
    rw [hfind] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hmem := List.mem_of_find?_eq_some hfind
    have hmatch := List.find?_some hfind
    have hp := hkn.strs e hmem
    obtain ⟨h1, h2, h3⟩ := matchEntry_eval hF hrf ⟨hp.1, hp.2.1⟩ hmatch
    simp only at h1 h2 h3
    exact ⟨by rw [h1]; exact hp.1, h2, Or.inl ⟨e, hmem, rfl, rfl, h1.symm, h3.symm⟩⟩
  | none =>
    rw [hfind] at h
    simp only at h
    split at h
    · rename_i K m
      cases hs : env.model.sub K with
      | none => rw [hs] at h; cases h
      | some s =>
        rw [hs] at h
        simp only at h
        cases hd2 : framePath A1 m its d' s.dp with
        | none => rw [hd2] at h; cases h
        | some p1 =>
        obtain ⟨d2, fs1⟩ := p1
        cases hk2 : framePath A1 m its d' s.kp with
        | none => rw [hd2, hk2] at h; cases h
        | some p2 =>
        obtain ⟨k2, fs2⟩ := p2
        rw [hd2, hk2] at h
        simp only at h
        cases hfe : kn.strs.find? (matchEntry env ref · (d2, k2)) with
        | none => rw [hfe] at h; cases h
        | some e =>
        rw [hfe] at h
        simp only at h
        split at h
        · rename_i hcands
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hmem := List.mem_of_find?_eq_some hfe
          have hmatch := List.find?_some hfe
          have hp := hkn.strs e hmem
          obtain ⟨h1, h2, h3⟩ := matchEntry_eval hF hrf ⟨hp.1, hp.2.1⟩ hmatch
          simp only at h1 h2 h3
          -- `d'` is a pointer: the frame path from it exists.
          have hd'p : d'.isPtr = true := by
            cases hdp : s.dp with
            | nil =>
              rw [hdp] at hd2
              simp only [framePath, Option.some.injEq, Prod.mk.injEq] at hd2
              rw [hd2.1, h1]; exact hp.1
            | cons k ks =>
              rw [hdp] at hd2
              simp only [framePath] at hd2
              cases hf : (d'.addK k).frameOff? with
              | none => rw [hf] at hd2; cases hd2
              | some f =>
                have := AVal.frameOff?_some hf
                cases d' <;> simp_all [AVal.addK, AVal.isPtr]
          obtain ⟨hw1, hk1, hf1⟩ := framePath_sound hy1 hm1 hsl (holds_self hd'p) hd2
          obtain ⟨hw2, hk2', hf2⟩ := framePath_sound hy1 hm1 hsl (holds_self hd'p) hk2
          have hd2p : d2.isPtr = true := by rw [h1]; exact hp.1
          have hd2e : d2.eval E = derefM y.getMem (d'.eval E) s.dp := holds_eval hw1 hd2p
          have hk2e : k2.eval E = derefM y.getMem (d'.eval E) s.kp := holds_eval hw2 h2
          have hkeyf : ∀ a ∈ s.keys y.getMem (d'.eval E), ∃ f ∈ fs1 ++ fs2, a = E .x2 + f := by
            intro a ha
            simp only [Sub.keys, List.mem_append] at ha
            rcases ha with ha | ha
            · obtain ⟨f, hf, ha⟩ := hk1 a ha; exact ⟨f, List.mem_append_left _ hf, ha⟩
            · obtain ⟨f, hf, ha⟩ := hk2' a ha; exact ⟨f, List.mem_append_right _ hf, ha⟩
          have hfsl : ∀ f ∈ fs1 ++ fs2, (8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0) ∧
              negOff f ≤ m ∧ ∀ it ∈ its, slotClear f it = true := by
            intro f hf
            rcases List.mem_append.mp hf with hf | hf
            · exact hf1 f hf
            · exact hf2 f hf
          refine ⟨hd'p, rfl, Or.inr ⟨e, hmem, m, K, s, rfl, rfl, rfl, hs, by rw [← h1, hd2e],
            by rw [← h3, hk2e], hkeyf, hfsl, ?_, ?_, fun a ha => ?_⟩⟩
          · rw [← hd2e, ← hk2e, h1, h3]; exact hp.2.2.1
          · exact inCands_sound hF hkn.roots hw2 hcands
          · obtain ⟨f, hf, rfl⟩ := hkeyf a ha
            have hkey := slot_facts hF (hfsl f hf).1
            refine ⟨hkey.1, fun hh => ?_⟩
            rw [← hd2e, ← hk2e, h1, h3] at hh
            exact (hp.2.2.2.1 _ hh).1 (Or.inl hkey.2)
        · cases h
    · cases h

theorem mapM_some_mem_rev {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → ∀ y ∈ l', ∃ x ∈ l, f x = some y
  | [], l', h, y, hy => by simp [List.mapM_nil] at h; subst h; simp at hy
  | a :: l, l', h, y, hy => by
    cases hb : f a with
    | none => rw [List.mapM_cons, hb] at h; simp at h
    | some b =>
      cases hl : l.mapM f with
      | none => rw [List.mapM_cons, hb, hl] at h; simp at h
      | some l'' =>
        rw [List.mapM_cons, hb, hl] at h
        simp at h
        subst h
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a, List.mem_cons_self .., hb⟩
        · obtain ⟨x, hx, hfx⟩ := mapM_some_mem_rev hl y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-- A caller writer `e` stands for a callee writer of kind `K` at `q`: it is that writer, or
    the one the callee's structural writer, built in the caller's frame, wraps. -/
def Stands (env : Env) (E : Ent) (M : Word → Word) (fs : List Word) (e : AVal × AVal)
    (K q : Word) : Prop :=
  (e.1.eval E = q ∧ e.2.eval E = K) ∨
  ∃ s, env.model.sub K = some s ∧ e.1.eval E = derefM M q s.dp ∧ e.2.eval E = derefM M q s.kp ∧
    (∀ a ∈ s.keys M q, ∃ f ∈ fs, a = E .x2 + f) ∧ SubOk env.model.writerOk env.model.hit q M s

/-- What `strsOk` establishes: the writers passed are the caller's; every slot a callee
    writer is built from is in the frame, at or above the callee's stack pointer and clear
    of its items; each callee writer has a caller writer standing for it, and each passed
    writer stands for a callee writer; and the caller's writers are recovered. -/
theorem strsOk_sound (hF : Facts env σ E s0) {ref : Option (AVal × Word)} (hrf : RefOk E ref)
    {kn : Kn} {A1 : AState} {y : MachineState} (hkn : KnOk env σ E s0 y.getMem ref kn)
    (hy1 : RegsHold E A1 y) (hm1 : MemOk σ E A1 y.getMem)
    (hsl : ∀ p ∈ A1.slots, 8 ≤ negOff p.1 ∧ negOff p.1 ≤ σ.depth ∧ negOff p.1 % 8 = 0)
    {g : Iface} {mo : Option Nat} {its : List Item} {passed : List (AVal × AVal)} {fs : List Word}
    (hok : strsOk env σ kn ref A1 mo its g = some (passed, fs)) :
    (∀ p ∈ passed, p ∈ kn.strs) ∧
    (∀ f ∈ fs, ∃ m, mo = some m ∧ (8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0) ∧
      negOff f ≤ m ∧ ∀ it ∈ its, slotClear f it = true) ∧
    (∀ eg ∈ g.strs, ∃ e ∈ passed,
      Stands env E y.getMem fs e (eg.2.eval (regsOf y)) (eg.1.eval (regsOf y))) ∧
    (∀ e ∈ passed, ∃ eg ∈ g.strs,
      Stands env E y.getMem fs e (eg.2.eval (regsOf y)) (eg.1.eval (regsOf y))) ∧
    (g.strs = [] ∨ ∀ e ∈ σ.strs, recov env ref kn passed 2 e = true) := by
  unfold strsOk at hok
  cases hps : g.strs.mapM (fun e =>
      passEntry env σ kn ref A1 mo its (instVal σ kn A1 e.1) (instVal σ kn A1 e.2)) with
  | none => rw [hps] at hok; cases hok
  | some ps =>
  rw [hps] at hok
  simp only at hok
  split at hok
  · rename_i hall
    simp only [Option.some.injEq, Prod.mk.injEq] at hok
    obtain ⟨rfl, rfl⟩ := hok
    -- Each callee writer, through its `passEntry`.
    have key : ∀ eg ∈ g.strs, ∀ es fs', passEntry env σ kn ref A1 mo its (instVal σ kn A1 eg.1)
        (instVal σ kn A1 eg.2) = some (es, fs') →
        (∀ f ∈ fs', ∃ m, mo = some m ∧ (8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0) ∧
          negOff f ≤ m ∧ ∀ it ∈ its, slotClear f it = true) ∧
        ∃ e ∈ kn.strs, es = [e] ∧ ∀ fsA, (∀ f ∈ fs', f ∈ fsA) →
          Stands env E y.getMem fsA e (eg.2.eval (regsOf y)) (eg.1.eval (regsOf y)) := by
      intro eg _ es fs' hpe
      obtain ⟨hd'p, hk'p, hcase⟩ := passEntry_sound hF hrf hkn hy1 hm1 hsl hpe
      have hd'e := instVal_eval hy1 hm1 hkn.cells hd'p
      have hk'e := instVal_eval hy1 hm1 hkn.cells hk'p
      rcases hcase with ⟨e, hmem, rfl, rfl, h1, h3⟩ |
        ⟨e, hmem, m, K, s, rfl, rfl, hK, hs, h1, h3, hkeys, hfsl, hsub⟩
      · exact ⟨fun f hf => by simp at hf, e, hmem, rfl, fun _ _ =>
          Or.inl ⟨by rw [h1, hd'e], by rw [h3, hk'e]⟩⟩
      · refine ⟨fun f hf => ⟨m, rfl, hfsl f hf⟩, e, hmem, rfl, fun fsA hfsA =>
          Or.inr ⟨s, ?_, ?_, ?_, ?_, ?_⟩⟩
        · rw [← hk'e, hK]; exact hs
        · rw [← hd'e]; exact h1
        · rw [← hd'e]; exact h3
        · rw [← hd'e]; exact fun a ha => let ⟨f, hf, ha⟩ := hkeys a ha; ⟨f, hfsA f hf, ha⟩
        · rw [← hd'e]; exact hsub
    have hfsA : ∀ q ∈ ps, ∀ f ∈ q.2, f ∈ (ps.map (·.2)).flatten := fun q hq f hf =>
      List.mem_flatten.mpr ⟨q.2, List.mem_map.mpr ⟨q, hq, rfl⟩, hf⟩
    refine ⟨fun p hp => ?_, fun f hf => ?_, fun eg heg => ?_, fun e he => ?_, ?_⟩
    · obtain ⟨es, hes, hp⟩ := List.mem_flatten.mp hp
      obtain ⟨⟨es', fs'⟩, hin, rfl⟩ := List.mem_map.mp hes
      obtain ⟨eg, heg, hpe⟩ := mapM_some_mem_rev hps _ hin
      obtain ⟨_, e, hmem, rfl, _⟩ := key eg heg _ _ hpe
      simp only [List.mem_singleton] at hp
      subst hp
      exact hmem
    · obtain ⟨fs', hfs', hf⟩ := List.mem_flatten.mp hf
      obtain ⟨⟨es', fs''⟩, hin, rfl⟩ := List.mem_map.mp hfs'
      obtain ⟨eg, heg, hpe⟩ := mapM_some_mem_rev hps _ hin
      exact (key eg heg _ _ hpe).1 f hf
    · obtain ⟨⟨es, fs'⟩, hin, hpe⟩ := mapM_some_mem hps eg heg
      obtain ⟨_, e, _, rfl, hst⟩ := key eg heg _ _ hpe
      exact ⟨e, List.mem_flatten.mpr ⟨[e], List.mem_map.mpr ⟨([e], fs'), hin, rfl⟩, by simp⟩,
        hst _ (hfsA _ hin)⟩
    · obtain ⟨es, hes, hp⟩ := List.mem_flatten.mp he
      obtain ⟨⟨es', fs'⟩, hin, rfl⟩ := List.mem_map.mp hes
      obtain ⟨eg, heg, hpe⟩ := mapM_some_mem_rev hps _ hin
      obtain ⟨_, e', _, rfl, hst⟩ := key eg heg _ _ hpe
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨eg, heg, hst _ (hfsA _ hin)⟩
    · simp only [Bool.or_eq_true, List.isEmpty_iff, List.all_eq_true] at hall
      exact hall
  · cases hok

section Stands

variable {M : Word → Word} {fs : List Word}

/-- A writer standing for a callee's: the callee's precondition for it. -/
theorem stands_pre (hF : Facts env σ E s0) {e : AVal × AVal} (he : EntryOk env σ E s0 M e)
    {K q : Word} (h : Stands env E M fs e K q)
    (hfs : ∀ f ∈ fs, 8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0)
    {g : Iface} {y : MachineState} (hW : ∀ a, Aligned a → Written g (regsOf y) a → Written σ E a)
    (hslot : ∀ f ∈ fs, ¬ Written g (regsOf y) (E .x2 + f)) :
    env.model.writerOk K q M ∧
    (∀ a, env.model.hit K q M a → ¬ Written g (regsOf y) a ∧ ¬ env.InProt a) ∧
    (∀ a, env.model.stable K q M a → Aligned a ∧ ¬ env.InOwn a) := by
  obtain ⟨_, _, hw, hhit, hst⟩ := he
  rcases h with ⟨rfl, rfl⟩ | ⟨s, hs, hd, hk, hkeys, hsub⟩
  · exact ⟨hw, fun a ha => ⟨fun hwg => (hhit a ha).1 (hW a (env.model.hit_aligned ha) hwg),
      (hhit a ha).2.1⟩, fun a ha => ⟨(hst a ha).1, (hst a ha).2.1⟩⟩
  · rw [hd, hk] at hw hhit hst
    refine ⟨env.model.sub_intro hs hsub, fun a ha => ?_, fun a ha => ?_⟩
    · rcases (env.model.hit_struct hs a).mp ha with ha | ha
      · obtain ⟨f, hf, rfl⟩ := hkeys a ha
        exact ⟨hslot f hf, not_prot_of_inWin hF.wf hF.top hF.depth (slot_facts hF (hfs f hf)).2⟩
      · exact ⟨fun hwg => (hhit a ha).1 (hW a (env.model.hit_aligned ha) hwg), (hhit a ha).2.1⟩
    · rcases (env.model.stable_struct hs a).mp ha with ha | ha
      · obtain ⟨f, hf, rfl⟩ := hkeys a ha
        exact ⟨(slot_facts hF (hfs f hf)).1,
          not_own_of_inWin hF.wf hF.top hF.depth (slot_facts hF (hfs f hf)).2⟩
      · exact ⟨(hst a ha).1, (hst a ha).2.1⟩

/-- A key of a callee's writer: a slot its structural writer is built from (then a stable
    key of that writer), or a key of the caller's writer standing for it. -/
theorem stands_hit {e : AVal × AVal} {K q : Word} (h : Stands env E M fs e K q) {a : Word}
    (ha : env.model.hit K q M a) :
    (env.model.stable K q M a ∧ ∃ f ∈ fs, a = E .x2 + f) ∨
    env.model.hit (e.2.eval E) (e.1.eval E) M a := by
  rcases h with ⟨rfl, rfl⟩ | ⟨s, hs, hd, hk, hkeys, _⟩
  · exact Or.inr ha
  · rcases (env.model.hit_struct hs a).mp ha with ha | ha
    · exact Or.inl ⟨(env.model.stable_struct hs a).mpr (Or.inl ha), hkeys a ha⟩
    · rw [hd, hk]; exact Or.inr ha

/-- A callee writer kept is the caller's writer standing for it kept. -/
theorem stands_keeps {e : AVal × AVal} {K q : Word} (h : Stands env E M fs e K q)
    {t : Word → Word} (hk : env.model.Keeps K q M t) :
    env.model.Keeps (e.2.eval E) (e.1.eval E) M t := by
  rcases h with ⟨rfl, rfl⟩ | ⟨s, hs, hd, hk', hkeys, hsub⟩
  · exact hk
  · rw [hd, hk']
    -- The paths' keys are stable: the wrapped writer's pointer and kind are as they were.
    have hpres : ∀ b ∈ s.keys M q, t b = M b := fun b hb =>
      hk.2.2 b ((env.model.stable_struct hs b).mpr (Or.inl hb))
    have hdd : derefM t q s.dp = derefM M q s.dp :=
      derefM_congr fun b hb => hpres b (by simp [Sub.keys, hb])
    have hdk : derefM t q s.kp = derefM M q s.kp :=
      derefM_congr fun b hb => hpres b (by simp [Sub.keys, hb])
    have hsub' := env.model.sub_elim hs hk.1
    simp only [SubOk] at hsub'
    rw [hdd, hdk] at hsub'
    refine ⟨hsub'.1, fun a ha => ?_,
      fun a ha => hk.2.2 a ((env.model.stable_struct hs a).mpr (Or.inr ha))⟩
    have ha' : env.model.hit K q t a := by
      rw [env.model.hit_struct hs a, hdd, hdk]; exact Or.inr ha
    rcases (env.model.hit_struct hs a).mp (hk.2.1 a ha') with hk1 | hk1
    · have hkt : a ∈ s.keys t q := by
        simp only [Sub.keys, List.mem_append] at hk1 ⊢
        rw [pathKeys_congr (fun b hb => hpres b (by simp [Sub.keys, hb])),
          pathKeys_congr (fun b hb => hpres b (by simp [Sub.keys, hb]))]
        exact hk1
      exact absurd ha (hsub'.2.2 a hkt).2
    · exact hk1

end Stands

/-- After a call, a caller writer `recov` accepts is kept: given back by the callee, or
    wrapping one given back, its paths untouched. -/
theorem recov_sound (hF : Facts env σ E s0) {ref : Option (AVal × Word)} (hrf : RefOk E ref)
    {kn : Kn} {M t : Word → Word} (hkn : KnOk env σ E s0 M ref kn) {passed : List (AVal × AVal)}
    (hgiven : ∀ p ∈ passed, env.model.Keeps (p.2.eval E) (p.1.eval E) M t)
    (hmemg : ∀ a, Aligned a → ¬ Written σ E a → ¬ env.InOwn a →
      (∀ p ∈ passed, ¬ env.model.hit (p.2.eval E) (p.1.eval E) M a) → t a = M a) :
    ∀ (fuel : Nat) (e : AVal × AVal), EntryOk env σ E s0 M e →
      recov env ref kn passed fuel e = true → env.model.Keeps (e.2.eval E) (e.1.eval E) M t
  | 0, e, _, h => hgiven e (List.contains_iff_mem.mp h)
  | fuel + 1, e, he, h => by
    simp only [recov, Bool.or_eq_true] at h
    rcases h with h | h
    · exact hgiven e (List.contains_iff_mem.mp h)
    cases hse : subEntry env ref e with
    | none => rw [hse] at h; cases h
    | some x =>
    obtain ⟨s, d2, k2⟩ := x
    rw [hse] at h
    simp only [Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hrec, hsubs⟩ := h
    obtain ⟨K, hK, hs, hd, hk⟩ := subEntry_some hse
    obtain ⟨_, _, hd2e, hk2e, he2, _, hkeys⟩ := sub_entryOk hF hrf he hK hs hd hk
    have ih := recov_sound hF hrf hkn hgiven hmemg fuel (d2, k2) he2 hrec
    have hK' := kindConst_eval hF hrf he.2.1 hK
    -- Every writer passed is the one `e` wraps.
    have hpassed : ∀ p ∈ passed, p = (d2, k2) := by
      intro p hp
      have := hkn.subs _ (List.contains_iff_mem.mp (hsubs p hp))
      obtain ⟨s', hs'⟩ := this.2
      rw [hse] at hs'
      simp only [Option.some.injEq, Prod.mk.injEq] at hs'
      exact Prod.ext hs'.2.1.symm hs'.2.2.symm
    -- The paths' keys survive the call.
    have hpres : ∀ b ∈ s.keys M (e.1.eval E), t b = M b := by
      intro b hb
      have hb' := hkeys b hb
      refine hmemg b hb'.1 hb'.2.1 hb'.2.2.1 fun p hp => ?_
      rw [hpassed p hp]
      exact hb'.2.2.2.2
    have hdd : derefM t (e.1.eval E) s.dp = derefM M (e.1.eval E) s.dp :=
      derefM_congr fun b hb => hpres b (by simp [Sub.keys, hb])
    have hdk : derefM t (e.1.eval E) s.kp = derefM M (e.1.eval E) s.kp :=
      derefM_congr fun b hb => hpres b (by simp [Sub.keys, hb])
    have hkeyst : s.keys t (e.1.eval E) = s.keys M (e.1.eval E) := by
      simp only [Sub.keys]
      rw [pathKeys_congr (fun b hb => hpres b (by simp [Sub.keys, hb])),
        pathKeys_congr (fun b hb => hpres b (by simp [Sub.keys, hb]))]
    simp only at ih
    rw [hd2e, hk2e] at ih
    have hsubM := env.model.sub_elim hs (by rw [← hK']; exact he.2.2.1)
    rw [hK']
    refine ⟨env.model.sub_intro hs ⟨?_, ?_, fun a ha => ?_⟩, fun a ha => ?_, fun a ha => ?_⟩
    · rw [hdd, hdk]; exact ih.1
    · rw [hdk]; exact hsubM.2.1
    · rw [hkeyst] at ha
      rw [hdd, hdk]
      exact ⟨(hsubM.2.2 a ha).1, fun hh => (hsubM.2.2 a ha).2 (ih.2.1 a hh)⟩
    · rcases (env.model.hit_struct hs a).mp ha with ha | ha
      · rw [hkeyst] at ha
        exact (env.model.hit_struct hs a).mpr (Or.inl ha)
      · rw [hdd, hdk] at ha
        exact (env.model.hit_struct hs a).mpr (Or.inr (ih.2.1 a ha))
    · rcases (env.model.stable_struct hs a).mp ha with ha | ha
      · exact hpres a ha
      · exact ih.2.2 a ha

/-- What `callOk` checks, unfolded. -/
theorem callOk_some {A1 : AState} {g : Iface} {ref : Option (AVal × Word)} {m : Nat}
    {its : List Item} (hok : callOk env σ A1 g ref = some (m, its)) :
    spOff A1 = some m ∧ m + g.depth ≤ σ.depth ∧
    g.foot.mapM (instItem σ (closure env σ ref) A1) = some its ∧
    ∃ passed fs, strsOk env σ (closure env σ ref) ref A1 (some m) its g = some (passed, fs) ∧
      its.all (itemOk σ m) = true ∧ g.nz.all (nzOk σ (closure env σ ref) A1) = true ∧
      g.vals.all (valOk env σ (closure env σ ref) A1) = true ∧
      g.cells.all (cellOk env σ (closure env σ ref) fs A1 (some m) its) = true := by
  unfold callOk at hok
  simp only at hok
  cases hsp : spOff A1 with
  | none => rw [hsp] at hok; cases hok
  | some m' =>
  rw [hsp] at hok
  simp only at hok
  split at hok
  · rename_i hdep
    cases hits : g.foot.mapM (instItem σ (closure env σ ref) A1) with
    | none => rw [hits] at hok; cases hok
    | some its' =>
    rw [hits] at hok
    simp only at hok
    cases hso : strsOk env σ (closure env σ ref) ref A1 (some m') its' g with
    | none => rw [hso] at hok; cases hok
    | some pf =>
    obtain ⟨passed, fs⟩ := pf
    rw [hso] at hok
    simp only at hok
    split at hok
    · rename_i hall
      simp only [Option.some.injEq, Prod.mk.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      simp only [Bool.and_eq_true] at hall
      exact ⟨rfl, hdep, rfl, passed, fs, hso, hall.1.1.1, hall.1.1.2, hall.1.2, hall.2⟩
    · cases hok
  · cases hok

/-- The writers' keys at a call, seen from the caller: a slot a callee writer is built
    from, or a key of a caller writer passed. -/
theorem strHit_call {M : Word → Word} {fs : List Word} {passed : List (AVal × AVal)}
    {g : Iface} {y : MachineState}
    (hst : ∀ eg ∈ g.strs, ∃ e ∈ passed,
      Stands env E M fs e (eg.2.eval (regsOf y)) (eg.1.eval (regsOf y)))
    {a : Word} (h : StrHit env g (regsOf y) M a) :
    (∃ eg ∈ g.strs, env.model.stable (eg.2.eval (regsOf y)) (eg.1.eval (regsOf y)) M a ∧
      ∃ f ∈ fs, a = E .x2 + f) ∨
    ∃ e ∈ passed, env.model.hit (e.2.eval E) (e.1.eval E) M a := by
  obtain ⟨eg, heg, hh⟩ := h
  obtain ⟨e, he, hs⟩ := hst eg heg
  rcases stands_hit hs hh with ⟨h1, h2⟩ | h1
  · exact Or.inl ⟨eg, heg, h1, h2⟩
  · exact Or.inr ⟨e, he, h1⟩

/-- What a checked call site gives the callee: its precondition. -/
theorem call_pre (hF : Facts env σ E s0) {ref : Option (AVal × Word)} (hrf : RefOk E ref)
    {A A1 : AState} {x y : MachineState} {g : Iface} {m : Nat} {its : List Item}
    (hx : St env σ C E s0 A x) (hy1 : RegsHold E A1 y) (hA1 : A1.slots = A.slots)
    (hmem : y.mem = x.mem) (hcode : y.code = C)
    (hok : callOk env σ A1 g ref = some (m, its)) :
    Pre env C g y ∧ y.getReg .x2 = E .x2 - BitVec.ofNat 64 m ∧ m % 8 = 0 ∧
      m + g.depth ≤ σ.depth ∧ g.foot.mapM (instItem σ (closure env σ ref) A1) = some its ∧
      its.all (itemOk σ m) = true := by
  have hm1 := memOk_call hF hx hA1 hmem
  have hyx : y.getMem = x.getMem := funext fun a => by simp [MachineState.getMem, hmem]
  have hkn : KnOk env σ E s0 y.getMem ref (closure env σ ref) := by
    rw [hyx]; exact closure_ok hF hx hrf
  obtain ⟨hsp, hdep, hits, passed, fs, hso, hall1, hall2, hall3, hall4⟩ := callOk_some hok
  simp only [List.all_eq_true] at hall1 hall2 hall3 hall4
  obtain ⟨hsp1, hm8⟩ := spOff_sound hy1 hsp
  have he := hF.depth
  have hsp' : (y.getReg .x2).toNat = (E .x2).toNat - m := by
    rw [hsp1]; have := (E .x2).isLt; bv_omega
  have ht := hF.top
  have hW := callee_written hF hy1 hm1 hkn.cells hsp1 hm8 hdep hits hall1
  have hsl : ∀ p ∈ A1.slots, 8 ≤ negOff p.1 ∧ negOff p.1 ≤ σ.depth ∧ negOff p.1 % 8 = 0 :=
    fun p hp => hx.slots p (hA1 ▸ hp)
  obtain ⟨hpassed, hfs, hstands, _, _⟩ := strsOk_sound hF hrf hkn hy1 hm1 hsl hso
  have hfs' : ∀ f ∈ fs, 8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0 := fun f hf =>
    let ⟨_, _, h, _⟩ := hfs f hf; h
  have hslot : ∀ f ∈ fs, ¬ Written g (regsOf y) (E .x2 + f) := by
    intro f hf
    obtain ⟨m', hm', hsf, hpm, hclr⟩ := hfs f hf
    cases hm'
    exact slot_callee hF hy1 hm1 hkn.cells hsp1 hm8 hdep hits hall1 hsf hpm hclr
  have hcellOk := fun c hc => cellOk_sound hF hy1 hm1 hkn.cells hkn.roots hsl hW
    (fun m0 f hm0 hsl' hpm hclr => by
      cases hm0
      exact slot_callee hF hy1 hm1 hkn.cells hsp1 hm8 hdep hits hall1 hsl' hpm hclr)
    (hall4 c hc)
  refine ⟨⟨hcode, by omega, by omega, by rw [hsp1]; exact aligned_sub hF.al hm8,
    fun a ha hp => ?_, fun it hit a ha hh => ?_, fun v hv => ?_, fun p hp => ?_,
    fun c hc => (hcellOk c hc).1, ?_, ?_⟩, hsp1, hm8, hdep, hits, by simpa [List.all_eq_true] using hall1⟩
  · simp only [MachineState.getMem, hmem]
    exact St.prot hF hx ha hp
  · obtain ⟨it', hit', hinst⟩ := mapM_some_mem hits it hit
    have hio := hall1 it' hit'
    unfold itemOk at hio
    cases hfo : it'.base.frameOff? with
    | some k =>
      rw [hfo] at hio
      cases hl : it'.len with
      | reg _ => rw [hl] at hio; cases hio
      | regPlus _ _ => rw [hl] at hio; cases hio
      | n l =>
        rw [hl] at hio
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hio
        have hb := AVal.frameOff?_some hfo
        have hh' := instItem_hits hy1 hm1 hkn.cells hinst (by simp [hb, AVal.isPtr]) hh
        unfold Item.Hits at hh'
        rw [hb, hl] at hh'
        simp only [AVal.eval, Len.eval] at hh'
        rw [add_frame] at hh'
        have := frameItem_keys (Dg := g.depth) hF.depth hF.al hm8 hdep hio.1.1 hio.1.2 ha hh'
        rw [hsp1]
        exact ⟨this.1, not_prot_of_inWin hF.wf hF.top hF.depth this.2,
          not_own_of_inWin hF.wf hF.top hF.depth this.2⟩
    | none =>
      rw [hfo] at hio
      simp only [Bool.and_eq_true, List.any_eq_true] at hio
      obtain ⟨hnt, d, hd, hwd⟩ := hio
      have hh' := instItem_hits hy1 hm1 hkn.cells hinst hnt hh
      have hdh := within_hits hwd hh'
      have hf := hF.foot d hd a ha hdh
      rw [hsp1]
      exact ⟨fun hw => hf.1 (inWin_callee hF.al hm8 hdep ha hw), hf.2⟩
  · exact nzOk_sound hF.nz hy1 hm1 hkn.cells (hall2 v hv)
  · exact valOk_sound hF hkn.roots hy1 (hall3 p hp)
  · rw [hyx]; exact hx.inv
  · refine ⟨fun eg heg => ?_, fun c hc hsh => ?_⟩
    · obtain ⟨e, he, hst⟩ := hstands eg heg
      exact stands_pre hF (hkn.strs e (hpassed e he)) hst hfs' hW hslot
    · -- A cell of the callee is not a key of a writer it was given.
      obtain ⟨_, hcell⟩ := hcellOk c hc
      rcases strHit_call hstands hsh with ⟨_, _, _, f', hf', hf'a⟩ | ⟨e, he, hh⟩
      · rcases hcell with ⟨f, hfn, _, hca⟩ | ⟨c', hc', hca⟩
        · rw [hca] at hf'a
          have : f = f' := by
            have := congrArg (· - E .x2) hf'a
            simpa using this
          exact hfn (this ▸ hf')
        · have hk := slot_facts hF (hfs' f' hf')
          rw [← hca] at hf'a
          exact (hF.cells c' hc').2.1 (by rw [hf'a]; exact Or.inl hk.2)
      · have hwa := (hkn.strs e (hpassed e he)).2.2.2.1 _ hh
        rcases hcell with ⟨f, _, hsf, hca⟩ | ⟨c', hc', hca⟩
        · exact hwa.1 (by rw [hca]; exact Or.inl (slot_facts hF hsf).2)
        · exact hF.strs.2 c' hc' (by rw [hca]; exact hwa.2.2)

/-- What a checked call site gets back: at the return, the invariant with `afterCall`. -/
theorem call_post (hF : Facts env σ E s0) {ref : Option (AVal × Word)} (hrf : RefOk E ref)
    {A : AState} {x y t : MachineState} {g : Iface} {m : Nat} {its : List Item} {A1 : AState}
    (hx : St env σ C E s0 A x) (hy1 : RegsHold E A1 y) (hA1 : A1.slots = A.slots)
    (hycode : y.code = C)
    (hregs : ∀ r, r ≠ .x1 → y.getReg r = x.getReg r)
    (hmem : y.mem = x.mem) (hok : callOk env σ A1 g ref = some (m, its))
    (hpost : Post env g y t) :
    St env σ C E s0 (afterCall A m its) t := by
  obtain ⟨_, _, hsaved, hun, hcode, hinv, hpstrs⟩ := hpost
  have hm1 := memOk_call hF hx hA1 hmem
  have hyx : y.getMem = x.getMem := funext fun a => by simp [MachineState.getMem, hmem]
  have hkn : KnOk env σ E s0 y.getMem ref (closure env σ ref) := by
    rw [hyx]; exact closure_ok hF hx hrf
  obtain ⟨hsp, hdep, hits, passed, fs, hso, hall, _, _, _⟩ := callOk_some hok
  simp only [List.all_eq_true] at hall
  obtain ⟨hsp1, hm8⟩ := spOff_sound hy1 hsp
  have hwr := callee_written hF hy1 hm1 hkn.cells hsp1 hm8 hdep hits hall
  have hsl : ∀ p ∈ A1.slots, 8 ≤ negOff p.1 ∧ negOff p.1 ≤ σ.depth ∧ negOff p.1 % 8 = 0 :=
    fun p hp => hx.slots p (hA1 ▸ hp)
  obtain ⟨hpassed, hfs, hstands, hstands', hrecov⟩ := strsOk_sound hF hrf hkn hy1 hm1 hsl hso
  -- A key of a callee writer is a slot a writer was built from, or a key of a caller writer.
  have hsh : ∀ a, StrHit env g (regsOf y) y.getMem a →
      (∃ eg ∈ g.strs, env.model.stable (eg.2.eval (regsOf y)) (eg.1.eval (regsOf y)) y.getMem a ∧
        Written σ E a) ∨
      (¬ Written σ E a ∧ StrHit env σ E s0.getMem a ∧
        ∃ e ∈ passed, env.model.hit (e.2.eval E) (e.1.eval E) y.getMem a) := by
    intro a ha
    rcases strHit_call hstands ha with ⟨eg, heg, hst, f, hf, rfl⟩ | ⟨e, he, hh⟩
    · obtain ⟨_, _, hsf, _⟩ := hfs f hf
      exact Or.inl ⟨eg, heg, hst, Or.inl (slot_facts hF hsf).2⟩
    · have hp := (hkn.strs e (hpassed e he)).2.2.2.1 a hh
      exact Or.inr ⟨hp.1, hp.2.2, e, he, hh⟩
  -- Every writer passed is kept by the callee.
  have hgiven : ∀ p ∈ passed, env.model.Keeps (p.2.eval E) (p.1.eval E) y.getMem t.getMem := by
    intro p hp
    obtain ⟨eg, heg, hst⟩ := hstands' p hp
    exact stands_keeps hst (hpstrs.1 eg heg)
  have hmemg : ∀ a, Aligned a → ¬ Written σ E a → ¬ env.InOwn a →
      (∀ p ∈ passed, ¬ env.model.hit (p.2.eval E) (p.1.eval E) y.getMem a) →
      t.getMem a = y.getMem a := by
    intro a ha hnw hno hnp
    refine hun a ha (fun hw => hnw (hwr a ha hw)) hno fun hs => ?_
    rcases hsh a hs with ⟨_, _, _, hw⟩ | ⟨_, _, e, he, hh⟩
    · exact hnw hw
    · exact hnp e he hh
  refine ⟨⟨fun r => ?_, fun p hp => ?_⟩, by rw [hcode, hycode], fun a ha hnw hno hns => ?_, hinv,
    fun p hp => ?_, ?_⟩
  · rw [afterCall_get]
    split
    · rename_i h0; subst h0; simp [AVal.Holds, MachineState.getReg]
    · split
      · rename_i hs
        have hr : r ∈ savedRegs := List.contains_iff_mem.mp hs
        have hr1 : r ≠ .x1 := by rintro rfl; exact absurd hr (by decide)
        rw [hsaved r hr, hregs r hr1]; exact hx.holds.1 r
      · trivial
  · simp only [afterCall, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true] at hp
    obtain ⟨hp, hpm, hclr⟩ := hp
    have hsl' := hx.slots p hp
    have hkey := slot_facts hF hsl'
    have hnw := slot_callee hF hy1 hm1 hkn.cells hsp1 hm8 hdep hits hall hsl' hpm hclr
    have hval : t.getMem (E .x2 + p.1) = y.getMem (E .x2 + p.1) := by
      by_cases hs : StrHit env g (regsOf y) y.getMem (E .x2 + p.1)
      · rcases hsh _ hs with ⟨eg, heg, hst, _⟩ | ⟨hnw', _⟩
        · exact (hpstrs.1 eg heg).2.2 _ hst
        · exact absurd (Or.inl hkey.2) hnw'
      · exact hun _ hkey.1 hnw (not_own_of_inWin hF.wf hF.top hF.depth hkey.2) hs
    rw [hval, hyx]
    exact hx.holds.2 p hp
  · have : t.getMem a = y.getMem a := by
      refine hun a ha (fun hw => hnw (hwr a ha hw)) hno fun hs => ?_
      rcases hsh a hs with ⟨_, _, _, hw⟩ | ⟨_, hs', _⟩
      · exact hnw hw
      · exact hns hs'
    rw [this, hyx]
    exact hx.mem a ha hnw hno hns
  · simp only [afterCall, List.mem_filter] at hp
    exact hx.slots p hp.1
  · refine ⟨fun e he => (hx.strs.1 e he).trans (hyx ▸ ?_), fun k p hw hh => ?_⟩
    · rcases hrecov with hg | hrecov
      · -- The callee has no writers: it keeps every writer it does not write.
        have hp := St.entryOk hF hx he
        rw [← hyx] at hp
        refine hpstrs.2 _ _ hp.2.2.1 fun a ha =>
          ⟨fun hw => (hp.2.2.2.1 a ha).1 (hwr a (env.model.hit_aligned ha) hw), fun hs => ?_⟩
        obtain ⟨eg, heg, _⟩ := hs
        rw [hg] at heg; simp at heg
      · exact recov_sound hF hrf hkn hgiven hmemg 2 e (hyx ▸ St.entryOk hF hx he) (hrecov e he)
    · have h1 := hx.strs.2 k p hw hh
      refine h1.trans (hyx ▸ ?_)
      have hw' : env.model.writerOk k p y.getMem := by rw [hyx]; exact h1.1
      refine hpstrs.2 k p hw' fun a ha => ?_
      have ha0 : env.model.hit k p s0.getMem a := h1.2.1 a (hyx ▸ ha)
      refine ⟨fun hwg => (hh a ha0).1 (hwr a (env.model.hit_aligned ha) hwg), fun hs => ?_⟩
      rcases hsh a hs with ⟨_, _, _, hw⟩ | ⟨_, hs', _⟩
      · exact (hh a ha0).1 hw
      · exact (hh a ha0).2 hs'

/-- A tail call: `f` leaves for `g` with its callee-saved registers and `ra` restored. The
    callee's precondition holds, and its postcondition is `f`'s. -/
theorem tail_sound (hF : Facts env σ E s0) {ref : Option (AVal × Word)} (hrf : RefOk E ref)
    {A : AState} {x : MachineState} {g : Iface}
    (hpre0 : s0.code = C) (hE : E = regsOf s0)
    (hx : St env σ C E s0 A x) (hok : tailOk env σ A g ref = true) :
    Pre env C g x ∧ ∀ t, Post env g x t → Post env σ s0 t := by
  unfold tailOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨hexit, hdep⟩, hret⟩, hfoot⟩ := hok
  obtain ⟨hx1, hsv⟩ := okExit_regs hexit hx.holds.1
  have hx2 : x.getReg .x2 = E .x2 := hsv .x2 (by decide)
  have hm := St.memOk hF hx
  have hkn := closure_ok hF hx hrf
  cases hits : g.foot.mapM (instItem σ (closure env σ ref) A) with
  | none => rw [hits] at hfoot; cases hfoot
  | some its =>
  rw [hits] at hfoot
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hfoot
  obtain ⟨⟨⟨⟨hall, hnz⟩, hvals⟩, hcells⟩, ⟨passed, fs⟩, hso⟩ := hfoot
  have hdD := hF.depth
  -- Each callee item is covered by one of `f`'s.
  have hcov : ∀ it ∈ g.foot, ∀ a, it.Hits (regsOf x) a → ∃ d ∈ σ.foot, d.Hits E a := by
    intro it hit a hh
    obtain ⟨it', hit', hinst⟩ := mapM_some_mem hits it hit
    obtain ⟨⟨_, hnt⟩, d, hd, hwd⟩ := hall it' hit'
    exact ⟨d, hd, within_hits hwd (instItem_hits hx.holds.1 hm hkn.cells hinst hnt hh)⟩
  have hwin : ∀ a, Aligned a → InWin (E .x2) g.depth a → InWin (E .x2) σ.depth a := by
    intro a ha hw
    have := inWin_callee (e := E .x2) (D := σ.depth) (m := 0) (Dg := g.depth) hF.al (by decide)
      (by omega) ha
    simpa using this (by simpa using hw)
  have hW : ∀ a, Aligned a → Written g (regsOf x) a → Written σ E a := by
    rintro a ha (hw | ⟨it, hit, hh⟩)
    · exact Or.inl (hwin a ha (by rw [← hx2]; exact hw))
    · obtain ⟨d, hd, hdh⟩ := hcov it hit a hh
      exact Or.inr ⟨d, hd, hdh⟩
  obtain ⟨hpassed, hfs, hstands, hstands', hrecov⟩ :=
    strsOk_sound hF hrf hkn hx.holds.1 hm hx.slots hso
  have hfs0 : ∀ f ∈ fs, False := fun f hf => by obtain ⟨_, h, _⟩ := hfs f hf; cases h
  have hsh : ∀ a, StrHit env g (regsOf x) x.getMem a →
      ¬ Written σ E a ∧ StrHit env σ E s0.getMem a ∧
      ∃ e ∈ passed, env.model.hit (e.2.eval E) (e.1.eval E) x.getMem a := by
    intro a ha
    rcases strHit_call hstands ha with ⟨_, _, _, f, hf, _⟩ | ⟨e, he, hh⟩
    · exact (hfs0 f hf).elim
    · have hp := (hkn.strs e (hpassed e he)).2.2.2.1 a hh
      exact ⟨hp.1, hp.2.2, e, he, hh⟩
  have hcellOk := fun c hc => cellOk_sound hF hx.holds.1 hm hkn.cells hkn.roots hx.slots hW
    (fun _ _ h => by cases h) (hcells c hc)
  refine ⟨⟨hx.code, by rw [hx2]; exact Nat.le_trans hdep hdD, by rw [hx2]; exact hF.top,
    by rw [hx2]; exact hF.al, fun a ha hp => St.prot hF hx ha hp, fun it hit a ha hh => ?_,
    fun v hv => ?_, fun p hp => valOk_sound hF hkn.roots hx.holds.1 (hvals p hp),
    fun c hc => (hcellOk c hc).1, hx.inv, ?_⟩, fun t ht => ?_⟩
  · obtain ⟨d, hd, hdh⟩ := hcov it hit a hh
    have hf := hF.foot d hd a ha hdh
    rw [hx2]
    exact ⟨fun hw => hf.1 (hwin a ha hw), hf.2⟩
  · exact nzOk_sound hF.nz hx.holds.1 hm hkn.cells (hnz v hv)
  · refine ⟨fun eg heg => ?_, fun c hc hs => ?_⟩
    · obtain ⟨e, he, hst⟩ := hstands eg heg
      exact stands_pre hF (hkn.strs e (hpassed e he)) hst (fun f hf => (hfs0 f hf).elim) hW
        (fun f hf => (hfs0 f hf).elim)
    · obtain ⟨_, hcell⟩ := hcellOk c hc
      obtain ⟨hnw, hsh', _⟩ := hsh _ hs
      rcases hcell with ⟨f, _, hsf, hca⟩ | ⟨c', hc', hca⟩
      · exact hnw (by rw [hca]; exact Or.inl (slot_facts hF hsf).2)
      · exact hF.strs.2 c' hc' (by rw [hca]; exact hsh')
  · obtain ⟨hgr, hpc, hsaved, hun, hcode, hinv, hpstrs⟩ := ht
    have hgiven : ∀ p ∈ passed, env.model.Keeps (p.2.eval E) (p.1.eval E) x.getMem t.getMem :=
      fun p hp => let ⟨eg, heg, hst⟩ := hstands' p hp; stands_keeps hst (hpstrs.1 eg heg)
    have hmemg : ∀ a, Aligned a → ¬ Written σ E a → ¬ env.InOwn a →
        (∀ p ∈ passed, ¬ env.model.hit (p.2.eval E) (p.1.eval E) x.getMem a) →
        t.getMem a = x.getMem a := by
      intro a ha hnw hno hnp
      refine hun a ha (fun hw => hnw (hW a ha hw)) hno fun hs => ?_
      obtain ⟨_, _, e, he, hh⟩ := hsh a hs
      exact hnp e he hh
    refine ⟨?_, ?_, fun r hr => ?_, fun a ha hnw hno hns => ?_, ?_, hinv, ?_⟩
    · rcases hret with h | h
      · exact h
      · rw [hgr] at h; cases h
    · rw [hpc, hx1, hE]; rfl
    · rw [hsaved r hr, hsv r hr, hE]; rfl
    · rw [← hE] at hnw hns
      have : t.getMem a = x.getMem a := by
        refine hun a ha (fun hw => hnw (hW a ha hw)) hno fun hs => ?_
        obtain ⟨_, hs', _⟩ := hsh a hs
        exact hns hs'
      rw [this]
      exact hx.mem a ha hnw hno hns
    · rw [hcode, hx.code, hpre0]
    · rw [← hE]
      refine ⟨fun e he => (hx.strs.1 e he).trans ?_, fun k p hw hh => ?_⟩
      · rcases hrecov with hg | hrecov
        · have hp := St.entryOk hF hx he
          refine hpstrs.2 _ _ hp.2.2.1 fun a ha =>
            ⟨fun hw => (hp.2.2.2.1 a ha).1 (hW a (env.model.hit_aligned ha) hw), fun hs => ?_⟩
          obtain ⟨eg, heg, _⟩ := hs
          rw [hg] at heg; simp at heg
        · exact recov_sound hF hrf hkn hgiven hmemg 2 e (St.entryOk hF hx he) (hrecov e he)
      · have h1 := hx.strs.2 k p hw hh
        refine h1.trans ?_
        refine hpstrs.2 k p h1.1 fun a ha => ?_
        have ha0 := h1.2.1 a ha
        refine ⟨fun hwg => (hh a ha0).1 (hW a (env.model.hit_aligned ha) hwg), fun hs => ?_⟩
        obtain ⟨_, hs', _⟩ := hsh a hs
        exact (hh a ha0).2 hs'

/-- A `ret` with every callee-saved register and `ra` restored is `f`'s postcondition. -/
theorem ret_sound {A : AState} {x : MachineState}
    (hpre0 : s0.code = C) (hE : E = regsOf s0) (hr : σ.returns = true)
    (hx : St env σ C E s0 A x) (hok : okExit A = true) :
    Post env σ s0 (execInstrBr x (.JALR .x0 .x1 0)) := by
  obtain ⟨hx1, hsv⟩ := okExit_regs hok hx.holds.1
  refine ⟨hr, ?_, fun r hr' => ?_, fun a ha hnw hno hns => ?_, ?_,
    Env.Inv_congr (fun _ _ _ => by simp [execInstrBr, setReg_x0]) hx.inv, ?_⟩
  · simp only [execInstrBr, setReg_x0]
    show (x.getReg .x1 + signExtend12 0) &&& ~~~1#64 = _
    rw [hx1, hE]; simp [signExtend12, regsOf]
  · simp only [execInstrBr, setReg_x0, MachineState.getReg_setPC]
    rw [hsv r hr', hE]; rfl
  · rw [← hE] at hnw hns
    simpa [execInstrBr, setReg_x0] using hx.mem a ha hnw hno hns
  · simp [execInstrBr, setReg_x0, hx.code, hpre0]
  · rw [← hE]
    simpa [execInstrBr, setReg_x0] using hx.strs

end Call

/-! ## The activation -/

theorem Ctx.lookup_some {c : Ctx} {pc : Word} {g : Iface} (h : c.lookup pc = some g) :
    g ∈ c.tbl ∧ g.entry = pc := by
  unfold Ctx.lookup at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem plainStep_ecall {env : Env} {σ : Iface} {kn : Kn} {pc : Word} {A : AState} :
    plainStep env σ kn pc A .ECALL = none := by
  simp [plainStep, aluResult, loadOf, storeOf]

theorem plainStep_some_plain {env : Env} {σ : Iface} {kn : Kn} {pc : Word} {A B : AState}
    {i : Instr} (h : plainStep env σ kn pc A i = some B) :
    i ≠ .ECALL ∧ i ≠ .EBREAK ∧ ∀ c r, i ≠ .CSRS c r := by
  refine ⟨?_, ?_, fun c r => ?_⟩ <;>
    (rintro rfl; simp [plainStep, aluResult, loadOf, storeOf] at h)

theorem St.le {env σ C E s0} {A B : AState} {x : MachineState} (h : St env σ C E s0 A x)
    (hle : A.le B = true) : St env σ C E s0 B x := by
  refine ⟨AState.holds_of_le hle h.holds, h.code, h.mem, h.inv, fun p hp => h.slots p ?_, h.strs⟩
  simp only [AState.le, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hle
  exact hle.2 p hp

theorem St.setPC {env σ C E s0} {A : AState} {x : MachineState} {v : Word}
    (h : St env σ C E s0 A x) : St env σ C E s0 A (x.setPC v) :=
  ⟨AState.holds_setPC h.holds, by simp [h.code],
    fun a ha hnw hno hns => by simpa using h.mem a ha hnw hno hns,
    Env.Inv_congr (fun _ _ _ => by simp) h.inv, h.slots, by simpa using h.strs⟩

theorem St.setReg {env σ C E s0} {A : AState} {x : MachineState} {r : Reg} {v : AVal} {w : Word}
    (h : St env σ C E s0 A x) (hv : v.Holds E w) : St env σ C E s0 (A.set r v) (x.setReg r w) :=
  ⟨AState.holds_set h.holds hv, by simp [h.code],
    fun a ha hnw hno hns => by simpa using h.mem a ha hnw hno hns,
    Env.Inv_congr (fun _ _ _ => by simp) h.inv, by
      intro p hp
      exact h.slots p (by simpa [AState.set] using hp), by simpa using h.strs⟩

/-! ## Items a syscall writes -/

section SysItems

variable {env : Env} {σ : Iface} {C : Word → Option Instr} {E : Ent} {s0 : MachineState}

theorem frameItem_inWin {e : Word} {D mk l : Nat} (hD : D ≤ e.toNat) (hl : l ≤ mk) (hk : mk ≤ D)
    {a : Word} (h : Hits (e - BitVec.ofNat 64 mk) l a) : InWin e D a := by
  have hl0 : 0 < l := by
    rcases h with h | ⟨h0, _⟩
    · exact Nat.lt_of_le_of_lt (Nat.zero_le _) h
    · exact h0
  have hb : (e - (e - BitVec.ofNat 64 mk)).toNat = mk := by
    have : e - (e - BitVec.ofNat 64 mk) = BitVec.ofNat 64 mk := by bv_omega
    rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := e.isLt; omega)]
  exact inWin_of_hits (by omega) (by omega) hl0 h

/-- An item `itemOk` accepts with `m = depth` is something the function may write, and its
    base is known. -/
theorem itemOk_depth (hF : Facts env σ E s0) {it : Item} (h : itemOk σ σ.depth it = true) :
    it.base.isPtr = true ∧ ∀ a, it.Hits E a → Written σ E a := by
  unfold itemOk at h
  cases hfo : it.base.frameOff? with
  | some k =>
    rw [hfo] at h
    have hb := AVal.frameOff?_some hfo
    cases hl : it.len with
    | reg _ => rw [hl] at h; cases h
    | regPlus _ _ => rw [hl] at h; cases h
    | n l =>
      rw [hl] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      refine ⟨by simp [hb, AVal.isPtr], fun a ha => Or.inl ?_⟩
      unfold Item.Hits at ha
      rw [hb, hl] at ha
      simp only [AVal.eval, Len.eval] at ha
      rw [add_frame] at ha
      exact frameItem_inWin hF.depth h.1.1 h.1.2 ha
  | none =>
    rw [hfo] at h
    simp only [Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨hnt, d, hd, hwd⟩ := h
    exact ⟨hnt, fun a ha => Or.inr ⟨d, hd, within_hits hwd ha⟩⟩

/-- A slot that `slotClear` keeps is not hit by an item `itemOk` accepts. -/
theorem slot_clear_items (hF : Facts env σ E s0) {p : Word × AVal}
    (hsl : 8 ≤ negOff p.1 ∧ negOff p.1 ≤ σ.depth ∧ negOff p.1 % 8 = 0) {it : Item}
    (hok : itemOk σ σ.depth it = true) (hc : slotClear p.1 it = true) :
    ¬ it.Hits E (E .x2 + p.1) := by
  have hkey := slot_facts hF hsl
  unfold itemOk at hok
  unfold slotClear at hc
  cases hfo : it.base.frameOff? with
  | some k =>
    rw [hfo] at hok hc
    have hb := AVal.frameOff?_some hfo
    cases hl : it.len with
    | reg _ => rw [hl] at hok; cases hok
    | regPlus _ _ => rw [hl] at hok; cases hok
    | n l =>
      rw [hl] at hok hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hc
      intro hh
      unfold Item.Hits at hh
      rw [hb, hl] at hh
      simp only [AVal.eval, Len.eval] at hh
      rw [add_frame, add_frame] at hh
      have := hF.depth
      exact slot_not_hits (by omega) (by omega) hsl.1 hok.1.1 hc hh
  | none =>
    rw [hfo] at hok
    simp only [Bool.and_eq_true, List.any_eq_true] at hok
    obtain ⟨_, d, hd, hwd⟩ := hok
    intro hh
    exact (hF.foot d hd _ hkey.1 (within_hits hwd hh)).1 hkey.2

end SysItems

section Act

variable {c : Ctx} {anno : Array (Option AState)} {C : Word → Option Instr} {n : Nat}
  {G : MachineState → Prop} {P : Prop} {s0 : MachineState}

/-- The invariant at a state of the activation: at instruction `i` with its annotation. -/
def Ctx.At (c : Ctx) (anno : Array (Option AState)) (C : Word → Option Instr) (s0 : MachineState)
    (x : MachineState) : Prop :=
  ∃ i A, c.f.idx? x.pc = some i ∧ Fn.annoAt anno i = some A ∧ St c.env c.σ C (regsOf s0) s0 A x

/-- The hypotheses of the activation argument. -/
structure ActHyp (c : Ctx) (anno : Array (Option AState)) (C : Word → Option Instr) (n : Nat)
    (G : MachineState → Prop) (P : Prop) (s0 : MachineState) : Prop where
  valid : c.valid anno = true
  code : CodeAt c.f C
  tbl : ∀ g ∈ c.tbl, ∀ m < n, g.HoldsN c.env C m
  code0 : s0.code = C
  facts : Facts c.env c.σ (regsOf s0) s0
  k : ∀ t, Post c.env c.σ s0 t → SafeN G n P t
  cfi : ∀ x, G x → c.env.Cfi x

theorem ActHyp.instrOk (h : ActHyp c anno C n G P s0) {i : Nat} (hi : i < c.f.prog.length) :
    c.instrOk anno i = true := by
  have := h.valid
  simp only [Ctx.valid, Bool.and_eq_true, List.all_eq_true, List.mem_range] at this
  exact this.2 i hi

/-- A jump to `tgt` from a state with invariant `A`: inside the function (then the target's
    annotation holds), or a tail call (then the callee's interface carries it). -/
theorem jump_sound (h : ActHyp c anno C n G P s0) {k : Nat} (hk : k < n)
    (ih : ∀ x, c.At anno C s0 x → SafeN G k P x) {A : AState} {z : MachineState} {tgt : Word}
    {ref : Option (AVal × Word)} (hrf : RefOk (regsOf s0) ref)
    {es : List Edge} (hj : c.jump A tgt ref = some es) (hes : ∀ e ∈ es, edgeOk anno e = true)
    (hz : St c.env c.σ C (regsOf s0) s0 A z) (hpc : z.pc = tgt) : SafeN G k P z := by
  unfold Ctx.jump at hj
  cases hidx : c.f.idx? tgt with
  | some j =>
    rw [hidx] at hj; cases hj
    have he := hes _ (List.mem_singleton_self _)
    simp only [edgeOk] at he
    cases hC : Fn.annoAt anno j with
    | none => rw [hC] at he; cases he
    | some B => rw [hC] at he; exact ih z ⟨j, B, by rw [hpc]; exact hidx, hC, hz.le he⟩
  | none =>
    rw [hidx] at hj
    cases hg : c.lookup tgt with
    | none => rw [hg] at hj; cases hj
    | some g =>
      rw [hg] at hj
      simp only at hj
      split at hj
      · rename_i htail
        obtain ⟨hmem, hent⟩ := Ctx.lookup_some hg
        obtain ⟨hpre, hpost⟩ := tail_sound h.facts hrf h.code0 rfl hz htail
        exact h.tbl g hmem k hk G h.cfi P z (by rw [hpc, hent]) hpre
          (fun t ht => SafeN.mono (Nat.le_of_lt hk) (h.k t (hpost t ht)))
      · cases hj

/-- An outlined fragment, run from its `n`-th instruction to its closing `jalr zero, 0(t0)`. -/
theorem frag_sound (h : ActHyp c anno C n G P s0) {k : Nat} {fb : Word} :
    ∀ (fp : List (Option Instr)) (m : Nat) {A B : AState} {z : MachineState},
    c.runFrag A fb fp m = some B →
    (∀ j ins, fp[j]? = some (some ins) → C (fb + BitVec.ofNat 64 (4 * (m + j))) = some ins) →
    z.pc = fb + BitVec.ofNat 64 (4 * m) → St c.env c.σ C (regsOf s0) s0 A z →
    (∀ z', St c.env c.σ C (regsOf s0) s0 B z' → z'.pc = z'.getReg .x5 &&& ~~~1#64 → SafeN G k P z') →
    SafeN G k P z
  | [], _, _, _, _, hr, _, _, _, _ => by simp [Ctx.runFrag] at hr
  | none :: _, _, _, _, _, hr, _, _, _, _ => by simp [Ctx.runFrag] at hr
  | some i :: rest, m, A, B, z, hr, hcode, hpc, hz, hk => by
    have hfetch : z.code z.pc = some i := by
      rw [hz.code, hpc]; simpa using hcode 0 i rfl
    by_cases hj : i = .JALR .x0 .x5 0
    · subst hj
      simp only [Ctx.runFrag, if_true, Option.some.injEq] at hr; subst hr
      cases hs : stepSp1 z with
      | none => exact SafeN.stuck hs (fun ha => absurd ha (not_accepted_of_code hfetch (by simp)))
      | some z' =>
        have hex := stepSp1_exec hfetch (by simp) (by simp) (by simp) hs
        subst hex
        refine SafeN.of_step (not_accepted_of_code hfetch (by simp)) hs (hk _ ?_ ?_)
        · simp only [execInstrBr, setReg_x0]; exact hz.setPC
        · simp only [execInstrBr, setReg_x0]
          show (z.getReg .x5 + signExtend12 0) &&& ~~~1#64 = _
          simp [signExtend12]
    · simp only [Ctx.runFrag, hj, if_false] at hr
      cases hp : plainStep c.env c.σ (closure c.env c.σ none) (fb + BitVec.ofNat 64 (4 * m)) A i with
      | none => rw [hp] at hr; cases hr
      | some A' =>
        rw [hp] at hr
        simp only at hr
        obtain ⟨he, hb, hcs⟩ := plainStep_some_plain hp
        cases hs : stepSp1 z with
        | none => exact SafeN.stuck hs (fun ha => absurd ha (not_accepted_of_code hfetch he))
        | some z' =>
          have hex := stepSp1_exec hfetch he hb hcs hs
          subst hex
          obtain ⟨hz', hpc'⟩ := plainStep_sound h.facts hpc hz (closure_ok h.facts hz refOk_none).cells
            (closure_ok h.facts hz refOk_none).roots hp
          refine SafeN.of_step (not_accepted_of_code hfetch he) hs ?_
          refine frag_sound h rest (m + 1) hr (fun j ins hm => ?_) ?_ hz' hk
          · have := hcode (j + 1) ins (by simpa using hm)
            rw [show m + (j + 1) = m + 1 + j by omega] at this
            exact this
          · rw [hpc', hpc, ofNat_four_mul_succ, BitVec.add_assoc]

/-- A call: the callee's interface, then the annotation after the call. -/
theorem call_sound' (h : ActHyp c anno C n G P s0) {k : Nat} (hk : k < n)
    (ih : ∀ x, c.At anno C s0 x → SafeN G k P x) {A : AState} {x y : MachineState} {pc tgt : Word}
    {ref : Option (AVal × Word)} (hrf : RefOk (regsOf s0) ref)
    {es : List Edge} (hcall : c.call pc A tgt ref = some es) (hes : ∀ e ∈ es, edgeOk anno e = true)
    (hx : St c.env c.σ C (regsOf s0) s0 A x)
    (hy : y = (x.setReg .x1 (pc + 4)).setPC tgt) : SafeN G k P y := by
  unfold Ctx.call at hcall
  cases hg : c.lookup tgt with
  | none => rw [hg] at hcall; cases hcall
  | some g =>
  rw [hg] at hcall
  simp only at hcall
  obtain ⟨hmem, hent⟩ := Ctx.lookup_some hg
  cases hok : callOk c.env c.σ (A.set .x1 (.const (pc + 4))) g ref with
  | none => rw [hok] at hcall; cases hcall
  | some r =>
  obtain ⟨m, its⟩ := r
  rw [hok] at hcall
  simp only at hcall
  have hy1 : RegsHold (regsOf s0) (A.set .x1 (.const (pc + 4))) y := by
    rw [hy]; exact (AState.holds_setPC (AState.holds_set hx.holds (by simp [AVal.Holds]))).1
  have hycode : y.code = C := by rw [hy]; simp [hx.code]
  have hymem : y.mem = x.mem := by rw [hy]; simp [MachineState.setReg, MachineState.setPC]
  obtain ⟨hpre, -, -, -, -, -⟩ := call_pre h.facts hrf hx hy1 rfl hymem hycode hok
  refine h.tbl g hmem k hk G h.cfi P y (by rw [hy, hent]; rfl) hpre (fun t ht => ?_)
  have hregs : ∀ r, r ≠ .x1 → y.getReg r = x.getReg r := by
    intro r hr
    rw [hy, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  have hst := call_post h.facts hrf hx hy1 rfl hycode hregs hymem hok ht
  split at hcall
  · rename_i hret
    split at hcall
    · rename_i hal
      cases hj : c.f.idx? (pc + 4) with
      | none => rw [hj] at hcall; cases hcall
      | some j =>
        rw [hj] at hcall; cases hcall
        have he := hes _ (List.mem_singleton_self _)
        simp only [edgeOk] at he
        cases hC : Fn.annoAt anno j with
        | none => rw [hC] at he; cases he
        | some B =>
          rw [hC] at he
          refine ih t ⟨j, B, ?_, hC, hst.le he⟩
          rw [ht.2.1, hy]
          simp only [MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide), hal]
          exact hj
    · cases hcall
  · rename_i hnr
    exact absurd ht.1 (by simpa using hnr)

/-- **The activation.** Every state of it with an annotation is safe for every budget up
    to `n`. -/
theorem act (h : ActHyp c anno C n G P s0) : ∀ k ≤ n, ∀ x, c.At anno C s0 x → SafeN G k P x := by
  intro k
  induction k with
  | zero => intro _ _ _; exact SafeN.zero
  | succ k ih =>
  intro hkn x ⟨i, A, hi, hA, hx⟩
  apply SafeN.assume
  intro hGx
  have hkn' : k < n := hkn
  have ih' := ih (Nat.le_of_lt hkn')
  have ⟨hpcx, hilen⟩ := Fn.idx?_some hi
  have hok := h.instrOk hilen
  unfold Ctx.instrOk at hok
  rw [hA] at hok
  simp only at hok
  cases hstp : c.step i A with
  | none => rw [hstp] at hok; cases hok
  | some es =>
  rw [hstp] at hok
  simp only [List.all_eq_true] at hok
  unfold Ctx.step at hstp
  cases hpi : c.f.prog[i]? with
  | none => rw [hpi] at hstp; cases hstp
  | some oi =>
  rw [hpi] at hstp
  simp only at hstp
  have hfetch : x.code x.pc = oi := by rw [hx.code, hpcx]; exact h.code.1 i oi hpi
  rw [← hpcx] at hstp
  cases oi with
  | none =>
    have hs : stepSp1 x = none := by simp [stepSp1, hfetch]
    exact SafeN.stuck hs (fun ha => by have := ha.1; rw [hfetch] at this; cases this)
  | some ins =>
  unfold Ctx.stepAt at hstp
  simp only at hstp
  by_cases hec : ins = .ECALL
  · -- A syscall.
    subst hec
    simp only [branchOff?] at hstp
    have hregs : ∀ r, (A.get r).Holds (regsOf s0) (x.getReg r) := hx.holds.1
    cases hss : sysStep c.σ A with
    | none => rw [hss] at hstp; cases hstp
    | some out =>
    rw [hss] at hstp
    obtain ⟨hstop, hnext⟩ := sysStep_sound hss hregs h.facts.nz hfetch
    cases out with
    | stop =>
      obtain ⟨hs, hna⟩ := hstop rfl
      exact SafeN.stuck hs (fun ha => absurd ha hna)
    | next B its =>
      simp only at hstp
      split at hstp
      · rename_i hall
        simp only [List.all_eq_true] at hall
        have hit := fun it hi => itemOk_depth h.facts (hall it hi)
        obtain ⟨hna, hy⟩ := hnext B its rfl (fun it hi => (hit it hi).1)
        refine SafeN.intro (n := k) (P := P) hna (fun y hst => ?_)
        obtain ⟨hpc, hcode, hB, hsl, hmem⟩ := hy y hst
        refine jump_sound h hkn' ih' refOk_none hstp hok ?_ hpc
        refine ⟨⟨fun r => hB r, fun p hp => ?_⟩, by rw [hcode, hx.code], fun a ha hnw hno hns => ?_,
          Env.Inv_congr (fun a ha ho => hmem a (fun it hi hh =>
            h.facts.not_own ha ((hit it hi).2 a hh) ho)) hx.inv, fun p hp => ?_,
          StrsPost.congr h.facts hx.strs (fun a hna => hmem a (fun it hi hh => hna ((hit it hi).2 a hh)))⟩
        · simp only [List.mem_filter, List.all_eq_true] at hp
          rw [hsl] at hp
          rw [hmem _ (fun it hi => slot_clear_items h.facts (hx.slots p hp.1) (hall it hi)
            (hp.2 it hi))]
          exact hx.holds.2 p hp.1
        · rw [hmem a (fun it hi hh => hnw ((hit it hi).2 a hh))]
          exact hx.mem a ha hnw hno hns
        · simp only [List.mem_filter] at hp
          rw [hsl] at hp
          exact hx.slots p hp.1
      · cases hstp
  have hne : ins ≠ .ECALL := hec
  have hna := not_accepted_of_code hfetch hne
  refine SafeN.intro (n := k) (P := P) hna (fun y hst => ?_)
  split at hstp
  · -- A conditional branch.
    rename_i off hb
    have hex := stepSp1_exec hfetch hne (by rintro rfl; simp [branchOff?] at hb)
      (by rintro c r rfl; simp [branchOff?] at hb) hst
    subst hex
    cases h1 : c.jump A (x.pc + 4) with
    | none => rw [h1] at hstp; simp at hstp
    | some e1 =>
    cases h2 : c.jump A (x.pc + signExtend13 off) with
    | none => rw [h1, h2] at hstp; simp at hstp
    | some e2 =>
    rw [h1, h2] at hstp
    simp at hstp
    subst hstp
    rcases branch_exec (s := x) hb with he | he <;> rw [he]
    · exact jump_sound h hkn' ih' refOk_none h1 (fun e he' => hok e (List.mem_append_left _ he')) hx.setPC rfl
    · exact jump_sound h hkn' ih' refOk_none h2 (fun e he' => hok e (List.mem_append_right _ he')) hx.setPC rfl
  · split at hstp
    · -- `jal rd, off`
      rename_i rd off _
      have hex := stepSp1_exec hfetch hne (by simp) (by simp) hst
      subst hex
      split at hstp
      · rename_i h0; subst h0
        simp only [execInstrBr, setReg_x0]
        exact jump_sound h hkn' ih' refOk_none hstp hok hx.setPC rfl
      · split at hstp
        · rename_i h1; subst h1
          exact call_sound' h hkn' ih' refOk_none hstp hok hx rfl
        · cases hstp
    · -- `jalr rd, off(rs)`
      rename_i rd rs off _
      have hex := stepSp1_exec hfetch hne (by simp) (by simp) hst
      subst hex
      split at hstp
      · rename_i h0; subst h0
        split at hstp
        · rename_i hr; obtain ⟨rfl, rfl⟩ := hr
          split at hstp
          · rename_i hret
            cases hstp
            have he := hok _ (List.mem_singleton_self _)
            simp only [edgeOk] at he
            exact SafeN.mono (Nat.le_of_lt hkn') (h.k _ (ret_sound h.code0 rfl hret hx he))
          · cases hstp
        · simp only [execInstrBr, setReg_x0]
          have hrs := hx.holds.1 rs
          split at hstp
          · rename_i es' hfo
            cases hstp
            obtain ⟨root, c', es'', hroot, hk, hsub⟩ := fanOut_sound h.facts hrs hfo
            exact jump_sound h hkn' ih' (fun rf hrf => by cases hrf; exact hroot) hk
              (fun e he => hok e (hsub e he)) hx.setPC rfl
          · cases hl : c.env.cfi.lookup x.pc with
            | none => rw [hl] at hstp; cases hstp
            | some ts =>
              rw [hl] at hstp
              simp only [Option.bind_some] at hstp
              have hin := h.cfi x hGx _ (lookup_mem hl) rfl _ _ _ hfetch
              obtain ⟨es', h1, hsub⟩ := allEdges_mem hstp hin
              exact jump_sound h hkn' ih' refOk_none h1 (fun e he => hok e (hsub e he)) hx.setPC rfl
      · split at hstp
        · rename_i h1; subst h1
          have hrs := hx.holds.1 rs
          split at hstp
          · rename_i es' hfo
            cases hstp
            obtain ⟨root, c', es'', hroot, hk, hsub⟩ := fanOut_sound h.facts hrs hfo
            exact call_sound' h hkn' ih' (fun rf hrf => by cases hrf; exact hroot) hk
              (fun e he => hok e (hsub e he)) hx (by simp [execInstrBr])
          · cases hl : c.env.cfi.lookup x.pc with
            | none => rw [hl] at hstp; cases hstp
            | some ts =>
              rw [hl] at hstp
              simp only [Option.bind_some] at hstp
              have hin := h.cfi x hGx _ (lookup_mem hl) rfl _ _ _ hfetch
              obtain ⟨es', h1, hsub⟩ := allEdges_mem hstp hin
              exact call_sound' h hkn' ih' refOk_none h1 (fun e he => hok e (hsub e he)) hx
                (by simp [execInstrBr])
        · split at hstp
          · -- An outlined fragment.
            rename_i h5; obtain ⟨rfl, rfl⟩ := h5
            unfold Ctx.outlined at hstp
            have h5v := hx.holds.1 .x5
            split at hstp
            · rename_i t ht
              rw [ht] at h5v; simp only [AVal.Holds] at h5v
              dsimp only at hstp
              cases hfp : c.f.frags.lookup ((t + signExtend12 off) &&& ~~~1#64) with
              | none => rw [hfp] at hstp; simp at hstp
              | some fp =>
              cases hj : c.f.idx? (x.pc + 4) with
              | none => rw [hfp, hj] at hstp; simp at hstp
              | some j =>
              rw [hfp, hj] at hstp
              simp only at hstp
              cases hB : c.runFrag (A.set .x5 (.const (x.pc + 4))) ((t + signExtend12 off) &&& ~~~1#64)
                  fp 0 with
              | none => rw [hB] at hstp; simp at hstp
              | some B =>
              rw [hB] at hstp
              simp only at hstp
              split at hstp
              · rename_i hcond
                cases hstp
                have he := hok _ (List.mem_singleton_self _)
                simp only [edgeOk] at he
                cases hC : Fn.annoAt anno j with
                | none => rw [hC] at he; cases he
                | some D =>
                rw [hC] at he
                refine frag_sound h fp 0 hB (fun m ins hm => ?_) ?_ ?_ (fun z' hz' hpc' => ?_)
                · have := h.code.2 _ fp hfp m ins hm
                  simpa using this
                · show (x.getReg .x5 + signExtend12 off) &&& ~~~1#64 = _
                  rw [h5v]; simp
                · simp only [execInstrBr]; exact (hx.setReg (by simp [AVal.Holds])).setPC
                · have h5' := hz'.holds.1 .x5
                  rw [hcond.1] at h5'; simp only [AVal.Holds] at h5'
                  refine ih' z' ⟨j, D, ?_, hC, hz'.le he⟩
                  rw [hpc', h5', hcond.2]; exact hj
              · cases hstp
            · cases hstp
          · cases hstp
    · -- `ebreak` traps.
      simp [stepSp1, hfetch] at hst
    · exact absurd rfl hec
    · -- A straight-line instruction.
      cases hp : plainStep c.env c.σ (closure c.env c.σ none) x.pc A ins with
      | none => rw [hp] at hstp; simp at hstp
      | some B =>
        rw [hp] at hstp
        simp only [Option.bind_some] at hstp
        obtain ⟨he, hb, hcs⟩ := plainStep_some_plain hp
        have hex := stepSp1_exec hfetch he hb hcs hst
        subst hex
        obtain ⟨hy, hpc'⟩ := plainStep_sound h.facts rfl hx (closure_ok h.facts hx refOk_none).cells
          (closure_ok h.facts hx refOk_none).roots hp
        exact jump_sound h hkn' ih' refOk_none hstp hok hy hpc'

end Act

/-! ## Soundness -/

/-- The entry state describes the entry, given the `vals` premise. -/
theorem holds_entryState {σ : Iface} {s : MachineState}
    (hv : ∀ p ∈ σ.vals, s.getReg p.1 ∈ p.2) : σ.entryState.Holds (regsOf s) s := by
  refine ⟨fun r => ?_, fun p hp => by simp [Iface.entryState] at hp⟩
  by_cases h0 : r = .x0
  · subst h0; simp [AState.get, AVal.Holds, MachineState.getReg]
  · simp only [AState.get, h0, if_false, Iface.entryState, getD_map_allRegs]
    cases hl : σ.vals.lookup r with
    | none => simp [AVal.Holds, regsOf]
    | some cs => exact hv (r, cs) (lookup_mem hl)

/-- **The checker is sound.** If it accepts the annotation, and every callee in the table
    meets its interface for every budget below `n`, the function meets its own for `n`. -/
theorem Ctx.sound {c : Ctx} {anno : Array (Option AState)} {C : Word → Option Instr} {n : Nat}
    (hv : c.valid anno = true) (hcode : CodeAt c.f C) (hne : 0 < c.f.prog.length)
    (hwf : c.env.wf = true) (htbl : ∀ g ∈ c.tbl, ∀ m < n, g.HoldsN c.env C m) :
    c.σ.HoldsN c.env C n := by
  intro G hG P s hpc hpre hk
  have hv0 := hv
  simp only [Ctx.valid, Bool.and_eq_true, beq_iff_eq] at hv0
  obtain ⟨⟨⟨hptr, hbase⟩, h0⟩, _⟩ := hv0
  have hptr' : ∀ e ∈ c.σ.strs, e.1.isPtr = true ∧ e.2.isPtr = true := fun e he => by
    have := List.all_eq_true.mp hptr e he
    simpa [Bool.and_eq_true] using this
  have hF := Facts.of_pre hwf hptr' hpre
  cases hA : Fn.annoAt anno 0 with
  | none => rw [hA] at h0; simp at h0
  | some A =>
  rw [hA] at h0
  have hAct : ActHyp c anno C n G P s := ⟨hv, hcode, htbl, hpre.1, hF, hk, hG⟩
  refine act hAct n (Nat.le_refl _) s ⟨0, A, ?_, hA, ?_⟩
  · simp [Fn.idx?, hpc, ← hbase, hne]
  · refine ⟨AState.holds_of_le h0 (holds_entryState hF.vals), hpre.1,
      fun _ _ _ _ _ => rfl, hF.inv, fun p hp => ?_,
      ⟨fun e he => Model.Keeps.refl (hF.strs.1 e he).1, fun k p hw _ => Model.Keeps.refl hw⟩⟩
    simp only [AState.le, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h0
    have := h0.2 p hp
    simp [Iface.entryState] at this

/-! ## Composition -/

/-- A fact for every member of a list, as nested conjunctions: the form a generated proof
    writes as `⟨h₁, h₂, …, trivial⟩`. -/
theorem forall_mem_of_foldr {α : Type} {P : α → Prop} :
    ∀ {l : List α}, l.foldr (fun a acc => P a ∧ acc) True → ∀ a ∈ l, P a
  | [], _, a, ha => by simp at ha
  | b :: l, h, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h.1
    · exact forall_mem_of_foldr h.2 a ha

/-- **Composition.** If every interface of a table follows, for each budget `n`, from the
    whole table for budgets below `n` (by the checker, or by any other proof), then every
    interface holds. Recursion is covered: the induction is on the budget. -/
theorem table_sound {env : Env} {C : Word → Option Instr} {tbl : List Iface}
    (h : ∀ g ∈ tbl, ∀ n, (∀ g' ∈ tbl, ∀ m < n, g'.HoldsN env C m) → g.HoldsN env C n) :
    ∀ g ∈ tbl, g.Holds env C := by
  have : ∀ n, ∀ g ∈ tbl, g.HoldsN env C n := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih => exact fun g hg => h g hg n (fun g' hg' m hm => ih m hm g' hg')
  exact fun g hg n => this n g hg

end AsmVerif.RiscV.Check
