/-
  AsmVerif.RiscV.Check.Sound.Kn

  The checker's soundness, part 2: knowledge. What `closure` computes holds at every state
  of the activation: the function's writers are well-typed at entry, their stable keys
  are as at entry, the writers they wrap too, and the paths to those are stable. And a
  writer the check finds well-typed now is.
-/

import AsmVerif.RiscV.Check.Sound.Core

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame

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
    | sym _ _ _ => simp [AVal.path] at h

/-- A writer the function has, as of a memory `M` of its activation: well-typed at entry;
    its keys at entry nothing the function writes, not protected, among its writers' keys;
    its stable keys aligned, not owned, and as at entry; its field keys aligned, not owned,
    and field keys of the function's writers. -/
def EntryOk (env : Env) (σ : Iface) (E : Ent) (s0 : MachineState) (M : Word → Word)
    (e : AVal × AVal) : Prop :=
  e.1.isPtr = true ∧ e.2.isPtr = true ∧
  env.model.writerOk (e.2.eval E) (e.1.eval E) s0.getMem ∧
  (∀ a, env.model.hit (e.2.eval E) (e.1.eval E) s0.getMem a →
    ¬ Written σ E a ∧ ¬ env.InProt a ∧ StrHit env σ E s0.getMem a) ∧
  (∀ a, env.model.stable (e.2.eval E) (e.1.eval E) s0.getMem a →
    Aligned a ∧ ¬ env.InOwn a ∧ M a = s0.getMem a) ∧
  (∀ a, env.model.fields (e.2.eval E) (e.1.eval E) s0.getMem a →
    Aligned a ∧ ¬ env.InOwn a ∧ FieldKey env σ E s0.getMem a)

/-- A wrapped writer, in terms of the writer wrapping it. -/
def IsSub (env : Env) (ref : Option (AVal × Word)) (e' e : AVal × AVal) : Prop :=
  ∃ s, subEntry env ref e = some (s, e'.1, e'.2)

theorem subEntry_some {env : Env} {ref : Option (AVal × Word)} {e : AVal × AVal} {s : Sub}
    {d' k' : AVal} (h : subEntry env ref e = some (s, d', k')) :
    ∃ K kd, kindConst env ref e.2 = some K ∧ env.model.kinds K = some kd ∧ kd.pure = true ∧
      kd.sub = some s ∧ e.1.path s.dp = some d' ∧ e.1.path s.kp = some k' := by
  unfold subEntry at h
  cases hks : (kindConst env ref e.2).bind env.model.kinds with
  | none => rw [hks] at h; cases h
  | some kd =>
    rw [hks] at h
    simp only at h
    obtain ⟨K, hK, hkd⟩ := Option.bind_eq_some_iff.mp hks
    split at h
    · rename_i hpu
      cases hsub : kd.sub with
      | none => rw [hsub] at h; cases h
      | some s' =>
        rw [hsub] at h
        simp only at h
        cases hd : e.1.path s'.dp with
        | none => rw [hd] at h; cases h
        | some d'' =>
          cases hk : e.1.path s'.kp with
          | none => rw [hd, hk] at h; cases h
          | some k'' =>
            rw [hd, hk] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            exact ⟨K, kd, hK, hkd, hpu, hsub, hd, hk⟩
    · cases h

structure KnOk (env : Env) (σ : Iface) (E : Ent) (s0 : MachineState) (M : Word → Word)
    (ref : Option (AVal × Word)) (kn : Kn) : Prop where
  cells : KnCells E M kn
  roots : KnRoots E kn
  strs : ∀ e ∈ kn.strs, EntryOk env σ E s0 M e
  subs : ∀ q ∈ kn.subs, q.2 ∈ kn.strs ∧ IsSub env ref q.1 q.2

theorem knOk_empty {M : Word → Word} {ref : Option (AVal × Word)} :
    KnOk env σ E s0 M ref {} :=
  ⟨knCells_empty, knRoots_empty, fun _ h => by simp at h, fun _ h => by simp at h⟩

/-- The function's writers, in any memory where their stable keys are as at entry. -/
theorem EntryOk.of_stable (hF : Facts env σ E s0) {M : Word → Word} {e : AVal × AVal}
    (he : e ∈ σ.strs)
    (hst : ∀ a, env.model.stable (e.2.eval E) (e.1.eval E) s0.getMem a → M a = s0.getMem a) :
    EntryOk env σ E s0 M e := by
  obtain ⟨hp1, hp2⟩ := hF.strsPtr e he
  have hpre := hF.strs.1 e he
  refine ⟨hp1, hp2, hpre.1, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
  · exact ⟨(hpre.2.1 a ha).1, (hpre.2.1 a ha).2, e, he, ha⟩
  · exact ⟨(hpre.2.2.1 a ha).1, (hpre.2.2.1 a ha).2, hst a ha⟩
  · exact ⟨(hpre.2.2.2 a ha).1, (hpre.2.2.2 a ha).2, e, he, ha⟩

/-- The function's writers, at any state of the activation. -/
theorem St.entryOk (hF : Facts env σ E s0) {C} {A : AState} {x : MachineState}
    (hx : St env σ C E s0 A x) {e : AVal × AVal} (he : e ∈ σ.strs) :
    EntryOk env σ E s0 x.getMem e :=
  EntryOk.of_stable hF he (hx.strs.1 e he)

/-- What a structural writer wraps, as of `M`: a writer too; its pointer and kind are the
    paths' contents at entry, which are stable keys, and the paths' keys are not its own. -/
theorem sub_entryOk (hF : Facts env σ E s0) {M : Word → Word}
    {e : AVal × AVal} (he : EntryOk env σ E s0 M e) {K : Word} {kd : Kind}
    {s : Sub} (hK' : e.2.eval E = K) (hkd : env.model.kinds K = some kd)
    (hs : kd.sub = some s) {d' k' : AVal}
    (hd : e.1.path s.dp = some d') (hk : e.1.path s.kp = some k') :
    pathKeys M (e.1.eval E) s.dp = pathKeys E.mem (e.1.eval E) s.dp ∧
    pathKeys M (e.1.eval E) s.kp = pathKeys E.mem (e.1.eval E) s.kp ∧
    d'.eval E = derefM s0.getMem (e.1.eval E) s.dp ∧ k'.eval E = derefM s0.getMem (e.1.eval E) s.kp ∧
    derefM M (e.1.eval E) s.dp = derefM s0.getMem (e.1.eval E) s.dp ∧
    derefM M (e.1.eval E) s.kp = derefM s0.getMem (e.1.eval E) s.kp ∧
    s.keys M (e.1.eval E) = s.keys s0.getMem (e.1.eval E) ∧
    EntryOk env σ E s0 M (d', k') ∧ (∀ w, k'.Holds E w → w ∈ s.kinds) ∧
    (∀ a ∈ s.keys s0.getMem (e.1.eval E), Aligned a ∧ ¬ Written σ E a ∧ ¬ env.InOwn a ∧
      M a = s0.getMem a ∧ ¬ env.model.hit (k'.eval E) (d'.eval E) s0.getMem a) := by
  obtain ⟨hp1, hp2, hw, hhit, hst, hfl⟩ := he
  rw [hK'] at hw hhit hst hfl
  have hsub := Model.sub_elim hkd hs hw
  obtain ⟨hw', hkind, hkeys⟩ := hsub
  have hal : ∀ b ∈ s.keys s0.getMem (e.1.eval E), Aligned b := fun b hb => (hkeys b hb).1
  -- The paths' keys are stable, hence as at entry.
  have hkey : ∀ a ∈ s.keys s0.getMem (e.1.eval E), Aligned a ∧ ¬ Written σ E a ∧ ¬ env.InOwn a ∧
      M a = s0.getMem a := by
    intro a ha
    have hst' := hst a (Model.stable_of_keys hkd hs hal ha)
    exact ⟨(hkeys a ha).1, (hhit a (Model.stable_hit (Model.stable_of_keys hkd hs hal ha))).1,
      hst'.2.1, hst'.2.2⟩
  have hdp : ∀ b ∈ pathKeys s0.getMem (e.1.eval E) s.dp, E.mem b = s0.getMem b := fun b _ => hF.emem b
  have hkp : ∀ b ∈ pathKeys s0.getMem (e.1.eval E) s.kp, E.mem b = s0.getMem b := fun b _ => hF.emem b
  have hdpM : ∀ b ∈ pathKeys s0.getMem (e.1.eval E) s.dp, M b = s0.getMem b := fun b hb =>
    (hkey b (by simp [Sub.keys, hb])).2.2.2
  have hkpM : ∀ b ∈ pathKeys s0.getMem (e.1.eval E) s.kp, M b = s0.getMem b := fun b hb =>
    (hkey b (by simp [Sub.keys, hb])).2.2.2
  have hpdE := pathKeys_congr hdp
  have hpkE := pathKeys_congr hkp
  have hpdM := pathKeys_congr hdpM
  have hpkM := pathKeys_congr hkpM
  have hddE := derefM_congr hdp
  have hdkE := derefM_congr hkp
  have hddM := derefM_congr hdpM
  have hdkM := derefM_congr hkpM
  have hd'h : d'.Holds E (derefM s0.getMem (e.1.eval E) s.dp) := by
    rw [← hddE, ← Ent.deref_eq]; exact path_holds (holds_self hp1) hd
  have hk'h : k'.Holds E (derefM s0.getMem (e.1.eval E) s.kp) := by
    rw [← hdkE, ← Ent.deref_eq]; exact path_holds (holds_self hp1) hk
  have hd'p := path_isPtr hp1 hd
  have hk'p := path_isPtr hp1 hk
  have hd'e := holds_eval hd'h hd'p
  have hk'e := holds_eval hk'h hk'p
  have hkeysM : s.keys M (e.1.eval E) = s.keys s0.getMem (e.1.eval E) := by
    simp only [Sub.keys]; rw [hpdM, hpkM]
  refine ⟨by rw [hpdM, hpdE], by rw [hpkM, hpkE], hd'e, hk'e, hddM, hdkM, hkeysM,
    ⟨hd'p, hk'p, ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩, fun w hw => ?_, fun a ha => ?_⟩
  · rw [hd'e, hk'e]; exact hw'
  · rw [hd'e, hk'e] at ha
    exact hhit a (Model.hit_of_sub hkd hs hal ha)
  · rw [hd'e, hk'e] at ha
    exact hst a (Model.stable_of_sub hkd hs hal ha)
  · rw [hd'e, hk'e] at ha
    exact hfl a (.sub hkd hs hal ha)
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
  | sym _ _ _ => simp [AVal.path] at hu

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
    obtain ⟨K, kd, hK, hkd, _, hs, hd, hk⟩ := subEntry_some hse
    simp only
    obtain ⟨hpd, hpk, _, _, _, _, _, he', hkinds, hkeys⟩ :=
      sub_entryOk hF he (kindConst_eval hF hrf he.2.1 hK) hkd hs hd hk
    have hp : e.1.Holds E (e.1.eval E) := holds_self he.1
    have hpdS : pathKeys E.mem (e.1.eval E) s.dp = pathKeys s0.getMem (e.1.eval E) s.dp :=
      pathKeys_congr fun b _ => hF.emem b
    have hpkS : pathKeys E.mem (e.1.eval E) s.kp = pathKeys s0.getMem (e.1.eval E) s.kp :=
      pathKeys_congr fun b _ => hF.emem b
    have hcd : ∀ a ∈ pathKeys E.mem (e.1.eval E) s.dp, M a = E.mem a := fun a ha => by
      rw [hpdS] at ha
      rw [hF.emem]; exact (hkeys a (by simp [Sub.keys, ha])).2.2.2.1
    have hck : ∀ a ∈ pathKeys E.mem (e.1.eval E) s.kp, M a = E.mem a := fun a ha => by
      rw [hpkS] at ha
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

theorem closure_ok_of (hF : Facts env σ E s0) {M : Word → Word} {ref : Option (AVal × Word)}
    (hrf : RefOk E ref) (hent : ∀ e ∈ σ.strs, EntryOk env σ E s0 M e) :
    KnOk env σ E s0 M ref (closure env σ ref) := by
  unfold closure
  have : ∀ (l : List (AVal × AVal)), (∀ e ∈ l, e ∈ σ.strs) → ∀ kn, KnOk env σ E s0 M ref kn →
      KnOk env σ E s0 M ref (l.foldl (addEntry env ref) kn) := by
    intro l
    induction l with
    | nil => intro _ kn hkn; exact hkn
    | cons e l ih =>
      intro hl kn hkn
      simp only [List.foldl_cons]
      exact ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) _
        (addEntry_ok hF hrf hkn (hent e (hl e (List.mem_cons_self ..))))
  exact this σ.strs (fun _ h => h) {} knOk_empty

theorem closure_ok (hF : Facts env σ E s0) {C} {A : AState} {x : MachineState}
    (hx : St env σ C E s0 A x) {ref : Option (AVal × Word)} (hrf : RefOk E ref) :
    KnOk env σ E s0 x.getMem ref (closure env σ ref) :=
  closure_ok_of hF hrf fun _ he => St.entryOk hF hx he

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

/-! ### Well-typed now -/

/-- A field's content, as the state tracks it. -/
theorem fieldAt_holds {C} {A : AState} {x : MachineState} (hx : St env σ C E s0 A x)
    {addr v : AVal} (h : fieldAt A addr = some v) :
    v.isPtr = true → v.Holds E (x.getMem (addr.eval E)) := by
  intro hv
  unfold fieldAt at h
  cases hf : addr.frameOff? with
  | some f =>
    rw [hf] at h
    rw [AVal.frameOff?_some hf]
    simp only [AVal.eval]
    exact hx.holds.2 _ (lookup_mem h)
  | none =>
    rw [hf] at h
    exact (hx.wmem _ (lookup_mem h)).2.2

theorem mapM_some_index {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length ∧
      ∀ (i : Nat) (a : α), l[i]? = some a → ∃ b, l'[i]? = some b ∧ f a = some b
  | [], l', h => by
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun i a ha => by simp at ha⟩
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
        obtain ⟨hlen, ih⟩ := mapM_some_index hl
        refine ⟨by simp [hlen], fun i x hx => ?_⟩
        cases i with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hx; subst hx; exact ⟨b, rfl, hb⟩
        | succ i =>
          simp only [List.getElem?_cons_succ] at hx ⊢
          exact ih i x hx

/-- The invariant instantiated with a writer's pointer and field values, as facts, is the
    invariant of the writer. -/
theorem instInv_sound {C} {A : AState} {x : MachineState} (hx : St env σ C E s0 A x)
    {d : AVal} (hd : d.isPtr = true) {kd : Kind} {vals : List AVal}
    (hvals : writerFields A d kd = some vals)
    (hin : ∀ f ∈ instInv kd d vals, f ∈ A.facts) :
    ∀ f ∈ kd.inv, f.Holds (env.model.atomIn x.getMem) (kd.val (d.eval E) x.getMem) := by
  intro f hf
  obtain ⟨hlen, hidx⟩ := mapM_some_index hvals
  have hfld : ∀ (i : Nat) off, kd.fields[i]? = some off → ∃ v : AVal, vals[i]? = some v ∧
      v.isPtr = true ∧ v.Holds E (x.getMem (d.eval E + off)) := by
    intro i off hoff
    obtain ⟨v, hv, hfv⟩ := hidx i off hoff
    simp only [Option.bind_eq_some_iff] at hfv
    obtain ⟨u, hu, huv⟩ := hfv
    split at huv
    · rename_i hup
      simp only [Option.some.injEq] at huv; subst huv
      refine ⟨u, hv, hup, ?_⟩
      have := fieldAt_holds hx hu hup
      rw [AVal.eval_addK_ptr hd] at this
      exact this
    · cases huv
  have hν : AVal.eval E ∘ (fun j => if j = 0 then d else vals.getD (j - 1) .top) =
      kd.val (d.eval E) x.getMem := by
    funext j
    cases j with
    | zero => rfl
    | succ i =>
      simp only [Function.comp, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, Kind.val]
      cases hoff : kd.fields[i]? with
      | none =>
        have : vals[i]? = none := by
          rw [List.getElem?_eq_none_iff] at hoff ⊢; omega
        simp [List.getD_eq_getElem?_getD, this, AVal.eval]
      | some off =>
        obtain ⟨v, hv, hvp, hvh⟩ := hfld i off hoff
        simp only [List.getD_eq_getElem?_getD, hv, Option.getD_some]
        exact holds_eval hvh hvp
  have := hx.facts _ (hin _ (List.mem_map.mpr ⟨f, hf, rfl⟩))
  rw [Fact.holds_map, hν] at this
  exact this

/-- A frame writer's pointer: a frame address, aligned. -/
theorem frameAddrOk_sound (hF : Facts env σ E s0) {d : AVal} (h : frameAddrOk σ d = true) :
    d.isPtr = true ∧ Aligned (d.eval E) ∧
    ∃ f, d = .lin .x2 f ∧ negOff f % 8 = 0 ∧ 8 ≤ negOff f ∧ negOff f ≤ σ.depth := by
  unfold frameAddrOk at h
  cases hf : d.frameOff? with
  | none => rw [hf] at h; cases h
  | some f =>
    rw [hf] at h
    simp only [slotOk, Bool.and_eq_true, decide_eq_true_eq] at h
    have hd := AVal.frameOff?_some hf
    subst hd
    refine ⟨rfl, ?_, f, rfl, h.1.1, h.1.2, h.2⟩
    simp only [AVal.eval]
    rw [add_frame]; exact aligned_sub hF.al h.1.1

/-- What `fwOk` says of a frame writer. -/
theorem fwOk_mem {A : AState} (h : fwOk env σ A = true) {e : AVal × AVal} (he : e ∈ A.fw) :
    frameAddrOk σ e.1 = true ∧ ∃ K kd, e.2 = .const K ∧ env.model.kinds K = some kd ∧
      kd.pure = false ∧ kd.sub = none := by
  simp only [fwOk, List.all_eq_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h e he
  refine ⟨h1, ?_⟩
  cases hk : kindOf env e.2 with
  | none => rw [hk] at h2; cases h2
  | some kd =>
    rw [hk] at h2
    simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at h2
    cases e2 : e.2 with
    | const K => rw [e2] at hk; exact ⟨K, kd, rfl, hk, h2.1, h2.2⟩
    | _ => rw [e2] at hk; simp [kindOf] at hk

/-- The kinds the check considers include the writer's. -/
theorem writerKinds_mem (hF : Facts env σ E s0) {ref : Option (AVal × Word)} (hrf : RefOk E ref)
    {kn : Kn} (hkr : KnRoots E kn) {k : AVal} (hk : k.isPtr = true) {Ks : List Word}
    (h : writerKinds env σ kn ref k = some Ks) : k.eval E ∈ Ks := by
  unfold writerKinds at h
  split at h
  · rename_i K
    simp only [Option.some.injEq] at h; subst h; simp [AVal.eval]
  · split at h
    · rename_i K hK
      simp only [Option.some.injEq] at h; subst h
      rw [kindConst_eval hF hrf hk hK]; simp
    · exact cands_mem hF hkr (holds_self hk) h

/-- A writer the check finds well-typed now is well-typed in the current memory. -/
theorem writerOkNow_sound (hF : Facts env σ E s0) {C} {A : AState} {x : MachineState}
    (hx : St env σ C E s0 A x) {ref : Option (AVal × Word)} (hrf : RefOk E ref) {kn : Kn}
    (hkn : KnOk env σ E s0 x.getMem ref kn) (hfw : fwOk env σ A = true) :
    ∀ (fuel : Nat) (e : AVal × AVal), (e ∈ kn.strs ∨ e ∈ A.fw) →
      writerOkNow env σ kn ref A fuel e = true →
      e.1.isPtr = true ∧ e.2.isPtr = true ∧ env.model.writerOk (e.2.eval E) (e.1.eval E) x.getMem
  | 0, _, _, h => by simp [writerOkNow] at h
  | fuel + 1, e, hmem, h => by
    simp only [writerOkNow] at h
    cases hks : writerKinds env σ kn ref e.2 with
    | none => rw [hks] at h; cases h
    | some Ks =>
    rw [hks] at h
    simp only [List.all_eq_true] at h
    -- The writer's pointer and kind are known, its pointer aligned.
    have hbase : e.1.isPtr = true ∧ e.2.isPtr = true ∧ Aligned (e.1.eval E) := by
      rcases hmem with hmem | hmem
      · have he := hkn.strs e hmem
        obtain ⟨_, _, hal, _⟩ := Model.writerOk_kind he.2.2.1
        exact ⟨he.1, he.2.1, hal⟩
      · obtain ⟨hfa, K, kd, hK, _, _, _⟩ := fwOk_mem hfw hmem
        obtain ⟨hp, hal, _⟩ := frameAddrOk_sound hF hfa
        exact ⟨hp, by rw [hK]; rfl, hal⟩
    obtain ⟨hp1, hp2, hal⟩ := hbase
    have hKs := writerKinds_mem hF hrf hkn.roots hp2 hks
    have hK := h _ hKs
    cases hkd : env.model.kinds (e.2.eval E) with
    | none => rw [hkd] at hK; cases hK
    | some kd =>
    rw [hkd] at hK
    simp only at hK
    split at hK
    · rename_i hpu
      cases hs : kd.sub with
      | none => exact ⟨hp1, hp2, Model.unit_writerOk hkd hpu hs hal⟩
      | some s =>
        rw [hs] at hK
        simp only at hK
        -- A structural kind: the writer is one of the function's, not built in the frame.
        have hmem' : e ∈ kn.strs := by
          rcases hmem with hmem | hmem
          · exact hmem
          · obtain ⟨_, K, kd', hK', hkd', hnp, _⟩ := fwOk_mem hfw hmem
            rw [hK'] at hkd
            simp only [AVal.eval] at hkd
            rw [hkd'] at hkd; cases hkd
            rw [hpu] at hnp; cases hnp
        have he := hkn.strs e hmem'
        cases hd : e.1.path s.dp with
        | none => rw [hd] at hK; cases hK
        | some d' =>
        cases hk : e.1.path s.kp with
        | none => rw [hd, hk] at hK; cases hK
        | some k' =>
        rw [hd, hk] at hK
        simp only [Bool.and_eq_true, List.contains_iff_mem] at hK
        obtain ⟨hsub, hrec⟩ := hK
        obtain ⟨_, _, hd'e, hk'e, hddM, hdkM, hkeysM, he', hkinds, hkeys⟩ :=
          sub_entryOk hF he rfl hkd hs hd hk
        obtain ⟨hd'p, hk'p, hw'⟩ := writerOkNow_sound hF hx hrf hkn hfw fuel (d', k') (Or.inl hsub) hrec
        rw [hd'e, hk'e] at hw'
        refine ⟨hp1, hp2, Model.sub_intro_pure hkd hpu hs hal ⟨?_, ?_, fun a ha => ?_⟩⟩
        · rw [hddM, hdkM]; exact hw'
        · rw [hdkM]; rw [← hk'e]; exact hkinds _ (holds_self hk'p)
        · rw [hkeysM] at ha
          obtain ⟨hal', _, _, _, hnh⟩ := hkeys a ha
          refine ⟨hal', fun hh => hnh ?_⟩
          rw [hddM, hdkM, ← hd'e, ← hk'e] at hh
          exact Model.hit_congr_stable (fun b hb => (he'.2.2.2.2.1 b hb).2.2) a hh
    · rename_i hnp
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hK
      obtain ⟨hs, hK⟩ := hK
      cases hvals : writerFields A e.1 kd with
      | none => rw [hvals] at hK; cases hK
      | some vals =>
      rw [hvals] at hK
      simp only [List.all_eq_true, List.contains_iff_mem] at hK
      refine ⟨hp1, hp2, .mk hkd hal (instInv_sound hx hp1 hvals hK) ?_ ?_ ?_⟩ <;>
        intro s' hs' <;> rw [hs] at hs' <;> cases hs'

end Kn

end AsmVerif.RiscV.Check
