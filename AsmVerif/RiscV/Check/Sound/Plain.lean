/-
  AsmVerif.RiscV.Check.Sound.Plain

  The checker's soundness, part 3: straight-line instructions. An ALU instruction, a load,
  a store (through the frame, covered by the footprint, at a writer's field, or into a
  writer's buffer) keep the invariant, with the symbols made along the way given their
  values.
-/

import AsmVerif.RiscV.Check.Sound.Kn

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64 AsmVerif.RiscV.Frame

section Plain

variable {env : Env} {σ : Iface} {C : Word → Option Instr} {E : Ent} {s0 : MachineState}

theorem Ent.withSym_self (E : Ent) : E.withSym E.sym = E := by cases E; rfl

/-! ### Loads -/

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
      cases hwm : A.wmem.lookup b with
      | some v =>
        obtain ⟨hp, _, hv⟩ := h.wmem _ (lookup_mem hwm)
        simp only at hp hv
        show v.Holds E (x.getMem addr)
        rw [← holds_eval hb hp]; exact hv
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

/-- What a narrow unsigned load is bounded by. -/
def LoadBoundOk : Instr → Word → Prop
  | .LBU _ _ _, w => w.toNat ≤ 255
  | .LHU _ _ _, w => w.toNat ≤ 65535
  | .LWU _ _ _, w => w.toNat ≤ 2 ^ 32 - 1
  | _, _ => True

theorem loadOf_shape' {s : MachineState} {i : Instr} {rd rs : Reg} {off : BitVec 12} {isD : Bool}
    (h : loadOf i = some (rd, rs, off, isD)) :
    ∃ w, execInstrBr s i = (s.setReg rd w).setPC (s.pc + 4) ∧
      (isD = true → w = s.getMem (s.getReg rs + signExtend12 off)) ∧ LoadBoundOk i w := by
  cases i <;> simp only [loadOf, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl, rfl, rfl⟩ := h; refine ⟨_, rfl, by simp, ?_⟩; simp only [LoadBoundOk]
  case LBU rd rs off =>
    have := (s.getByte (s.getReg rs + signExtend12 off)).isLt
    simp only [BitVec.toNat_setWidth]; omega
  case LHU rd rs off =>
    have := (s.getHalfword (s.getReg rs + signExtend12 off)).isLt
    simp only [BitVec.toNat_setWidth]; omega
  case LWU rd rs off =>
    have := (s.getWord32 (s.getReg rs + signExtend12 off)).isLt
    simp only [BitVec.toNat_setWidth]; omega

theorem loadBound_sound {i : Instr} {w : Word} (hb : LoadBoundOk i w) {E' : Ent} {s : AVal}
    (hs : s.eval E' = w) {M : Nat → List Word → Prop} :
    ∀ f ∈ loadBound i s, f.Holds M (AVal.eval E') := by
  intro f hf
  cases i <;> simp only [loadBound, List.mem_singleton, List.not_mem_nil] at hf <;> subst hf <;>
    simp only [Fact.Holds, LinTerm.eval_var, LinTerm.eval_ofNat, Fact.nat, hs] <;>
    simp only [LoadBoundOk] at hb <;> omega

/-- A load: its value if known, else a fresh symbol. -/
theorem loadStep_sound (hF : Facts env σ E s0) {kn : Kn} {A : AState} {x : MachineState}
    {pc : Word} {i : Instr} {rd rs : Reg} {off : BitVec 12} {isD : Bool}
    (h : St env σ C E s0 A x) (hk : KnCells E x.getMem kn) (hkr : KnRoots E kn)
    (hl : loadOf i = some (rd, rs, off, isD)) :
    ∃ V, St env σ C (E.withSym V) s0 (loadStep env σ kn pc A i rd rs off isD) (execInstrBr x i) := by
  obtain ⟨w, he, hw, hbnd⟩ := loadOf_shape' (s := x) hl
  rw [he]
  unfold loadStep
  simp only
  split
  · refine ⟨E.sym, ?_⟩
    rw [Ent.withSym_self]
    refine (St.setReg h ?_).setPC
    cases isD with
    | false => simp [loadVal, AVal.Holds]
    | true =>
      rw [hw rfl]
      exact loadVal_sound hF h hk hkr (AVal.holds_addK (h.holds.1 rs))
  · refine ⟨_, (St.mkSym hF.symFree h pc.toNat 0 rd w ?_).setPC⟩
    exact loadBound_sound hbnd (by simp [AVal.eval])

/-! ### ALU instructions -/

/-- The operands of an operation are register values or constants. -/
theorem aluOp_args {A : AState} {i : Instr} {rd : Reg} {o : Op} {args : List AVal}
    (h : aluOp A i = some (rd, o, args)) :
    ∀ a ∈ args, (∃ r, a = A.get r) ∨ ∃ c, a = .const c := by
  intro a ha
  cases i <;> simp only [aluOp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals try (split at h; rotate_left; cases h)
  all_goals obtain ⟨rfl, rfl, rfl⟩ := h
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  all_goals first
    | (rcases ha with rfl | rfl <;> first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr ⟨_, rfl⟩)
    | (subst ha; exact Or.inl ⟨_, rfl⟩)

@[simp] theorem AVal.eval_const (c : Word) : (AVal.const c).eval E = c := rfl

/-- What the machine computes for an operation on known operands. -/
theorem aluOp_sound {A : AState} {x : MachineState} {i : Instr} {rd : Reg} {o : Op}
    {args : List AVal} (h : aluOp A i = some (rd, o, args))
    (hregs : ∀ r, (A.get r).Holds E (x.getReg r)) (hargs : ∀ a ∈ args, a.isPtr = true) :
    execInstrBr x i = (x.setReg rd (o.eval (args.map (·.eval E)))).setPC (x.pc + 4) := by
  have hev : ∀ r, (A.get r).isPtr = true → (A.get r).eval E = x.getReg r := fun r hr =>
    holds_eval (hregs r) hr
  cases i <;> simp only [aluOp, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
  all_goals try (split at h; rotate_left; cases h; rename_i c hc)
  all_goals obtain ⟨rfl, rfl, rfl⟩ := h
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq] at hargs
  all_goals simp only [List.map_cons, List.map_nil, Op.eval, AVal.eval_const]
  all_goals first
    | (rw [hev _ hargs.1, hev _ hargs.2]; rfl)
    | (rw [hev _ hargs.1]; rfl)
    | (rw [hev _ hargs]; rfl)
    | skip
  all_goals try (
    have h2 : ∀ r, A.get r = .const c → x.getReg r = c := fun r hr => by
      have := hregs r
      rw [hr] at this
      exact this
    rw [hev _ hargs, ← h2 _ hc]
    rfl)

/-- The value of an operation on constants. -/
theorem aluOp_const {args : List AVal} (h : args.all AVal.isConst = true) (E : Ent) :
    args.map (·.eval E) = args.map AVal.constVal := by
  apply List.map_congr_left
  intro a ha
  have := List.all_eq_true.mp h a ha
  cases a <;> simp [AVal.isConst, AVal.eval, AVal.constVal] at this ⊢

/-- An ALU instruction. -/
theorem aluStep_sound (hF : Facts env σ E s0) {A B : AState} {x : MachineState}
    {pc : Word} {i : Instr} (hpc : x.pc = pc) (h : St env σ C E s0 A x)
    (hs : aluStep pc A i = some B) :
    ∃ V, St env σ C (E.withSym V) s0 B (execInstrBr x i) := by
  unfold aluStep at hs
  cases hr : aluResult pc A i with
  | none => rw [hr] at hs; cases hs
  | some rv =>
  obtain ⟨rd, v⟩ := rv
  rw [hr] at hs
  simp only at hs
  obtain ⟨w, he, hw⟩ := aluResult_sound hpc h.holds hr
  split at hs
  · -- `Frame` knows the value.
    cases hs
    exact ⟨E.sym, by rw [Ent.withSym_self, he]; exact (St.setReg h hw).setPC⟩
  · rename_i hnt
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hnt
    subst hnt
    cases hop : aluOp A i with
    | none =>
      rw [hop] at hs
      cases hs
      exact ⟨E.sym, by rw [Ent.withSym_self, he]; exact (St.setReg h (by trivial)).setPC⟩
    | some roa =>
    obtain ⟨rd', o, args⟩ := roa
    rw [hop] at hs
    simp only at hs
    split at hs
    · -- Constants: the value is computed.
      rename_i hc
      cases hs
      have hargs : ∀ a ∈ args, a.isPtr = true := fun a ha => by
        have := List.all_eq_true.mp hc a ha
        cases a <;> simp [AVal.isConst, AVal.isPtr] at this ⊢
      have he' := aluOp_sound hop h.holds.1 hargs
      -- The destination is `rd` by both accounts.
      have hrd : rd' = rd := by
        cases i <;> simp only [aluResult, aluOp, Option.some.injEq, Prod.mk.injEq,
          reduceCtorEq] at hr hop
        all_goals try (split at hop; rotate_left; cases hop)
        all_goals (obtain ⟨rfl, -⟩ := hr; obtain ⟨rfl, -⟩ := hop; rfl)
      rw [hrd] at he'
      refine ⟨E.sym, ?_⟩
      rw [Ent.withSym_self, he']
      refine (St.setReg h ?_).setPC
      simp only [AVal.Holds]
      rw [aluOp_const hc]
    · -- Unknown operands: a fresh symbol.
      cases hop' : aluOp (A.kill pc.toNat 0) i with
      | none =>
        rw [hop'] at hs
        cases hs
        exact ⟨E.sym, by rw [Ent.withSym_self, he]; exact (St.setReg (h.kill _ _) (by trivial)).setPC⟩
      | some roa' =>
      obtain ⟨rd'', o', args'⟩ := roa'
      rw [hop'] at hs
      simp only at hs
      split at hs
      · rename_i hall
        cases hs
        have hargs : ∀ a ∈ args', a.isPtr = true := fun a ha => List.all_eq_true.mp hall a ha
        have hk := h.kill pc.toNat 0
        have he' := aluOp_sound hop' hk.holds.1 hargs
        have hrd : rd'' = rd := by
          cases i <;> simp only [aluResult, aluOp, Option.some.injEq, Prod.mk.injEq,
            reduceCtorEq] at hr hop'
          all_goals try (split at hop'; rotate_left; cases hop')
          all_goals (obtain ⟨rfl, -⟩ := hr; obtain ⟨rfl, -⟩ := hop'; rfl)
        rw [hrd] at he'
        rw [he']
        -- The operands do not mention the symbol being made.
        have hfree : ∀ a ∈ args', a.mentions pc.toNat 0 = false := by
          intro a ha
          rcases aluOp_args hop' a ha with ⟨r, rfl⟩ | ⟨c, rfl⟩
          · rw [AState.get_kill]; split
            · rfl
            · rename_i hm; simpa using hm
          · rfl
        generalize hw : o'.eval (args'.map (·.eval E)) = w
        refine ⟨_, (St.mkSym hF.symFree h pc.toNat 0 rd w ?_).setPC⟩
        intro f hf
        simp only [List.mem_singleton] at hf
        subst hf
        have hV : ∀ i' j', (i' = pc.toNat ∧ j' = 0) ∨
            (if i' = pc.toNat ∧ j' = 0 then w else E.sym i' j') = E.sym i' j' := fun i' j' => by
          by_cases hc : i' = pc.toNat ∧ j' = 0
          · exact Or.inl hc
          · exact Or.inr (if_neg hc)
        have hm : args'.map (·.eval (E.withSym fun i' j' =>
              if i' = pc.toNat ∧ j' = 0 then w else E.sym i' j')) = args'.map (·.eval E) :=
          List.map_congr_left fun a ha => AVal.eval_agree hV (hfree a ha)
        simp only [Fact.Holds, hm, hw]
        simp [AVal.eval]
      · cases hs
        exact ⟨E.sym, by rw [Ent.withSym_self, he]; exact (St.setReg (h.kill _ _) (by trivial)).setPC⟩

/-! ### Stores -/

theorem AVal.eval_base {v : AVal} (hv : v.isPtr = true) :
    v.eval E = v.base.1.eval E + v.base.2 := by
  cases v <;> simp [AVal.isPtr, AVal.base, AVal.eval] at hv ⊢

theorem AVal.base_eq {v u : AVal} (hv : v.isPtr = true) (hu : u.isPtr = true)
    (hb : v.base.1 = u.base.1) (ho : v.base.2 = u.base.2) : v = u := by
  cases v <;> cases u <;> simp_all [AVal.isPtr, AVal.base]

theorem aligned_alignToDword_eq {a : Word} (h : Aligned a) : alignToDword a = a := by
  unfold Aligned at h
  unfold alignToDword
  bv_decide

/-- A field store: the key is a field key of the function's one writer; everything but
    that doubleword's tracking is as it was. -/
theorem fieldStore_sound (hF : Facts env σ E s0) {A B : AState} {x : MachineState}
    {b : AVal} {w : Width} {v : AVal} {addr : Word} (h : St env σ C E s0 A x)
    (hb : b.Holds E addr) {val : Word} (hv : w = .d → v.Holds E val)
    (hs : fieldStore env σ A b w v = some B) :
    St env σ C E s0 B (x.setMem (w.target addr) val) := by
  unfold fieldStore at hs
  split at hs
  · cases hs
  rename_i hcond
  simp only [not_or, bne_iff_ne, ne_eq, Decidable.not_not, Nat.not_lt] at hcond
  obtain ⟨rfl, hlen⟩ := hcond
  split at hs
  · rename_i hany
    cases hs
    simp only [List.any_eq_true] at hany
    obtain ⟨e, he, hcond⟩ := hany
    cases hkd : kindOf env e.2 with
    | none => rw [hkd] at hcond; cases hcond
    | some kd =>
    rw [hkd] at hcond
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq, List.contains_iff_mem,
      Option.isNone_iff_eq_none] at hcond
    obtain ⟨⟨⟨⟨⟨hnp, hsub⟩, hp1⟩, hbase⟩, hfld⟩, hnst⟩ := hcond
    obtain ⟨K, hK⟩ : ∃ K, e.2 = .const K := by
      cases e2 : e.2 <;> rw [e2] at hkd <;> simp [kindOf] at hkd; exact ⟨_, rfl⟩
    rw [hK] at hkd
    simp only [kindOf] at hkd
    have hent := St.entryOk hF h he
    have hKe : e.2.eval E = K := by rw [hK]; rfl
    obtain ⟨kd', hkd', hal, _⟩ := Model.writerOk_kind hent.2.2.1
    rw [hKe, hkd] at hkd'; cases hkd'
    -- The key.
    have hbp : b.isPtr = true := by
      have := holds_eval hb
      cases b <;> cases hb1 : e.1 <;> simp_all [AVal.isPtr, AVal.base]
    simp only [Width.target]
    have hkey : addr = e.1.eval E + (b.base.2 - e.1.base.2) := by
      rw [← holds_eval hb hbp, AVal.eval_base hbp, AVal.eval_base hp1, hbase]
      bv_omega
    have hoff : (b.base.2 - e.1.base.2) ∈ kd.fields := hfld
    have hfk : addr ∈ kd.fieldKeys (e.1.eval E) := by
      rw [hkey]; exact List.mem_map.mpr ⟨_, hoff, rfl⟩
    have hkal : Aligned addr := by rw [hkey]; exact Model.field_aligned hkd hal hoff
    have hfields : env.model.fields (e.2.eval E) (e.1.eval E) s0.getMem addr := by
      rw [hKe]; exact .own hkd hfk hkal
    obtain ⟨_, hno, hfkey⟩ := hent.2.2.2.2.2 addr hfields
    obtain ⟨hnw, _, hsh⟩ := hent.2.2.2.1 addr (Model.fields_hit hfields)
    have hnh : ¬ env.model.heap addr := fun hh => hno (hF.ok.1 addr hh)
    -- The only writer is `e`.
    have hone : ∀ e' ∈ σ.strs, e' = e := by
      intro e' he'
      cases hl : σ.strs with
      | nil => rw [hl] at he; simp at he
      | cons a l =>
        rw [hl] at hlen he he'
        simp only [List.length_cons] at hlen
        have : l = [] := List.length_eq_zero_iff.mp (by omega)
        subst this
        simp only [List.mem_singleton] at he he'
        rw [he', he]
    -- No stable key is the field.
    have hnstable : ∀ a, env.model.stable (e.2.eval E) (e.1.eval E) s0.getMem a → a ≠ addr := by
      intro a ha heq
      subst heq
      rw [hKe] at ha
      cases ha with
      | own hk ho =>
        rw [hkd] at hk; cases hk
        rcases ho with ⟨ho, _⟩ | ⟨s, hs, _⟩
        · simp only [Kind.stableKeys, List.mem_map] at ho
          obtain ⟨off', hoff', heq⟩ := ho
          rw [hkey] at heq
          have : off' = b.base.2 - e.1.base.2 := by bv_omega
          subst this
          exact absurd hoff' (by simpa using hnst)
        · rw [hsub] at hs; cases hs
      | sub hk hs _ _ =>
        rw [hkd] at hk; cases hk
        rw [hsub] at hs; cases hs
    refine ⟨⟨fun r => by rw [getReg_setMem]; exact h.holds.1 r, fun p hp => ?_⟩, by simp [h.code],
      fun a ha hnw' hno' hns => ?_, fun hh a hha hnp => ?_, Env.Inv_setMem_not_own h.inv hno,
      h.slots, St.facts_setMem h hnh, fun p hp => ?_, ?_⟩
    · have hsl := slot_facts hF (h.slots p hp)
      rw [getMem_setMem, if_neg]
      · exact h.holds.2 p hp
      · intro heq; exact hnw (Or.inl (heq ▸ hsl.2))
    · rw [getMem_setMem, if_neg]
      · exact h.mem a ha hnw' hno' hns
      · rintro rfl; exact hns hsh
    · rw [getMem_setMem, if_neg]
      · exact h.heap hh a hha hnp
      · rintro rfl; exact hnh hha
    · by_cases hvp : v.isPtr = true
      · rw [if_pos hvp] at hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · refine ⟨hbp, by rw [holds_eval hb hbp]; exact hfkey, ?_⟩
          rw [holds_eval hb hbp, getMem_setMem, if_pos rfl]
          exact hv rfl
        · obtain ⟨hpm, hpc⟩ := List.mem_filter.mp hp
          obtain ⟨hp1', hp2', hp3'⟩ := h.wmem p hpm
          refine ⟨hp1', hp2', ?_⟩
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hpc
          rw [getMem_setMem, if_neg]
          · exact hp3'
          · intro heq
            apply hpc.1
            apply AVal.base_eq hp1' hbp hpc.2
            rw [AVal.eval_base hp1', hpc.2, ← holds_eval hb hbp, AVal.eval_base hbp] at heq
            bv_omega
      · rw [if_neg hvp] at hp
        obtain ⟨hpm, hpc⟩ := List.mem_filter.mp hp
        obtain ⟨hp1', hp2', hp3'⟩ := h.wmem p hpm
        refine ⟨hp1', hp2', ?_⟩
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hpc
        rw [getMem_setMem, if_neg]
        · exact hp3'
        · intro heq
          apply hpc.1
          apply AVal.base_eq hp1' hbp hpc.2
          rw [AVal.eval_base hp1', hpc.2, ← holds_eval hb hbp, AVal.eval_base hbp] at heq
          bv_omega
    · refine ⟨fun e' he' a ha => ?_, fun hh k p hw hhit hf hst => ?_⟩
      · rw [hone e' he'] at ha
        rw [getMem_setMem, if_neg (hnstable a ha)]
        exact h.strs.1 e he a ha
      · refine (h.strs.2 hh k p hw hhit hf hst).congr fun a ha => ?_
        rw [getMem_setMem, if_neg]
        rintro rfl
        exact (hhit a ha).2 hsh
  · cases hs

/-- `LinTerm.ofVal` evaluates to the value's. -/
theorem ofVal_eval {v : AVal} (hv : v.isPtr = true) :
    (LinTerm.ofVal v).eval (Fact.nat (AVal.eval E)) = (v.eval E).toNat := by
  cases v <;> simp [AVal.isPtr, LinTerm.ofVal, LinTerm.eval_var, LinTerm.eval_ofNat, Fact.nat,
    AVal.eval] at hv ⊢

/-- A store into a writer's buffer: the key is a payload key; nothing the state tracks
    changes. -/
theorem bufStore_sound (hF : Facts env σ E s0) {kn : Kn} {A : AState} {x : MachineState}
    (hkn : KnOk env σ E s0 x.getMem none kn) (hfw : fwOk env σ A = true) {b : AVal} {w : Width} {e : AVal × AVal} {addr : Word}
    (h : St env σ C E s0 A x) (hbp : b.isPtr = true) (hb : b.Holds E addr)
    (hal : w = .d → Aligned addr) (hs : bufStore env σ kn A b w e = true) (val : Word) :
    St env σ C E s0 A (x.setMem (w.target addr) val) := by
  unfold bufStore at hs
  simp only [Bool.and_eq_true, Bool.or_eq_true, List.contains_iff_mem] at hs
  obtain ⟨⟨hmem, hok⟩, hs⟩ := hs
  obtain ⟨hp1, hp2, hw⟩ := writerOkNow_sound hF h refOk_none hkn hfw 4 e hmem hok
  cases hkd : kindOf env e.2 with
  | none => rw [hkd] at hs; cases hs
  | some kd =>
  rw [hkd] at hs
  obtain ⟨K, hK⟩ : ∃ K, e.2 = .const K := by
    cases e2 : e.2 <;> rw [e2] at hkd <;> simp [kindOf] at hkd; exact ⟨_, rfl⟩
  rw [hK] at hkd
  simp only [kindOf] at hkd
  have hKe : e.2.eval E = K := by rw [hK]; rfl
  simp only at hs
  cases hbuf : kd.buf with
  | none => rw [hbuf] at hs; cases hs
  | some pc' =>
  obtain ⟨pi, ci⟩ := pc'
  cases hvals : writerFields A e.1 kd with
  | none => rw [hbuf, hvals] at hs; cases hs
  | some vals =>
  rw [hbuf, hvals] at hs
  simp only at hs
  cases hptr : vals[pi]? with
  | none => rw [hptr] at hs; cases hs
  | some ptr =>
  cases hcap : vals[ci]? with
  | none => rw [hptr, hcap] at hs; cases hs
  | some cap =>
  rw [hptr, hcap] at hs
  simp only [Bool.and_eq_true, List.contains_iff_mem] at hs
  obtain ⟨hf1, hf2⟩ := hs
  -- The fields' values.
  obtain ⟨hlen, hidx⟩ := mapM_some_index hvals
  have hval : ∀ (i : Nat) (v : AVal), vals[i]? = some v →
      v.isPtr = true ∧ kd.val (e.1.eval E) x.getMem (i + 1) = v.eval E := by
    intro i v hv
    have hi : i < kd.fields.length := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hv).1
    obtain ⟨off, hoff⟩ : ∃ off, kd.fields[i]? = some off := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨v', hv', hfv⟩ := hidx i off hoff
    rw [hv] at hv'; cases hv'
    simp only [Option.bind_eq_some_iff] at hfv
    obtain ⟨u, hu, huv⟩ := hfv
    split at huv
    · rename_i hup
      simp only [Option.some.injEq] at huv; subst huv
      refine ⟨hup, ?_⟩
      simp only [Kind.val, hoff]
      have := fieldAt_holds h hu hup
      rw [AVal.eval_addK_ptr hp1] at this
      exact (holds_eval this hup).symm
    · cases huv
  obtain ⟨hpp, hpv⟩ := hval pi ptr hptr
  obtain ⟨hcp, hcv⟩ := hval ci cap hcap
  have hf1' := h.facts _ hf1
  have hf2' := h.facts _ hf2
  simp only [Fact.Holds, LinTerm.eval_add, LinTerm.eval_ofNat, ofVal_eval hpp, ofVal_eval hcp,
    ofVal_eval hbp] at hf1' hf2'
  rw [holds_eval hb hbp] at hf1' hf2'
  have hw1 : 1 ≤ wbytes w := by cases w <;> simp [wbytes]
  have hbk : env.model.BufKey (e.2.eval E) (e.1.eval E) x.getMem addr := by
    rw [hKe]
    refine ⟨kd, pi, ci, hkd, hbuf, ?_, ?_⟩
    · rw [hpv]; exact hf1'
    · rw [hpv, hcv]; omega
  obtain ⟨hpay, hhit, _⟩ := Model.bufKey_payload hw hbk
  have hkey : w.target addr = alignToDword addr := by
    cases w with
    | d => simp only [Width.target]; rw [aligned_alignToDword_eq (hal rfl)]
    | sub => rfl
  rw [hkey]
  have hheap : env.model.heap (alignToDword addr) := env.model.payload_heap _ _ hpay
  have hown : env.InOwn (alignToDword addr) := hF.ok.1 _ hheap
  have hchg : ∀ a, env.model.heap a → (x.setMem (alignToDword addr) val).getMem a = x.getMem a ∨
      env.model.payload x.getMem a := by
    intro a _
    by_cases heq : a = alignToDword addr
    · subst heq; exact Or.inr hpay
    · left; rw [getMem_setMem, if_neg heq]
  refine ⟨⟨fun r => by rw [getReg_setMem]; exact h.holds.1 r, fun p hp => ?_⟩, by simp [h.code],
    fun a ha hnw hno hns => ?_, fun hh a hha hnp => ?_, ?_, h.slots, fun f hf => ?_,
    St.wmem_setMem hF h (Or.inr hown), ⟨fun e' he' a ha => ?_, fun hh k p hw' hhit hfl hst => ?_⟩⟩
  · have hsl := slot_facts hF (h.slots p hp)
    rw [getMem_setMem, if_neg]
    · exact h.holds.2 p hp
    · intro heq; exact not_own_of_inWin hF.wf hF.top hF.depth hsl.2 (heq ▸ hown)
  · rw [getMem_setMem, if_neg]
    · exact h.mem a ha hnw hno hns
    · rintro rfl; exact hno hown
  · rw [getMem_setMem, if_neg]
    · exact h.heap hh a hha hnp
    · rintro rfl
      apply hnp
      have hk' : ∀ a', env.model.heap a' → x.getMem a' = s0.getMem a' ∨
          env.model.payload s0.getMem a' := fun a' ha' => by
        by_cases hp' : env.model.payload s0.getMem a'
        · exact Or.inr hp'
        · exact Or.inl (h.heap hh a' ha' hp')
      exact (env.model.payload_keep _ _ hk' _).mp hpay
  · have := hF.ok.2 x.getMem (alignToDword addr) val h.inv hpay
    have hm : (x.setMem (alignToDword addr) val).getMem =
        fun b => if b = alignToDword addr then val else x.getMem b := by
      funext b; rw [getMem_setMem]
    rw [hm]; exact this
  · have := h.facts f hf
    cases f with
    | le l r => exact this
    | op o y args => exact this
    | atom i args =>
      simp only [Fact.Holds, Model.atomIn] at this ⊢
      exact env.model.atom_keep i _ _ _ hchg this
  · rw [getMem_setMem, if_neg]
    · exact h.strs.1 e' he' a ha
    · rintro rfl; exact ((hF.strs.1 e' he').2.2.1 _ ha).2 hown
  · have h1 := h.strs.2 hh k p hw' hhit hfl hst
    refine h1.trans (Model.Keeps.of_keep h1.1 (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_))
    · by_cases heq : a = alignToDword addr
      · subst heq; exact Or.inr ⟨hheap, hpay⟩
      · left; rw [getMem_setMem, if_neg heq]
    · intro hh'
      exact hfl a (Model.fields_congr_stable h1.2.2 a ha) (hF.ok.1 a hh')
    · intro hh'
      exact hst a ((Model.stable_congr h1.2.2 a).mp ha) (hF.ok.1 a hh')

/-- A store: through the frame (slots updated), covered by the footprint, at a writer's
    field, or into a writer's buffer. -/
theorem storeStep_sound (hF : Facts env σ E s0) {kn : Kn} {A B : AState} {x : MachineState}
    (hkn : KnOk env σ E s0 x.getMem none kn) (hfw : fwOk env σ A = true)
    {rs1 rs2 : Reg} {off : BitVec 12} {w : Width} {v : Word} {wtr : Option (AVal × AVal)}
    (h : St env σ C E s0 A x) (hv : w = .d → v = x.getReg rs2)
    (hal : w = .d → Aligned (x.getReg rs1 + signExtend12 off))
    (hs : storeStep env σ kn A rs1 rs2 off w wtr = some B) :
    St env σ C E s0 B (x.setMem (w.target (x.getReg rs1 + signExtend12 off)) v) := by
  have hb := AVal.holds_addK (d := signExtend12 off) (h.holds.1 rs1)
  have hregs : ∀ a, ∀ r, (A.get r).Holds E ((x.setMem a v).getReg r) := fun a r => by
    rw [getReg_setMem]; exact h.holds.1 r
  unfold storeStep at hs
  generalize (A.get rs1).addK (signExtend12 off) = b at hb hs
  generalize haddr : x.getReg rs1 + signExtend12 off = addr at hb hal
  cases hk : b.frameOff? with
  | some k =>
    simp only [hk] at hs
    split at hs
    · rename_i hwin
      cases hs
      simp only [winOk, Bool.and_eq_true, decide_eq_true_eq] at hwin
      rw [AVal.frameOff?_some hk] at hb
      simp only [AVal.Holds] at hb
      generalize hkey : w.target addr = key
      rw [hb, add_frame] at hkey
      have hkw : InWin (E .x2) σ.depth key := by
        rw [← hkey]; exact inWin_store hF.depth hwin.1 hwin.2
      have hkeyF : w.target (E .x2 + k) = key := by rw [add_frame]; exact hkey
      have hnh : ¬ env.model.heap key := fun hh =>
        hF.not_heap (env.model.heap_aligned _ hh) (Or.inl hkw) hh
      refine ⟨⟨hregs _, fun p hp => ?_⟩, by simp [h.code], fun a ha hnw hno hns => ?_,
        fun hh a hha hnp => ?_, St.inv_setMem hF h (fun _ => Or.inl hkw), fun p hp => ?_,
        St.facts_setMem h hnh, St.wmem_setMem hF h (Or.inl (Or.inl hkw)), St.strs_setMem hF h (Or.inl hkw)⟩
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
          | _ =>
            simp only [hr2] at hp
            split at hp
            · rcases List.mem_cons.mp hp with rfl | hp
              · rw [← hkeyF, getMem_setMem, if_pos (by simp [Width.target]), hv rfl, ← hr2]
                exact h.holds.1 rs2
              · exact keep p hp
            · exact keep p hp
      · rw [getMem_setMem, if_neg (fun he => hnw (Or.inl (by rw [he]; exact hkw)))]
        exact h.mem a ha hnw hno hns
      · rw [getMem_setMem, if_neg]
        · exact h.heap hh a hha hnp
        · rintro rfl; exact hnh hha
      · have sub : ∀ p ∈ A.slots.filter (fun p => !mayHit w k p.1), p ∈ A.slots :=
          fun p hp => (List.mem_filter.mp hp).1
        cases w with
        | sub => exact h.slots p (sub p hp)
        | d =>
          simp only at hp
          cases hr2 : A.get rs2 with
          | top => simp only [hr2] at hp; exact h.slots p (sub p hp)
          | _ =>
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
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hnt
      split at hs
      · rename_i hcov
        cases hs
        obtain ⟨d, hd, hwd⟩ := List.any_eq_true.mp hcov
        -- The key is hit by the store's bytes, so by `d`.
        have hhit : d.Hits E (w.target addr) := by
          apply within_hits hwd
          unfold Item.Hits
          rw [holds_eval hb hnt]
          simp only [Len.eval]
          exact hits_target w _
        refine St.setMem_written hF h (Or.inr ⟨d, hd, hhit⟩) fun p hp => ?_
        have hsl := slot_facts hF (h.slots p hp)
        have hne : E .x2 + p.1 ≠ w.target addr := by
          intro he
          rw [← he] at hhit
          exact (hF.foot d hd _ hsl.1 hhit).1 hsl.2
        rw [getMem_setMem, if_neg hne]; exact h.holds.2 p hp
      · cases hfs : fieldStore env σ A b w (A.get rs2) with
        | some B' =>
          rw [hfs] at hs
          cases hs
          exact fieldStore_sound hF h hb (fun hw => by rw [hv hw]; exact h.holds.1 rs2) hfs
        | none =>
          rw [hfs] at hs
          cases wtr with
          | none => cases hs
          | some e =>
            simp only at hs
            split at hs
            · rename_i hbs
              cases hs
              exact bufStore_sound hF hkn hfw h hnt hb hal hbs v
            · cases hs

/-! ### A straight-line instruction -/

theorem plainStep_sound (hF : Facts env σ E s0) {kn : Kn} {A B : AState} {x : MachineState}
    (hkn : KnOk env σ E s0 x.getMem none kn)
    (hfw : fwOk env σ A = true) {pc : Word} {i : Instr} {wtr : Option (AVal × AVal)}
    (hpc : x.pc = pc) (h : St env σ C E s0 A x)
    (hmem : ∀ rs1 rs2 off, i = .SD rs1 rs2 off → Aligned (x.getReg rs1 + signExtend12 off))
    (hs : plainStep env σ kn pc A i wtr = some B) :
    ∃ V, St env σ C (E.withSym V) s0 B (execInstrBr x i) ∧ (execInstrBr x i).pc = x.pc + 4 := by
  unfold plainStep at hs
  cases ha : aluStep pc A i with
  | some B' =>
    rw [ha] at hs; cases hs
    obtain ⟨V, hV⟩ := aluStep_sound hF hpc h ha
    refine ⟨V, hV, ?_⟩
    unfold aluStep at ha
    cases hr : aluResult pc A i with
    | none => rw [hr] at ha; cases ha
    | some rv =>
      obtain ⟨w, he, _⟩ := aluResult_sound hpc h.holds hr
      rw [he]; rfl
  | none =>
  rw [ha] at hs
  simp only at hs
  split at hs
  · rename_i rd rs off isD hl
    cases hs
    obtain ⟨V, hV⟩ := loadStep_sound hF h hkn.cells hkn.roots (pc := pc) hl
    refine ⟨V, hV, ?_⟩
    obtain ⟨w, he, _⟩ := loadOf_shape (s := x) hl
    rw [he]; rfl
  · split at hs
    · rename_i rs1 rs2 off w hst
      obtain ⟨v, he, hv⟩ := storeOf_shape (s := x) hst
      rw [he]
      have hal : w = .d → Aligned (x.getReg rs1 + signExtend12 off) := by
        intro hw
        subst hw
        cases i <;> simp [storeOf] at hst
        obtain ⟨rfl, rfl, rfl⟩ := hst
        exact hmem _ _ _ rfl
      have := storeStep_sound hF hkn hfw h hv hal hs
      exact ⟨E.sym, by rw [Ent.withSym_self]; exact this.setPC, rfl⟩
    · split at hs
      · cases hs
        exact ⟨E.sym, by rw [Ent.withSym_self]; simpa [execInstrBr] using h.setPC, rfl⟩
      · cases hs
        exact ⟨E.sym, by rw [Ent.withSym_self]; simpa [execInstrBr] using h.setPC, rfl⟩
      · cases hs

end Plain

end AsmVerif.RiscV.Check
