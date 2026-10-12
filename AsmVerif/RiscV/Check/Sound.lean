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

/-- What the precondition at the activation's entry gives, with `E` its registers. -/
structure Facts (env : Env) (σ : Iface) (E : Reg → Word) (s0 : MachineState) : Prop where
  wf : env.wf = true
  depth : σ.depth ≤ (E .x2).toNat
  top : (E .x2).toNat ≤ env.stackTop
  al : Aligned (E .x2)
  prot : ∀ a, Aligned a → env.InProt a → s0.getMem a = env.init a
  foot : ∀ it ∈ σ.foot, ∀ a, Aligned a → it.Hits E a → ¬ InWin (E .x2) σ.depth a ∧ ¬ env.InProt a
  nz : ∀ v ∈ σ.nz, v.eval E ≠ 0
  vals : ∀ p ∈ σ.vals, E p.1 ∈ p.2

theorem Facts.of_pre {env : Env} {C} {σ : Iface} {s0 : MachineState} (hwf : env.wf = true)
    (h : Pre env C σ s0) : Facts env σ (regsOf s0) s0 :=
  ⟨hwf, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2⟩

/-- The checker's invariant at a state `x` of the activation, with abstract state `A`. -/
structure St (σ : Iface) (C : Word → Option Instr) (E : Reg → Word) (s0 : MachineState)
    (A : AState) (x : MachineState) : Prop where
  holds : A.Holds E x
  code : x.code = C
  mem : ∀ a, Aligned a → ¬ Written σ E a → x.getMem a = s0.getMem a
  slots : ∀ p ∈ A.slots, 8 ≤ negOff p.1 ∧ negOff p.1 ≤ σ.depth ∧ negOff p.1 % 8 = 0

section Facts

variable {env : Env} {σ : Iface} {E : Reg → Word} {s0 : MachineState}

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

/-- The protected regions hold their contents at every state of the activation. -/
theorem St.prot {C} {A : AState} {x : MachineState} (hF : Facts env σ E s0)
    (h : St σ C E s0 A x) {a : Word} (ha : Aligned a) (hp : env.InProt a) :
    x.getMem a = env.init a := by
  rw [h.mem a ha, hF.prot a ha hp]
  rintro (hw | ⟨it, hit, hh⟩)
  · exact not_prot_of_inWin hF.wf hF.top hF.depth hw hp
  · exact (hF.foot it hit a ha hh).2 hp

end Facts

/-! ## Straight-line instructions -/

theorem protKey_inProt {env : Env} {a : Word} (h : env.protKey a = true) :
    Aligned a ∧ env.InProt a := by
  simp only [Env.protKey, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  obtain ⟨hal, ⟨b, l⟩, hR, hb, hl⟩ := h
  refine ⟨(aligned_iff a).mpr hal, ⟨b, l⟩, hR, Or.inl ?_⟩
  simp only
  have := a.isLt; have := b.isLt
  bv_omega

section Plain

variable {env : Env} {σ : Iface} {C : Word → Option Instr} {E : Reg → Word} {s0 : MachineState}

theorem loadVal_sound (hF : Facts env σ E s0) {A : AState} {x : MachineState} {b : AVal}
    {addr : Word} (h : St σ C E s0 A x) (hb : b.Holds E addr) :
    (loadVal env A b true).Holds E (x.getMem addr) := by
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
    · trivial

theorem storeStep_sound (hF : Facts env σ E s0) {A B : AState} {x : MachineState}
    {rs1 rs2 : Reg} {off : BitVec 12} {w : Width} {v : Word}
    (h : St σ C E s0 A x) (hv : w = .d → v = x.getReg rs2)
    (hs : storeStep σ A rs1 rs2 off w = some B) :
    St σ C E s0 B (x.setMem (w.target (x.getReg rs1 + signExtend12 off)) v) := by
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
      refine ⟨⟨hregs _, fun p hp => ?_⟩, by simp [h.code], fun a ha hnw => ?_, fun p hp => ?_⟩
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
      · rw [getMem_setMem, if_neg (fun he => hnw (Or.inl (by rw [he]; exact hkw)))]
        exact h.mem a ha hnw
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
          simp only [this, Len.eval]
          rw [← hkey]; exact hits_target w _
        refine ⟨⟨hregs _, fun p hp => ?_⟩, by simp [h.code], fun a ha hnw => ?_, h.slots⟩
        · have hsl := slot_facts hF (h.slots p hp)
          have hne : E .x2 + p.1 ≠ key := by
            intro he
            rw [← he] at hhit
            exact (hF.foot d hd _ hsl.1 hhit).1 hsl.2
          rw [getMem_setMem, if_neg hne]; exact h.holds.2 p hp
        · have hne : a ≠ key := fun he => hnw (Or.inr ⟨d, hd, he ▸ hhit⟩)
          rw [getMem_setMem, if_neg hne]; exact h.mem a ha hnw
      · cases hs

theorem plainStep_sound (hF : Facts env σ E s0) {A B : AState} {x : MachineState} {pc : Word}
    {i : Instr} (hpc : x.pc = pc) (h : St σ C E s0 A x) (hs : plainStep env σ pc A i = some B) :
    St σ C E s0 B (execInstrBr x i) ∧ (execInstrBr x i).pc = x.pc + 4 := by
  unfold plainStep at hs
  split at hs
  · rename_i rd v hr
    cases hs
    obtain ⟨w, he, hw⟩ := aluResult_sound hpc h.holds hr
    rw [he]
    exact ⟨⟨AState.holds_setPC (AState.holds_set h.holds hw), by simp [h.code],
      fun a ha hnw => by simpa using h.mem a ha hnw, h.slots⟩, rfl⟩
  · split at hs
    · rename_i rd rs off isD hl
      cases hs
      obtain ⟨w, he, hw⟩ := loadOf_shape (s := x) hl
      rw [he]
      refine ⟨⟨AState.holds_setPC (AState.holds_set h.holds ?_), by simp [h.code],
        fun a ha hnw => by simpa using h.mem a ha hnw, h.slots⟩, rfl⟩
      cases isD with
      | false => simp [loadVal, AVal.Holds]
      | true =>
        rw [hw rfl]
        exact loadVal_sound hF h (AVal.holds_addK (h.holds.1 rs))
    · split at hs
      · rename_i rs1 rs2 off w hst
        obtain ⟨v, he, hv⟩ := storeOf_shape (s := x) hst
        rw [he]
        have := storeStep_sound hF h hv hs
        exact ⟨⟨AState.holds_setPC this.holds, by simpa using this.code,
          fun a ha hnw => by simpa using this.mem a ha hnw, this.slots⟩, rfl⟩
      · split at hs
        · cases hs
          exact ⟨⟨AState.holds_setPC h.holds, by simp [execInstrBr, h.code],
            fun a ha hnw => by simpa [execInstrBr] using h.mem a ha hnw, h.slots⟩, rfl⟩
        · cases hs
          exact ⟨⟨AState.holds_setPC h.holds, by simp [execInstrBr, h.code],
            fun a ha hnw => by simpa [execInstrBr] using h.mem a ha hnw, h.slots⟩, rfl⟩
        · cases hs

end Plain


/-! ## Instantiating a callee's interface -/

section Inst

variable {E : Reg → Word} {A : AState} {y : MachineState}

/-- `A` describes the registers of `y`. -/
def RegsHold (E : Reg → Word) (A : AState) (y : MachineState) : Prop :=
  ∀ r, (A.get r).Holds E (y.getReg r)

theorem instVal_eval (h : RegsHold E A y) {v : AVal} (hv : (instVal A v).isPtr = true) :
    (instVal A v).eval E = v.eval (regsOf y) := by
  cases v with
  | lin r k =>
    simp only [instVal] at hv ⊢
    have hr := h r
    cases hA : A.get r with
    | lin r' k' =>
      rw [hA] at hr; simp only [AVal.Holds] at hr
      simp [AVal.addK, AVal.eval, regsOf, hr, BitVec.add_assoc]
    | const c =>
      rw [hA] at hr; simp only [AVal.Holds] at hr
      simp [AVal.addK, AVal.eval, regsOf, hr]
    | top => rw [hA] at hv; simp [AVal.addK, AVal.isPtr] at hv
    | oneOf _ => rw [hA] at hv; simp [AVal.addK, AVal.isPtr] at hv
  | const c => rfl
  | top => simp [instVal, AVal.isPtr] at hv
  | oneOf _ => simp [instVal, AVal.isPtr] at hv

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

theorem instItem_hits (h : RegsHold E A y) {it it' : Item} (hi : instItem A it = some it')
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
    rw [instVal_eval h hnt, instLen_eval h hl]
    exact ha

/-- An entry-relative or constant value, instantiated in a state `A` describes. -/
theorem instVal_holds (h : RegsHold E A y) {v : AVal} (hv : v.isPtr = true) :
    (instVal A v).Holds E (v.eval (regsOf y)) := by
  cases v with
  | lin r k => exact AVal.holds_addK (h r)
  | const c => simp [instVal, AVal.Holds, AVal.eval]
  | top => simp [AVal.isPtr] at hv
  | oneOf _ => simp [AVal.isPtr] at hv

theorem nzOk_sound {σ : Iface} (hnz : ∀ v ∈ σ.nz, v.eval E ≠ 0) (h : RegsHold E A y) {v : AVal}
    (hok : nzOk σ A v = true) : v.eval (regsOf y) ≠ 0 := by
  unfold nzOk at hok
  simp only [Bool.and_eq_true] at hok
  exact nzVal_holds hnz (instVal_holds h hok.1) hok.2

theorem valOk_sound (h : RegsHold E A y) {p : Reg × List Word} (hok : valOk A p = true) :
    y.getReg p.1 ∈ p.2 := by
  unfold valOk at hok
  have hr := h p.1
  split at hok
  · rename_i c hc
    rw [hc] at hr; simp only [AVal.Holds] at hr
    rw [hr]; exact List.contains_iff_mem.mp hok
  · rename_i cs hc
    rw [hc] at hr; simp only [AVal.Holds] at hr
    exact List.contains_iff_mem.mp (List.all_eq_true.mp hok _ hr)
  · cases hok

end Inst



/-! ## Calls, tail calls, returns -/

theorem mapM_some_mem {f : α → Option β} :
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
        · obtain ⟨y, hy, hfy⟩ := mapM_some_mem hl x hx
          exact ⟨y, List.mem_cons_of_mem _ hy, hfy⟩

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

theorem okExit_regs {A : AState} {E : Reg → Word} {x : MachineState} (hx : okExit A = true)
    (h : RegsHold E A x) : x.getReg .x1 = E .x1 ∧ ∀ r ∈ savedRegs, x.getReg r = E r := by
  simp only [okExit, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hx
  refine ⟨?_, fun r hr => ?_⟩
  · have := h .x1; rw [hx.1] at this; simpa [AVal.Holds] using this
  · have := h r; rw [hx.2 r hr] at this; simpa [AVal.Holds] using this

section Call

variable {env : Env} {σ : Iface} {C : Word → Option Instr} {E : Reg → Word} {s0 : MachineState}

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

/-- What a checked call site gives the callee: its precondition. -/
theorem call_pre (hF : Facts env σ E s0) {A A1 : AState} {x y : MachineState} {g : Iface}
    {m : Nat} {its : List Item}
    (hx : St σ C E s0 A x) (hy1 : RegsHold E A1 y)
    (hmem : y.mem = x.mem) (hcode : y.code = C)
    (hok : callOk σ A1 g = some (m, its)) :
    Pre env C g y ∧ y.getReg .x2 = E .x2 - BitVec.ofNat 64 m ∧ m % 8 = 0 ∧
      m + g.depth ≤ σ.depth ∧ g.foot.mapM (instItem A1) = some its ∧
      its.all (itemOk σ m) = true := by
  unfold callOk at hok
  cases hsp : spOff A1 with
  | none => rw [hsp] at hok; cases hok
  | some m' =>
  rw [hsp] at hok
  simp only at hok
  split at hok
  · rename_i hdep
    cases hits : g.foot.mapM (instItem A1) with
    | none => rw [hits] at hok; cases hok
    | some its' =>
    rw [hits] at hok
    simp only at hok
    split at hok
    · rename_i hall
      simp only [Option.some.injEq, Prod.mk.injEq] at hok
      obtain ⟨rfl, rfl⟩ := hok
      simp only [Bool.and_eq_true, List.all_eq_true] at hall
      obtain ⟨⟨hall1, hall2⟩, hall3⟩ := hall
      obtain ⟨hsp1, hm8⟩ := spOff_sound hy1 hsp
      have he := hF.depth
      have hsp' : (y.getReg .x2).toNat = (E .x2).toNat - m' := by
        rw [hsp1]; have := (E .x2).isLt; bv_omega
      have ht := hF.top
      refine ⟨⟨hcode, by omega, by omega, by rw [hsp1]; exact aligned_sub hF.al hm8,
        fun a ha hp => ?_, fun it hit a ha hh => ?_, fun v hv => ?_, fun p hp => ?_⟩,
        hsp1, hm8, hdep, rfl, by simpa [List.all_eq_true] using hall1⟩
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
            have hh' := instItem_hits hy1 hinst (by simp [hb, AVal.isPtr]) hh
            unfold Item.Hits at hh'
            rw [hb, hl] at hh'
            simp only [AVal.eval, Len.eval] at hh'
            rw [add_frame] at hh'
            have := frameItem_keys (Dg := g.depth) hF.depth hF.al hm8 hdep hio.1.1 hio.1.2 ha hh'
            rw [hsp1]
            exact ⟨this.1, not_prot_of_inWin hF.wf hF.top hF.depth this.2⟩
        | none =>
          rw [hfo] at hio
          simp only [Bool.and_eq_true, List.any_eq_true] at hio
          obtain ⟨hnt, d, hd, hwd⟩ := hio
          have hh' := instItem_hits hy1 hinst hnt hh
          have hdh := within_hits hwd hh'
          have hf := hF.foot d hd a ha hdh
          rw [hsp1]
          exact ⟨fun hw => hf.1 (inWin_callee hF.al hm8 hdep ha hw), hf.2⟩
      · exact nzOk_sound hF.nz hy1 (hall2 v hv)
      · exact valOk_sound hy1 (hall3 p hp)
    · cases hok
  · cases hok

/-- What a checked call site gets back: at the return, the invariant with `afterCall`. -/
theorem call_post (hF : Facts env σ E s0) {A : AState} {x y t : MachineState} {g : Iface}
    {m : Nat} {its : List Item} {A1 : AState}
    (hx : St σ C E s0 A x) (hy1 : RegsHold E A1 y) (hycode : y.code = C)
    (hregs : ∀ r, r ≠ .x1 → y.getReg r = x.getReg r)
    (hmem : y.mem = x.mem) (hsp : y.getReg .x2 = E .x2 - BitVec.ofNat 64 m) (hm8 : m % 8 = 0)
    (hdep : m + g.depth ≤ σ.depth) (hits : g.foot.mapM (instItem A1) = some its)
    (hall : its.all (itemOk σ m) = true) (hpost : Post g y t) :
    St σ C E s0 (afterCall A m its) t := by
  obtain ⟨_, _, hsaved, hun, hcode⟩ := hpost
  simp only [List.all_eq_true] at hall
  -- Everything the callee may write, the caller may write.
  have hwr : ∀ a, Aligned a → Written g (regsOf y) a → Written σ E a := by
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
          have hh' := instItem_hits hy1 hinst (by simp [hb, AVal.isPtr]) hh
          unfold Item.Hits at hh'
          rw [hb, hl] at hh'
          simp only [AVal.eval, Len.eval] at hh'
          rw [add_frame] at hh'
          exact Or.inl (frameItem_keys (Dg := g.depth) hF.depth hF.al hm8 hdep hio.1.1 hio.1.2 ha hh').2
      | none =>
        rw [hfo] at hio
        simp only [Bool.and_eq_true, List.any_eq_true] at hio
        obtain ⟨hnt, d, hd, hwd⟩ := hio
        exact Or.inr ⟨d, hd, within_hits hwd (instItem_hits hy1 hinst hnt hh)⟩
  refine ⟨⟨fun r => ?_, fun p hp => ?_⟩, by rw [hcode, hycode], fun a ha hnw => ?_, fun p hp => ?_⟩
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
    have hsl := hx.slots p hp
    have hkey := slot_facts hF hsl
    have hnw : ¬ Written g (regsOf y) (E .x2 + p.1) := by
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
            have hh' := instItem_hits hy1 hinst (by simp [hb, AVal.isPtr]) hh
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
          have := within_hits hwd (instItem_hits hy1 hinst hnt hh)
          exact (hF.foot d hd _ hkey.1 this).1 hkey.2
    rw [hun _ hkey.1 hnw]
    simp only [MachineState.getMem, hmem]
    exact hx.holds.2 p hp
  · by_cases hw : Written g (regsOf y) a
    · exact absurd (hwr a ha hw) hnw
    · rw [hun a ha hw]
      simp only [MachineState.getMem, hmem]
      exact hx.mem a ha hnw
  · simp only [afterCall, List.mem_filter] at hp
    exact hx.slots p hp.1

/-- A tail call: `f` leaves for `g` with its callee-saved registers and `ra` restored. The
    callee's precondition holds, and its postcondition is `f`'s. -/
theorem tail_sound (hF : Facts env σ E s0) {A : AState} {x : MachineState} {g : Iface}
    (hpre0 : s0.code = C) (hE : E = regsOf s0)
    (hx : St σ C E s0 A x) (hok : tailOk σ A g = true) :
    Pre env C g x ∧ ∀ t, Post g x t → Post σ s0 t := by
  unfold tailOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hok
  obtain ⟨⟨⟨hexit, hdep⟩, hret⟩, hfoot⟩ := hok
  obtain ⟨hx1, hsv⟩ := okExit_regs hexit hx.holds.1
  have hx2 : x.getReg .x2 = E .x2 := hsv .x2 (by decide)
  cases hits : g.foot.mapM (instItem A) with
  | none => rw [hits] at hfoot; cases hfoot
  | some its =>
  rw [hits] at hfoot
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    Option.isNone_iff_eq_none] at hfoot
  obtain ⟨⟨hall, hnz⟩, hvals⟩ := hfoot
  have hdD := hF.depth
  -- Each callee item is covered by one of `f`'s.
  have hcov : ∀ it ∈ g.foot, ∀ a, it.Hits (regsOf x) a → ∃ d ∈ σ.foot, d.Hits E a := by
    intro it hit a hh
    obtain ⟨it', hit', hinst⟩ := mapM_some_mem hits it hit
    obtain ⟨⟨_, hnt⟩, d, hd, hwd⟩ := hall it' hit'
    exact ⟨d, hd, within_hits hwd (instItem_hits hx.holds.1 hinst hnt hh)⟩
  have hwin : ∀ a, Aligned a → InWin (E .x2) g.depth a → InWin (E .x2) σ.depth a := by
    intro a ha hw
    have := inWin_callee (e := E .x2) (D := σ.depth) (m := 0) (Dg := g.depth) hF.al (by decide)
      (by omega) ha
    simpa using this (by simpa using hw)
  refine ⟨⟨hx.code, by rw [hx2]; exact Nat.le_trans hdep hdD, by rw [hx2]; exact hF.top,
    by rw [hx2]; exact hF.al, fun a ha hp => St.prot hF hx ha hp, fun it hit a ha hh => ?_, fun v hv => ?_,
    fun p hp => valOk_sound hx.holds.1 (hvals p hp)⟩, fun t ht => ?_⟩
  · obtain ⟨d, hd, hdh⟩ := hcov it hit a hh
    have hf := hF.foot d hd a ha hdh
    rw [hx2]
    exact ⟨fun hw => hf.1 (hwin a ha hw), hf.2⟩
  · exact nzOk_sound hF.nz hx.holds.1 (hnz v hv)
  · obtain ⟨hgr, hpc, hsaved, hun, hcode⟩ := ht
    refine ⟨?_, ?_, fun r hr => ?_, fun a ha hnw => ?_, ?_⟩
    · rcases hret with h | h
      · exact h
      · rw [hgr] at h; cases h
    · rw [hpc, hx1, hE]; rfl
    · rw [hsaved r hr, hsv r hr, hE]; rfl
    · rw [← hE] at hnw
      have hnw' : ¬ Written g (regsOf x) a := by
        rintro (hw | ⟨it, hit, hh⟩)
        · exact hnw (Or.inl (hwin a ha (by rw [← hx2]; exact hw)))
        · obtain ⟨d, hd, hdh⟩ := hcov it hit a hh
          exact hnw (Or.inr ⟨d, hd, hdh⟩)
      rw [hun a ha hnw']
      exact hx.mem a ha hnw
    · rw [hcode, hx.code, hpre0]

/-- A `ret` with every callee-saved register and `ra` restored is `f`'s postcondition. -/
theorem ret_sound {A : AState} {x : MachineState}
    (hpre0 : s0.code = C) (hE : E = regsOf s0) (hr : σ.returns = true)
    (hx : St σ C E s0 A x) (hok : okExit A = true) :
    Post σ s0 (execInstrBr x (.JALR .x0 .x1 0)) := by
  obtain ⟨hx1, hsv⟩ := okExit_regs hok hx.holds.1
  refine ⟨hr, ?_, fun r hr' => ?_, fun a ha hnw => ?_, ?_⟩
  · simp only [execInstrBr, setReg_x0]
    show (x.getReg .x1 + signExtend12 0) &&& ~~~1#64 = _
    rw [hx1, hE]; simp [signExtend12, regsOf]
  · simp only [execInstrBr, setReg_x0, MachineState.getReg_setPC]
    rw [hsv r hr', hE]; rfl
  · rw [← hE] at hnw
    simpa [execInstrBr, setReg_x0] using hx.mem a ha hnw
  · simp [execInstrBr, setReg_x0, hx.code, hpre0]

end Call

/-! ## The activation -/

theorem Ctx.lookup_some {c : Ctx} {pc : Word} {g : Iface} (h : c.lookup pc = some g) :
    g ∈ c.tbl ∧ g.entry = pc := by
  unfold Ctx.lookup at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem plainStep_ecall {env : Env} {σ : Iface} {pc : Word} {A : AState} :
    plainStep env σ pc A .ECALL = none := by
  simp [plainStep, aluResult, loadOf, storeOf]

theorem plainStep_some_plain {env : Env} {σ : Iface} {pc : Word} {A B : AState} {i : Instr}
    (h : plainStep env σ pc A i = some B) : i ≠ .ECALL ∧ i ≠ .EBREAK ∧ ∀ c r, i ≠ .CSRS c r := by
  refine ⟨?_, ?_, fun c r => ?_⟩ <;>
    (rintro rfl; simp [plainStep, aluResult, loadOf, storeOf] at h)

theorem St.le {σ C E s0} {A B : AState} {x : MachineState} (h : St σ C E s0 A x)
    (hle : A.le B = true) : St σ C E s0 B x := by
  refine ⟨AState.holds_of_le hle h.holds, h.code, h.mem, fun p hp => h.slots p ?_⟩
  simp only [AState.le, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hle
  exact hle.2 p hp

theorem St.setPC {σ C E s0} {A : AState} {x : MachineState} {v : Word} (h : St σ C E s0 A x) :
    St σ C E s0 A (x.setPC v) :=
  ⟨AState.holds_setPC h.holds, by simp [h.code], fun a ha hnw => by simpa using h.mem a ha hnw,
    h.slots⟩

theorem St.setReg {σ C E s0} {A : AState} {x : MachineState} {r : Reg} {v : AVal} {w : Word}
    (h : St σ C E s0 A x) (hv : v.Holds E w) : St σ C E s0 (A.set r v) (x.setReg r w) :=
  ⟨AState.holds_set h.holds hv, by simp [h.code], fun a ha hnw => by simpa using h.mem a ha hnw,
    by
      intro p hp
      exact h.slots p (by simpa [AState.set] using hp)⟩

/-! ## Items a syscall writes -/

section SysItems

variable {env : Env} {σ : Iface} {C : Word → Option Instr} {E : Reg → Word} {s0 : MachineState}

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
  {P : Prop} {s0 : MachineState}

/-- The invariant at a state of the activation: at instruction `i` with its annotation. -/
def Ctx.At (c : Ctx) (anno : Array (Option AState)) (C : Word → Option Instr) (s0 : MachineState)
    (x : MachineState) : Prop :=
  ∃ i A, c.f.idx? x.pc = some i ∧ Fn.annoAt anno i = some A ∧ St c.σ C (regsOf s0) s0 A x

/-- The hypotheses of the activation argument. -/
structure ActHyp (c : Ctx) (anno : Array (Option AState)) (C : Word → Option Instr) (n : Nat)
    (P : Prop) (s0 : MachineState) : Prop where
  valid : c.valid anno = true
  code : CodeAt c.f C
  tbl : ∀ g ∈ c.tbl, ∀ m < n, g.HoldsN c.env C m
  code0 : s0.code = C
  facts : Facts c.env c.σ (regsOf s0) s0
  k : ∀ t, Post c.σ s0 t → SafeN n P t

theorem ActHyp.instrOk (h : ActHyp c anno C n P s0) {i : Nat} (hi : i < c.f.prog.length) :
    c.instrOk anno i = true := by
  have := h.valid
  simp only [Ctx.valid, Bool.and_eq_true, List.all_eq_true, List.mem_range] at this
  exact this.2 i hi

/-- A jump to `tgt` from a state with invariant `A`: inside the function (then the target's
    annotation holds), or a tail call (then the callee's interface carries it). -/
theorem jump_sound (h : ActHyp c anno C n P s0) {k : Nat} (hk : k < n)
    (ih : ∀ x, c.At anno C s0 x → SafeN k P x) {A : AState} {z : MachineState} {tgt : Word}
    {es : List Edge} (hj : c.jump A tgt = some es) (hes : ∀ e ∈ es, edgeOk anno e = true)
    (hz : St c.σ C (regsOf s0) s0 A z) (hpc : z.pc = tgt) : SafeN k P z := by
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
        obtain ⟨hpre, hpost⟩ := tail_sound h.facts h.code0 rfl hz htail
        exact h.tbl g hmem k hk P z (by rw [hpc, hent]) hpre
          (fun t ht => SafeN.mono (Nat.le_of_lt hk) (h.k t (hpost t ht)))
      · cases hj

/-- An outlined fragment, run from its `n`-th instruction to its closing `jalr zero, 0(t0)`. -/
theorem frag_sound (h : ActHyp c anno C n P s0) {k : Nat} {fb : Word} :
    ∀ (fp : List (Option Instr)) (m : Nat) {A B : AState} {z : MachineState},
    c.runFrag A fb fp m = some B →
    (∀ j ins, fp[j]? = some (some ins) → C (fb + BitVec.ofNat 64 (4 * (m + j))) = some ins) →
    z.pc = fb + BitVec.ofNat 64 (4 * m) → St c.σ C (regsOf s0) s0 A z →
    (∀ z', St c.σ C (regsOf s0) s0 B z' → z'.pc = z'.getReg .x5 &&& ~~~1#64 → SafeN k P z') →
    SafeN k P z
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
      cases hp : plainStep c.env c.σ (fb + BitVec.ofNat 64 (4 * m)) A i with
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
          obtain ⟨hz', hpc'⟩ := plainStep_sound h.facts hpc hz hp
          refine SafeN.of_step (not_accepted_of_code hfetch he) hs ?_
          refine frag_sound h rest (m + 1) hr (fun j ins hm => ?_) ?_ hz' hk
          · have := hcode (j + 1) ins (by simpa using hm)
            rw [show m + (j + 1) = m + 1 + j by omega] at this
            exact this
          · rw [hpc', hpc, ofNat_four_mul_succ, BitVec.add_assoc]

/-- A call: the callee's interface, then the annotation after the call. -/
theorem call_sound' (h : ActHyp c anno C n P s0) {k : Nat} (hk : k < n)
    (ih : ∀ x, c.At anno C s0 x → SafeN k P x) {A : AState} {x y : MachineState} {pc tgt : Word}
    {es : List Edge} (hcall : c.call pc A tgt = some es) (hes : ∀ e ∈ es, edgeOk anno e = true)
    (hx : St c.σ C (regsOf s0) s0 A x)
    (hy : y = (x.setReg .x1 (pc + 4)).setPC tgt) : SafeN k P y := by
  unfold Ctx.call at hcall
  cases hg : c.lookup tgt with
  | none => rw [hg] at hcall; cases hcall
  | some g =>
  rw [hg] at hcall
  simp only at hcall
  obtain ⟨hmem, hent⟩ := Ctx.lookup_some hg
  cases hok : callOk c.σ (A.set .x1 (.const (pc + 4))) g with
  | none => rw [hok] at hcall; cases hcall
  | some r =>
  obtain ⟨m, its⟩ := r
  rw [hok] at hcall
  simp only at hcall
  have hy1 : RegsHold (regsOf s0) (A.set .x1 (.const (pc + 4))) y := by
    rw [hy]; exact (AState.holds_setPC (AState.holds_set hx.holds (by simp [AVal.Holds]))).1
  have hycode : y.code = C := by rw [hy]; simp [hx.code]
  have hymem : y.mem = x.mem := by rw [hy]; simp [MachineState.setReg, MachineState.setPC]
  obtain ⟨hpre, hsp, hm8, hdep, hits, hall⟩ := call_pre h.facts hx hy1 hymem hycode hok
  refine h.tbl g hmem k hk P y (by rw [hy, hent]; rfl) hpre (fun t ht => ?_)
  have hregs : ∀ r, r ≠ .x1 → y.getReg r = x.getReg r := by
    intro r hr
    rw [hy, MachineState.getReg_setPC, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  have hst := call_post h.facts hx hy1 hycode hregs hymem hsp hm8 hdep hits hall ht
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
theorem act (h : ActHyp c anno C n P s0) : ∀ k ≤ n, ∀ x, c.At anno C s0 x → SafeN k P x := by
  intro k
  induction k with
  | zero => intro _ _ _; exact SafeN.zero
  | succ k ih =>
  intro hkn x ⟨i, A, hi, hA, hx⟩
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
        refine jump_sound h hkn' ih' hstp hok ?_ hpc
        refine ⟨⟨fun r => hB r, fun p hp => ?_⟩, by rw [hcode, hx.code], fun a ha hnw => ?_,
          fun p hp => ?_⟩
        · simp only [List.mem_filter, List.all_eq_true] at hp
          rw [hsl] at hp
          rw [hmem _ (fun it hi => slot_clear_items h.facts (hx.slots p hp.1) (hall it hi)
            (hp.2 it hi))]
          exact hx.holds.2 p hp.1
        · rw [hmem a (fun it hi hh => hnw ((hit it hi).2 a hh))]
          exact hx.mem a ha hnw
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
    · exact jump_sound h hkn' ih' h1 (fun e he' => hok e (List.mem_append_left _ he')) hx.setPC rfl
    · exact jump_sound h hkn' ih' h2 (fun e he' => hok e (List.mem_append_right _ he')) hx.setPC rfl
  · split at hstp
    · -- `jal rd, off`
      rename_i rd off _
      have hex := stepSp1_exec hfetch hne (by simp) (by simp) hst
      subst hex
      split at hstp
      · rename_i h0; subst h0
        simp only [execInstrBr, setReg_x0]
        exact jump_sound h hkn' ih' hstp hok hx.setPC rfl
      · split at hstp
        · rename_i h1; subst h1
          exact call_sound' h hkn' ih' hstp hok hx rfl
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
          · rename_i t ht
            rw [ht] at hrs; simp only [AVal.Holds] at hrs
            exact jump_sound h hkn' ih' hstp hok hx.setPC
              (by show (x.getReg rs + signExtend12 off) &&& ~~~1#64 = _; rw [hrs])
          · rename_i ts ht
            rw [ht] at hrs; simp only [AVal.Holds] at hrs
            obtain ⟨es', h1, hsub⟩ := allEdges_mem hstp hrs
            exact jump_sound h hkn' ih' h1 (fun e he => hok e (hsub e he)) hx.setPC rfl
          · cases hstp
      · split at hstp
        · rename_i h1; subst h1
          have hrs := hx.holds.1 rs
          split at hstp
          · rename_i t ht
            rw [ht] at hrs; simp only [AVal.Holds] at hrs
            exact call_sound' h hkn' ih' hstp hok hx (by simp [execInstrBr, hrs])
          · rename_i ts ht
            rw [ht] at hrs; simp only [AVal.Holds] at hrs
            obtain ⟨es', h1, hsub⟩ := allEdges_mem hstp hrs
            exact call_sound' h hkn' ih' h1 (fun e he => hok e (hsub e he)) hx
              (by simp [execInstrBr])
          · cases hstp
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
      cases hp : plainStep c.env c.σ x.pc A ins with
      | none => rw [hp] at hstp; simp at hstp
      | some B =>
        rw [hp] at hstp
        simp only [Option.bind_some] at hstp
        obtain ⟨he, hb, hcs⟩ := plainStep_some_plain hp
        have hex := stepSp1_exec hfetch he hb hcs hst
        subst hex
        obtain ⟨hy, hpc'⟩ := plainStep_sound h.facts rfl hx hp
        exact jump_sound h hkn' ih' hstp hok hy hpc'

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
  intro P s hpc hpre hk
  have hF := Facts.of_pre hwf hpre
  have hv0 := hv
  simp only [Ctx.valid, Bool.and_eq_true, beq_iff_eq] at hv0
  obtain ⟨⟨hbase, h0⟩, _⟩ := hv0
  cases hA : Fn.annoAt anno 0 with
  | none => rw [hA] at h0; simp at h0
  | some A =>
  rw [hA] at h0
  have hAct : ActHyp c anno C n P s := ⟨hv, hcode, htbl, hpre.1, hF, hk⟩
  refine act hAct n (Nat.le_refl _) s ⟨0, A, ?_, hA, ?_⟩
  · simp [Fn.idx?, hpc, ← hbase, hne]
  · refine ⟨AState.holds_of_le h0 (holds_entryState hF.vals), hpre.1,
      fun _ _ _ => rfl, fun p hp => ?_⟩
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
