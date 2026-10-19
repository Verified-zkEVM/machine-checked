/-
  MachineChecked.RiscV.Check.Sound.Call

  The checker's soundness, part 4: calls, tail calls and returns. A callee's interface,
  instantiated in the caller's state, is its precondition; what it gives back, with the
  call's symbols given their values, is the state after the call.
-/

import MachineChecked.RiscV.Check.Sound.Plain

namespace MachineChecked.RiscV.Check

open RiscvZkvm.Rv64 MachineChecked.RiscV.Frame

/-! ## Instantiating a callee's interface -/

section Inst

variable {E : Ent} {A : AState} {y : MachineState}

/-- `A` describes the registers of `y`. -/
def RegsHold (E : Ent) (A : AState) (y : MachineState) : Prop :=
  ∀ r, (A.get r).Holds E (y.getReg r)

/-- An entry-relative, loaded or constant value, instantiated in a state `A` describes. -/
theorem instVal_holds {σ : Iface} {kn : Kn} (h : RegsHold E A y) (hm : MemOk σ E A y.getMem)
    (hk : KnCells E y.getMem kn) (hw : WmemOk E A y.getMem) {v : AVal} (hv : v.isPtr = true) :
    (instVal σ kn A v).Holds E (v.eval (regsOf y)) := by
  cases v with
  | lin r k => exact AVal.holds_addK (h r)
  | const c => simp [instVal, AVal.Holds, AVal.eval]
  | top => simp [AVal.isPtr] at hv
  | oneOf _ => simp [AVal.isPtr] at hv
  | sym _ _ _ => simp [instVal, AVal.Holds]
  | cell r ks d =>
    simp only [instVal]
    cases hp : instPath σ kn A (A.get r) ks with
    | none => simp [AVal.Holds]
    | some v' =>
      simp only [Option.map_some, Option.getD_some]
      exact AVal.holds_addK (instPath_holds (E' := regsOf y) hm hk hw (h r) hp)

theorem instVal_isPtr {σ : Iface} {kn : Kn} {v : AVal} (hv : (instVal σ kn A v).isPtr = true) :
    v.isPtr = true := by
  cases v <;> first | rfl | simp [instVal, AVal.isPtr] at hv

theorem instVal_eval {σ : Iface} {kn : Kn} (h : RegsHold E A y) (hm : MemOk σ E A y.getMem)
    (hk : KnCells E y.getMem kn) (hw : WmemOk E A y.getMem) {v : AVal}
    (hv : (instVal σ kn A v).isPtr = true) :
    (instVal σ kn A v).eval E = v.eval (regsOf y) :=
  holds_eval (instVal_holds h hm hk hw (instVal_isPtr hv)) hv

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
    | sym _ _ _ => rw [hA] at hl; cases hl
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
    | sym _ _ _ => rw [hA] at hl; cases hl

theorem instItem_hits {σ : Iface} {kn : Kn} (h : RegsHold E A y) (hm : MemOk σ E A y.getMem)
    (hk : KnCells E y.getMem kn) (hw : WmemOk E A y.getMem) {it it' : Item}
    (hi : instItem σ kn A it = some it') (hnt : it'.base.isPtr = true) {a : Word}
    (ha : it.Hits (regsOf y) a) : it'.Hits E a := by
  unfold instItem at hi
  cases hl : instLen A it.len with
  | none => rw [hl] at hi; cases hi
  | some l =>
    rw [hl] at hi
    simp only [Option.map_some, Option.some.injEq] at hi
    subst hi
    unfold Item.Hits at ha ⊢
    simp only at hnt ⊢
    rw [instVal_eval h hm hk hw hnt, instLen_eval h hl]
    exact ha

theorem nzOk_sound {σ : Iface} {kn : Kn} (hnz : ∀ v ∈ σ.nz, v.eval E ≠ 0) (h : RegsHold E A y)
    (hm : MemOk σ E A y.getMem) (hk : KnCells E y.getMem kn) (hw : WmemOk E A y.getMem) {v : AVal}
    (hok : nzOk σ kn A v = true) : v.eval (regsOf y) ≠ 0 := by
  unfold nzOk at hok
  simp only [Bool.and_eq_true] at hok
  exact nzVal_holds hnz (instVal_holds h hm hk hw hok.1) hok.2

/-- A callee's `pre` fact the caller has, instantiated, holds at the call. -/
theorem preOk_sound {σ : Iface} {kn : Kn} {Atom : Nat → List Word → Prop} (h : RegsHold E A y)
    (hm : MemOk σ E A y.getMem) (hk : KnCells E y.getMem kn) (hw : WmemOk E A y.getMem)
    (hf : ∀ f ∈ A.facts, f.Holds Atom (AVal.eval E)) {f : Fact AVal}
    (hok : preOk σ kn A f = true) : f.Holds Atom (AVal.eval (regsOf y)) := by
  simp only [preOk, Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hok
  obtain ⟨⟨_, hptr⟩, hmem⟩ := hok
  have := hf _ hmem
  rw [Fact.holds_map] at this
  rw [Fact.any_map] at hptr
  rw [← Fact.holds_congr Atom (fun v => !(instVal σ kn A v).isPtr)
    (fun v hv => instVal_eval h hm hk hw (by simpa using hv)) hptr]
  exact this

end Inst

theorem valOk_sound {env : Env} {σ : Iface} {E : Ent} {s0 : MachineState} (hF : Facts env σ E s0)
    {kn : Kn} (hk : KnRoots E kn) {A : AState} {y : MachineState} (h : RegsHold E A y)
    {p : Reg × List Word} (hok : valOk env σ kn A p = true) : y.getReg p.1 ∈ p.2 :=
  inCands_sound hF hk (h p.1) hok

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

section Callee

variable (hF : Facts env σ E s0) {kn : Kn} {A1 : AState} {y : MachineState} {g : Iface} {m : Nat}
  {its : List Item} (hy1 : RegsHold E A1 y) (hm1 : MemOk σ E A1 y.getMem)
  (hk : KnCells E y.getMem kn) (hw : WmemOk E A1 y.getMem)
  (hsp : y.getReg .x2 = E .x2 - BitVec.ofNat 64 m) (hm8 : m % 8 = 0)
  (hdep : m + g.depth ≤ σ.depth) (hits : g.foot.mapM (instItem σ kn A1) = some its)
  (hall : ∀ it ∈ its, itemOk σ m it = true)
include hF hy1 hm1 hk hw hsp hm8 hdep hits hall

/-- Everything a checked callee may write, the caller may write. -/
theorem callee_written : ∀ a, Aligned a → Written g (regsOf y) a → Written σ E a := by
  intro a ha hw'
  rcases hw' with hw' | ⟨it, hit, hh⟩
  · left
    rw [show (regsOf y) .x2 = y.getReg .x2 from rfl, hsp] at hw'
    exact inWin_callee hF.al hm8 hdep ha hw'
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
        have hh' := instItem_hits hy1 hm1 hk hw hinst (by simp [hb, AVal.isPtr]) hh
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
      exact Or.inr ⟨d, hd, within_hits hwd (instItem_hits hy1 hm1 hk hw hinst hnt hh)⟩

/-- A caller slot at or above the callee's stack pointer that `slotClear` keeps clear of the
    callee's items is not something the callee may write. -/
theorem slot_callee {f : Word} (hsl : 8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0)
    (hpm : negOff f ≤ m) (hclr : ∀ it ∈ its, slotClear f it = true) :
    ¬ Written g (regsOf y) (E .x2 + f) := by
  have hkey := slot_facts hF hsl
  rintro (hw' | ⟨it, hit, hh⟩)
  · rw [show (regsOf y) .x2 = y.getReg .x2 from rfl, hsp, add_frame] at hw'
    exact not_inWin_callee_slot hF.depth hF.al hm8 hdep hsl.2.2 hpm hw'
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
        have hh' := instItem_hits hy1 hm1 hk hw hinst (by simp [hb, AVal.isPtr]) hh
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
      have := within_hits hwd (instItem_hits hy1 hm1 hk hw hinst hnt hh)
      exact (hF.foot d hd _ hkey.1 this).1 hkey.2

end Callee

/-- A callee's cell premise, discharged by `cellOk`: given that the callee writes only what
    the caller may (`hW`), and leaves the caller's slots that `slotClear` keeps (`hslot`).
    The cell's key is a slot not among `fs`, or one of the caller's cells. -/
theorem cellOk_sound (hF : Facts env σ E s0) {kn : Kn} {fs : List Word} {A : AState}
    {y : MachineState} {g : Iface} {mo : Option Nat} {its : List Item} {c : Cell}
    (hy : RegsHold E A y) (hm : MemOk σ E A y.getMem) (hk : KnCells E y.getMem kn)
    (hkr : KnRoots E kn) (hw : WmemOk E A y.getMem)
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
    AVal.holds_addK (instPath_holds (E' := regsOf y) hm hk hw (hy c.r) hp)
  cases hs : stableAt σ A mo its (v.addK c.k) with
  | none => rw [hs] at hok; cases hok
  | some w =>
  rw [hs] at hok
  simp only at hok
  -- The contents, and the address stays put.
  have hw' : w.Holds E (y.getMem (c.addr (regsOf y))) ∧ Aligned (c.addr (regsOf y)) ∧
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
  refine ⟨⟨hw'.2.1, hw'.2.2.1, hw'.2.2.2.1, fun cs hcs => ?_⟩, hw'.2.2.2.2⟩
  rw [hcs] at hok
  exact inCands_sound hF hkr hw'.1 hok

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

/-! ### Writers built in the frame -/

/-- A writer built in the caller's frame: its kind has fields, which are slots of the
    caller, and no wrapper; it is well-typed in `M`. -/
def FrameW (env : Env) (E : Ent) (M : Word → Word) (A : AState) (e : AVal × AVal) : Prop :=
  (∃ f0, e.1 = .lin .x2 f0) ∧
  (∃ K kd, e.2 = .const K ∧ env.model.kinds K = some kd ∧ kd.pure = false ∧ kd.sub = none ∧
    ∀ off ∈ kd.fields, ∃ f, e.1.addK off = .lin .x2 f ∧ ∃ v, (f, v) ∈ A.slots) ∧
  env.model.writerOk (e.2.eval E) (e.1.eval E) M

theorem FrameW.isPtr {M : Word → Word} {A : AState} {e : AVal × AVal}
    (h : FrameW env E M A e) : e.1.isPtr = true ∧ e.2.isPtr = true := by
  obtain ⟨⟨f0, h1⟩, ⟨K, _, h2, _⟩, _⟩ := h
  rw [h1, h2]; exact ⟨rfl, rfl⟩

theorem FrameW.symFree {M : Word → Word} {A : AState} {e : AVal × AVal}
    (h : FrameW env E M A e) : e.1.symFree = true ∧ e.2.symFree = true := by
  obtain ⟨⟨f0, h1⟩, ⟨K, _, h2, _⟩, _⟩ := h
  rw [h1, h2]; exact ⟨rfl, rfl⟩

/-- A key of a frame writer that is a field: a slot of the caller. -/
def FrameW.Slot (env : Env) (E : Ent) (A : AState) (e : AVal × AVal) (a : Word) : Prop :=
  ∃ kd, env.model.kinds (e.2.eval E) = some kd ∧ ∃ off ∈ kd.fields, ∃ f, e.1.addK off = .lin .x2 f ∧
    a = E .x2 + f ∧ ∃ v, (f, v) ∈ A.slots

theorem FrameW.kinds {M : Word → Word} {A : AState} {e : AVal × AVal} (h : FrameW env E M A e) :
    ∃ kd, env.model.kinds (e.2.eval E) = some kd ∧ kd.pure = false ∧ kd.sub = none ∧
      ∀ off ∈ kd.fields, ∃ f, e.1.addK off = .lin .x2 f ∧ ∃ v, (f, v) ∈ A.slots := by
  obtain ⟨_, ⟨K, kd, h2, hkd, hnp, hs, hfld⟩, _⟩ := h
  exact ⟨kd, by rw [h2]; exact hkd, hnp, hs, hfld⟩

theorem FrameW.field_slot {M : Word → Word} {A : AState} {e : AVal × AVal}
    (h : FrameW env E M A e) {kd : Kind} (hkd : env.model.kinds (e.2.eval E) = some kd)
    {off : Word} (hoff : off ∈ kd.fields) :
    FrameW.Slot env E A e (e.1.eval E + off) := by
  obtain ⟨kd', hkd', _, _, hfld⟩ := h.kinds
  rw [hkd] at hkd'; cases hkd'
  obtain ⟨f, hf, v, hv⟩ := hfld off hoff
  refine ⟨kd, hkd, off, hoff, f, hf, ?_, v, hv⟩
  have := AVal.eval_addK_ptr (E := E) h.isPtr.1 off
  rw [hf] at this
  simp only [AVal.eval] at this
  exact this.symm

theorem FrameW.hit {M : Word → Word} {A : AState} {e : AVal × AVal} (h : FrameW env E M A e)
    {a : Word} (ha : env.model.hit (e.2.eval E) (e.1.eval E) M a) :
    FrameW.Slot env E A e a ∨ env.model.heap a := by
  obtain ⟨kd, hkd, _, hs, _⟩ := h.kinds
  rcases Model.hit_cases hkd ha with ho | ⟨s, hs', _, _⟩
  · rcases ho with ⟨hm, _⟩ | ⟨_, hh⟩ | ⟨s, hs', _⟩
    · obtain ⟨off, hoff, rfl⟩ := List.mem_map.mp hm
      exact Or.inl (h.field_slot hkd hoff)
    · exact Or.inr hh
    · rw [hs] at hs'; cases hs'
  · rw [hs] at hs'; cases hs'

theorem FrameW.stable {M : Word → Word} {A : AState} {e : AVal × AVal} (h : FrameW env E M A e)
    {a : Word} (ha : env.model.stable (e.2.eval E) (e.1.eval E) M a) :
    FrameW.Slot env E A e a := by
  obtain ⟨kd, hkd, _, hs, _⟩ := h.kinds
  rcases Model.stable_cases hkd ha with ho | ⟨s, hs', _, _⟩
  · rcases ho with ⟨hm, _⟩ | ⟨s, hs', _⟩
    · obtain ⟨off, hoff, rfl⟩ := List.mem_map.mp hm
      exact h.field_slot hkd ((env.model.kinds_wf _ _ hkd).2.1 off hoff)
    · rw [hs] at hs'; cases hs'
  · rw [hs] at hs'; cases hs'

theorem FrameW.fields {M : Word → Word} {A : AState} {e : AVal × AVal} (h : FrameW env E M A e)
    {a : Word} (ha : env.model.fields (e.2.eval E) (e.1.eval E) M a) :
    FrameW.Slot env E A e a := by
  obtain ⟨kd, hkd, _, hs, _⟩ := h.kinds
  cases ha with
  | own hk' hm _ =>
    rw [hkd] at hk'; cases hk'
    obtain ⟨off, hoff, rfl⟩ := List.mem_map.mp hm
    exact h.field_slot hkd hoff
  | sub hk' hs' _ _ =>
    rw [hkd] at hk'; cases hk'
    rw [hs] at hs'; cases hs'

/-- A slot of a frame writer, given the caller's slots: aligned, in the window. -/
theorem FrameW.Slot.facts (hF : Facts env σ E s0) {A : AState}
    (hsl : ∀ p ∈ A.slots, 8 ≤ negOff p.1 ∧ negOff p.1 ≤ σ.depth ∧ negOff p.1 % 8 = 0)
    {e : AVal × AVal} {a : Word} (h : FrameW.Slot env E A e a) :
    ∃ f, (8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0) ∧ a = E .x2 + f ∧
      InWin (E .x2) σ.depth a := by
  obtain ⟨_, _, _, _, f, _, rfl, v, hv⟩ := h
  exact ⟨f, hsl _ hv, rfl, (slot_facts hF (hsl _ hv)).2⟩

theorem writerFields_some {A : AState} {d : AVal} {kd : Kind} {vals : List AVal}
    (h : writerFields A d kd = some vals) :
    ∀ off ∈ kd.fields, ∃ v, fieldAt A (d.addK off) = some v ∧ v.isPtr = true := by
  intro off hoff
  obtain ⟨v, _, hv⟩ := mapM_some_mem h off hoff
  simp only [Option.bind_eq_some_iff] at hv
  obtain ⟨u, hu, huv⟩ := hv
  split at huv
  · rename_i hup; simp only [Option.some.injEq] at huv; subst huv; exact ⟨u, hu, hup⟩
  · cases huv

/-- A frame writer the check finds well-typed now is one. -/
theorem writerOkNow_frame (hF : Facts env σ E s0) {A : AState} {x : MachineState}
    (hx : St env σ C E s0 A x) {ref : Option (AVal × Word)} (hrf : RefOk E ref) {kn : Kn}
    (hkn : KnOk env σ E s0 x.getMem ref kn) (hfw : fwOk env σ A = true) {fuel : Nat}
    {e : AVal × AVal} (hmem : e ∈ A.fw) (h : writerOkNow env σ kn ref A (fuel + 1) e = true) :
    FrameW env E x.getMem A e := by
  obtain ⟨_, _, hw⟩ := writerOkNow_sound hF hx hrf hkn hfw (fuel + 1) e (Or.inr hmem) h
  obtain ⟨hfa, K, kd, hK, hkd, hnp, hs⟩ := fwOk_mem hfw hmem
  obtain ⟨_, _, f0, hf0, _⟩ := frameAddrOk_sound hF hfa
  refine ⟨⟨f0, hf0⟩, ⟨K, kd, hK, hkd, hnp, hs, fun off hoff => ?_⟩, hw⟩
  simp only [writerOkNow] at h
  rw [hK] at h
  simp only [writerKinds, List.all_cons, List.all_nil, Bool.and_true, hkd, hnp, Bool.false_eq_true,
    if_false, Bool.and_eq_true] at h
  cases hvals : writerFields A e.1 kd with
  | none => rw [hvals] at h; simp at h
  | some vals =>
    obtain ⟨v, hv, _⟩ := writerFields_some hvals off hoff
    rw [hf0] at hv ⊢
    simp only [AVal.addK, fieldAt, AVal.frameOff?, if_true] at hv ⊢
    exact ⟨f0 + off, rfl, v, lookup_mem hv⟩

/-! ### Passing writers -/

/-- A caller writer `e` stands for a callee writer of kind `K` at `q`: it is that writer, or
    the one the callee's structural writer, built in the caller's frame, wraps. -/
def Stands (env : Env) (E : Ent) (M : Word → Word) (fs : List Word) (e : AVal × AVal)
    (K q : Word) : Prop :=
  (e.1.eval E = q ∧ e.2.eval E = K ∧ env.model.writerOk K q M) ∨
  ∃ kd s, env.model.kinds K = some kd ∧ kd.pure = true ∧ kd.sub = some s ∧
    e.1.eval E = derefM M q s.dp ∧ e.2.eval E = derefM M q s.kp ∧
    (∀ a ∈ s.keys M q, ∃ f ∈ fs, a = E .x2 + f) ∧ env.model.SubOk q M s

/-- A callee writer of a unit kind: nothing stands for it, and it has no keys. -/
def UnitW (env : Env) (K q : Word) : Prop :=
  ∃ kd, env.model.kinds K = some kd ∧ kd.pure = true ∧ kd.sub = none ∧ Aligned q

/-- What passing a callee writer establishes: it is one the caller has, or a structural
    writer built in the caller's frame around one the caller has, or a unit in the frame,
    or a writer the caller built in its frame. -/
theorem passEntry_sound (hF : Facts env σ E s0) {ref : Option (AVal × Word)} (hrf : RefOk E ref)
    {kn : Kn} {A1 : AState} {y : MachineState} (hkn : KnOk env σ E s0 y.getMem ref kn)
    (hx : St env σ C E s0 A1 y) (hfw : fwOk env σ A1 = true)
    {mo : Option Nat} {its : List Item} {d' k' : AVal} {es : List (AVal × AVal)} {fs : List Word}
    (h : passEntry env σ kn ref A1 mo its d' k' = some (es, fs)) :
    d'.isPtr = true ∧ k'.isPtr = true ∧
    ((∃ e ∈ kn.strs, es = [e] ∧ fs = [] ∧ e.1 = d' ∧ e.2.eval E = k'.eval E ∧
        env.model.writerOk (e.2.eval E) (e.1.eval E) y.getMem) ∨
     (∃ e ∈ kn.strs, ∃ m K kd s, mo = some m ∧ es = [e] ∧ k' = .const K ∧
        env.model.kinds K = some kd ∧ kd.pure = true ∧ kd.sub = some s ∧
        e.1.eval E = derefM y.getMem (d'.eval E) s.dp ∧
        e.2.eval E = derefM y.getMem (d'.eval E) s.kp ∧
        (∀ a ∈ s.keys y.getMem (d'.eval E), ∃ f ∈ fs, a = E .x2 + f) ∧
        (∀ f ∈ fs, (8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0) ∧ negOff f ≤ m ∧
          ∀ it ∈ its, slotClear f it = true) ∧
        env.model.SubOk (d'.eval E) y.getMem s) ∨
     (∃ K kd, es = [] ∧ fs = [] ∧ k' = .const K ∧ env.model.kinds K = some kd ∧ kd.pure = true ∧
        kd.sub = none ∧ Aligned (d'.eval E)) ∨
     (∃ m K kd, mo = some m ∧ es = [(d', k')] ∧ k' = .const K ∧ env.model.kinds K = some kd ∧
        kd.pure = false ∧ FrameW env E y.getMem A1 (d', k') ∧
        (∀ off ∈ kd.fields, ∃ f ∈ fs, d'.addK off = .lin .x2 f) ∧
        (∀ f ∈ fs, (8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0) ∧ negOff f ≤ m ∧
          ∀ it ∈ its, slotClear f it = true))) := by
  have hy1 : RegsHold E A1 y := hx.holds.1
  have hm1 : MemOk σ E A1 y.getMem := St.memOk hF hx
  have hsl := hx.slots
  unfold passEntry at h
  cases hfind : kn.strs.find? (matchEntry env ref · (d', k')) with
  | some e =>
    rw [hfind] at h
    simp only at h
    split at h
    · rename_i hwn
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hmem := List.mem_of_find?_eq_some hfind
      have hmatch := List.find?_some hfind
      have hp := hkn.strs e hmem
      obtain ⟨h1, h2, h3⟩ := matchEntry_eval hF hrf ⟨hp.1, hp.2.1⟩ hmatch
      simp only at h1 h2 h3
      obtain ⟨_, _, hw⟩ := writerOkNow_sound hF hx hrf hkn hfw 4 e (Or.inl hmem) hwn
      exact ⟨by rw [h1]; exact hp.1, h2, Or.inl ⟨e, hmem, rfl, rfl, h1.symm, h3.symm, hw⟩⟩
    · cases h
  | none =>
    rw [hfind] at h
    simp only at h
    split at h
    · rename_i K m
      cases hkd : env.model.kinds K with
      | none => rw [hkd] at h; cases h
      | some kd =>
      rw [hkd] at h
      simp only at h
      split at h
      · rename_i hpu
        cases hs : kd.sub with
        | none =>
          rw [hs] at h
          simp only at h
          cases hfo : d'.frameOff? with
          | none => rw [hfo] at h; cases h
          | some f =>
            rw [hfo] at h
            simp only at h
            split at h
            · rename_i hf8
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hd := AVal.frameOff?_some hfo
              refine ⟨by rw [hd]; rfl, rfl,
                Or.inr (Or.inr (Or.inl ⟨K, kd, rfl, rfl, rfl, hkd, hpu, hs, ?_⟩))⟩
              rw [hd]
              simp only [AVal.eval]
              rw [add_frame]
              exact aligned_sub hF.al hf8
            · cases h
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
          simp only [Bool.and_eq_true] at hcands
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
          refine ⟨hd'p, rfl, Or.inr (Or.inl ⟨e, hmem, m, K, kd, s, rfl, rfl, rfl, hkd, hpu, hs,
            by rw [← h1, hd2e], by rw [← h3, hk2e], hkeyf, hfsl, ?_, ?_, fun a ha => ?_⟩)⟩
          · rw [← hd2e, ← hk2e, h1, h3]
            -- well-typed now, in `y`
            obtain ⟨_, _, hw⟩ := writerOkNow_sound hF hx hrf hkn hfw 4 e (Or.inl hmem) hcands.2
            exact hw
          · exact inCands_sound hF hkn.roots hw2 hcands.1
          · obtain ⟨f, hf, rfl⟩ := hkeyf a ha
            have hkey := slot_facts hF (hfsl f hf).1
            refine ⟨hkey.1, fun hh => ?_⟩
            rw [← hd2e, ← hk2e, h1, h3] at hh
            have hh0 := Model.hit_congr_stable (fun b hb => (hp.2.2.2.2.1 b hb).2.2) _ hh
            exact (hp.2.2.2.1 _ hh0).1 (Or.inl hkey.2)
        · cases h
      · -- a frame writer of the caller
        rename_i hnp
        simp only [Bool.not_eq_true] at hnp
        split at h
        · rename_i hok
          simp only [Bool.and_eq_true, List.contains_iff_mem] at hok
          split at h
          · rename_i hfs
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hfr := writerOkNow_frame hF hx hrf hkn hfw hok.1 hok.2
            simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hfs
            refine ⟨hfr.isPtr.1, rfl, Or.inr (Or.inr (Or.inr ⟨m, K, kd, rfl, rfl, rfl, hkd, hnp,
              hfr, fun off hoff => ?_, fun f hf => ?_⟩))⟩
            · obtain ⟨kd', hkd', _, _, hfld⟩ := hfr.kinds
              simp only [AVal.eval] at hkd'
              rw [hkd] at hkd'; cases hkd'
              obtain ⟨f, hf, v, hv⟩ := hfld off hoff
              refine ⟨f, ?_, hf⟩
              simp only [fieldSlots, List.mem_filterMap]
              exact ⟨off, hoff, by rw [hf]; rfl⟩
            · simp only [fieldSlots, List.mem_filterMap] at hf
              obtain ⟨off, hoff, hf'⟩ := hf
              obtain ⟨kd', hkd', _, _, hfld⟩ := hfr.kinds
              simp only [AVal.eval] at hkd'
              rw [hkd] at hkd'; cases hkd'
              obtain ⟨f', hf'', v, hv⟩ := hfld off hoff
              rw [hf''] at hf'
              simp only [AVal.frameOff?, if_true, Option.some.injEq] at hf'
              subst hf'
              exact ⟨hsl _ hv, (hfs f' (by
                simp only [fieldSlots, List.mem_filterMap]
                exact ⟨off, hoff, by rw [hf'']; rfl⟩)).1,
                fun it hit => (hfs f' (by
                  simp only [fieldSlots, List.mem_filterMap]
                  exact ⟨off, hoff, by rw [hf'']; rfl⟩)).2 it hit⟩
          · cases h
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

/-- What `strsOk` establishes: the writers passed are the caller's, or built in its frame;
    every slot a callee writer is built from is in the frame, at or above the callee's
    stack pointer and clear of its items; each callee writer has a caller writer standing
    for it, and each passed writer stands for a callee writer; and the caller's writers are
    recovered. -/
theorem strsOk_sound (hF : Facts env σ E s0) {ref : Option (AVal × Word)} (hrf : RefOk E ref)
    {kn : Kn} {A1 : AState} {y : MachineState} (hkn : KnOk env σ E s0 y.getMem ref kn)
    (hx : St env σ C E s0 A1 y) (hfw : fwOk env σ A1 = true)
    {g : Iface} {mo : Option Nat} {its : List Item} {passed : List (AVal × AVal)} {fs : List Word}
    (hok : strsOk env σ kn ref A1 mo its g = some (passed, fs)) :
    (∀ p ∈ passed, p ∈ kn.strs ∨ ((∃ m, mo = some m) ∧ FrameW env E y.getMem A1 p)) ∧
    (∀ f ∈ fs, ∃ m, mo = some m ∧ (8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0) ∧
      negOff f ≤ m ∧ ∀ it ∈ its, slotClear f it = true) ∧
    (∀ eg ∈ g.strs,
      (∃ e ∈ passed, e ∈ kn.strs ∧
        Stands env E y.getMem fs e (eg.2.eval (regsOf y)) (eg.1.eval (regsOf y))) ∨
      (∃ e ∈ passed, (∃ m, mo = some m) ∧ FrameW env E y.getMem A1 e ∧
        e.1.eval E = eg.1.eval (regsOf y) ∧
        e.2.eval E = eg.2.eval (regsOf y) ∧
        ∀ kd, env.model.kinds (e.2.eval E) = some kd →
          ∀ off ∈ kd.fields, ∃ f ∈ fs, e.1.addK off = .lin .x2 f) ∨
      UnitW env (eg.2.eval (regsOf y)) (eg.1.eval (regsOf y))) ∧
    (∀ e ∈ passed, ∃ eg ∈ g.strs,
      Stands env E y.getMem fs e (eg.2.eval (regsOf y)) (eg.1.eval (regsOf y))) ∧
    (g.strs = [] ∨ ∀ e ∈ σ.strs, recov env ref kn passed 2 e = true) := by
  have hy1 : RegsHold E A1 y := hx.holds.1
  have hm1 : MemOk σ E A1 y.getMem := St.memOk hF hx
  have hw1 : WmemOk E A1 y.getMem := hx.wmemOk
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
        ((∃ e ∈ kn.strs, es = [e] ∧ ∀ fsA, (∀ f ∈ fs', f ∈ fsA) →
          Stands env E y.getMem fsA e (eg.2.eval (regsOf y)) (eg.1.eval (regsOf y))) ∨
         (∃ e, es = [e] ∧ (∃ m, mo = some m) ∧ FrameW env E y.getMem A1 e ∧
           e.1.eval E = eg.1.eval (regsOf y) ∧ e.2.eval E = eg.2.eval (regsOf y) ∧
           ∀ kd, env.model.kinds (e.2.eval E) = some kd →
             ∀ off ∈ kd.fields, ∃ f ∈ fs', e.1.addK off = .lin .x2 f) ∨
         (es = [] ∧ UnitW env (eg.2.eval (regsOf y)) (eg.1.eval (regsOf y)))) := by
      intro eg _ es fs' hpe
      obtain ⟨hd'p, hk'p, hcase⟩ := passEntry_sound hF hrf hkn hx hfw hpe
      have hd'e := instVal_eval hy1 hm1 hkn.cells hw1 hd'p
      have hk'e := instVal_eval hy1 hm1 hkn.cells hw1 hk'p
      rcases hcase with ⟨e, hmem, rfl, rfl, h1, h3, hw⟩ |
        ⟨e, hmem, m, K, kd, s, rfl, rfl, hK, hkd, hpu, hs, h1, h3, hkeys, hfsl, hsub⟩ |
        ⟨K, kd, rfl, rfl, hK, hkd, hpu, hs, hal⟩ |
        ⟨m, K, kd, rfl, rfl, hK, hkd, hnp, hfr, hfld, hfsl⟩
      · exact ⟨fun f hf => by simp at hf, Or.inl ⟨e, hmem, rfl, fun _ _ =>
          Or.inl ⟨by rw [h1, hd'e], by rw [h3, hk'e], by rw [← hd'e, ← hk'e, ← h1, ← h3]; exact hw⟩⟩⟩
      · refine ⟨fun f hf => ⟨m, rfl, hfsl f hf⟩, Or.inl ⟨e, hmem, rfl, fun fsA hfsA =>
          Or.inr ⟨kd, s, ?_, hpu, hs, ?_, ?_, ?_, ?_⟩⟩⟩
        · rw [← hk'e, hK]; exact hkd
        · rw [← hd'e]; exact h1
        · rw [← hd'e]; exact h3
        · rw [← hd'e]; exact fun a ha => let ⟨f, hf, ha⟩ := hkeys a ha; ⟨f, hfsA f hf, ha⟩
        · rw [← hd'e]; exact hsub
      · refine ⟨fun f hf => by simp at hf, Or.inr (Or.inr ⟨rfl, kd, ?_, hpu, hs, ?_⟩)⟩
        · rw [← hk'e, hK]; exact hkd
        · rw [← hd'e]; exact hal
      · refine ⟨fun f hf => ⟨m, rfl, hfsl f hf⟩, Or.inr (Or.inl ⟨_, rfl, ⟨m, rfl⟩, hfr, hd'e, hk'e,
          fun kd' hkd' off hoff => ?_⟩)⟩
        simp only [hK, AVal.eval] at hkd'
        rw [hkd] at hkd'; cases hkd'
        exact hfld off hoff
    have hfsA : ∀ q ∈ ps, ∀ f ∈ q.2, f ∈ (ps.map (·.2)).flatten := fun q hq f hf =>
      List.mem_flatten.mpr ⟨q.2, List.mem_map.mpr ⟨q, hq, rfl⟩, hf⟩
    refine ⟨fun p hp => ?_, fun f hf => ?_, fun eg heg => ?_, fun e he => ?_, ?_⟩
    · obtain ⟨es, hes, hp⟩ := List.mem_flatten.mp hp
      obtain ⟨⟨es', fs'⟩, hin, rfl⟩ := List.mem_map.mp hes
      obtain ⟨eg, heg, hpe⟩ := mapM_some_mem_rev hps _ hin
      obtain ⟨_, hk⟩ := key eg heg _ _ hpe
      rcases hk with ⟨e, hmem, rfl, _⟩ | ⟨e, rfl, hm, hfr, _⟩ | ⟨rfl, _⟩
      · simp only [List.mem_singleton] at hp
        subst hp
        exact Or.inl hmem
      · simp only [List.mem_singleton] at hp
        subst hp
        exact Or.inr ⟨hm, hfr⟩
      · simp at hp
    · obtain ⟨fs', hfs', hf⟩ := List.mem_flatten.mp hf
      obtain ⟨⟨es', fs''⟩, hin, rfl⟩ := List.mem_map.mp hfs'
      obtain ⟨eg, heg, hpe⟩ := mapM_some_mem_rev hps _ hin
      exact (key eg heg _ _ hpe).1 f hf
    · obtain ⟨⟨es, fs'⟩, hin, hpe⟩ := mapM_some_mem hps eg heg
      obtain ⟨_, hk⟩ := key eg heg _ _ hpe
      rcases hk with ⟨e, hmem, rfl, hst⟩ | ⟨e, rfl, hm, hfr, h1, h2, hfld⟩ | ⟨rfl, hu⟩
      · exact Or.inl ⟨e, List.mem_flatten.mpr ⟨[e], List.mem_map.mpr ⟨([e], fs'), hin, rfl⟩, by simp⟩,
          hmem, hst _ (hfsA _ hin)⟩
      · refine Or.inr (Or.inl ⟨e, List.mem_flatten.mpr ⟨[e], List.mem_map.mpr ⟨([e], fs'), hin, rfl⟩,
          by simp⟩, hm, hfr, h1, h2, fun kd hkd off hoff => ?_⟩)
        obtain ⟨f, hf, hfo⟩ := hfld kd hkd off hoff
        exact ⟨f, hfsA _ hin f hf, hfo⟩
      · exact Or.inr (Or.inr hu)
    · obtain ⟨es, hes, hp⟩ := List.mem_flatten.mp he
      obtain ⟨⟨es', fs'⟩, hin, rfl⟩ := List.mem_map.mp hes
      obtain ⟨eg, heg, hpe⟩ := mapM_some_mem_rev hps _ hin
      obtain ⟨_, hk⟩ := key eg heg _ _ hpe
      rcases hk with ⟨e', _, rfl, hst⟩ | ⟨e', rfl, _, hfr, h1, h2, _⟩ | ⟨rfl, _⟩
      · simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨eg, heg, hst _ (hfsA _ hin)⟩
      · simp only [List.mem_singleton] at hp
        subst hp
        exact ⟨eg, heg, Or.inl ⟨h1, h2, by have := hfr.2.2; rw [h1, h2] at this; exact this⟩⟩
      · simp at hp
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
    (∀ a, env.model.stable K q M a → Aligned a ∧ ¬ env.InOwn a) ∧
    (∀ a, env.model.fields K q M a → Aligned a ∧ ¬ env.InOwn a) := by
  obtain ⟨_, _, hw, hhit, hst, hfl⟩ := he
  have hstM : ∀ a, env.model.stable (e.2.eval E) (e.1.eval E) s0.getMem a → M a = s0.getMem a :=
    fun a ha => (hst a ha).2.2
  -- The writer's keys in `M` are keys at entry.
  have hhitM : ∀ a, env.model.hit (e.2.eval E) (e.1.eval E) M a →
      ¬ Written g (regsOf y) a ∧ ¬ env.InProt a := fun a ha =>
    let ha0 := Model.hit_congr_stable hstM a ha
    ⟨fun hwg => (hhit a ha0).1 (hW a (Model.hit_aligned ha) hwg), (hhit a ha0).2.1⟩
  have hstM' : ∀ a, env.model.stable (e.2.eval E) (e.1.eval E) M a → Aligned a ∧ ¬ env.InOwn a :=
    fun a ha => let ha0 := (Model.stable_congr hstM a).mp ha; ⟨(hst a ha0).1, (hst a ha0).2.1⟩
  have hflM : ∀ a, env.model.fields (e.2.eval E) (e.1.eval E) M a → Aligned a ∧ ¬ env.InOwn a :=
    fun a ha => let ha0 := Model.fields_congr_stable hstM a ha; ⟨(hfl a ha0).1, (hfl a ha0).2.1⟩
  rcases h with ⟨rfl, rfl, hwM⟩ | ⟨kd, s, hkd, hpu, hs, hd, hk, hkeys, hsub⟩
  · exact ⟨hwM, hhitM, hstM', hflM⟩
  · rw [hd, hk] at hhitM hstM' hflM
    have hal : ∀ b ∈ s.keys M q, Aligned b := fun b hb => (hsub.2.2 b hb).1
    refine ⟨Model.sub_intro_pure hkd hpu hs (Model.aligned_of_sub hkd hs hal) hsub,
      fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩
    · rcases (Model.hit_struct_pure hkd hpu hs hal a).mp ha with ha | ha
      · obtain ⟨f, hf, rfl⟩ := hkeys a ha
        exact ⟨hslot f hf, not_prot_of_inWin hF.wf hF.top hF.depth (slot_facts hF (hfs f hf)).2⟩
      · exact hhitM a ha
    · rcases (Model.stable_struct_pure hkd hpu hs hal a).mp ha with ha | ha
      · obtain ⟨f, hf, rfl⟩ := hkeys a ha
        exact ⟨(slot_facts hF (hfs f hf)).1,
          not_own_of_inWin hF.wf hF.top hF.depth (slot_facts hF (hfs f hf)).2⟩
      · exact hstM' a ha
    · exact hflM a (Model.fields_struct_pure hkd hpu hs ha)

/-- A frame writer lent: the callee's precondition for it. -/
theorem stands_pre_frame (hF : Facts env σ E s0) {A1 : AState}
    (hsl : ∀ p ∈ A1.slots, 8 ≤ negOff p.1 ∧ negOff p.1 ≤ σ.depth ∧ negOff p.1 % 8 = 0)
    {e : AVal × AVal} (hfr : FrameW env E M A1 e)
    {g : Iface} {y : MachineState} (hW : ∀ a, Aligned a → Written g (regsOf y) a → Written σ E a)
    (hfld : ∀ kd, env.model.kinds (e.2.eval E) = some kd →
      ∀ off ∈ kd.fields, ∃ f ∈ fs, e.1.addK off = .lin .x2 f)
    (hslot : ∀ f ∈ fs, ¬ Written g (regsOf y) (E .x2 + f)) :
    env.model.writerOk (e.2.eval E) (e.1.eval E) M ∧
    (∀ a, env.model.hit (e.2.eval E) (e.1.eval E) M a → ¬ Written g (regsOf y) a ∧ ¬ env.InProt a) ∧
    (∀ a, env.model.stable (e.2.eval E) (e.1.eval E) M a → Aligned a ∧ ¬ env.InOwn a) ∧
    (∀ a, env.model.fields (e.2.eval E) (e.1.eval E) M a → Aligned a ∧ ¬ env.InOwn a) := by
  have hslotF : ∀ a, FrameW.Slot env E A1 e a → Aligned a ∧ ¬ env.InOwn a := by
    intro a ha
    obtain ⟨f, hb, rfl, hw⟩ := ha.facts hF hsl
    exact ⟨(slot_facts hF hb).1, not_own_of_inWin hF.wf hF.top hF.depth hw⟩
  refine ⟨hfr.2.2, fun a ha => ?_, fun a ha => hslotF a (hfr.stable ha),
    fun a ha => hslotF a (hfr.fields ha)⟩
  rcases hfr.hit ha with ⟨kd, hkd, off, hoff, f, hf, rfl, v, hv⟩ | hh
  · obtain ⟨f', hf', hf'e⟩ := hfld kd hkd off hoff
    rw [hf] at hf'e
    simp only [AVal.lin.injEq, true_and] at hf'e
    subst hf'e
    exact ⟨hslot f hf', not_prot_of_inWin hF.wf hF.top hF.depth (slot_facts hF (hsl _ hv)).2⟩
  · have hal := env.model.heap_aligned a hh
    have hno : env.InOwn a := hF.ok.1 a hh
    exact ⟨fun hwg => hF.not_own hal (hW a hal hwg) hno, fun hp => not_own_of_prot hF.wf hp hno⟩

/-- A unit writer: the callee's precondition for it is trivial. -/
theorem stands_pre_unit {K q : Word} (h : UnitW env K q) {g : Iface} {y : MachineState} :
    env.model.writerOk K q M ∧
    (∀ a, env.model.hit K q M a → ¬ Written g (regsOf y) a ∧ ¬ env.InProt a) ∧
    (∀ a, env.model.stable K q M a → Aligned a ∧ ¬ env.InOwn a) ∧
    (∀ a, env.model.fields K q M a → Aligned a ∧ ¬ env.InOwn a) := by
  obtain ⟨kd, hkd, hpu, hs, hal⟩ := h
  exact ⟨Model.unit_writerOk hkd hpu hs hal, fun a ha => (Model.unit_no_hit hkd hpu hs ha).elim,
    fun a ha => (Model.unit_no_hit hkd hpu hs (Model.stable_hit ha)).elim,
    fun a ha => (Model.unit_no_hit hkd hpu hs (Model.fields_hit ha)).elim⟩

/-- A key of a callee's writer: a slot its structural writer is built from (then a stable
    key of that writer), or a key of the caller's writer standing for it. -/
theorem stands_hit {e : AVal × AVal} {K q : Word} (h : Stands env E M fs e K q) {a : Word}
    (ha : env.model.hit K q M a) :
    (env.model.stable K q M a ∧ ∃ f ∈ fs, a = E .x2 + f) ∨
    env.model.hit (e.2.eval E) (e.1.eval E) M a := by
  rcases h with ⟨rfl, rfl, _⟩ | ⟨kd, s, hkd, hpu, hs, hd, hk, hkeys, hsub⟩
  · exact Or.inr ha
  · have hal : ∀ b ∈ s.keys M q, Aligned b := fun b hb => (hsub.2.2 b hb).1
    rcases (Model.hit_struct_pure hkd hpu hs hal a).mp ha with ha | ha
    · exact Or.inl ⟨Model.stable_of_keys hkd hs hal ha, hkeys a ha⟩
    · rw [hd, hk]; exact Or.inr ha

/-- A callee writer kept is the caller's writer standing for it kept. -/
theorem stands_keeps {e : AVal × AVal} {K q : Word} (h : Stands env E M fs e K q)
    {t : Word → Word} (hk : env.model.Keeps K q M t) :
    env.model.Keeps (e.2.eval E) (e.1.eval E) M t := by
  rcases h with ⟨rfl, rfl, _⟩ | ⟨kd, s, hkd, hpu, hs, hd, hk', hkeys, hsub⟩
  · exact hk
  · rw [hd, hk']
    have halM : ∀ b ∈ s.keys M q, Aligned b := fun b hb => (hsub.2.2 b hb).1
    -- The paths' keys are stable: the wrapped writer's pointer and kind are as they were.
    have hpres : ∀ b ∈ s.keys M q, t b = M b := fun b hb =>
      hk.2.2 b (Model.stable_of_keys hkd hs halM hb)
    have hdd : derefM t q s.dp = derefM M q s.dp :=
      derefM_congr fun b hb => hpres b (by simp [Sub.keys, hb])
    have hdk : derefM t q s.kp = derefM M q s.kp :=
      derefM_congr fun b hb => hpres b (by simp [Sub.keys, hb])
    have hsub' := Model.sub_elim hkd hs hk.1
    simp only [Model.SubOk] at hsub'
    rw [hdd, hdk] at hsub'
    have halT : ∀ b ∈ s.keys t q, Aligned b := fun b hb => (hsub'.2.2 b hb).1
    refine ⟨hsub'.1, fun a ha => ?_,
      fun a ha => hk.2.2 a (Model.stable_of_sub hkd hs halM ha)⟩
    have ha' : env.model.hit K q t a :=
      Model.hit_of_sub hkd hs halT (by rw [hdd, hdk]; exact ha)
    rcases (Model.hit_struct_pure hkd hpu hs halM a).mp (hk.2.1 a ha') with hk1 | hk1
    · have hkt : a ∈ s.keys t q := by
        simp only [Sub.keys, List.mem_append] at hk1 ⊢
        rw [pathKeys_congr (fun b hb => hpres b (by simp [Sub.keys, hb])),
          pathKeys_congr (fun b hb => hpres b (by simp [Sub.keys, hb]))]
        exact hk1
      exact absurd ha (hsub'.2.2 a hkt).2
    · exact hk1

end Stands

/-- After a call, a caller writer `recov` accepts is kept from the call on: given back by
    the callee, or wrapping one given back, its paths untouched. -/
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
    obtain ⟨K, kd, hK, hkd, hpu, hs, hd, hk⟩ := subEntry_some hse
    have hK' := kindConst_eval hF hrf he.2.1 hK
    obtain ⟨_, _, hd2e, hk2e, hddM, hdkM, hkeysM, he2, hkinds, hkeys⟩ :=
      sub_entryOk hF he hK' hkd hs hd hk
    have ih := recov_sound hF hrf hkn hgiven hmemg fuel (d2, k2) he2 hrec
    -- Every writer passed is the one `e` wraps.
    have hpassed : ∀ p ∈ passed, p = (d2, k2) := by
      intro p hp
      have := hkn.subs _ (List.contains_iff_mem.mp (hsubs p hp))
      obtain ⟨s', hs'⟩ := this.2
      rw [hse] at hs'
      simp only [Option.some.injEq, Prod.mk.injEq] at hs'
      exact Prod.ext hs'.2.1.symm hs'.2.2.symm
    -- The wrapped writer's keys in `M` are its keys at entry.
    have hst2 : ∀ a, env.model.stable (k2.eval E) (d2.eval E) s0.getMem a → M a = s0.getMem a :=
      fun a ha => (he2.2.2.2.2.1 a ha).2.2
    -- The paths' keys survive the call.
    have hpres : ∀ b ∈ s.keys M (e.1.eval E), t b = M b := by
      intro b hb
      rw [hkeysM] at hb
      have hb' := hkeys b hb
      refine hmemg b hb'.1 hb'.2.1 hb'.2.2.1 fun p hp => ?_
      rw [hpassed p hp]
      exact fun hh => hb'.2.2.2.2 (Model.hit_congr_stable hst2 b hh)
    have hdd : derefM t (e.1.eval E) s.dp = derefM M (e.1.eval E) s.dp :=
      derefM_congr fun b hb => hpres b (by simp [Sub.keys, hb])
    have hdk : derefM t (e.1.eval E) s.kp = derefM M (e.1.eval E) s.kp :=
      derefM_congr fun b hb => hpres b (by simp [Sub.keys, hb])
    have hkeyst : s.keys t (e.1.eval E) = s.keys M (e.1.eval E) := by
      simp only [Sub.keys]
      rw [pathKeys_congr (fun b hb => hpres b (by simp [Sub.keys, hb])),
        pathKeys_congr (fun b hb => hpres b (by simp [Sub.keys, hb]))]
    simp only at ih
    rw [hd2e, hk2e, ← hddM, ← hdkM] at ih
    have halM : ∀ b ∈ s.keys M (e.1.eval E), Aligned b := fun b hb =>
      (hkeys b (hkeysM ▸ hb)).1
    have halT : ∀ b ∈ s.keys t (e.1.eval E), Aligned b := fun b hb =>
      halM b (by rw [← hkeyst]; exact hb)
    obtain ⟨_, _, halp, _⟩ := Model.writerOk_kind he.2.2.1
    rw [hK']
    refine ⟨Model.sub_intro_pure hkd hpu hs halp ⟨?_, ?_, fun a ha => ?_⟩, fun a ha => ?_,
      fun a ha => ?_⟩
    · rw [hdd, hdk]; exact ih.1
    · rw [hdk, hdkM, ← hk2e]; exact hkinds _ (holds_self he2.2.1)
    · rw [hkeyst] at ha
      rw [hdd, hdk]
      refine ⟨halM a ha, fun hh => ?_⟩
      have hh' := ih.2.1 a hh
      rw [hddM, hdkM, ← hd2e, ← hk2e] at hh'
      rw [hkeysM] at ha
      exact (hkeys a ha).2.2.2.2 (Model.hit_congr_stable hst2 a hh')
    · rcases (Model.hit_struct_pure hkd hpu hs halT a).mp ha with ha | ha
      · rw [hkeyst] at ha
        exact Model.hit_of_keys hkd hs halM ha
      · rw [hdd, hdk] at ha
        exact Model.hit_of_sub hkd hs halM (ih.2.1 a ha)
    · rcases (Model.stable_struct_pure hkd hpu hs halM a).mp ha with ha | ha
      · exact hpres a ha
      · exact ih.2.2 a ha

/-- What `callOk` checks, unfolded. -/
theorem callOk_some {A1 : AState} {g : Iface} {ref : Option (AVal × Word)} {co : CallOut}
    (hok : callOk env σ A1 g ref = some co) :
    spOff A1 = some co.m ∧ co.m + g.depth ≤ σ.depth ∧ (g.heap = true → σ.heap = true) ∧
    g.foot.mapM (instItem σ (closure env σ ref) A1) = some co.its ∧
    ∃ fs, strsOk env σ (closure env σ ref) ref A1 (some co.m) co.its g = some (co.lent, fs) ∧
      co.its.all (itemOk σ co.m) = true ∧ g.nz.all (nzOk σ (closure env σ ref) A1) = true ∧
      g.vals.all (valOk env σ (closure env σ ref) A1) = true ∧
      g.cells.all (cellOk env σ (closure env σ ref) fs A1 (some co.m) co.its) = true ∧
      g.pre.all (preOk σ (closure env σ ref) A1) = true := by
  unfold callOk at hok
  simp only at hok
  cases hsp : spOff A1 with
  | none => rw [hsp] at hok; cases hok
  | some m' =>
  rw [hsp] at hok
  simp only at hok
  split at hok
  · rename_i hdep
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true'] at hdep
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
      simp only [Option.some.injEq] at hok
      subst hok
      simp only [Bool.and_eq_true] at hall
      refine ⟨rfl, hdep.1, fun hg => ?_, rfl, fs, hso, hall.1.1.1.1, hall.1.1.1.2, hall.1.1.2,
        hall.1.2, hall.2⟩
      rcases hdep.2 with h | h
      · rw [hg] at h; cases h
      · exact h
    · cases hok
  · cases hok

/-- The writers' keys at a call, seen from the caller: a slot a callee writer is built
    from, or a key of a caller writer passed, or of a frame writer passed. -/
theorem strHit_call {M : Word → Word} {fs : List Word} {passed : List (AVal × AVal)} {kn : Kn}
    {A1 : AState} {g : Iface} {y : MachineState} {mo : Option Nat}
    (hst : ∀ eg ∈ g.strs,
      (∃ e ∈ passed, e ∈ kn.strs ∧
        Stands env E M fs e (eg.2.eval (regsOf y)) (eg.1.eval (regsOf y))) ∨
      (∃ e ∈ passed, (∃ m, mo = some m) ∧ FrameW env E M A1 e ∧ e.1.eval E = eg.1.eval (regsOf y) ∧
        e.2.eval E = eg.2.eval (regsOf y) ∧
        ∀ kd, env.model.kinds (e.2.eval E) = some kd →
          ∀ off ∈ kd.fields, ∃ f ∈ fs, e.1.addK off = .lin .x2 f) ∨
      UnitW env (eg.2.eval (regsOf y)) (eg.1.eval (regsOf y)))
    {a : Word} (h : StrHit env g (regsOf y) M a) :
    (∃ eg ∈ g.strs, env.model.stable (eg.2.eval (regsOf y)) (eg.1.eval (regsOf y)) M a ∧
      ∃ f ∈ fs, a = E .x2 + f) ∨
    (∃ e ∈ passed, e ∈ kn.strs ∧ env.model.hit (e.2.eval E) (e.1.eval E) M a) ∨
    (∃ e ∈ passed, (∃ m, mo = some m) ∧ FrameW env E M A1 e ∧
      (∀ kd, env.model.kinds (e.2.eval E) = some kd →
        ∀ off ∈ kd.fields, ∃ f ∈ fs, e.1.addK off = .lin .x2 f) ∧
      env.model.hit (e.2.eval E) (e.1.eval E) M a) := by
  obtain ⟨eg, heg, hh⟩ := h
  rcases hst eg heg with ⟨e, he, hmem, hs⟩ | ⟨e, he, hm, hfr, h1, h2, hfld⟩ | ⟨kd, hkd, hpu, hsn, _⟩
  · rcases stands_hit hs hh with ⟨h1, h2⟩ | h1
    · exact Or.inl ⟨eg, heg, h1, h2⟩
    · exact Or.inr (Or.inl ⟨e, he, hmem, h1⟩)
  · rw [← h1, ← h2] at hh
    exact Or.inr (Or.inr ⟨e, he, hm, hfr, hfld, hh⟩)
  · exact (Model.unit_no_hit hkd hpu hsn hh).elim

/-- What a checked call site gives the callee: its precondition. `A1` describes the
    callee's entry state `y`. -/
theorem call_pre (hF : Facts env σ E s0) {ref : Option (AVal × Word)} (hrf : RefOk E ref)
    {A1 : AState} {y : MachineState} {g : Iface} {co : CallOut}
    (hx1 : St env σ C E s0 A1 y) (hfw : fwOk env σ A1 = true)
    (hok : callOk env σ A1 g ref = some co) : Pre env C g y := by
  have hy1 : RegsHold E A1 y := hx1.holds.1
  have hm1 : MemOk σ E A1 y.getMem := St.memOk hF hx1
  have hw1 : WmemOk E A1 y.getMem := hx1.wmemOk
  have hkn : KnOk env σ E s0 y.getMem ref (closure env σ ref) := closure_ok hF hx1 hrf
  obtain ⟨hsp, hdep, _, hits, fs, hso, hall1, hall2, hall3, hall4, hall5⟩ := callOk_some hok
  simp only [List.all_eq_true] at hall1 hall2 hall3 hall4 hall5
  obtain ⟨hsp1, hm8⟩ := spOff_sound hy1 hsp
  have he := hF.depth
  have hsp' : (y.getReg .x2).toNat = (E .x2).toNat - co.m := by
    rw [hsp1]; have := (E .x2).isLt; bv_omega
  have ht := hF.top
  have hW := callee_written hF hy1 hm1 hkn.cells hw1 hsp1 hm8 hdep hits hall1
  have hsl := hx1.slots
  obtain ⟨hpassed, hfs, hstands, _, _⟩ := strsOk_sound hF hrf hkn hx1 hfw hso
  have hfs' : ∀ f ∈ fs, 8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0 := fun f hf =>
    let ⟨_, _, h, _⟩ := hfs f hf; h
  have hslot : ∀ f ∈ fs, ¬ Written g (regsOf y) (E .x2 + f) := by
    intro f hf
    obtain ⟨m', hm', hsf, hpm, hclr⟩ := hfs f hf
    cases hm'
    exact slot_callee hF hy1 hm1 hkn.cells hw1 hsp1 hm8 hdep hits hall1 hsf hpm hclr
  have hcellOk := fun c hc => cellOk_sound hF hy1 hm1 hkn.cells hkn.roots hw1 hsl hW
    (fun m0 f hm0 hsl' hpm hclr => by
      cases hm0
      exact slot_callee hF hy1 hm1 hkn.cells hw1 hsp1 hm8 hdep hits hall1 hsl' hpm hclr)
    (hall4 c hc)
  refine ⟨hx1.code, by omega, by omega, by rw [hsp1]; exact aligned_sub hF.al hm8,
    fun a ha hp => St.prot hF hx1 ha hp, fun it hit a ha hh => ?_, fun v hv => ?_, fun p hp => ?_,
    fun c hc => (hcellOk c hc).1, hx1.inv, ?_,
    fun f hf => preOk_sound hy1 hm1 hkn.cells hw1 hx1.facts (hall5 f hf)⟩
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
        have hh' := instItem_hits hy1 hm1 hkn.cells hw1 hinst (by simp [hb, AVal.isPtr]) hh
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
      have hh' := instItem_hits hy1 hm1 hkn.cells hw1 hinst hnt hh
      have hdh := within_hits hwd hh'
      have hf := hF.foot d hd a ha hdh
      rw [hsp1]
      exact ⟨fun hw => hf.1 (inWin_callee hF.al hm8 hdep ha hw), hf.2⟩
  · exact nzOk_sound hF.nz hy1 hm1 hkn.cells hw1 (hall2 v hv)
  · exact valOk_sound hF hkn.roots hy1 (hall3 p hp)
  · refine ⟨fun eg heg => ?_, fun c hc hsh => ?_⟩
    · rcases hstands eg heg with ⟨e, he, hmem, hst⟩ | ⟨e, he, _, hfr, h1, h2, hfld⟩ | hu
      · exact stands_pre hF (hkn.strs e hmem) hst hfs' hW hslot
      · have := stands_pre_frame hF hsl hfr hW hfld hslot
        rw [h1, h2] at this
        exact this
      · exact stands_pre_unit hu
    · -- A cell of the callee is not a key of a writer it was given.
      obtain ⟨_, hcell⟩ := hcellOk c hc
      rcases strHit_call hstands hsh with ⟨_, _, _, f', hf', hf'a⟩ |
        ⟨e, he, hmem, hh⟩ | ⟨e, he, _, hfr, hfld, hh⟩
      · rcases hcell with ⟨f, hfn, _, hca⟩ | ⟨c', hc', hca⟩
        · rw [hca] at hf'a
          have : f = f' := by
            have := congrArg (· - E .x2) hf'a
            simpa using this
          exact hfn (this ▸ hf')
        · have hk := slot_facts hF (hfs' f' hf')
          rw [← hca] at hf'a
          exact (hF.cells c' hc').2.1 (by rw [hf'a]; exact Or.inl hk.2)
      · have hp := hkn.strs e hmem
        have hh0 := Model.hit_congr_stable (fun b hb => (hp.2.2.2.2.1 b hb).2.2) _ hh
        have hwa := hp.2.2.2.1 _ hh0
        rcases hcell with ⟨f, _, hsf, hca⟩ | ⟨c', hc', hca⟩
        · exact hwa.1 (by rw [hca]; exact Or.inl (slot_facts hF hsf).2)
        · exact hF.strs.2 c' hc' (by rw [hca]; exact hwa.2.2)
      · rcases hfr.hit hh with hsl' | hh'
        · obtain ⟨f, hb, hca', hw⟩ := hsl'.facts hF hsl
          rcases hcell with ⟨f', _, _, hca⟩ | ⟨c', hc', hca⟩
          · -- a slot a frame writer's field is in is not a cell of the callee
            obtain ⟨kd, hkd, off, hoff, f'', hf'', hca'', v, hv⟩ := hsl'
            rw [hca] at hca''
            have : f' = f'' := by
              have := congrArg (· - E .x2) hca''
              simpa using this
            subst this
            -- it is among `fs`
            obtain ⟨f3, hf3, hf3e⟩ := hfld kd hkd off hoff
            rw [hf''] at hf3e
            simp only [AVal.lin.injEq, true_and] at hf3e
            subst hf3e
            rename_i hfn _
            exact hfn hf3
          · exact (hF.cells c' hc').2.1 (by rw [hca]; exact Or.inl hw)
        · rcases hcell with ⟨f, _, hsf, hca⟩ | ⟨c', hc', hca⟩
          · exact not_own_of_inWin hF.wf hF.top hF.depth (by rw [hca]; exact (slot_facts hF hsf).2)
              (hF.ok.1 _ hh')
          · exact hF.cellsOwn c' hc' (by rw [hca]; exact hF.ok.1 _ hh')


/-! ### After a call -/

/-- The value of a call's fresh symbol: what its target holds at the return. -/
def callVal (E : Ent) (t : MachineState) : FreshAt → Word
  | .reg r => t.getReg r
  | .slot f => t.getMem (E .x2 + f)
  | .field a => t.getMem (a.eval E)

/-- The symbols' values after a call at `n` with targets `fl`. -/
def callV (E : Ent) (n : Nat) (fl : List FreshAt) (t : MachineState) : Nat → Nat → Word :=
  fun i j => if i = n then (fl[j]?.map (callVal E t)).getD (E.sym i j) else E.sym i j

theorem callV_agree {n : Nat} {fl : List FreshAt} {t : MachineState} :
    ∀ i' j', i' = n ∨ callV E n fl t i' j' = E.sym i' j' := by
  intro i' j'
  by_cases h : i' = n
  · exact Or.inl h
  · exact Or.inr (by simp [callV, h])

theorem freshOf_mem {n : Nat} {fl : List FreshAt} {t' : FreshAt} (h : t' ∈ fl) :
    ∃ j, fl[j]? = some t' ∧ freshOf n fl t' = .sym n j 0 := by
  have := List.isSome_idxOf?.mpr h
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp this
  obtain ⟨hlt, hget, _⟩ := List.idxOf?_eq_some_iff.mp hj
  refine ⟨j, by rw [List.getElem?_eq_getElem hlt, hget], ?_⟩
  simp [freshOf, freshFor, hj]

theorem freshOf_holds {n : Nat} {fl : List FreshAt} {t : MachineState} {t' : FreshAt}
    (h : t' ∈ fl) {w : Word} :
    (freshOf n fl t').Holds (E.withSym (callV E n fl t)) w ↔ w = callVal E t t' := by
  obtain ⟨j, hj, hf⟩ := freshOf_mem (n := n) h
  rw [hf]
  simp [AVal.Holds, callV, hj]

theorem freshOf_eval {n : Nat} {fl : List FreshAt} {t : MachineState} {t' : FreshAt}
    (h : t' ∈ fl) : (freshOf n fl t').eval (E.withSym (callV E n fl t)) = callVal E t t' := by
  obtain ⟨j, hj, hf⟩ := freshOf_mem (n := n) h
  rw [hf]
  simp [AVal.eval, callV, hj]

theorem freshFor_some {n : Nat} {fl : List FreshAt} {t' : FreshAt} {v : AVal}
    (h : freshFor n fl t' = some v) : t' ∈ fl ∧ v = freshOf n fl t' := by
  simp only [freshFor, Option.map_eq_some_iff] at h
  obtain ⟨j, hj, rfl⟩ := h
  refine ⟨List.isSome_idxOf?.mp (by simp [hj]), ?_⟩
  simp [freshOf, freshFor, hj]

theorem slotOk_sound {f : Word} (h : slotOk σ f = true) :
    8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0 := by
  simp only [slotOk, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2, h.1.1⟩

theorem slotOk_of_bounds {f : Word} (h : 8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0) :
    slotOk σ f = true := by
  simp only [slotOk, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨h.2.2, h.1⟩, h.2.1⟩

theorem kindOf_some {v : AVal} {kd : Kind} (h : kindOf env v = some kd) :
    ∃ K, v = .const K ∧ env.model.kinds K = some kd := by
  cases v with
  | const K => exact ⟨K, rfl, h⟩
  | _ => simp [kindOf] at h

/-- The targets of a call's symbols. -/
theorem freshList_mem {kn : Kn} {A : AState} {g : Iface} {lent : List (AVal × AVal)}
    {t' : FreshAt} (h : t' ∈ freshList env σ kn A g lent) :
    t' = .reg .x10 ∨ t' = .reg .x11 ∨
    (∃ e ∈ lent, ∃ kd, kindOf env e.2 = some kd ∧ ∃ off ∈ kd.fields,
      (∃ f, (e.1.addK off).frameOff? = some f ∧ slotOk σ f = true ∧ t' = .slot f) ∨
      (t' = .field (e.1.addK off) ∧
        ∀ f, (e.1.addK off).frameOff? = some f → slotOk σ f = false)) ∨
    (∃ a ∈ outAddrs g, ∃ f, (instVal σ kn A a).frameOff? = some f ∧ slotOk σ f = true ∧
      t' = .slot f) := by
  simp only [freshList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_flatMap, List.mem_filterMap] at h
  rcases h with ((h | h) | ⟨e, he, h⟩) | ⟨a, ha, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr (Or.inl ⟨e, he, ?_⟩))
    cases hk : kindOf env e.2 with
    | none => rw [hk] at h; simp at h
    | some kd =>
      rw [hk] at h
      simp only [List.mem_map] at h
      obtain ⟨off, hoff, ht⟩ := h
      refine ⟨kd, rfl, off, hoff, ?_⟩
      cases hfo : (e.1.addK off).frameOff? with
      | none =>
        rw [hfo] at ht
        exact Or.inr ⟨ht.symm, fun f hf => by cases hf⟩
      | some f =>
        rw [hfo] at ht
        simp only at ht
        split at ht
        · exact Or.inl ⟨f, rfl, by assumption, ht.symm⟩
        · rename_i hso
          exact Or.inr ⟨ht.symm, fun f' hf' => by cases hf'; simpa using hso⟩
  · refine Or.inr (Or.inr (Or.inr ⟨a, ha, ?_⟩))
    cases hfo : (instVal σ kn A a).frameOff? with
    | none => rw [hfo] at h; cases h
    | some f =>
      rw [hfo] at h
      simp only at h
      split at h
      · simp only [Option.some.injEq] at h
        exact ⟨f, rfl, by assumption, h.symm⟩
      · cases h

/-- A slot a lent writer's field is in is a target. -/
theorem freshList_slot_mem {kn : Kn} {A : AState} {g : Iface} {lent : List (AVal × AVal)}
    {e : AVal × AVal} (he : e ∈ lent) {kd : Kind} (hk : kindOf env e.2 = some kd) {off : Word}
    (hoff : off ∈ kd.fields) {f : Word} (hf : (e.1.addK off).frameOff? = some f)
    (hso : slotOk σ f = true) : FreshAt.slot f ∈ freshList env σ kn A g lent := by
  simp only [freshList, List.mem_append, List.mem_flatMap]
  refine Or.inl (Or.inr ⟨e, he, ?_⟩)
  rw [hk]
  simp only [List.mem_map]
  exact ⟨off, hoff, by rw [hf]; simp [hso]⟩

theorem mem_callSlots {n : Nat} {fl : List FreshAt} {co : CallOut} {A : AState} {p : Word × AVal}
    (h : p ∈ callSlots n fl co A) :
    (FreshAt.slot p.1 ∈ fl ∧ p.2 = freshOf n fl (.slot p.1)) ∨
    (p ∈ A.slots ∧ negOff p.1 ≤ co.m ∧ (∀ it ∈ co.its, slotClear p.1 it = true) ∧
      FreshAt.slot p.1 ∉ fl) := by
  unfold callSlots at h
  have key : ∀ (l : List FreshAt) (sl : List (Word × AVal)),
      p ∈ l.foldl (fun sl t => match t with
        | .slot f => (f, freshOf n fl t) :: sl.filter (·.1 != f)
        | _ => sl) sl →
      (FreshAt.slot p.1 ∈ l ∧ p.2 = freshOf n fl (.slot p.1)) ∨
      (p ∈ sl ∧ FreshAt.slot p.1 ∉ l) := by
    intro l
    induction l with
    | nil => intro sl h; exact Or.inr ⟨h, by simp⟩
    | cons t l ih =>
      intro sl h
      rw [List.foldl_cons] at h
      rcases ih _ h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨List.mem_cons_of_mem _ h1, h2⟩
      · cases t with
        | slot f =>
          simp only [List.mem_cons, List.mem_filter, bne_iff_ne, ne_eq] at h1
          rcases h1 with rfl | ⟨h1, hne⟩
          · exact Or.inl ⟨List.mem_cons_self .., rfl⟩
          · refine Or.inr ⟨h1, fun hm => ?_⟩
            rcases List.mem_cons.mp hm with hm | hm
            · exact hne (FreshAt.slot.inj hm)
            · exact h2 hm
        | reg r =>
          refine Or.inr ⟨h1, fun hm => ?_⟩
          rcases List.mem_cons.mp hm with hm | hm
          · cases hm
          · exact h2 hm
        | field a =>
          refine Or.inr ⟨h1, fun hm => ?_⟩
          rcases List.mem_cons.mp hm with hm | hm
          · cases hm
          · exact h2 hm
  rcases key fl _ h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · simp only [List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h1
    exact Or.inr ⟨h1.1, h1.2.1, h1.2.2, h2⟩

theorem mem_callFresh {n : Nat} {fl : List FreshAt} {p : AVal × AVal} (h : p ∈ callFresh n fl) :
    FreshAt.field p.1 ∈ fl ∧ p.2 = freshOf n fl (.field p.1) := by
  simp only [callFresh, List.mem_filterMap] at h
  obtain ⟨t', ht', h⟩ := h
  cases t' with
  | field a => simp only [Option.some.injEq] at h; subst h; exact ⟨ht', rfl⟩
  | _ => cases h

theorem mem_callWmem {n : Nat} {fl : List FreshAt} {kn : Kn} {co : CallOut} {A : AState}
    {p : AVal × AVal} (h : p ∈ callWmem n fl kn co A) :
    p ∈ callFresh n fl ∨
    ((∀ e ∈ co.lent, e ∈ A.fw ∧ e ∉ kn.strs) ∧ p ∈ A.wmem) := by
  unfold callWmem at h
  simp only at h
  split at h
  · rename_i hc
    simp only [List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem, Bool.not_eq_true'] at hc
    rcases List.mem_append.mp h with h | h
    · exact Or.inl h
    · refine Or.inr ⟨fun e he => ⟨(hc e he).1, fun hm => ?_⟩, (List.mem_filter.mp h).1⟩
      have := (hc e he).2
      rw [List.contains_iff_mem.mpr hm] at this
      cases this
  · exact Or.inl h

theorem mem_callInvs {co : CallOut} {A : AState} {f : Fact AVal} (h : f ∈ callInvs env co A) :
    ∃ e ∈ co.lent, ∃ kd vals, kindOf env e.2 = some kd ∧ writerFields A e.1 kd = some vals ∧
      f ∈ instInv kd e.1 vals := by
  simp only [callInvs, List.mem_flatMap] at h
  obtain ⟨e, he, h⟩ := h
  cases hk : kindOf env e.2 with
  | none => rw [hk] at h; simp at h
  | some kd =>
    rw [hk] at h
    simp only at h
    cases hv : writerFields A e.1 kd with
    | none => rw [hv] at h; simp at h
    | some vals => rw [hv] at h; exact ⟨e, he, kd, vals, hk, hv, h⟩

/-- A field's content, as a state's slots and tracked fields have it. -/
theorem fieldAt_holds' {E' : Ent} {A : AState} {M : Word → Word}
    (hsl : ∀ p ∈ A.slots, p.2.Holds E' (M (E' .x2 + p.1)))
    (hw : ∀ p ∈ A.wmem, p.1.isPtr = true ∧ p.2.Holds E' (M (p.1.eval E')))
    {addr v : AVal} (h : fieldAt A addr = some v) :
    v.isPtr = true → v.Holds E' (M (addr.eval E')) := by
  intro _
  unfold fieldAt at h
  cases hf : addr.frameOff? with
  | some f =>
    rw [hf] at h
    rw [AVal.frameOff?_some hf]
    simp only [AVal.eval]
    exact hsl _ (lookup_mem h)
  | none =>
    rw [hf] at h
    exact (hw _ (lookup_mem h)).2

/-- A writer's invariant, instantiated over its tracked fields, holds when the invariant
    does. -/
theorem instInv_holds {E' : Ent} {A : AState} {M : Word → Word}
    (hsl : ∀ p ∈ A.slots, p.2.Holds E' (M (E' .x2 + p.1)))
    (hw : ∀ p ∈ A.wmem, p.1.isPtr = true ∧ p.2.Holds E' (M (p.1.eval E')))
    {d : AVal} (hd : d.isPtr = true) {kd : Kind} {vals : List AVal}
    (hvals : writerFields A d kd = some vals)
    (hinv : ∀ f ∈ kd.inv, f.Holds (env.model.atomIn M) (kd.val (d.eval E') M)) :
    ∀ f ∈ instInv kd d vals, f.Holds (env.model.atomIn M) (AVal.eval E') := by
  intro f hf
  obtain ⟨f0, hf0, rfl⟩ := List.mem_map.mp hf
  obtain ⟨hlen, hidx⟩ := mapM_some_index hvals
  have hfld : ∀ (i : Nat) off, kd.fields[i]? = some off → ∃ v : AVal, vals[i]? = some v ∧
      v.isPtr = true ∧ v.Holds E' (M (d.eval E' + off)) := by
    intro i off hoff
    obtain ⟨v, hv, hfv⟩ := hidx i off hoff
    simp only [Option.bind_eq_some_iff] at hfv
    obtain ⟨u, hu, huv⟩ := hfv
    split at huv
    · rename_i hup
      simp only [Option.some.injEq] at huv; subst huv
      refine ⟨u, hv, hup, ?_⟩
      have := fieldAt_holds' hsl hw hu hup
      rw [AVal.eval_addK_ptr hd] at this
      exact this
    · cases huv
  have hν : AVal.eval E' ∘ (fun j => if j = 0 then d else vals.getD (j - 1) .top) =
      kd.val (d.eval E') M := by
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
  rw [Fact.holds_map, hν]
  exact hinv f0 hf0

/-- The writers a knowledge has mention no symbols. -/
theorem AVal.path_symFree {b : AVal} (hb : b.symFree = true) {ks : List Word} {u : AVal}
    (h : b.path ks = some u) : u.symFree = true := by
  cases ks with
  | nil => simp only [AVal.path, Option.some.injEq] at h; subst h; exact hb
  | cons k ks =>
    cases b with
    | lin r k0 => simp only [AVal.path, Option.some.injEq] at h; subst h; rfl
    | cell r ks0 d => simp only [AVal.path, Option.some.injEq] at h; subst h; rfl
    | const _ => simp [AVal.path] at h
    | top => simp [AVal.path] at h
    | oneOf _ => simp [AVal.path] at h
    | sym _ _ _ => simp [AVal.symFree] at hb

theorem closure_symFree (hsf : σ.symFree = true) {ref : Option (AVal × Word)} :
    ∀ e ∈ (closure env σ ref).strs, e.1.symFree = true ∧ e.2.symFree = true := by
  unfold closure
  have hs := (Iface.symFree_parts hsf).2.2.1
  have : ∀ (l : List (AVal × AVal)), (∀ e ∈ l, e.1.symFree = true ∧ e.2.symFree = true) →
      ∀ kn : Kn, (∀ e ∈ kn.strs, e.1.symFree = true ∧ e.2.symFree = true) →
      ∀ e ∈ (l.foldl (addEntry env ref) kn).strs, e.1.symFree = true ∧ e.2.symFree = true := by
    intro l
    induction l with
    | nil => intro _ kn hkn; exact hkn
    | cons e l ih =>
      intro hl kn hkn
      simp only [List.foldl_cons]
      refine ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) _ fun e' he' => ?_
      have he := hl e (List.mem_cons_self ..)
      unfold addEntry at he'
      cases hse : subEntry env ref e with
      | none =>
        rw [hse] at he'
        simp only [List.mem_cons] at he'
        rcases he' with rfl | he'
        · exact he
        · exact hkn e' he'
      | some x =>
        obtain ⟨s, d', k'⟩ := x
        rw [hse] at he'
        simp only [List.mem_cons] at he'
        obtain ⟨_, _, _, _, _, _, hd, hk⟩ := subEntry_some hse
        rcases he' with rfl | rfl | he'
        · exact ⟨AVal.path_symFree he.1 hd, AVal.path_symFree he.1 hk⟩
        · exact he
        · exact hkn e' he'
  exact this σ.strs hs {} (fun _ h => by simp at h)

theorem AVal.symFree_addK {v : AVal} (h : v.symFree = true) (d : Word) :
    (v.addK d).symFree = true := by
  cases v <;> simp_all [AVal.symFree, AVal.addK]

/-- A `post` variable, in the caller's terms after the call, is what the postcondition
    names. -/
theorem postVar_eval {σ : Iface} {kn : Kn} {A' : AState} {y t : MachineState} {n : Nat}
    {fl : List FreshAt} {E : Ent} (hy : RegsHold (E.withSym (callV E n fl t)) A' y)
    (hm : MemOk σ (E.withSym (callV E n fl t)) A' y.getMem)
    (hk : KnCells (E.withSym (callV E n fl t)) y.getMem kn)
    (hw : WmemOk (E.withSym (callV E n fl t)) A' y.getMem)
    {pv : PVal} {w : AVal} (h : postVar σ kn A' n fl pv = some w) (hwp : w.isPtr = true) :
    w.eval (E.withSym (callV E n fl t)) = postVal y t pv := by
  cases pv with
  | ent v =>
    simp only [postVar] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      exact instVal_eval hy hm hk hw hwp
    · cases h
  | ret r =>
    simp only [postVar] at h
    obtain ⟨hmem, rfl⟩ := freshFor_some h
    rw [freshOf_eval hmem]
    rfl
  | out a =>
    simp only [postVar] at h
    cases hfo : (instVal σ kn A' a).frameOff? with
    | none => rw [hfo] at h; cases h
    | some f =>
      rw [hfo] at h
      obtain ⟨hmem, rfl⟩ := freshFor_some h
      rw [freshOf_eval hmem]
      have hp : (instVal σ kn A' a).isPtr = true := by
        rw [AVal.frameOff?_some hfo]; rfl
      have := instVal_eval hy hm hk hw hp
      rw [AVal.frameOff?_some hfo] at this
      simp only [postVal, callVal]
      rw [← this]
      rfl

theorem afterCall_eq {kn : Kn} {pc : Word} {A : AState} {co : CallOut} {g : Iface} :
    afterCall env σ kn pc A co g =
      { regs := callRegs pc.toNat (freshList env σ kn (A.killAll pc.toNat) g co.lent) (A.killAll pc.toNat)
        slots := callSlots pc.toNat (freshList env σ kn (A.killAll pc.toNat) g co.lent) co
          (A.killAll pc.toNat)
        facts := (if g.heap then (A.killAll pc.toNat).facts.filter (fun f => match f with
            | .atom i _ => env.model.fixed i
            | _ => true)
          else (A.killAll pc.toNat).facts) ++
          callInvs env co { A.killAll pc.toNat with
            slots := callSlots pc.toNat (freshList env σ kn (A.killAll pc.toNat) g co.lent) co
              (A.killAll pc.toNat)
            wmem := callWmem pc.toNat (freshList env σ kn (A.killAll pc.toNat) g co.lent) kn co
              (A.killAll pc.toNat) } ++
          g.post.filterMap (instPost σ kn (A.killAll pc.toNat) pc.toNat
            (freshList env σ kn (A.killAll pc.toNat) g co.lent))
        wmem := callWmem pc.toNat (freshList env σ kn (A.killAll pc.toNat) g co.lent) kn co
          (A.killAll pc.toNat)
        fw := (A.killAll pc.toNat).fw } := rfl

/-- What a checked call site gets back: at the return, the invariant with `afterCall`, the
    call's symbols standing for what it returned. `A1` describes the callee's entry state
    `y`. -/
theorem call_post (hF : Facts env σ E s0) {ref : Option (AVal × Word)} (hrf : RefOk E ref)
    (hrs : ∀ rf, ref = some rf → rf.1.symFree = true)
    {A1 : AState} {y t : MachineState} {g : Iface} {co : CallOut} {pc : Word}
    (hx1 : St env σ C E s0 A1 y) (hfw : fwOk env σ A1 = true)
    (hok : callOk env σ A1 g ref = some co) (hpost : Post env g y t) :
    ∃ V, St env σ C (E.withSym V) s0 (afterCall env σ (closure env σ ref) pc A1 co g) t := by
  have hsf := hF.symFree
  have hkn : KnOk env σ E s0 y.getMem ref (closure env σ ref) := closure_ok hF hx1 hrf
  have hy1 : RegsHold E A1 y := hx1.holds.1
  have hm1 := St.memOk hF hx1
  have hw1 := hx1.wmemOk
  obtain ⟨_, _, hsaved, hun, hcode, hinv, hpstrs, hpfacts, hpheap⟩ := hpost
  obtain ⟨hsp, hdep, hheap, hits, fs, hso, hall, _, _, _, _⟩ := callOk_some hok
  simp only [List.all_eq_true] at hall
  obtain ⟨hsp1, hm8⟩ := spOff_sound hy1 hsp
  have hwr := callee_written hF hy1 hm1 hkn.cells hw1 hsp1 hm8 hdep hits hall
  have hsl := hx1.slots
  obtain ⟨hpassed, hfs, hstands, hstands', hrecov⟩ := strsOk_sound hF hrf hkn hx1 hfw hso
  have hknsf := closure_symFree (env := env) (ref := ref) hsf
  -- The killed state, under the call's symbols.
  rw [afterCall_eq]
  generalize hA' : A1.killAll pc.toNat = A'
  generalize hfl : freshList env σ (closure env σ ref) A' g co.lent = fl
  have hx0 : St env σ C E s0 A' y := hA' ▸ hx1.killAll pc.toNat
  have hV := callV_agree (E := E) (n := pc.toNat) (fl := fl) (t := t)
  have hx' : St env σ C (E.withSym (callV E pc.toNat fl t)) s0 A' y :=
    hA' ▸ St.resymAll hsf (hx1.killAll pc.toNat) hV
  refine ⟨callV E pc.toNat fl t, ?_⟩
  generalize hE' : E.withSym (callV E pc.toNat fl t) = E' at hx'
  have hE'x2 : E' .x2 = E .x2 := by rw [← hE']; rfl
  have hWE : ∀ a, Written σ E' a ↔ Written σ E a := fun a => by rw [← hE']; exact Written_withSym hsf a
  have hSE : ∀ a, StrHit env σ E' s0.getMem a ↔ StrHit env σ E s0.getMem a := fun a => by
    rw [← hE']; exact StrHit_withSym hsf _ a
  have hFE : ∀ a, FieldKey env σ E' s0.getMem a ↔ FieldKey env σ E s0.getMem a := fun a => by
    rw [← hE']; exact FieldKey_withSym hsf _ a
  have hF' : Facts env σ E' s0 := hE' ▸ Facts.withSym hsf hF
  have hrf' : RefOk E' ref := fun rf h => by
    rw [← hE', AVal.holds_withSym (hrs rf h)]; exact hrf rf h
  have hkn' : KnOk env σ E' s0 y.getMem ref (closure env σ ref) := closure_ok hF' hx' hrf'
  have hy' : RegsHold E' A' y := hx'.holds.1
  have hm' := St.memOk hF' hx'
  have hw' := hx'.wmemOk
  have hA'fw : A'.fw = A1.fw := by rw [← hA']; exact AState.killAll_fw _ _
  have hA'slots : ∀ p ∈ A'.slots, p ∈ A1.slots := fun p hp => by
    rw [← hA'] at hp; exact (AState.killAll_slots hp).1
  -- Symbol-free values evaluate as before.
  have hevE : ∀ v : AVal, v.symFree = true → v.eval E' = v.eval E := fun v hv => by
    rw [← hE']; exact AVal.eval_withSym hv
  have hlentsf : ∀ e ∈ co.lent, e.1.symFree = true ∧ e.2.symFree = true := fun e he => by
    rcases hpassed e he with h | ⟨_, h⟩
    · exact hknsf e h
    · exact h.symFree
  have hlentp : ∀ e ∈ co.lent, e.1.isPtr = true ∧ e.2.isPtr = true := fun e he => by
    rcases hpassed e he with h | ⟨_, h⟩
    · exact ⟨(hkn.strs e h).1, (hkn.strs e h).2.1⟩
    · exact h.isPtr
  -- The fresh symbols' values.
  have hfresh : ∀ t' ∈ fl, ∀ w, (freshOf pc.toNat fl t').Holds E' w ↔ w = callVal E t t' :=
    fun t' ht' w => by rw [← hE']; exact freshOf_holds ht'
  -- A doubleword nothing the callee writes or was lent, not owned, is as at the call.
  have hunch : ∀ a, Aligned a → ¬ Written σ E a → ¬ env.InOwn a →
      ¬ StrHit env g (regsOf y) y.getMem a → t.getMem a = y.getMem a :=
    fun a ha hnw hno hns => hun a ha (fun hw => hnw (hwr a ha hw)) hno hns
  have hsh := fun a (h : StrHit env g (regsOf y) y.getMem a) => strHit_call hstands h
  -- A slot of a frame writer lent is a target of the call.
  have hslotfl : ∀ e ∈ co.lent, FrameW env E y.getMem A1 e → ∀ a, FrameW.Slot env E A1 e a →
      ∃ f, a = E .x2 + f ∧ FreshAt.slot f ∈ fl ∧
        (8 ≤ negOff f ∧ negOff f ≤ σ.depth ∧ negOff f % 8 = 0) := by
    intro e he hfr a ha
    obtain ⟨kd, hkd, off, hoff, f, hf, rfl, v, hv⟩ := ha
    obtain ⟨K, kd', hK, hkd', _⟩ := hfr.2.1
    have hkO : kindOf env e.2 = some kd := by
      rw [hK] at hkd ⊢; simpa [AVal.eval, kindOf] using hkd
    refine ⟨f, rfl, ?_, hsl _ hv⟩
    rw [← hfl]
    exact freshList_slot_mem he hkO hoff (by rw [hf]; rfl) (slotOk_of_bounds (hsl _ hv))
  -- Where the callee's writers hit: a slot in `fs`, a caller writer lent, or a frame
  -- writer's slot or heap key.
  have hshW : ∀ a, StrHit env g (regsOf y) y.getMem a → ¬ Written σ E a →
      (∃ e ∈ co.lent, e ∈ (closure env σ ref).strs ∧
        env.model.hit (e.2.eval E) (e.1.eval E) s0.getMem a) ∨ env.model.heap a := by
    intro a hs hnw
    rcases hsh a hs with ⟨_, _, _, f, hf, rfl⟩ | ⟨e, he, hmem, hh⟩ | ⟨e, he, _, hfr, _, hh⟩
    · obtain ⟨_, _, hb, _⟩ := hfs f hf
      exact absurd (Or.inl (slot_facts hF hb).2) hnw
    · have hp := hkn.strs e hmem
      exact Or.inl ⟨e, he, hmem, Model.hit_congr_stable (fun b hb => (hp.2.2.2.2.1 b hb).2.2) _ hh⟩
    · rcases hfr.hit hh with hsl' | hh'
      · obtain ⟨f, rfl, _, hb⟩ := hslotfl e he hfr a hsl'
        exact absurd (Or.inl (slot_facts hF hb).2) hnw
      · exact Or.inr hh'
  -- Every writer lent is kept by the callee.
  have hgiven : ∀ p ∈ co.lent, env.model.Keeps (p.2.eval E) (p.1.eval E) y.getMem t.getMem :=
    fun p hp => let ⟨eg, heg, hst⟩ := hstands' p hp; stands_keeps hst (hpstrs.1 eg heg)
  have hmemg : ∀ a, Aligned a → ¬ Written σ E a → ¬ env.InOwn a →
      (∀ p ∈ co.lent, ¬ env.model.hit (p.2.eval E) (p.1.eval E) y.getMem a) →
      t.getMem a = y.getMem a := by
    intro a ha hnw hno hnp
    refine hunch a ha hnw hno fun hs => ?_
    rcases hsh a hs with ⟨_, _, _, f, hf, rfl⟩ | ⟨e, he, _, hh⟩ | ⟨e, he, _, _, _, hh⟩
    · obtain ⟨_, _, hb, _⟩ := hfs f hf; exact hnw (Or.inl (slot_facts hF hb).2)
    · exact hnp e he hh
    · exact hnp e he hh
  have hgf : σ.heap = false → g.heap = false := fun h => by
    cases hg : g.heap
    · rfl
    · rw [hheap hg] at h; cases h
  -- The slots after the call.
  have hslots2 : ∀ p ∈ callSlots pc.toNat fl co A', p.2.Holds E' (t.getMem (E' .x2 + p.1)) := by
    intro p hp
    rw [hE'x2]
    rcases mem_callSlots hp with ⟨hmem, hp2⟩ | ⟨hp, hpm, hclr, hnot⟩
    · rw [hp2, hfresh _ hmem]; rfl
    · have hsl' := hx0.slots p hp
      have hkey := slot_facts hF hsl'
      have hnw := slot_callee hF hy1 hm1 hkn.cells hw1 hsp1 hm8 hdep hits hall hsl' hpm hclr
      have hval : t.getMem (E .x2 + p.1) = y.getMem (E .x2 + p.1) := by
        by_cases hs : StrHit env g (regsOf y) y.getMem (E .x2 + p.1)
        · rcases hsh _ hs with ⟨eg, heg, hst, _⟩ | ⟨e, _, hmem, hh⟩ | ⟨e, he, _, hfr, _, hh⟩
          · exact (hpstrs.1 eg heg).2.2 _ hst
          · have hp' := hkn.strs e hmem
            have hh0 := Model.hit_congr_stable (fun b hb => (hp'.2.2.2.2.1 b hb).2.2) _ hh
            exact absurd (Or.inl hkey.2) (hp'.2.2.2.1 _ hh0).1
          · rcases hfr.hit hh with hsl'' | hh'
            · obtain ⟨f, hfe, hmem', _⟩ := hslotfl e he hfr _ hsl''
              have : p.1 = f := by
                have := congrArg (· - E .x2) hfe
                simpa using this
              rw [this] at hnot
              exact absurd hmem' hnot
            · exact absurd (hF.ok.1 _ hh') (not_own_of_inWin hF.wf hF.top hF.depth hkey.2)
        · exact hun _ hkey.1 hnw (not_own_of_inWin hF.wf hF.top hF.depth hkey.2) hs
      rw [hval]
      have := hx'.holds.2 p hp
      rw [hE'x2] at this
      exact this
  -- The tracked fields after the call.
  have hwmem2 : ∀ p ∈ callWmem pc.toNat fl (closure env σ ref) co A', p.1.isPtr = true ∧
      FieldKey env σ E' s0.getMem (p.1.eval E') ∧ p.2.Holds E' (t.getMem (p.1.eval E')) := by
    intro p hp
    rcases mem_callWmem hp with hp | ⟨hcond, hp⟩
    · obtain ⟨hmem, hp2⟩ := mem_callFresh hp
      have hmem' := hmem
      rw [← hfl] at hmem'
      rcases freshList_mem hmem' with h | h | ⟨e, he, kd, hk, off, hoff, h⟩ | ⟨_, _, _, _, _, h⟩
      · cases h
      · cases h
      · rcases h with ⟨_, _, _, h⟩ | ⟨h, hns⟩
        · cases h
        have hp1 : p.1 = e.1.addK off := FreshAt.field.inj h
        have he1 := (hlentsf e he).1
        have hsfp : p.1.symFree = true := by rw [hp1]; exact AVal.symFree_addK he1 off
        have hpe : p.1.eval E' = e.1.eval E + off := by
          rw [hevE _ hsfp, hp1, AVal.eval_addK_ptr (hlentp e he).1]
        refine ⟨by rw [hp1]; exact AVal.isPtr_addK (hlentp e he).1 off, ?_, ?_⟩
        · rw [hFE, hpe]
          obtain ⟨K, hK, hkd⟩ := kindOf_some hk
          have hke : env.model.kinds (e.2.eval E) = some kd := by rw [hK]; exact hkd
          rcases hpassed e he with hmem'' | ⟨_, hfr⟩
          · have hp' := hkn.strs e hmem''
            obtain ⟨_, _, halp, _⟩ := Model.writerOk_kind hp'.2.2.1
            refine (hp'.2.2.2.2.2 _ (.own hke ?_ ?_)).2.2
            · exact List.mem_map.mpr ⟨off, hoff, rfl⟩
            · exact Model.field_aligned hke halp hoff
          · exfalso
            obtain ⟨kd', hkd', _, _, hfld⟩ := hfr.kinds
            rw [hke] at hkd'; cases hkd'
            obtain ⟨f, hf, v, hv⟩ := hfld off hoff
            have := hns f (by rw [hf]; rfl)
            rw [slotOk_of_bounds (hsl _ hv)] at this
            cases this
        · rw [hp2, hfresh _ hmem]
          simp only [callVal]
          rw [hevE _ hsfp]
      · cases h
    · obtain ⟨h1, h2, h3⟩ := hx'.wmem p hp
      refine ⟨h1, h2, ?_⟩
      obtain ⟨ha, hno, hsh'⟩ := hF'.fieldKey h2
      have hnw : ¬ Written σ E (p.1.eval E') := fun h => (hF'.strHit hsh').1 ((hWE _).mpr h)
      have : t.getMem (p.1.eval E') = y.getMem (p.1.eval E') := by
        refine hunch _ ha hnw hno fun hs => ?_
        rcases hsh _ hs with ⟨_, _, _, f, hf, hfe⟩ | ⟨e, he, hmem, _⟩ | ⟨e, he, _, hfr, _, hh⟩
        · obtain ⟨_, _, hb, _⟩ := hfs f hf
          exact hnw (by rw [hfe]; exact Or.inl (slot_facts hF hb).2)
        · exact (hcond e he).2 hmem
        · rcases hfr.hit hh with hsl' | hh'
          · obtain ⟨f, hfe, _, hb⟩ := hslotfl e he hfr _ hsl'
            exact hnw (by rw [hfe]; exact Or.inl (slot_facts hF hb).2)
          · exact hno (hF.ok.1 _ hh')
      rw [this]; exact h3
  refine ⟨⟨fun r => ?_, hslots2⟩, by rw [hcode, hx1.code], fun a ha hnw hno hns => ?_,
    fun hh a hha hnp => ?_, hinv, fun p hp => ?_, fun f hf => ?_, hwmem2, ?_⟩
  · -- the registers
    show (AState.get _ r).Holds E' (t.getReg r)
    by_cases h0 : r = .x0
    · subst h0; simp [AState.get, AVal.Holds, MachineState.getReg]
    simp only [AState.get, h0, if_false, callRegs, getD_map_allRegs]
    split
    · rename_i hr
      rw [hfresh _ (by rw [← hfl]; rcases hr with rfl | rfl <;> simp [freshList])]
      rfl
    · split
      · rename_i hs
        have hr : r ∈ savedRegs := List.contains_iff_mem.mp hs
        rw [hsaved r hr]
        have := hy' r
        simp only [AState.get, h0, if_false] at this
        exact this
      · trivial
  · -- memory outside what the function writes and its writers' keys
    rw [hWE] at hnw
    rw [hSE] at hns
    rw [← hx1.mem a ha hnw hno hns]
    refine hunch a ha hnw hno fun hs => ?_
    rcases hshW a hs hnw with ⟨e, _, hmem, hh⟩ | hh
    · exact hns ((hkn.strs e hmem).2.2.2.1 _ hh).2.2
    · exact hno (hF.ok.1 a hh)
  · -- the heap outside the blocks allocated at entry
    have hgf' := hgf hh
    have hpy : ¬ env.model.payload y.getMem a := by
      rw [env.model.payload_keep s0.getMem y.getMem (fun b hb => by
        by_cases hp : env.model.payload s0.getMem b
        · exact Or.inr hp
        · exact Or.inl (hx1.heap hh b hb hp))]
      exact hnp
    rw [hpheap hgf' a hha hpy]
    exact hx1.heap hh a hha hnp
  · -- the slots are in the window
    rcases mem_callSlots hp with ⟨hmem, _⟩ | ⟨hp, _⟩
    · rw [← hfl] at hmem
      rcases freshList_mem hmem with h | h | ⟨_, _, _, _, _, _, ⟨f, _, hso, h⟩ | ⟨h, _⟩⟩ |
        ⟨_, _, f, _, hso, h⟩
      · cases h
      · cases h
      · cases h; exact slotOk_sound hso
      · cases h
      · cases h; exact slotOk_sound hso
    · exact hx0.slots p hp
  · -- the facts
    simp only [List.mem_append] at hf
    rcases hf with (hf | hf) | hf
    · -- the caller's facts, less the atoms if the callee may change the heap
      split at hf
      · rename_i hg
        obtain ⟨hf, hfix⟩ := List.mem_filter.mp hf
        have := hx'.facts f hf
        cases f with
        | le l r => exact this
        | op o x args => exact this
        | atom i args =>
          exact env.model.fixed_sound i _ y.getMem t.getMem (by simpa using hfix) this
      · rename_i hg
        have hgf' : g.heap = false := by simpa using hg
        have := hx'.facts f hf
        cases f with
        | le l r => exact this
        | op o x args => exact this
        | atom i args =>
          exact env.model.atom_keep i _ y.getMem t.getMem (fun a ha => by
            by_cases hp : env.model.payload y.getMem a
            · exact Or.inr hp
            · exact Or.inl (hpheap hgf' a ha hp)) this
    · -- the lent writers' invariants
      obtain ⟨e, he, kd, vals, hk, hvals, hf⟩ := mem_callInvs hf
      obtain ⟨K, hK, hkd⟩ := kindOf_some hk
      have hw := (hgiven e he).1
      obtain ⟨kd', hkd', _, hinvs⟩ := Model.writerOk_kind hw
      rw [hK] at hkd'
      simp only [AVal.eval] at hkd'
      rw [hkd] at hkd'; cases hkd'
      refine instInv_holds (env := env) hslots2 (fun p hp => ⟨(hwmem2 p hp).1, (hwmem2 p hp).2.2⟩)
        (hlentp e he).1 hvals (fun f hf => ?_) f hf
      rw [hevE _ (hlentsf e he).1]
      exact hinvs f hf
    · -- the callee's `post` facts
      simp only [List.mem_filterMap] at hf
      obtain ⟨f0, hf0, hf⟩ := hf
      simp only [instPost] at hf
      split at hf
      · cases hf
      · rename_i hptr
        simp only [Option.some.injEq] at hf
        subst hf
        simp only [Bool.not_eq_true] at hptr
        have := hpfacts f0 hf0
        rw [Fact.holds_map]
        rw [Fact.any_map] at hptr
        rw [Fact.holds_congr (env.model.atomIn t.getMem) (fun pv => !((postVar σ (closure env σ ref) A' pc.toNat fl pv).getD .top).isPtr)
          (fun pv hpv => ?_) hptr]
        · exact this
        · simp only [Function.comp, Bool.not_eq_false'] at hpv ⊢
          cases hv : postVar σ (closure env σ ref) A' pc.toNat fl pv with
          | none => rw [hv] at hpv; simp [AVal.isPtr] at hpv
          | some w =>
            rw [hv] at hpv
            simp only [Option.getD_some] at hpv ⊢
            rw [← hE'] at hy' hm' hkn' hw' ⊢
            exact postVar_eval hy' hm' hkn'.cells hw' hv hpv
  · -- the writers
    rw [← hE', StrsInv_withSym hsf]
    refine ⟨fun e he a ha => ?_, fun hh k p hw hhit hf hs => ?_⟩
    · rw [← hx1.strs.1 e he a ha]
      rcases hrecov with hg | hrec
      · have hpre := hF.strs.1 e he
        refine hunch a (hpre.2.2.1 a ha).1 (hpre.2.1 a (Model.stable_hit ha)).1 (hpre.2.2.1 a ha).2
          fun ⟨eg, heg, _⟩ => ?_
        rw [hg] at heg; simp at heg
      · have hk := recov_sound hF hrf hkn hgiven hmemg 2 e (St.entryOk hF hx1 he) (hrec e he)
        exact hk.2.2 a ((Model.stable_congr (hx1.strs.1 e he) a).mpr ha)
    · have h1 := hx1.strs.2 hh k p hw hhit hf hs
      have hgf' := hgf hh
      refine h1.trans (Model.Keeps.of_keep h1.1 (fun a ha => ?_) (fun a ha hha => ?_)
        (fun a ha hha => ?_))
      · by_cases hha : env.model.heap a
        · by_cases hp : env.model.payload y.getMem a
          · exact Or.inr ⟨hha, hp⟩
          · exact Or.inl (hpheap hgf' a hha hp)
        · left
          have ha0 := h1.2.1 a ha
          have hnw := (hhit a ha0).1
          have hno : ¬ env.InOwn a := by
            rcases Model.hit_fields_stable_heap ha with hfa | hsa | hha'
            · exact hf a (Model.fields_congr_stable h1.2.2 a hfa)
            · exact hs a ((h1.stable_iff a).mp hsa)
            · exact absurd hha' hha
          refine hunch a (Model.hit_aligned ha) hnw hno fun hsg => ?_
          rcases hshW a hsg hnw with ⟨e, _, hmem, hh'⟩ | hh'
          · exact (hhit a ha0).2 ((hkn.strs e hmem).2.2.2.1 _ hh').2.2
          · exact hha hh'
      · exact hf a (Model.fields_congr_stable h1.2.2 a ha) (hF.ok.1 a hha)
      · exact hs a ((h1.stable_iff a).mp ha) (hF.ok.1 a hha)


/-- A writer of the function is in its knowledge. -/
theorem mem_closure {ref : Option (AVal × Word)} {e : AVal × AVal} (he : e ∈ σ.strs) :
    e ∈ (closure env σ ref).strs := by
  unfold closure
  have : ∀ (l : List (AVal × AVal)) (kn : Kn), e ∈ l ∨ e ∈ kn.strs →
      e ∈ (l.foldl (addEntry env ref) kn).strs := by
    intro l
    induction l with
    | nil => intro kn h; simpa using h
    | cons e' l ih =>
      intro kn h
      simp only [List.foldl_cons]
      refine ih _ ?_
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (by unfold addEntry; cases subEntry env ref e with
            | none => simp
            | some x => obtain ⟨_, _, _⟩ := x; simp)
        · exact Or.inl h
      · exact Or.inr (by unfold addEntry; cases subEntry env ref e' with
          | none => simp [h]
          | some x => obtain ⟨_, _, _⟩ := x; simp [h])
  exact this σ.strs {} (Or.inl he)

/-- A tail call: `f` leaves for `g` with its callee-saved registers and `ra` restored. The
    callee's precondition holds, and its postcondition is `f`'s. -/
theorem tail_sound (hF : Facts env σ E s0) {ref : Option (AVal × Word)} (hrf : RefOk E ref)
    {A : AState} {x : MachineState} {g : Iface} {V : Nat → Nat → Word}
    (hpre0 : s0.code = C) (hE : E = (regsOf s0).withSym V)
    (hx : St env σ C E s0 A x) (hfw : fwOk env σ A = true) (hok : tailOk env σ A g ref = true) :
    Pre env C g x ∧ ∀ t, Post env g x t → Post env σ s0 t := by
  unfold tailOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    List.all_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hexit, hdep⟩, hret⟩, hheap⟩, hpost0⟩, hwok⟩, hnoh⟩, hfoot⟩ := hok
  have hpost0' : σ.post = [] := List.isEmpty_iff.mp hpost0
  obtain ⟨hx1, hsv⟩ := okExit_regs hexit hx.holds.1
  have hx2 : x.getReg .x2 = E .x2 := hsv .x2 (by decide)
  have hm := St.memOk hF hx
  have hw := hx.wmemOk
  have hkn := closure_ok hF hx hrf
  cases hits : g.foot.mapM (instItem σ (closure env σ ref) A) with
  | none => rw [hits] at hfoot; cases hfoot
  | some its =>
  rw [hits] at hfoot
  simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true,
    Option.isNone_iff_eq_none, Option.isSome_iff_exists] at hfoot
  obtain ⟨⟨⟨⟨⟨hall, hnz⟩, hvals⟩, hcells⟩, hpre⟩, ⟨passed, fs⟩, hso⟩ := hfoot
  have hdD := hF.depth
  -- Each callee item is covered by one of `f`'s.
  have hcov : ∀ it ∈ g.foot, ∀ a, it.Hits (regsOf x) a → ∃ d ∈ σ.foot, d.Hits E a := by
    intro it hit a hh
    obtain ⟨it', hit', hinst⟩ := mapM_some_mem hits it hit
    obtain ⟨⟨_, hnt⟩, d, hd, hwd⟩ := hall it' hit'
    exact ⟨d, hd, within_hits hwd (instItem_hits hx.holds.1 hm hkn.cells hw hinst hnt hh)⟩
  have hwin : ∀ a, Aligned a → InWin (E .x2) g.depth a → InWin (E .x2) σ.depth a := by
    intro a ha hw'
    have := inWin_callee (e := E .x2) (D := σ.depth) (m := 0) (Dg := g.depth) hF.al (by decide)
      (by omega) ha
    simpa using this (by simpa using hw')
  have hW : ∀ a, Aligned a → Written g (regsOf x) a → Written σ E a := by
    rintro a ha (hw' | ⟨it, hit, hh⟩)
    · exact Or.inl (hwin a ha (by rw [← hx2]; exact hw'))
    · obtain ⟨d, hd, hdh⟩ := hcov it hit a hh
      exact Or.inr ⟨d, hd, hdh⟩
  obtain ⟨hpassed, hfs, hstands, hstands', hrecov⟩ := strsOk_sound hF hrf hkn hx hfw hso
  have hfs0 : ∀ f ∈ fs, False := fun f hf => by obtain ⟨_, h, _⟩ := hfs f hf; cases h
  have hpassed' : ∀ p ∈ passed, p ∈ (closure env σ ref).strs := fun p hp => by
    rcases hpassed p hp with h | ⟨⟨_, h⟩, _⟩
    · exact h
    · cases h
  have hsh : ∀ a, StrHit env g (regsOf x) x.getMem a →
      ¬ Written σ E a ∧ StrHit env σ E s0.getMem a ∧
      ∃ e ∈ passed, env.model.hit (e.2.eval E) (e.1.eval E) x.getMem a := by
    intro a ha
    rcases strHit_call hstands ha with ⟨_, _, _, f, hf, _⟩ | ⟨e, he, hmem, hh⟩ |
      ⟨_, _, ⟨_, h⟩, _⟩
    · exact (hfs0 f hf).elim
    · have hp' := hkn.strs e hmem
      have hh0 := Model.hit_congr_stable (fun b hb => (hp'.2.2.2.2.1 b hb).2.2) _ hh
      have hp := hp'.2.2.2.1 a hh0
      exact ⟨hp.1, hp.2.2, e, he, hh⟩
    · cases h
  have hcellOk := fun c hc => cellOk_sound hF hx.holds.1 hm hkn.cells hkn.roots hw hx.slots hW
    (fun _ _ h => by cases h) (hcells c hc)
  -- The function's writers are well-typed now.
  have hwnow : ∀ e ∈ σ.strs, env.model.writerOk (e.2.eval E) (e.1.eval E) x.getMem :=
    fun e he => (writerOkNow_sound hF hx hrf hkn hfw 4 e (Or.inl (mem_closure he)) (hwok e he)).2.2
  refine ⟨⟨hx.code, by rw [hx2]; exact Nat.le_trans hdep hdD, by rw [hx2]; exact hF.top,
    by rw [hx2]; exact hF.al, fun a ha hp => St.prot hF hx ha hp, fun it hit a ha hh => ?_,
    fun v hv => ?_, fun p hp => valOk_sound hF hkn.roots hx.holds.1 (hvals p hp),
    fun c hc => (hcellOk c hc).1, hx.inv, ?_,
    fun f hf => preOk_sound hx.holds.1 hm hkn.cells hw hx.facts (hpre f hf)⟩, fun t ht => ?_⟩
  · obtain ⟨d, hd, hdh⟩ := hcov it hit a hh
    have hf := hF.foot d hd a ha hdh
    rw [hx2]
    exact ⟨fun hw' => hf.1 (hwin a ha hw'), hf.2⟩
  · exact nzOk_sound hF.nz hx.holds.1 hm hkn.cells hw (hnz v hv)
  · refine ⟨fun eg heg => ?_, fun c hc hs => ?_⟩
    · rcases hstands eg heg with ⟨e, he, hmem, hst⟩ | ⟨_, _, ⟨_, h⟩, _⟩ | hu
      · exact stands_pre hF (hkn.strs e hmem) hst (fun f hf => (hfs0 f hf).elim) hW
          (fun f hf => (hfs0 f hf).elim)
      · cases h
      · exact stands_pre_unit hu
    · obtain ⟨_, hcell⟩ := hcellOk c hc
      obtain ⟨hnw, hsh', _⟩ := hsh _ hs
      rcases hcell with ⟨f, _, hsf, hca⟩ | ⟨c', hc', hca⟩
      · exact hnw (by rw [hca]; exact Or.inl (slot_facts hF hsf).2)
      · exact hF.strs.2 c' hc' (by rw [hca]; exact hsh')
  · obtain ⟨hgr, hpc, hsaved, hun, hcode, hinv, hpstrs, _, hpheap⟩ := ht
    have hgiven : ∀ p ∈ passed, env.model.Keeps (p.2.eval E) (p.1.eval E) x.getMem t.getMem :=
      fun p hp => let ⟨eg, heg, hst⟩ := hstands' p hp; stands_keeps hst (hpstrs.1 eg heg)
    have hmemg : ∀ a, Aligned a → ¬ Written σ E a → ¬ env.InOwn a →
        (∀ p ∈ passed, ¬ env.model.hit (p.2.eval E) (p.1.eval E) x.getMem a) →
        t.getMem a = x.getMem a := by
      intro a ha hnw hno hnp
      refine hun a ha (fun hw' => hnw (hW a ha hw')) hno fun hs => ?_
      obtain ⟨_, _, e, he, hh⟩ := hsh a hs
      exact hnp e he hh
    have hgf : σ.heap = false → g.heap = false := fun h => by
      rcases hheap with h' | h'
      · exact h'
      · rw [h'] at h; cases h
    refine ⟨?_, ?_, fun r hr => ?_, fun a ha hnw hno hns => ?_, ?_, hinv, ?_, ?_, ?_⟩
    · rcases hret with h | h
      · exact h
      · rw [hgr] at h; cases h
    · rw [hpc, hx1, hE]; rfl
    · rw [hsaved r hr, hsv r hr, hE]; rfl
    · have hnw' : ¬ Written σ E a := by rw [hE, Written_withSym hF.symFree]; exact hnw
      have hns' : ¬ StrHit env σ E s0.getMem a := by rw [hE, StrHit_withSym hF.symFree]; exact hns
      have : t.getMem a = x.getMem a := by
        refine hun a ha (fun hw' => hnw' (hW a ha hw')) hno fun hs => ?_
        obtain ⟨_, hs', _⟩ := hsh a hs
        exact hns' hs'
      rw [this]
      exact hx.mem a ha hnw' hno hns'
    · rw [hcode, hx.code, hpre0]
    · rw [show regsOf s0 = E.withSym (regsOf s0).sym from by rw [hE]; rfl, StrsPost_withSym hF.symFree]
      refine ⟨fun e he => ?_, fun hh k p hw' hhit hf hs => ?_⟩
      · -- each writer is kept: given back, or untouched by a callee with no writers
        refine Model.Keeps.of_stable (hx.strs.1 e he) ?_
        rcases hrecov with hg | hrecov
        · have hgf' : g.heap = false := by
            rcases hnoh with (h | h) | h
            · rw [List.isEmpty_iff] at h; rw [h] at he; simp at he
            · exact h
            · rw [hg] at h; simp at h
          have hpre' := hF.strs.1 e he
          refine hpstrs.2 hgf' _ _ (hwnow e he) (fun a ha => ?_) (fun a ha => ?_) (fun a ha => ?_)
          · have ha0 := Model.hit_congr_stable (hx.strs.1 e he) a ha
            refine ⟨fun hw'' => (hpre'.2.1 a ha0).1 (hW a (Model.hit_aligned ha) hw''), ?_⟩
            rintro ⟨eg, heg, _⟩
            rw [hg] at heg; simp at heg
          · exact (hpre'.2.2.2 a (Model.fields_congr_stable (hx.strs.1 e he) a ha)).2
          · exact (hpre'.2.2.1 a ((Model.stable_congr (hx.strs.1 e he) a).mp ha)).2
        · exact recov_sound hF hrf hkn hgiven hmemg 2 e (St.entryOk hF hx he) (hrecov e he)
      · have h1 := hx.strs.2 hh k p hw' hhit hf hs
        have hgf' := hgf hh
        refine h1.trans (Model.Keeps.of_keep h1.1 (fun a ha => ?_) (fun a ha hha => ?_)
          (fun a ha hha => ?_))
        · by_cases hha : env.model.heap a
          · by_cases hp : env.model.payload x.getMem a
            · exact Or.inr ⟨hha, hp⟩
            · exact Or.inl (hpheap hgf' a hha hp)
          · left
            have ha0 := h1.2.1 a ha
            have hnw := (hhit a ha0).1
            have hno : ¬ env.InOwn a := by
              rcases Model.hit_fields_stable_heap ha with hfa | hsa | hha'
              · exact hf a (Model.fields_congr_stable h1.2.2 a hfa)
              · exact hs a ((h1.stable_iff a).mp hsa)
              · exact absurd hha' hha
            refine hun a (Model.hit_aligned ha) (fun hw'' => hnw (hW a (Model.hit_aligned ha) hw''))
              hno fun hsg => ?_
            obtain ⟨_, hs', _⟩ := hsh a hsg
            exact (hhit a ha0).2 hs'
        · exact hf a (Model.fields_congr_stable h1.2.2 a ha) (hF.ok.1 a hha)
        · exact hs a ((h1.stable_iff a).mp ha) (hF.ok.1 a hha)
    · rw [hpost0']; simp
    · intro hh a hha hnp
      have hgf' := hgf hh
      have hpx : ¬ env.model.payload x.getMem a := by
        rw [env.model.payload_keep s0.getMem x.getMem (fun b hb => by
          by_cases hp : env.model.payload s0.getMem b
          · exact Or.inr hp
          · exact Or.inl (hx.heap hh b hb hp))]
        exact hnp
      rw [hpheap hgf' a hha hpx]
      exact hx.heap hh a hha hnp

/-- A `post` variable at the function's own return: what the postcondition names. -/
theorem retVar_eval (hF : Facts env σ E s0) {A : AState} {x : MachineState} {V : Nat → Nat → Word}
    (hx : St env σ C E s0 A x) (hE : E = (regsOf s0).withSym V) {kn : Kn}
    (hk : KnCells E x.getMem kn)
    {x' : MachineState} (hreg : ∀ r, x'.getReg r = x.getReg r) (hmem : x'.getMem = x.getMem)
    {pv : PVal} {w : AVal} (h : retVar σ kn A pv = some w) :
    w.eval E = postVal s0 x' pv := by
  cases pv with
  | ent v =>
    simp only [retVar] at h
    split at h
    · rename_i hv
      simp only [Bool.and_eq_true] at hv
      simp only [Option.some.injEq] at h; subst h
      simp only [postVal]
      rw [hE, AVal.eval_withSym hv.2]
    · cases h
  | ret r =>
    simp only [retVar] at h
    split at h
    · rename_i hp
      simp only [Option.some.injEq] at h; subst h
      simp only [postVal]
      rw [hreg, holds_eval (hx.holds.1 r) hp]
    · cases h
  | out a =>
    simp only [retVar] at h
    split at h
    · rename_i hap
      simp only [Bool.and_eq_true] at hap
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨v, hv, hw⟩ := h
      split at hw
      · rename_i hvp
        simp only [Option.some.injEq] at hw; subst hw
        have := contentAt_holds (St.memOk hF hx) hk hx.wmemOk (holds_self hap.1) hv
        simp only [postVal]
        rw [hmem, holds_eval this hvp, hE, AVal.eval_withSym hap.2]
      · cases hw
    · cases h

/-- A `ret` with every callee-saved register and `ra` restored, the writers well-typed and
    the `post` facts among the state's, is `f`'s postcondition. -/
theorem ret_sound (hF : Facts env σ E s0) {A : AState} {x : MachineState} {V : Nat → Nat → Word}
    (hpre0 : s0.code = C) (hE : E = (regsOf s0).withSym V) (hr : σ.returns = true)
    (hx : St env σ C E s0 A x) (hfw : fwOk env σ A = true) (hok : okExit A = true)
    (hret : retOk env σ (closure env σ none) A = true) :
    Post env σ s0 (execInstrBr x (.JALR .x0 .x1 0)) := by
  obtain ⟨hx1, hsv⟩ := okExit_regs hok hx.holds.1
  simp only [retOk, Bool.and_eq_true, List.all_eq_true] at hret
  obtain ⟨hwok, hposts⟩ := hret
  have hkn := closure_ok hF hx refOk_none
  have hmem : (execInstrBr x (.JALR .x0 .x1 0)).getMem = x.getMem := by
    simp [execInstrBr, setReg_x0]
  have hreg : ∀ r, (execInstrBr x (.JALR .x0 .x1 0)).getReg r = x.getReg r := by
    intro r; simp [execInstrBr, setReg_x0]
  refine ⟨hr, ?_, fun r hr' => ?_, fun a ha hnw hno hns => ?_, ?_,
    Env.Inv_congr (fun _ _ _ => by simp [execInstrBr, setReg_x0]) hx.inv, ?_, fun f hf => ?_,
    fun hh a hha hnp => ?_⟩
  · simp only [execInstrBr, setReg_x0]
    show (x.getReg .x1 + signExtend12 0) &&& ~~~1#64 = _
    rw [hx1, hE]; simp [signExtend12, regsOf, Ent.withSym]
  · rw [hreg, hsv r hr', hE]; rfl
  · have hnw' : ¬ Written σ E a := by rw [hE, Written_withSym hF.symFree]; exact hnw
    have hns' : ¬ StrHit env σ E s0.getMem a := by rw [hE, StrHit_withSym hF.symFree]; exact hns
    rw [hmem]; exact hx.mem a ha hnw' hno hns'
  · simp [execInstrBr, setReg_x0, hx.code, hpre0]
  · rw [show regsOf s0 = E.withSym (regsOf s0).sym from by rw [hE]; rfl, StrsPost_withSym hF.symFree,
      hmem]
    refine ⟨fun e he => ?_, hx.strs.2⟩
    have hw := (writerOkNow_sound hF hx refOk_none hkn hfw 4 e (Or.inl (mem_closure he))
      (hwok e he)).2.2
    exact ⟨hw, Model.hit_congr_stable (hx.strs.1 e he), hx.strs.1 e he⟩
  · have := hposts f hf
    cases hg : f.mapM (retVar σ (closure env σ none) A) with
    | none => rw [hg] at this; cases this
    | some g' =>
      rw [hg] at this
      simp only [List.contains_iff_mem] at this
      have hg' := hx.facts g' this
      rw [hmem]
      exact Fact.holds_mapM _ (fun pv w hpw => retVar_eval hF hx hE hkn.cells hreg hmem hpw) hg hg'
  · rw [hmem]; exact hx.heap hh a hha hnp


end Call

end MachineChecked.RiscV.Check
