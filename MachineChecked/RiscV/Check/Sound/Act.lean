/-
  MachineChecked.RiscV.Check.Sound.Act

  The checker's soundness, part 5: the activation. Every state of it with an annotation
  is safe, by induction on the budget; the checker accepting the annotation makes the
  function meet its interface.
-/

import MachineChecked.RiscV.Check.Sound.Call

namespace MachineChecked.RiscV.Check

open RiscvZkvm.Rv64 MachineChecked.RiscV.Frame

/-! ## The activation -/

theorem Ctx.lookup_some {c : Ctx} {pc : Word} {g : Iface} (h : c.lookup pc = some g) :
    g ∈ c.tbl ∧ g.entry = pc := by
  unfold Ctx.lookup at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem plainStep_some_plain {env : Env} {σ : Iface} {kn : Kn} {pc : Word} {A B : AState}
    {i : Instr} {wtr : Option (AVal × AVal)} (h : plainStep env σ kn pc A i wtr = some B) :
    i ≠ .ECALL ∧ i ≠ .EBREAK ∧ ∀ c r, i ≠ .CSRS c r := by
  refine ⟨?_, ?_, fun c r => ?_⟩ <;>
    (rintro rfl; simp [plainStep, aluStep, aluResult, loadOf, storeOf] at h)

/-- SP1 steps a doubleword store only at an aligned address. -/
theorem stepSp1_sd_aligned {x x' : MachineState} {rs1 rs2 : Reg} {off : BitVec 12}
    (hf : x.code x.pc = some (.SD rs1 rs2 off)) (hs : stepSp1 x = some x') :
    Aligned (x.getReg rs1 + signExtend12 off) := by
  unfold stepSp1 at hs
  rw [hf] at hs
  simp only [Instr.isMemAccess, if_true] at hs
  split at hs
  · rename_i hok
    simp only [memOkSp1, memAccess, Bool.and_eq_true, alignedFor, if_true, isAligned8,
      beq_iff_eq] at hok
    exact (aligned_iff _).mpr hok.1.2
  · cases hs

section Thy

variable {env : Env} {σ : Iface} {E : Ent} {s0 : MachineState}

/-- The axioms are true of the values by what they are. -/
theorem axOk_sound (hF : Facts env σ E s0) (M : Word → Word) {f : Fact AVal}
    (h : axOk env σ f = true) : f.Holds (env.model.atomIn M) (AVal.eval E) := by
  unfold axOk at h
  split at h
  · rename_i c n
    simp only [beq_iff_eq] at h; subst h
    simp [Fact.Holds, LinTerm.eval, Fact.nat, AVal.eval]
  · rename_i n c
    simp only [beq_iff_eq] at h; subst h
    simp [Fact.Holds, LinTerm.eval, Fact.nat, AVal.eval]
  · rename_i k m n
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨rfl, hk⟩, rfl⟩ := h
    simp only [Fact.Holds, LinTerm.eval, Fact.nat, AVal.eval, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
    rw [add_frame]
    have hd := hF.depth
    have ht := hF.top
    have := (E .x2).isLt
    bv_omega
  · rename_i v b off
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hv, hb⟩ := h
    simp only [Fact.Holds, Op.eval, List.map_cons, List.map_nil]
    rw [AVal.eval_base hv, ← hb]
    rfl
  · simp only [beq_iff_eq] at h; subst h
    exact Nat.le_refl _
  · cases h

/-- The theory certificates run in is sound at every state. -/
theorem thy_sound (hF : Facts env σ E s0) (M : Word → Word) :
    (thy env σ).Sound (env.model.atomIn M) (AVal.eval E) :=
  ⟨fun r hr => env.model.rules_sound M r hr, fun _ hf => axOk_sound hF M hf⟩

/-- Running a certificate keeps the invariant. -/
theorem saturate_sound (hF : Facts env σ E s0) {C : Word → Option Instr} {c : Ctx}
    (hc : c.env = env) (hσ : c.σ = σ) {A : AState} {x : MachineState}
    (h : St env σ C E s0 A x) (key : Word × Word) : St env σ C E s0 (c.saturate key A) x := by
  unfold Ctx.saturate
  cases c.certs.lookup key with
  | none => exact h
  | some pfs =>
    refine ⟨h.holds, h.code, h.mem, h.heap, h.inv, h.slots, ?_, h.wmem, h.strs⟩
    simp only
    rw [hc, hσ]
    exact fun f hf => Proof.runAll_sound (thy_sound hF x.getMem) h.facts f hf

/-- A branch decides its facts. -/
theorem branchFacts_sound {A : AState} {x : MachineState} {M : Word → Word}
    (hregs : ∀ r, (A.get r).Holds E (x.getReg r)) {i : Instr} {off : BitVec 13}
    (hb : branchOff? i = some off) :
    (execInstrBr x i = x.setPC (x.pc + signExtend13 off) ∧
      ∀ f ∈ (branchFacts A i).1, f.Holds (env.model.atomIn M) (AVal.eval E)) ∨
    (execInstrBr x i = x.setPC (x.pc + 4) ∧
      ∀ f ∈ (branchFacts A i).2, f.Holds (env.model.atomIn M) (AVal.eval E)) := by
  -- The two operands' values, when known.
  have key : ∀ rs1 rs2 (k : LinTerm AVal → LinTerm AVal → List (Fact AVal) × List (Fact AVal)),
      ∀ (P : Prop), (P → ∀ f ∈ (k (LinTerm.ofVal (A.get rs1)) (LinTerm.ofVal (A.get rs2))).1,
        (A.get rs1).isPtr = true → (A.get rs2).isPtr = true →
        f.Holds (env.model.atomIn M) (AVal.eval E)) →
      (¬ P → ∀ f ∈ (k (LinTerm.ofVal (A.get rs1)) (LinTerm.ofVal (A.get rs2))).2,
        (A.get rs1).isPtr = true → (A.get rs2).isPtr = true →
        f.Holds (env.model.atomIn M) (AVal.eval E)) →
      (P → ∀ f ∈ (branchFacts.cmp (A.get rs1) (A.get rs2) k).1,
        f.Holds (env.model.atomIn M) (AVal.eval E)) ∧
      (¬ P → ∀ f ∈ (branchFacts.cmp (A.get rs1) (A.get rs2) k).2,
        f.Holds (env.model.atomIn M) (AVal.eval E)) := by
    intro rs1 rs2 k P h1 h2
    unfold branchFacts.cmp
    split
    · rename_i hp
      simp only [Bool.and_eq_true] at hp
      exact ⟨fun hP f hf => h1 hP f hf hp.1 hp.2, fun hP f hf => h2 hP f hf hp.1 hp.2⟩
    · exact ⟨fun _ f hf => by simp at hf, fun _ f hf => by simp at hf⟩
  have hev : ∀ r, (A.get r).isPtr = true → (A.get r).eval E = x.getReg r := fun r hr =>
    holds_eval (hregs r) hr
  cases i <;> simp only [branchOff?, Option.some.injEq, reduceCtorEq] at hb <;> subst hb
  · -- BEQ
    rename_i rs1 rs2 off
    simp only [execInstrBr, branchFacts]
    obtain ⟨h1, h2⟩ := key rs1 rs2 (fun u v => ([.le u v, .le v u], []))
      (x.getReg rs1 = x.getReg rs2) (fun hP f hf hp1 hp2 => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl <;>
          simp [Fact.Holds, ofVal_eval hp1, ofVal_eval hp2, hev _ hp1, hev _ hp2, hP])
      (fun _ f hf => by simp at hf)
    by_cases hP : x.getReg rs1 = x.getReg rs2
    · exact Or.inl ⟨by simp [hP], h1 hP⟩
    · exact Or.inr ⟨by simp [hP], h2 hP⟩
  · -- BNE
    rename_i rs1 rs2 off
    simp only [execInstrBr, branchFacts]
    obtain ⟨h1, h2⟩ := key rs1 rs2 (fun u v => ([], [.le u v, .le v u]))
      (x.getReg rs1 ≠ x.getReg rs2) (fun _ f hf => by simp at hf)
      (fun hP f hf hp1 hp2 => by
        have hP : x.getReg rs1 = x.getReg rs2 := Decidable.not_not.mp hP
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl <;>
          simp [Fact.Holds, ofVal_eval hp1, ofVal_eval hp2, hev _ hp1, hev _ hp2, hP])
    by_cases hP : x.getReg rs1 = x.getReg rs2
    · exact Or.inr ⟨by simp [hP], h2 (by simpa using hP)⟩
    · exact Or.inl ⟨by simp [hP], h1 hP⟩
  · -- BLT: no facts
    rename_i rs1 rs2 off
    simp only [execInstrBr, branchFacts]
    split
    · exact Or.inl ⟨rfl, fun f hf => by simp at hf⟩
    · exact Or.inr ⟨rfl, fun f hf => by simp at hf⟩
  · -- BGE: no facts
    rename_i rs1 rs2 off
    simp only [execInstrBr, branchFacts]
    split
    · exact Or.inl ⟨rfl, fun f hf => by simp at hf⟩
    · exact Or.inr ⟨rfl, fun f hf => by simp at hf⟩
  · -- BLTU
    rename_i rs1 rs2 off
    simp only [execInstrBr, branchFacts]
    obtain ⟨h1, h2⟩ := key rs1 rs2 (fun u v => ([.le (u + .ofNat 1) v], [.le v u]))
      (BitVec.ult (x.getReg rs1) (x.getReg rs2)) (fun hP f hf hp1 hp2 => by
        simp only [List.mem_singleton] at hf; subst hf
        simp only [Fact.Holds, LinTerm.eval_add, ofVal_eval hp1, ofVal_eval hp2, hev _ hp1, hev _ hp2,
          LinTerm.eval_ofNat]
        have hP' : (x.getReg rs1).toNat < (x.getReg rs2).toNat := by simpa [BitVec.ult] using hP
        omega)
      (fun hP f hf hp1 hp2 => by
        simp only [List.mem_singleton] at hf; subst hf
        simp only [Fact.Holds, ofVal_eval hp1, ofVal_eval hp2, hev _ hp1, hev _ hp2]
        have hP' : ¬ (x.getReg rs1).toNat < (x.getReg rs2).toNat := by simpa [BitVec.ult] using hP
        omega)
    by_cases hP : BitVec.ult (x.getReg rs1) (x.getReg rs2)
    · exact Or.inl ⟨by simp [hP], h1 hP⟩
    · exact Or.inr ⟨by simp [hP], h2 hP⟩
  · -- BGEU
    rename_i rs1 rs2 off
    simp only [execInstrBr, branchFacts]
    obtain ⟨h1, h2⟩ := key rs1 rs2 (fun u v => ([.le v u], [.le (u + .ofNat 1) v]))
      (¬ BitVec.ult (x.getReg rs1) (x.getReg rs2)) (fun hP f hf hp1 hp2 => by
        simp only [List.mem_singleton] at hf; subst hf
        simp only [Fact.Holds, ofVal_eval hp1, ofVal_eval hp2, hev _ hp1, hev _ hp2]
        have hP' : ¬ (x.getReg rs1).toNat < (x.getReg rs2).toNat := by simpa [BitVec.ult] using hP
        omega)
      (fun hP f hf hp1 hp2 => by
        have hP : BitVec.ult (x.getReg rs1) (x.getReg rs2) = true := Decidable.not_not.mp hP
        simp only [List.mem_singleton] at hf; subst hf
        simp only [Fact.Holds, LinTerm.eval_add, ofVal_eval hp1, ofVal_eval hp2, hev _ hp1, hev _ hp2,
          LinTerm.eval_ofNat]
        have hP' : (x.getReg rs1).toNat < (x.getReg rs2).toNat := by simpa [BitVec.ult] using hP
        omega)
    by_cases hP : BitVec.ult (x.getReg rs1) (x.getReg rs2)
    · exact Or.inr ⟨by simp [hP], h2 (by simpa using hP)⟩
    · exact Or.inl ⟨by simp [hP], h1 hP⟩

end Thy

/-- A syscall's successor state differs from its predecessor in registers only. -/
theorem sysStep_next_shape {σ : Iface} {A B : AState} {its : List Item}
    (h : sysStep σ A = some (.next B its)) :
    B.slots = A.slots ∧ B.facts = A.facts ∧ B.wmem = A.wmem ∧ B.fw = A.fw := by
  unfold sysStep at h
  cases hx5 : A.get .x5 <;> rw [hx5] at h <;> try cases h
  simp only at h
  split at h
  · cases hl : accelLen _ with
    | none => rw [hl] at h; cases h
    | some L =>
      rw [hl] at h
      simp only [Option.map_some, Option.some.injEq, SysOut.next.injEq] at h
      obtain ⟨rfl, _⟩ := h; exact ⟨rfl, rfl, rfl, rfl⟩
  split at h
  · simp only [Option.some.injEq, SysOut.next.injEq] at h
    obtain ⟨rfl, _⟩ := h; exact ⟨rfl, rfl, rfl, rfl⟩
  split at h
  · cases hl : lenPlus (A.get .x11) 8 with
    | none => rw [hl] at h; cases h
    | some l =>
      rw [hl] at h
      simp only [Option.map_some, Option.some.injEq, SysOut.next.injEq] at h
      obtain ⟨rfl, _⟩ := h; exact ⟨rfl, rfl, rfl, rfl⟩
  split at h
  · simp only [Option.some.injEq, SysOut.next.injEq] at h
    obtain ⟨rfl, _⟩ := h; exact ⟨rfl, rfl, rfl, rfl⟩
  split at h
  · split at h <;> cases h
  split at h
  · simp only [Option.some.injEq, SysOut.next.injEq] at h
    obtain ⟨rfl, _⟩ := h; exact ⟨rfl, rfl, rfl, rfl⟩
  split at h
  · simp only [Option.some.injEq, SysOut.next.injEq] at h
    obtain ⟨rfl, _⟩ := h; exact ⟨rfl, rfl, rfl, rfl⟩
  · cases h

/-- A straight-line step keeps the frame writers. -/
theorem aluStep_fw {pc : Word} {A B : AState} {i : Instr} (h : aluStep pc A i = some B) :
    B.fw = A.fw := by
  unfold aluStep at h
  cases hr : aluResult pc A i with
  | none => rw [hr] at h; cases h
  | some rv =>
    obtain ⟨rd, v⟩ := rv
    rw [hr] at h
    simp only at h
    split at h
    · obtain rfl := Option.some.inj h; rfl
    · cases hop : aluOp A i with
      | none => rw [hop] at h; obtain rfl := Option.some.inj h; rfl
      | some roa =>
        obtain ⟨_, o, args⟩ := roa
        rw [hop] at h
        simp only at h
        split at h
        · obtain rfl := Option.some.inj h; rfl
        · cases hop' : aluOp (A.kill pc.toNat 0) i with
          | some roa' =>
            obtain ⟨_, o', args'⟩ := roa'
            rw [hop'] at h
            simp only at h
            split at h <;> (obtain rfl := Option.some.inj h; exact AState.kill_fw _ _ _)
          | none => rw [hop'] at h; obtain rfl := Option.some.inj h; exact AState.kill_fw _ _ _

theorem loadStep_fw {env : Env} {σ : Iface} {kn : Kn} {pc : Word} {A : AState} {i : Instr}
    {rd rs : Reg} {off : BitVec 12} {isD : Bool} :
    (loadStep env σ kn pc A i rd rs off isD).fw = A.fw := by
  unfold loadStep
  dsimp only
  split
  · rfl
  · exact AState.kill_fw _ _ _

theorem fieldStore_fw {env : Env} {σ : Iface} {A B : AState} {b : AVal} {w : Width} {v : AVal}
    (h : fieldStore env σ A b w v = some B) : B.fw = A.fw := by
  unfold fieldStore at h
  split at h
  · cases h
  split at h
  · cases h; rfl
  · cases h

theorem storeStep_fw {env : Env} {σ : Iface} {kn : Kn} {A B : AState} {rs1 rs2 : Reg}
    {off : BitVec 12} {w : Width} {wtr : Option (AVal × AVal)}
    (h : storeStep env σ kn A rs1 rs2 off w wtr = some B) : B.fw = A.fw := by
  unfold storeStep at h
  simp only at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · split at h
    · cases h
    split at h
    · cases h; rfl
    cases hfs : fieldStore env σ A _ w (A.get rs2) with
    | some B' => rw [hfs] at h; cases h; exact fieldStore_fw hfs
    | none =>
      rw [hfs] at h
      cases wtr with
      | none => cases h
      | some e =>
        simp only at h
        split at h
        · cases h; rfl
        · cases h

theorem plainStep_fw {env : Env} {σ : Iface} {kn : Kn} {pc : Word} {A B : AState} {i : Instr}
    {wtr : Option (AVal × AVal)} (h : plainStep env σ kn pc A i wtr = some B) : B.fw = A.fw := by
  unfold plainStep at h
  cases ha : aluStep pc A i with
  | some B' => rw [ha] at h; cases h; exact aluStep_fw ha
  | none =>
    rw [ha] at h
    cases hl : loadOf i with
    | some q =>
      obtain ⟨rd, rs, off, isD⟩ := q
      rw [hl] at h; simp only [Option.some.injEq] at h; subst h; exact loadStep_fw
    | none =>
      rw [hl] at h
      cases hs : storeOf i with
      | some q =>
        obtain ⟨rs1, rs2, off, w⟩ := q
        rw [hs] at h; exact storeStep_fw h
      | none =>
        rw [hs] at h
        cases i <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> (subst h; rfl)

theorem fwOk_congr {env : Env} {σ : Iface} {A B : AState} (h : B.fw = A.fw) :
    fwOk env σ B = fwOk env σ A := by simp [fwOk, h]

theorem Ctx.saturate_fw (c : Ctx) (key : Word × Word) (A : AState) :
    (c.saturate key A).fw = A.fw := by
  unfold Ctx.saturate
  cases c.certs.lookup key <;> rfl

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

/-- The state after a syscall that writes items the function may write. -/
theorem St.syscall (hF : Facts env σ E s0) {A B : AState} {x y : MachineState}
    (hx : St env σ C E s0 A x) {its : List Item}
    (hit : ∀ it ∈ its, it.base.isPtr = true ∧ ∀ a, it.Hits E a → Written σ E a)
    (hok : ∀ it ∈ its, itemOk σ σ.depth it = true) (hcode : y.code = x.code)
    (hB : ∀ r, (B.get r).Holds E (y.getReg r)) (hsl : B.slots = A.slots)
    (hfacts : B.facts = A.facts) (hwmem : B.wmem = A.wmem)
    (hmem : ∀ a, (∀ it ∈ its, ¬ it.Hits E a) → y.getMem a = x.getMem a) :
    St env σ C E s0 { B with slots := B.slots.filter fun p => its.all (slotClear p.1) } y := by
  have hnw : ∀ a, ¬ Written σ E a → y.getMem a = x.getMem a := fun a hnw =>
    hmem a fun it hi hh => hnw ((hit it hi).2 a hh)
  have hno : ∀ a, Aligned a → env.InOwn a → y.getMem a = x.getMem a := fun a ha ho =>
    hmem a fun it hi hh => hF.not_own ha ((hit it hi).2 a hh) ho
  refine ⟨⟨fun r => hB r, fun p hp => ?_⟩, by rw [hcode, hx.code], fun a ha hnw' hno' hns => ?_,
    fun hh a hha hnp => ?_, Env.Inv_congr (fun a ha ho => hno a ha ho) hx.inv, fun p hp => ?_,
    fun f hf => ?_, fun p hp => ?_, StrsInv.congr hF hx.strs hnw⟩
  · simp only [List.mem_filter, List.all_eq_true] at hp
    rw [hsl] at hp
    rw [hmem _ (fun it hi => slot_clear_items hF (hx.slots p hp.1) (hok it hi) (hp.2 it hi))]
    exact hx.holds.2 p hp.1
  · rw [hnw a hnw']
    exact hx.mem a ha hnw' hno' hns
  · rw [hno a (env.model.heap_aligned a hha) (hF.ok.1 a hha)]
    exact hx.heap hh a hha hnp
  · simp only [List.mem_filter] at hp
    rw [hsl] at hp
    exact hx.slots p hp.1
  · rw [hfacts] at hf
    have := hx.facts f hf
    cases f with
    | le l r => exact this
    | op o x args => exact this
    | atom i args =>
      exact env.model.atom_congr i _ _ _ (fun a ha =>
        hno a (env.model.heap_aligned a ha) (hF.ok.1 a ha)) this
  · rw [hwmem] at hp
    obtain ⟨h1, h2, h3⟩ := hx.wmem p hp
    refine ⟨h1, h2, ?_⟩
    rw [hnw _ (hF.strHit (hF.fieldKey h2).2.2).1]
    exact h3

end SysItems

section Act

variable {c : Ctx} {anno : Array (List AState)} {C : Word → Option Instr} {n : Nat}
  {G : MachineState → Prop} {P : Prop} {s0 : MachineState}

/-- The invariant at a state of the activation: at instruction `i` with one of its
    annotations, the symbols given some values. -/
def Ctx.At (c : Ctx) (anno : Array (List AState)) (C : Word → Option Instr) (s0 : MachineState)
    (x : MachineState) : Prop :=
  ∃ i A V, c.f.idx? x.pc = some i ∧ A ∈ annoAt anno i ∧
    St c.env c.σ C ((regsOf s0).withSym V) s0 A x

/-- The hypotheses of the activation argument. -/
structure ActHyp (c : Ctx) (anno : Array (List AState)) (C : Word → Option Instr) (n : Nat)
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

theorem ActHyp.factsV (h : ActHyp c anno C n G P s0) (V : Nat → Nat → Word) :
    Facts c.env c.σ ((regsOf s0).withSym V) s0 :=
  Facts.withSym h.facts.symFree h.facts

/-- A jump to `tgt` from a state with invariant `A`: pruned if its facts are contradictory;
    inside the function (then an annotation of the target holds); or a tail call (then the
    callee's interface carries it). -/
theorem jump_sound (h : ActHyp c anno C n G P s0) {k : Nat} (hk : k < n)
    (ih : ∀ x, c.At anno C s0 x → SafeN G k P x) {A : AState} {z : MachineState} {pc tgt : Word}
    {V : Nat → Nat → Word} {ref : Option (AVal × Word)} (hrf : RefOk ((regsOf s0).withSym V) ref)
    {es : List Edge} (hj : c.jump pc A tgt ref = some es) (hes : ∀ e ∈ es, c.edgeOk anno e = true)
    (hz : St c.env c.σ C ((regsOf s0).withSym V) s0 A z) (hfw : fwOk c.env c.σ A = true)
    (hpc : z.pc = tgt) : SafeN G k P z := by
  have hF := h.factsV V
  have hsf := hF.symFree
  unfold Ctx.jump at hj
  simp only at hj
  have hz' := (saturate_sound hF rfl rfl hz (pc, tgt)).gcIf
  have hfw' : fwOk c.env c.σ (c.saturate (pc, tgt) A).gcIf = true := by
    rw [fwOk_congr (show (c.saturate (pc, tgt) A).gcIf.fw = A.fw by
      unfold AState.gcIf; split <;> exact Ctx.saturate_fw c _ A)]
    exact hfw
  generalize hX : (c.saturate (pc, tgt) A).gcIf = X at hj hz' hfw'
  split at hj
  · -- pruned: the facts are contradictory, so the state is unreachable
    rename_i hfalse
    exact absurd (hz'.facts _ (List.contains_iff_mem.mp hfalse)) falseFact_false
  cases hidx : c.f.idx? tgt with
  | some j =>
    rw [hidx] at hj; cases hj
    have he := hes _ (List.mem_singleton_self _)
    simp only [Ctx.edgeOk, List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at he
    obtain ⟨B, hB, rfl | hle⟩ := he
    · exact ih z ⟨j, _, V, by rw [hpc]; exact hidx, hB, hz'⟩
    · have hzB := St.ofLeAt hsf hz' hle
      rw [Ent.withSym_withSym] at hzB
      exact ih z ⟨j, B, _, by rw [hpc]; exact hidx, hB, hzB⟩
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
        obtain ⟨hpre, hpost⟩ := tail_sound hF hrf h.code0 rfl hz' hfw' htail
        exact h.tbl g hmem k hk G h.cfi P z (by rw [hpc, hent]) hpre
          (fun t ht => SafeN.mono (Nat.le_of_lt hk) (h.k t (hpost t ht)))
      · cases hj

/-- An outlined fragment, run from its `n`-th instruction to its closing `jalr zero, 0(t0)`. -/
theorem frag_sound (h : ActHyp c anno C n G P s0) {k : Nat} {fb : Word} :
    ∀ (fp : List (Option Instr)) (m : Nat) {A B : AState} {z : MachineState} {V : Nat → Nat → Word},
    c.runFrag A fb fp m = some B →
    (∀ j ins, fp[j]? = some (some ins) → C (fb + BitVec.ofNat 64 (4 * (m + j))) = some ins) →
    z.pc = fb + BitVec.ofNat 64 (4 * m) → St c.env c.σ C ((regsOf s0).withSym V) s0 A z →
    fwOk c.env c.σ A = true →
    (∀ z' V', St c.env c.σ C ((regsOf s0).withSym V') s0 B z' →
      z'.pc = z'.getReg .x5 &&& ~~~1#64 → SafeN G k P z') →
    SafeN G k P z
  | [], _, _, _, _, _, hr, _, _, _, _, _ => by simp [Ctx.runFrag] at hr
  | none :: _, _, _, _, _, _, hr, _, _, _, _, _ => by simp [Ctx.runFrag] at hr
  | some i :: rest, m, A, B, z, V, hr, hcode, hpc, hz, hfw, hk => by
    have hfetch : z.code z.pc = some i := by
      rw [hz.code, hpc]; simpa using hcode 0 i rfl
    have hF := h.factsV V
    by_cases hj : i = .JALR .x0 .x5 0
    · subst hj
      simp only [Ctx.runFrag, if_true, Option.some.injEq] at hr; subst hr
      cases hs : stepSp1 z with
      | none => exact SafeN.stuck hs (fun ha => absurd ha (not_accepted_of_code hfetch (by simp)))
      | some z' =>
        have hex := stepSp1_exec hfetch (by simp) (by simp) (by simp) hs
        subst hex
        refine SafeN.of_step (not_accepted_of_code hfetch (by simp)) hs (hk _ V ?_ ?_)
        · simp only [execInstrBr, setReg_x0]; exact hz.setPC
        · simp only [execInstrBr, setReg_x0]
          show (z.getReg .x5 + signExtend12 0) &&& ~~~1#64 = _
          simp [signExtend12]
    · simp only [Ctx.runFrag, hj, if_false] at hr
      cases hp : plainStep c.env c.σ (closure c.env c.σ none) (fb + BitVec.ofNat 64 (4 * m)) A i
          none with
      | none => rw [hp] at hr; cases hr
      | some A' =>
        rw [hp] at hr
        simp only at hr
        obtain ⟨he, hb, hcs⟩ := plainStep_some_plain hp
        cases hs : stepSp1 z with
        | none => exact SafeN.stuck hs (fun ha => absurd ha (not_accepted_of_code hfetch he))
        | some z' =>
          have hex := stepSp1_exec hfetch he hb hcs hs
          have hal : ∀ rs1 rs2 off, i = .SD rs1 rs2 off →
              Aligned (z.getReg rs1 + signExtend12 off) := fun rs1 rs2 off hi =>
            stepSp1_sd_aligned (hi ▸ hfetch) hs
          subst hex
          obtain ⟨V', hz', hpc'⟩ := plainStep_sound hF (closure_ok hF hz refOk_none) hfw hpc hz hal hp
          refine SafeN.of_step (not_accepted_of_code hfetch he) hs ?_
          rw [Ent.withSym_withSym] at hz'
          refine frag_sound h rest (m + 1) hr (fun j ins hm => ?_) ?_ hz'
            (by rw [fwOk_congr (plainStep_fw hp)]; exact hfw) hk
          · have := hcode (j + 1) ins (by simpa using hm)
            rw [show m + (j + 1) = m + 1 + j by omega] at this
            exact this
          · rw [hpc', hpc, ofNat_four_mul_succ, BitVec.add_assoc]

/-- A call: the callee's interface, then an annotation after the call. -/
theorem call_sound' (h : ActHyp c anno C n G P s0) {k : Nat} (hk : k < n)
    (ih : ∀ x, c.At anno C s0 x → SafeN G k P x) {A : AState} {x y : MachineState} {pc tgt : Word}
    {V : Nat → Nat → Word} {ref : Option (AVal × Word)} (hrf : RefOk ((regsOf s0).withSym V) ref)
    (hrs : ∀ rf, ref = some rf → rf.1.symFree = true)
    {es : List Edge} (hcall : c.call pc A tgt ref = some es) (hes : ∀ e ∈ es, c.edgeOk anno e = true)
    (hx : St c.env c.σ C ((regsOf s0).withSym V) s0 A x) (hfw : fwOk c.env c.σ A = true)
    (hy : y = (x.setReg .x1 (pc + 4)).setPC tgt) : SafeN G k P y := by
  have hF := h.factsV V
  have hsf := hF.symFree
  unfold Ctx.call at hcall
  cases hg : c.lookup tgt with
  | none => rw [hg] at hcall; cases hcall
  | some g =>
  rw [hg] at hcall
  simp only at hcall
  obtain ⟨hmem, hent⟩ := Ctx.lookup_some hg
  cases hok : callOk c.env c.σ (A.set .x1 (.const (pc + 4))) g ref with
  | none => rw [hok] at hcall; cases hcall
  | some co =>
  rw [hok] at hcall
  simp only at hcall
  have hx1 : St c.env c.σ C ((regsOf s0).withSym V) s0 (A.set .x1 (.const (pc + 4))) y := by
    rw [hy]; exact (hx.setReg (by simp [AVal.Holds])).setPC
  have hfw1 : fwOk c.env c.σ (A.set .x1 (.const (pc + 4))) = true := hfw
  have hpre := call_pre hF hrf hx1 hfw1 hok
  refine h.tbl g hmem k hk G h.cfi P y (by rw [hy, hent]; rfl) hpre (fun t ht => ?_)
  obtain ⟨V', hst⟩ := call_post (pc := pc) hF hrf hrs hx1 hfw1 hok ht
  rw [Ent.withSym_withSym] at hst
  replace hst := hst.gcIf
  split at hcall
  · rename_i hret
    split at hcall
    · rename_i hal
      cases hj : c.f.idx? (pc + 4) with
      | none => rw [hj] at hcall; cases hcall
      | some j =>
        rw [hj] at hcall; cases hcall
        have he := hes _ (List.mem_singleton_self _)
        simp only [Ctx.edgeOk, List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at he
        have hpc' : t.pc = pc + 4 := by
          rw [ht.2.1, hy]
          simp only [MachineState.getReg_setPC]
          rw [MachineState.getReg_setReg_eq (by decide), hal]
        obtain ⟨B, hB, rfl | hle⟩ := he
        · exact ih t ⟨j, _, _, by rw [hpc']; exact hj, hB, hst⟩
        have htB := St.ofLeAt hsf hst hle
        rw [Ent.withSym_withSym] at htB
        exact ih t ⟨j, B, _, by rw [hpc']; exact hj, hB, htB⟩
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
  intro hkn x ⟨i, A0, V, hi, hA, hx0⟩
  apply SafeN.assume
  intro hGx
  have hkn' : k < n := hkn
  have ih' := ih (Nat.le_of_lt hkn')
  have ⟨hpcx, hilen⟩ := Fn.idx?_some hi
  have hF := h.factsV V
  have hsf := hF.symFree
  have hok := h.instrOk hilen
  unfold Ctx.instrOk at hok
  simp only [List.all_eq_true] at hok
  have hok := hok A0 hA
  cases hstp : c.step i A0 with
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
  have hfetch : x.code x.pc = oi := by rw [hx0.code, hpcx]; exact h.code.1 i oi hpi
  rw [← hpcx] at hstp
  cases oi with
  | none =>
    have hs : stepSp1 x = none := by simp [stepSp1, hfetch]
    exact SafeN.stuck hs (fun ha => by have := ha.1; rw [hfetch] at this; cases this)
  | some ins =>
  unfold Ctx.stepAt at hstp
  simp only at hstp
  -- The certificate at the instruction, and the frame writer it declares.
  have hx1 := saturate_sound hF rfl rfl hx0 (x.pc, x.pc)
  have hx : St c.env c.σ C ((regsOf s0).withSym V) s0 (c.withFw x.pc (c.saturate (x.pc, x.pc) A0)) x := by
    unfold Ctx.withFw
    cases c.fws.lookup x.pc with
    | none => exact hx1
    | some e => exact hx1.setFw _
  generalize hA : c.withFw x.pc (c.saturate (x.pc, x.pc) A0) = A at hstp hx
  split at hstp
  · cases hstp
  rename_i hfw
  have hfw : fwOk c.env c.σ A = true := by simpa using hfw
  have hkn0 := closure_ok hF hx refOk_none
  by_cases hec : ins = .ECALL
  · -- A syscall.
    subst hec
    simp only [branchOff?] at hstp
    have hregs : ∀ r, (A.get r).Holds ((regsOf s0).withSym V) (x.getReg r) := hx.holds.1
    cases hss : sysStep c.σ A with
    | none => rw [hss] at hstp; cases hstp
    | some out =>
    rw [hss] at hstp
    obtain ⟨hstop, hnext⟩ := sysStep_sound hss hregs hF.nz hfetch
    cases out with
    | stop =>
      obtain ⟨hs, hna⟩ := hstop rfl
      exact SafeN.stuck hs (fun ha => absurd ha hna)
    | next B its =>
      simp only at hstp
      split at hstp
      · rename_i hall
        simp only [List.all_eq_true] at hall
        have hit := fun it hi => itemOk_depth hF (hall it hi)
        obtain ⟨hna, hy⟩ := hnext B its rfl (fun it hi => (hit it hi).1)
        refine SafeN.intro (n := k) (P := P) hna (fun y hst => ?_)
        obtain ⟨hpc, hcode, hB, hsl, hmem⟩ := hy y hst
        obtain ⟨_, hfacts, hwmem, hfwB⟩ := sysStep_next_shape hss
        refine jump_sound (V := V) h hkn' ih' refOk_none hstp hok ?_ ?_ hpc
        · exact St.syscall hF hx hit hall hcode hB hsl hfacts hwmem hmem
        · show fwOk c.env c.σ { B with slots := _ } = true
          simp only [fwOk] at hfw ⊢
          rw [hfwB]; exact hfw
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
    cases h1 : c.jump x.pc (A.addFacts (branchFacts A ins).2) (x.pc + 4) with
    | none => rw [h1] at hstp; simp at hstp
    | some e1 =>
    cases h2 : c.jump x.pc (A.addFacts (branchFacts A ins).1) (x.pc + signExtend13 off) with
    | none => rw [h1, h2] at hstp; simp at hstp
    | some e2 =>
    rw [h1, h2] at hstp
    simp at hstp
    subst hstp
    rcases branchFacts_sound (env := c.env) (M := x.getMem) hx.holds.1 hb with ⟨he, hfs⟩ | ⟨he, hfs⟩
    · rw [he]
      exact jump_sound h hkn' ih' refOk_none h2 (fun e he' => hok e (List.mem_append_right _ he'))
        (hx.addFacts hfs).setPC hfw rfl
    · rw [he]
      exact jump_sound h hkn' ih' refOk_none h1 (fun e he' => hok e (List.mem_append_left _ he'))
        (hx.addFacts hfs).setPC hfw rfl
  · split at hstp
    · -- `jal rd, off`
      rename_i rd off _
      have hex := stepSp1_exec hfetch hne (by simp) (by simp) hst
      subst hex
      split at hstp
      · rename_i h0; subst h0
        simp only [execInstrBr, setReg_x0]
        exact jump_sound h hkn' ih' refOk_none hstp hok hx.setPC hfw rfl
      · split at hstp
        · rename_i h1; subst h1
          exact call_sound' h hkn' ih' refOk_none (fun _ h => by cases h) hstp hok hx hfw rfl
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
            simp only [Bool.and_eq_true] at hret
            cases hstp
            have he := hok _ (List.mem_singleton_self _)
            simp only [Ctx.edgeOk] at he
            exact SafeN.mono (Nat.le_of_lt hkn')
              (h.k _ (ret_sound hF h.code0 rfl hret.1 hx hfw he hret.2))
          · cases hstp
        · simp only [execInstrBr, setReg_x0]
          have hrs := hx.holds.1 rs
          split at hstp
          · rename_i es' hfo
            cases hstp
            obtain ⟨root, c', es'', hroot, _, hk, hsub⟩ := fanOut_sound hF hrs hfo
            exact jump_sound h hkn' ih' (fun rf hrf => by cases hrf; exact hroot) hk
              (fun e he => hok e (hsub e he)) hx.setPC hfw rfl
          · cases hl : c.env.cfi.lookup x.pc with
            | none => rw [hl] at hstp; cases hstp
            | some ts =>
              rw [hl] at hstp
              simp only [Option.bind_some] at hstp
              have hin := h.cfi x hGx _ (lookup_mem hl) rfl _ _ _ hfetch
              obtain ⟨es', h1, hsub⟩ := allEdges_mem hstp hin
              exact jump_sound h hkn' ih' refOk_none h1 (fun e he => hok e (hsub e he)) hx.setPC
                hfw rfl
      · split at hstp
        · rename_i h1; subst h1
          have hrs := hx.holds.1 rs
          split at hstp
          · rename_i es' hfo
            cases hstp
            obtain ⟨root, c', es'', hroot, hrsf, hk, hsub⟩ := fanOut_sound hF hrs hfo
            exact call_sound' h hkn' ih' (fun rf hrf => by cases hrf; exact hroot)
              (fun rf hrf => by cases hrf; exact hrsf) hk (fun e he => hok e (hsub e he)) hx hfw
              (by simp [execInstrBr])
          · cases hl : c.env.cfi.lookup x.pc with
            | none => rw [hl] at hstp; cases hstp
            | some ts =>
              rw [hl] at hstp
              simp only [Option.bind_some] at hstp
              have hin := h.cfi x hGx _ (lookup_mem hl) rfl _ _ _ hfetch
              obtain ⟨es', h1, hsub⟩ := allEdges_mem hstp hin
              exact call_sound' h hkn' ih' refOk_none (fun _ h => by cases h) h1
                (fun e he => hok e (hsub e he)) hx hfw (by simp [execInstrBr])
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
                simp only [Ctx.edgeOk, List.any_eq_true, Bool.or_eq_true, beq_iff_eq] at he
                obtain ⟨D, hD, hle⟩ := he
                refine frag_sound (V := V) h fp 0 hB (fun m ins hm => ?_) ?_ ?_ hfw
                  (fun z' V' hz' hpc' => ?_)
                · have := h.code.2 _ fp hfp m ins hm
                  simpa using this
                · show (x.getReg .x5 + signExtend12 off) &&& ~~~1#64 = _
                  rw [h5v]; simp
                · simp only [execInstrBr]; exact (hx.setReg (by simp [AVal.Holds])).setPC
                · have h5' := hz'.holds.1 .x5
                  rw [hcond.1] at h5'; simp only [AVal.Holds] at h5'
                  replace hz' := hz'.gcIf
                  rcases hle with rfl | hle
                  · exact ih' z' ⟨j, _, V', by rw [hpc', h5', hcond.2]; exact hj, hD, hz'⟩
                  have hzD := St.ofLeAt hsf hz' hle
                  rw [Ent.withSym_withSym] at hzD
                  refine ih' z' ⟨j, D, _, ?_, hD, hzD⟩
                  rw [hpc', h5', hcond.2]; exact hj
              · cases hstp
            · cases hstp
          · cases hstp
    · -- `ebreak` traps.
      simp [stepSp1, hfetch] at hst
    · exact absurd rfl hec
    · -- A straight-line instruction.
      cases hp : plainStep c.env c.σ (closure c.env c.σ none) x.pc A ins (c.wtr.lookup x.pc) with
      | none => rw [hp] at hstp; simp at hstp
      | some B =>
        rw [hp] at hstp
        simp only [Option.bind_some] at hstp
        obtain ⟨he, hb, hcs⟩ := plainStep_some_plain hp
        have hex := stepSp1_exec hfetch he hb hcs hst
        have hal : ∀ rs1 rs2 off, ins = .SD rs1 rs2 off →
            Aligned (x.getReg rs1 + signExtend12 off) := fun rs1 rs2 off hi =>
          stepSp1_sd_aligned (hi ▸ hfetch) hst
        subst hex
        obtain ⟨V', hy, hpc'⟩ := plainStep_sound hF hkn0 hfw rfl hx hal hp
        rw [Ent.withSym_withSym] at hy
        exact jump_sound h hkn' ih' refOk_none hstp hok hy
          (by rw [fwOk_congr (plainStep_fw hp)]; exact hfw) hpc'

end Act

/-! ## Soundness -/

section Entry

variable {env : Env} {σ : Iface} {C : Word → Option Instr} {s : MachineState}

/-- A writer with fields the function has, with its kind. -/
theorem entryWs_mem {e : AVal × AVal} {kd : Kind} (h : (e, kd) ∈ entryWs env σ) :
    e ∈ (closure env σ none).strs ∧ kindOf env e.2 = some kd ∧ kd.pure = false := by
  simp only [entryWs, List.mem_filterMap] at h
  obtain ⟨e', he', hek⟩ := h
  cases hk : kindOf env e'.2 with
  | none => rw [hk] at hek; cases hek
  | some kd' =>
    rw [hk] at hek
    simp only at hek
    split at hek
    · cases hek
    · simp only [Option.some.injEq, Prod.mk.injEq] at hek
      obtain ⟨rfl, rfl⟩ := hek
      exact ⟨he', hk, by simpa using ‹¬ kd'.pure = true›⟩

/-- The entry state describes the entry. -/
theorem entryState_sound (hF : Facts env σ (regsOf s) s) (hcode : s.code = C) :
    St env σ C (regsOf s) s (σ.entryState env) s := by
  have hkn := closure_ok_of hF refOk_none (M := s.getMem) fun e he =>
    EntryOk.of_stable hF he (fun _ _ => rfl)
  -- The registers.
  have hregs : ∀ r, ((σ.entryState env).get r).Holds (regsOf s) (s.getReg r) := by
    intro r
    by_cases h0 : r = .x0
    · subst h0; simp [AState.get, AVal.Holds, MachineState.getReg]
    · simp only [AState.get, h0, if_false, Iface.entryState, AState.addFacts, entryBase,
        getD_map_allRegs]
      cases hl : σ.vals.lookup r with
      | none => simp [AVal.Holds, regsOf]
      | some cs => exact hF.vals (r, cs) (lookup_mem hl)
  -- The tracked fields: the writers' fields' entry cells.
  have hwmem : ∀ p ∈ entryWmem env σ, p.1.isPtr = true ∧
      FieldKey env σ (regsOf s) s.getMem (p.1.eval (regsOf s)) ∧
      p.2.Holds (regsOf s) (s.getMem (p.1.eval (regsOf s))) := by
    intro p hp
    simp only [entryWmem, List.mem_flatMap, List.mem_filterMap] at hp
    obtain ⟨⟨e, kd⟩, he, off, hoff, hp⟩ := hp
    obtain ⟨hmem, hk, _⟩ := entryWs_mem he
    simp only [Option.map_eq_some_iff] at hp
    obtain ⟨v, hv, rfl⟩ := hp
    have hent := hkn.strs e hmem
    obtain ⟨K, hK, hkd⟩ := kindOf_some hk
    have hke : env.model.kinds (e.2.eval (regsOf s)) = some kd := by rw [hK]; exact hkd
    obtain ⟨_, _, halp, _⟩ := Model.writerOk_kind hent.2.2.1
    refine ⟨AVal.isPtr_addK hent.1 off, ?_, ?_⟩
    · rw [AVal.eval_addK_ptr hent.1]
      exact (hent.2.2.2.2.2 _ (.own hke (List.mem_map.mpr ⟨off, hoff, rfl⟩)
        (Model.field_aligned hke halp hoff))).2.2
    · have := cellOf_holds (E := regsOf s) (holds_self (AVal.isPtr_addK hent.1 off)) hv
      rw [hF.emem] at this
      exact this
  have hslots : (σ.entryState env).slots = [] := rfl
  refine ⟨⟨hregs, fun p hp => by rw [hslots] at hp; simp at hp⟩, hcode,
    fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, hF.inv,
    fun p hp => by rw [hslots] at hp; simp at hp, fun f hf => ?_, hwmem,
    ⟨fun _ _ _ _ => rfl, fun _ k p hw _ _ _ => Model.Keeps.refl hw⟩⟩
  -- The facts: the `pre` facts, and the writers' invariants over their entry cells.
  simp only [Iface.entryState, AState.addFacts, entryBase, List.mem_append] at hf
  rcases hf with hf | hf
  · exact hF.pre f hf
  · simp only [entryInvs, List.mem_flatMap] at hf
    obtain ⟨⟨e, kd⟩, he, hf⟩ := hf
    obtain ⟨hmem, hk, _⟩ := entryWs_mem he
    cases hvals : writerFields (entryBase env σ) e.1 kd with
    | none => rw [hvals] at hf; simp at hf
    | some vals =>
      rw [hvals] at hf
      have hent := hkn.strs e hmem
      obtain ⟨K, hK, hkd⟩ := kindOf_some hk
      have hke : env.model.kinds (e.2.eval (regsOf s)) = some kd := by rw [hK]; exact hkd
      obtain ⟨kd', hkd', _, hinvs⟩ := Model.writerOk_kind hent.2.2.1
      rw [hke] at hkd'; cases hkd'
      exact instInv_holds (env := env) (A := entryBase env σ) (fun p hp => by simp [entryBase] at hp)
        (fun p hp => ⟨(hwmem p hp).1, (hwmem p hp).2.2⟩) hent.1 hvals hinvs f hf

end Entry

/-- **The checker is sound.** If it accepts the annotation, and every callee in the table
    meets its interface for every budget below `n`, the function meets its own for `n`. -/
theorem Ctx.sound {c : Ctx} {anno : Array (List AState)} {C : Word → Option Instr} {n : Nat}
    (hv : c.valid anno = true) (hcode : CodeAt c.f C) (hne : 0 < c.f.prog.length)
    (hwf : c.env.wf = true) (hok : c.env.Ok) (htbl : ∀ g ∈ c.tbl, ∀ m < n, g.HoldsN c.env C m) :
    c.σ.HoldsN c.env C n := by
  intro G hG P s hpc hpre hk
  have hv0 := hv
  simp only [Ctx.valid, Bool.and_eq_true, beq_iff_eq] at hv0
  obtain ⟨⟨⟨⟨hptr, hsf⟩, hbase⟩, h0⟩, _⟩ := hv0
  have hptr' : ∀ e ∈ c.σ.strs, e.1.isPtr = true ∧ e.2.isPtr = true := fun e he => by
    have := List.all_eq_true.mp hptr e he
    simpa [Bool.and_eq_true] using this
  have hF := Facts.of_pre hwf hok hptr' hsf hpre
  simp only [List.any_eq_true] at h0
  obtain ⟨A, hA, hle⟩ := h0
  have hAct : ActHyp c anno C n G P s := ⟨hv, hcode, htbl, hpre.1, hF, hk, hG⟩
  refine act hAct n (Nat.le_refl _) s ⟨0, A,
    phiSym (regsOf s) c.f.base.toNat (phiOf c.f.base.toNat (c.σ.entryState c.env) A), ?_, hA, ?_⟩
  · simp [Fn.idx?, hpc, ← hbase, hne]
  · exact St.ofLeAt hsf (entryState_sound hF hpre.1) hle

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

end MachineChecked.RiscV.Check
