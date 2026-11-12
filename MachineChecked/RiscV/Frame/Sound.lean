/-
  MachineChecked.RiscV.Frame.Sound

  The frame analysis of `Frame.Domain` is sound against riscv-zkvm's `stepSp1`.
-/

import MachineChecked.RiscV.Frame.Domain
import MachineChecked.RiscV.Safe

namespace MachineChecked.RiscV.Frame

open RiscvZkvm.Rv64

/-! ## The machine: what a successful step is -/

/-- A step that succeeds on an instruction other than `ECALL`/`EBREAK`/`CSRS` is
    `execInstrBr`: the SP1 memory check only decides *whether* the step happens. -/
theorem stepSp1_exec {s s' : MachineState} {i : Instr} (hf : s.code s.pc = some i)
    (he : i ≠ .ECALL) (hb : i ≠ .EBREAK) (hc : ∀ c r, i ≠ .CSRS c r)
    (h : stepSp1 s = some s') : s' = execInstrBr s i := by
  unfold stepSp1 at h
  rw [hf] at h
  cases i <;> simp_all <;> (split at h <;> simp_all)

/-! ## Concretization -/

namespace AVal

theorem frameOff?_some {a : AVal} {k : Word} (h : a.frameOff? = some k) : a = .lin .x2 k := by
  cases a with
  | lin r k' =>
    simp only [frameOff?] at h
    split at h
    · cases h; subst_vars; rfl
    · cases h
  | const => cases h
  | top => cases h
  | oneOf => cases h
  | cell => cases h
  | sym => cases h

theorem holds_addK {E : Ent} {a : AVal} {x d : Word} (h : a.Holds E x) :
    (a.addK d).Holds E (x + d) := by
  cases a <;> simp_all [addK, Holds, BitVec.add_assoc]

end AVal

/-- What an abstract state says about a machine state, given the entry registers `E`. -/
def AState.Holds (E : Ent) (A : AState) (s : MachineState) : Prop :=
  (∀ r, (A.get r).Holds E (s.getReg r)) ∧
  ∀ p ∈ A.slots, p.2.Holds E (s.getMem (E .x2 + p.1))

theorem getD_map_allRegs (f : Reg → AVal) (r : Reg) (d : AVal) :
    (allRegs.map f).getD (regIdx r) d = f r := by
  cases r <;> rfl

theorem regIdx_inj {r r' : Reg} (h : regIdx r = regIdx r') : r = r' := by
  cases r <;> cases r' <;> first | rfl | (simp [regIdx] at h)

namespace AState

theorem get_x0 (A : AState) : A.get .x0 = .const 0 := by simp [get]

theorem get_set_ne {A : AState} {r r' : Reg} {v : AVal} (h : r' ≠ r) :
    (A.set r v).get r' = A.get r' := by
  unfold get set
  split
  · rfl
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
    have : regIdx r ≠ regIdx r' := fun e => h (regIdx_inj e).symm
    simp [this]

theorem get_set_eq_or {A : AState} {r : Reg} {v : AVal} :
    (A.set r v).get r = v ∨ (A.set r v).get r = .top ∨ r = .x0 := by
  unfold get set
  split
  · exact Or.inr (Or.inr ‹_›)
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
    by_cases hl : regIdx r < A.regs.length <;> simp [hl]

theorem holds_setPC {E} {A : AState} {s : MachineState} {v : Word} (h : A.Holds E s) :
    A.Holds E (s.setPC v) := by
  refine ⟨fun r => ?_, fun p hp => ?_⟩
  · simpa using h.1 r
  · simpa using h.2 p hp

theorem holds_set {E} {A : AState} {s : MachineState} {r : Reg} {v : AVal} {w : Word}
    (h : A.Holds E s) (hv : v.Holds E w) : (A.set r v).Holds E (s.setReg r w) := by
  refine ⟨fun r' => ?_, fun p hp => ?_⟩
  · by_cases hr : r' = r
    · subst hr
      rcases get_set_eq_or (A := A) (r := r') (v := v) with h1 | h1 | h1
      · rw [h1]
        by_cases h0 : r' = .x0
        · subst h0
          have := get_x0 (A.set .x0 v)
          rw [h1] at this; subst this; simp [AVal.Holds, MachineState.getReg]
        · rwa [MachineState.getReg_setReg_eq h0]
      · rw [h1]; trivial
      · subst h1; rw [get_x0]; simp [AVal.Holds, MachineState.getReg]
    · rw [get_set_ne hr, MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
      exact h.1 r'
  · simpa [MachineState.getMem_setReg] using h.2 p hp

theorem _root_.MachineChecked.RiscV.Frame.AVal.holds_of_le {E} {a b : AVal} {v : Word}
    (hle : a.le b = true) (h : a.Holds E v) : b.Holds E v := by
  unfold AVal.le at hle
  simp only [Bool.or_eq_true, beq_iff_eq] at hle
  rcases hle with (rfl | rfl) | hle
  · trivial
  · exact h
  · cases a <;> cases b <;> simp_all [AVal.Holds, List.all_eq_true]

theorem holds_of_le {E} {A B : AState} {s : MachineState} (hle : A.le B = true)
    (h : A.Holds E s) : B.Holds E s := by
  simp only [le, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hle
  exact ⟨fun r => AVal.holds_of_le (hle.1.1.1.1 r (mem_allRegs r)) (h.1 r),
    fun p hp => h.2 p (hle.1.1.1.2 p hp)⟩

theorem holds_entry {E} {s : MachineState} (hE : ∀ r, r ≠ .x0 → s.getReg r = E r) :
    entry.Holds E s := by
  refine ⟨fun r => ?_, fun p hp => by simp [entry] at hp⟩
  by_cases h0 : r = .x0
  · subst h0; simp [get, AVal.Holds, MachineState.getReg]
  · simp only [get, h0, ite_false, entry, getD_map_allRegs, AVal.Holds]
    simp [hE r h0]

end AState

/-! ## Machine facts the transfer proof needs -/

/-- An address lies less than 8 bytes above its doubleword. -/
theorem sub_alignToDword_lt (a : Word) : (a - alignToDword a).toNat < 8 := by
  have hdisj : (a &&& ~~~7#64) &&& (a &&& 7#64) = 0 := by
    ext i
    simp only [BitVec.getElem_and, BitVec.getElem_not]
    rcases Bool.eq_false_or_eq_true ((7#64)[i]) with h7 | h7 <;> simp [h7]
  have hor : (a &&& ~~~7#64) ||| (a &&& 7#64) = a := by
    ext i
    simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
    rcases Bool.eq_false_or_eq_true (a[i]) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true ((7#64)[i]) with h7 | h7 <;> simp [ha, h7]
  have hsum : alignToDword a + (a &&& 7#64) = a := by
    unfold alignToDword; rw [BitVec.add_eq_or_of_and_eq_zero _ _ hdisj, hor]
  have : a - alignToDword a = a &&& 7#64 := by
    have h : alignToDword a + (a &&& 7#64) - alignToDword a = a - alignToDword a := by
      rw [hsum]
    rw [← h, BitVec.add_comm, BitVec.add_sub_cancel]
  rw [this, BitVec.toNat_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {l : List (α × β)} {k : α} {v : β}
    (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp at h
  | cons p l ih =>
    obtain ⟨k', v'⟩ := p
    simp only [List.lookup] at h
    by_cases hk : k = k'
    · subst hk; simp at h; subst h; simp
    · have : (k == k') = false := by simpa using hk
      rw [this] at h; exact List.mem_cons_of_mem _ (ih h)

/-! ## Instruction shapes -/

theorem aluResult_sound {E} {A : AState} {s : MachineState} {pc : Word} {i : Instr}
    {rd : Reg} {v : AVal} (hpc : s.pc = pc) (h : A.Holds E s)
    (hr : aluResult pc A i = some (rd, v)) :
    ∃ w, execInstrBr s i = (s.setReg rd w).setPC (s.pc + 4) ∧ v.Holds E w := by
  cases i <;> simp only [aluResult, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hr <;>
    obtain ⟨rfl, rfl⟩ := hr <;> refine ⟨_, rfl, ?_⟩ <;> try trivial
  case ADD rd rs1 rs2 =>
    have h1 := h.1 rs1; have h2 := h.1 rs2
    split
    · rename_i c heq; rw [heq] at h2; simp only [AVal.Holds] at h2; rw [h2]
      exact AVal.holds_addK h1
    · rename_i c heq _; rw [heq] at h1; simp only [AVal.Holds] at h1; rw [h1, BitVec.add_comm]
      exact AVal.holds_addK h2
    · trivial
  case ADDI rd rs imm => exact AVal.holds_addK (h.1 rs)
  case MV rd rs => exact h.1 rs
  case AUIPC => simp [AVal.Holds, hpc]

theorem loadOf_shape {s : MachineState} {i : Instr} {rd rs : Reg} {off : BitVec 12} {isD : Bool}
    (h : loadOf i = some (rd, rs, off, isD)) :
    ∃ w, execInstrBr s i = (s.setReg rd w).setPC (s.pc + 4) ∧
      (isD = true → w = s.getMem (s.getReg rs + signExtend12 off)) := by
  cases i <;> simp only [loadOf, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h <;> exact ⟨_, rfl, by simp⟩

theorem storeOf_shape {s : MachineState} {i : Instr} {rs1 rs2 : Reg} {off : BitVec 12} {w : Width}
    (h : storeOf i = some (rs1, rs2, off, w)) :
    ∃ v, execInstrBr s i =
        (s.setMem (w.target (s.getReg rs1 + signExtend12 off)) v).setPC (s.pc + 4) ∧
      (w = .d → v = s.getReg rs2) := by
  cases i <;> simp only [storeOf, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := h <;> exact ⟨_, rfl, by simp⟩

/-! ## One straight-line instruction -/

/-- The doubleword a store instruction rewrites in state `s` (`0` for a non-store). -/
def storeTarget (s : MachineState) (i : Instr) : Word :=
  match storeOf i with
  | some (rs1, _, off, w) => w.target (s.getReg rs1 + signExtend12 off)
  | none => 0

/-- A frame store at offset `k` leaves every slot it may not hit unchanged. -/
theorem frame_keep {E : Ent} {s : MachineState} {w : Width} {k sk v : Word}
    (hm : mayHit w k sk = false) :
    (s.setMem (w.target (E .x2 + k)) v).getMem (E .x2 + sk) = s.getMem (E .x2 + sk) := by
  rw [getMem_setMem, ite_eq_right]
  intro heq
  cases w with
  | d =>
    simp only [Width.target] at heq
    have : sk = k := by simpa using heq
    simp [mayHit, this] at hm
  | sub =>
    simp only [Width.target] at heq
    have hlt := sub_alignToDword_lt (E .x2 + k)
    rw [← heq] at hlt
    have : E .x2 + k - (E .x2 + sk) = k - sk := by bv_omega
    rw [this] at hlt
    simp only [mayHit, decide_eq_false_iff_not] at hm
    exact hm hlt

theorem transferStore_sound {E} {A : AState} {s : MachineState} {pc : Word}
    {rs1 rs2 : Reg} {off : BitVec 12} {w : Width} {v : Word}
    (h : A.Holds E s) (hv : w = .d → v = s.getReg rs2)
    (hreq : ∀ q ∈ (transferStore pc A rs1 rs2 off w).reqs, q.Holds E)
    (hres : (transferStore pc A rs1 rs2 off w).residual ≠ [] →
       ∀ p ∈ A.slots, protects p = true →
         w.target (s.getReg rs1 + signExtend12 off) ≠ E .x2 + p.1) :
    (transferStore pc A rs1 rs2 off w).st.Holds E
      (s.setMem (w.target (s.getReg rs1 + signExtend12 off)) v) := by
  have hb := AVal.holds_addK (d := signExtend12 off) (h.1 rs1)
  have hregs : ∀ a, ∀ r, (A.get r).Holds E ((s.setMem a v).getReg r) := fun a r => by
    rw [getReg_setMem]; exact h.1 r
  unfold transferStore at hreq hres ⊢
  generalize (A.get rs1).addK (signExtend12 off) = b at hb hreq hres ⊢
  dsimp only at hreq hres ⊢
  cases hk : b.frameOff? with
  | some k =>
    simp only [hk] at hreq hres ⊢
    rw [AVal.frameOff?_some hk] at hb
    simp only [AVal.Holds] at hb
    rw [hb]
    refine ⟨hregs _, fun p hp => ?_⟩
    have keep : ∀ p ∈ A.slots.filter (fun p => !mayHit w k p.1),
        p.2.Holds E ((s.setMem (w.target (E .x2 + k)) v).getMem (E .x2 + p.1)) := by
      intro p hp
      simp only [List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      rw [frame_keep hp.2]; exact h.2 p hp.1
    cases w with
    | sub => exact keep p hp
    | d =>
      cases hr2 : A.get rs2 with
      | top => simp only [hr2] at hp; exact keep p hp
      | lin r j =>
        simp only [hr2, List.mem_cons] at hp
        rcases hp with rfl | hp
        · rw [getMem_setMem, ite_eq_left (by simp [Width.target]), hv rfl, ← hr2]
          exact h.1 rs2
        · exact keep p hp
      | const c =>
        simp only [hr2, List.mem_cons] at hp
        rcases hp with rfl | hp
        · rw [getMem_setMem, ite_eq_left (by simp [Width.target]), hv rfl, ← hr2]
          exact h.1 rs2
        · exact keep p hp
      | oneOf cs =>
        simp only [hr2, List.mem_cons] at hp
        rcases hp with rfl | hp
        · rw [getMem_setMem, ite_eq_left (by simp [Width.target]), hv rfl, ← hr2]
          exact h.1 rs2
        · exact keep p hp
      | cell r ks j =>
        simp only [hr2, List.mem_cons] at hp
        rcases hp with rfl | hp
        · rw [getMem_setMem, ite_eq_left (by simp [Width.target]), hv rfl, ← hr2]
          exact h.1 rs2
        · exact keep p hp
      | sym i j k =>
        simp only [hr2, List.mem_cons] at hp
        rcases hp with rfl | hp
        · rw [getMem_setMem, ite_eq_left (by simp [Width.target]), hv rfl, ← hr2]
          exact h.1 rs2
        · exact keep p hp
  | none =>
    simp only [hk] at hreq hres ⊢
    by_cases hnt : b = .top
    · simp only [hnt, ite_true] at hreq hres ⊢
      -- An unknown base: only return-address slots survive, each under the residual premise.
      refine ⟨hregs _, fun p hp => ?_⟩
      simp only [List.mem_filter] at hp
      have hne : (if (A.slots.filter protects).isEmpty then [] else [pc]) ≠ [] := by
        have : (A.slots.filter protects).isEmpty = false := by
          rw [List.isEmpty_eq_false_iff_exists_mem]; exact ⟨p, List.mem_filter.mpr hp⟩
        simp [this]
      rw [getMem_setMem, ite_eq_right (Ne.symm (hres hne p hp.1 hp.2))]
      exact h.2 p hp.1
    · simp only [hnt, ite_false] at hreq hres ⊢
      -- A base relative to another entry register, or a constant: the premise `Req`.
      refine ⟨hregs _, fun p hp => ?_⟩
      simp only [List.mem_filter] at hp
      have hq := hreq { pc, w, base := b, sk := p.1 }
        (List.mem_map.mpr ⟨p, List.mem_filter.mpr hp, rfl⟩)
      have hneq : w.target (s.getReg rs1 + signExtend12 off) ≠ E .x2 + p.1 := by
        cases b with
        | lin r k => simp only [AVal.Holds] at hb; simpa [Req.Holds, hb] using hq
        | const c => simp only [AVal.Holds] at hb; simpa [Req.Holds, hb] using hq
        | top => exact absurd rfl hnt
        | oneOf cs => simp only [AVal.Holds] at hb; exact hq _ hb
        | cell r ks k => simp only [AVal.Holds] at hb; simpa [Req.Holds, hb] using hq
        | sym i j k => simp only [AVal.Holds] at hb; simpa [Req.Holds, hb] using hq
      rw [getMem_setMem, ite_eq_right (Ne.symm hneq)]
      exact h.2 p hp.1

theorem transfer_sound {E} {A : AState} {s : MachineState} {pc : Word} {i : Instr} {o : Out}
    (hpc : s.pc = pc) (h : A.Holds E s) (ht : transfer pc A i = some o)
    (hreq : ∀ q ∈ o.reqs, q.Holds E)
    (hres : o.residual ≠ [] → ∀ p ∈ A.slots, protects p = true → storeTarget s i ≠ E .x2 + p.1) :
    o.st.Holds E (execInstrBr s i) ∧ (execInstrBr s i).pc = s.pc + 4 := by
  unfold transfer at ht
  split at ht
  · rename_i rd v hr
    cases ht
    obtain ⟨w, he, hw⟩ := aluResult_sound hpc h hr
    rw [he]; exact ⟨AState.holds_setPC (AState.holds_set h hw), rfl⟩
  · split at ht
    · rename_i rd rs off isD hl
      cases ht
      obtain ⟨w, he, hw⟩ := loadOf_shape (s := s) hl
      rw [he]
      refine ⟨AState.holds_setPC (AState.holds_set h ?_), rfl⟩
      have hb := AVal.holds_addK (d := signExtend12 off) (h.1 rs)
      generalize (A.get rs).addK (signExtend12 off) = b at hb ⊢
      split
      · rename_i k hk
        rw [AVal.frameOff?_some hk] at hb
        simp only [AVal.Holds] at hb
        cases hlk : A.slots.lookup k with
        | none => trivial
        | some v' =>
          simp only [Option.getD_some]
          rw [hw rfl, hb]; exact h.2 _ (lookup_mem hlk)
      · trivial
    · split at ht
      · rename_i rs1 rs2 off w _ hst
        cases ht
        obtain ⟨v, he, hv⟩ := storeOf_shape (s := s) hst
        rw [he]
        refine ⟨AState.holds_setPC (transferStore_sound h hv hreq ?_), rfl⟩
        intro hne p hp hpr
        have := hres hne p hp hpr
        simpa [storeTarget, hst] using this
      · split at ht <;> cases ht <;> exact ⟨AState.holds_setPC h, rfl⟩

/-! ## Addresses and code -/

theorem Fn.idx?_some {f : Fn} {p : Word} {j : Nat} (h : f.idx? p = some j) :
    p = f.pcOf j ∧ j < f.prog.length := by
  unfold Fn.idx? at h
  dsimp only at h
  split at h
  · rename_i hc
    cases h
    refine ⟨?_, hc.2⟩
    unfold Fn.pcOf
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hc.1), BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_omega
  · cases h

/-- The function's instructions (and its fragments') are where the image says. -/
def CodeOk (f : Fn) (s : MachineState) : Prop :=
  (∀ j ins, f.instrAt? j = some ins → s.code (f.pcOf j) = some ins) ∧
  ∀ fb fp, f.frags.lookup fb = some fp →
    ∀ m ins, fp[m]? = some (some ins) → s.code (fb + BitVec.ofNat 64 (4 * m)) = some ins

theorem CodeOk.of_code {f : Fn} {s s' : MachineState} (h : CodeOk f s) (hc : s'.code = s.code) :
    CodeOk f s' := by
  unfold CodeOk; rw [hc]; exact h

/-! ## Runs (`stepsSp1`, `MachineChecked.RiscV.Safe`) -/

/-- The number of instructions before a fragment's closing `jalr zero, 0(t0)`. -/
def fragLen : List (Option Instr) → Option Nat
  | [] => none
  | some i :: rest => if i = .JALR .x0 .x5 0 then some 0 else (fragLen rest).map (· + 1)
  | none :: _ => none

def IsCall (ins : Instr) : Prop :=
  (∃ off, ins = .JAL .x1 off) ∨ (∃ rs off, ins = .JALR .x1 rs off)

def IsOutlined (ins : Instr) : Prop := ∃ off, ins = .JALR .x5 .x5 off

/-- What a callee is assumed to do: return to the next instruction, keep the code, `sp` and
    `s0`-`s11`, and leave the caller's saved return addresses alone. -/
def CallRet (E : Ent) (A : AState) (s s' : MachineState) : Prop :=
  s'.pc = s.pc + 4 ∧ s'.code = s.code ∧
  (∀ r, calleeSaved.contains r = true → s'.getReg r = s.getReg r) ∧
  ∀ p ∈ A.slots, protects p = true → s'.getMem (E .x2 + p.1) = s.getMem (E .x2 + p.1)

/-- One activation of `f`, from `s0` until it leaves `f`: real `stepSp1` steps inside the
    function and through outlined fragments; calls as `CallRet` macro-steps (and only those
    whose return address is inside `f`: the others are assumed not to return). -/
inductive Run (f : Fn) (anno : Array (Option AState)) (E : Ent) (s0 : MachineState) :
    MachineState → Prop
  | start : Run f anno E s0 s0
  | step {s s' : MachineState} {i : Nat} {ins : Instr} :
      Run f anno E s0 s → f.idx? s.pc = some i → f.instrAt? i = some ins →
      ¬ IsCall ins → ¬ IsOutlined ins → ins ≠ .JALR .x0 .x1 0 →
      stepSp1 s = some s' → (f.idx? s'.pc).isSome → Run f anno E s0 s'
  | call {s s' : MachineState} {i : Nat} {ins : Instr} {A : AState} :
      Run f anno E s0 s → f.idx? s.pc = some i → f.instrAt? i = some ins → IsCall ins →
      Fn.annoAt anno i = some A → (f.idx? (s.pc + 4)).isSome → CallRet E A s s' →
      Run f anno E s0 s'
  | outlined {s s' : MachineState} {i k : Nat} {off : BitVec 12} {fp : List (Option Instr)} :
      Run f anno E s0 s → f.idx? s.pc = some i → f.instrAt? i = some (.JALR .x5 .x5 off) →
      f.frags.lookup ((s.getReg .x5 + signExtend12 off) &&& ~~~1#64) = some fp →
      fragLen fp = some k → stepsSp1 (k + 2) s = some s' → Run f anno E s0 s'

/-! ## Edges -/

theorem okExit_holds {E} {A : AState} {s : MachineState} (hx : okExit A = true)
    (h : A.Holds E s) : s.getReg .x1 = E .x1 ∧ s.getReg .x2 = E .x2 := by
  simp only [okExit, Bool.and_eq_true, beq_iff_eq] at hx
  have h1 := h.1 .x1
  have h2 := h.1 .x2
  rw [hx.1] at h1; rw [hx.2] at h2
  simp only [AVal.Holds] at h1 h2
  exact ⟨by simpa using h1, by simpa using h2⟩

/-- Where a checked step can land: on an instruction of `f` whose annotation holds, or
    outside `f` with `ra` and `sp` at their entry values. -/
def Lands (f : Fn) (anno : Array (Option AState)) (E : Ent) (s : MachineState) : Prop :=
  (∃ j C, f.idx? s.pc = some j ∧ Fn.annoAt anno j = some C ∧ C.Holds E s) ∨
  (f.idx? s.pc = none ∧ s.getReg .x1 = E .x1 ∧ s.getReg .x2 = E .x2)

theorem target_sound {f : Fn} {anno} {E} {A : AState} {s : MachineState} {pc' : Word}
    (hok : ∀ e ∈ f.target A pc', f.edgeOk anno e = true) (h : A.Holds E s) (hp : s.pc = pc') :
    Lands f anno E s := by
  subst hp
  unfold Fn.target at hok
  cases hj : f.idx? s.pc with
  | some j =>
    simp only [hj, List.mem_singleton, forall_eq, Fn.edgeOk] at hok
    cases hC : Fn.annoAt anno j with
    | some C => rw [hC] at hok; exact Or.inl ⟨j, C, hj, hC, AState.holds_of_le hok h⟩
    | none => rw [hC] at hok; cases hok
  | none =>
    simp only [hj, List.mem_singleton, forall_eq, Fn.edgeOk] at hok
    exact Or.inr ⟨hj, okExit_holds hok h⟩

theorem anywhere_sound {f : Fn} {anno} {E} {A : AState} {s : MachineState}
    (hok : f.edgeOk anno (.anywhere A) = true) (h : A.Holds E s)
    (hcfi : ∀ ts, f.jumps = some ts → (f.idx? s.pc).isSome → s.pc ∈ ts) : Lands f anno E s := by
  simp only [Fn.edgeOk, Bool.and_eq_true] at hok
  obtain ⟨hx, hall⟩ := hok
  cases hj : f.idx? s.pc with
  | none => exact Or.inr ⟨hj, okExit_holds hx h⟩
  | some j =>
    cases hjs : f.jumps with
    | none =>
      rw [hjs] at hall
      simp only [List.all_eq_true, List.mem_range] at hall
      have := hall j (Fn.idx?_some hj).2
      cases hC : Fn.annoAt anno j with
      | some C => rw [hC] at this; exact Or.inl ⟨j, C, hj, hC, AState.holds_of_le this h⟩
      | none => rw [hC] at this; cases this
    | some ts =>
      rw [hjs] at hall
      simp only [List.all_eq_true] at hall
      have := hall s.pc (hcfi ts hjs (by simp [hj]))
      rw [hj] at this
      dsimp only at this
      cases hC : Fn.annoAt anno j with
      | some C => rw [hC] at this; exact Or.inl ⟨j, C, hj, hC, AState.holds_of_le this h⟩
      | none => rw [hC] at this; cases this

theorem branch_exec {s : MachineState} {ins : Instr} {off : BitVec 13}
    (h : branchOff? ins = some off) :
    execInstrBr s ins = s.setPC (s.pc + 4) ∨ execInstrBr s ins = s.setPC (s.pc + signExtend13 off) := by
  cases ins <;> simp only [branchOff?, Option.some.injEq, reduceCtorEq] at h <;> subst h <;>
    simp only [execInstrBr] <;> split <;> simp

theorem transfer_some_plain {pc : Word} {A : AState} {i : Instr} {o : Out}
    (h : transfer pc A i = some o) : i ≠ .ECALL ∧ i ≠ .EBREAK ∧ ∀ c r, i ≠ .CSRS c r := by
  refine ⟨?_, ?_, fun c r => ?_⟩ <;> (rintro rfl; simp [transfer, aluResult, loadOf, storeOf] at h)

/-! ## One checked step -/

theorem Fn.step_of_instrAt {f : Fn} {i : Nat} {A : AState} {ins : Instr}
    (h : f.instrAt? i = some ins) : f.step i A = f.stepAt (f.pcOf i) (some ins) A := by
  simp only [Fn.instrAt?, Option.join_eq_some_iff] at h
  simp [Fn.step, h]

/-- The premises over the entry registers, for every reachable instruction. -/
def ReqOk (f : Fn) (anno : Array (Option AState)) (E : Ent) : Prop :=
  ∀ i A st, Fn.annoAt anno i = some A → f.step i A = some st → ∀ q ∈ st.reqs, q.Holds E

/-- The residual premise at one state: a store through an unknown pointer does not rewrite
    a saved return address. -/
def ResOk (f : Fn) (anno : Array (Option AState)) (E : Ent) (s : MachineState) : Prop :=
  ∀ i A st ins, f.idx? s.pc = some i → Fn.annoAt anno i = some A → f.step i A = some st →
    f.instrAt? i = some ins → st.residual ≠ [] →
    ∀ p ∈ A.slots, protects p = true → storeTarget s ins ≠ E .x2 + p.1

/-- An indirect jump: `jalr zero` through a register, other than `ret`. -/
def IsIndirect (ins : Instr) : Prop := ∃ rs off, ins = .JALR .x0 rs off ∧ ¬ (rs = .x1 ∧ off = 0)

/-- The control-flow premise at one state: an indirect jump in `f` lands outside `f`, or
    on one of `f.jumps`. Vacuous when `f.jumps = none`. -/
def CfiOk (f : Fn) (s : MachineState) : Prop :=
  ∀ ts, f.jumps = some ts → ∀ i ins s', f.idx? s.pc = some i → f.instrAt? i = some ins →
    IsIndirect ins → stepSp1 s = some s' → (f.idx? s'.pc).isSome → s'.pc ∈ ts

theorem cfiOk_none {f : Fn} (h : f.jumps = none) (s : MachineState) : CfiOk f s := by
  intro ts hts; rw [h] at hts; cases hts

theorem instrOk_of_valid {f : Fn} {anno} {i : Nat} (hv : f.valid anno = true)
    (hi : i < f.prog.length) : f.instrOk anno i = true := by
  simp only [Fn.valid, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hv
  exact hv.2 i hi

theorem step_sound {f : Fn} {anno} {E} {s s' : MachineState} {i : Nat} {A : AState} {ins : Instr}
    (hv : f.valid anno = true) (hreq : ReqOk f anno E) (hres : ResOk f anno E s)
    (hcfi : CfiOk f s)
    (hi : f.idx? s.pc = some i) (hA : Fn.annoAt anno i = some A) (h : A.Holds E s)
    (hc : CodeOk f s) (hins : f.instrAt? i = some ins)
    (hnc : ¬ IsCall ins) (hno : ¬ IsOutlined ins) (hnr : ins ≠ .JALR .x0 .x1 0)
    (hst : stepSp1 s = some s') : Lands f anno E s' ∧ s'.code = s.code := by
  have hpc := (Fn.idx?_some hi).1
  have hfetch : s.code s.pc = some ins := by rw [hpc]; exact hc.1 i ins hins
  have hok := instrOk_of_valid hv (Fn.idx?_some hi).2
  unfold Fn.instrOk at hok
  simp only [hA] at hok
  cases hstp : f.step i A with
  | none => rw [hstp] at hok; cases hok
  | some st =>
  rw [hstp] at hok
  simp only [List.all_eq_true] at hok
  have hreq' := hreq i A st hA hstp
  have hres' := hres i A st ins hi hA hstp hins
  rw [Fn.step_of_instrAt hins] at hstp
  unfold Fn.stepAt at hstp
  simp only at hstp
  rw [← hpc] at hstp
  split at hstp
  · -- A conditional branch.
    rename_i off hb
    cases hstp
    have hex := stepSp1_exec hfetch (by rintro rfl; simp [branchOff?] at hb)
      (by rintro rfl; simp [branchOff?] at hb) (by rintro c r rfl; simp [branchOff?] at hb) hst
    subst hex
    refine ⟨?_, by simp⟩
    rcases branch_exec (s := s) hb with he | he <;> rw [he]
    · exact target_sound (fun e he' => hok e (List.mem_append_left _ he'))
        (AState.holds_setPC h) rfl
    · exact target_sound (fun e he' => hok e (List.mem_append_right _ he'))
        (AState.holds_setPC h) rfl
  · split at hstp
    · -- `jal rd, off`
      rename_i rd off _
      have hex := stepSp1_exec hfetch (by simp) (by simp) (by simp) hst
      subst hex
      refine ⟨?_, by simp⟩
      split at hstp
      · rename_i h0; subst h0; cases hstp
        simp only [execInstrBr, setReg_x0]
        exact target_sound hok (AState.holds_setPC h) rfl
      · split at hstp
        · rename_i h1; subst h1; exact absurd (Or.inl ⟨off, rfl⟩) hnc
        · cases hstp
    · -- `jalr rd, off(rs)`
      rename_i rd rs off _
      have hex := stepSp1_exec hfetch (by simp) (by simp) (by simp) hst
      subst hex
      refine ⟨?_, by simp⟩
      split at hstp
      · rename_i h0; subst h0
        split at hstp
        · rename_i hr; obtain ⟨rfl, rfl⟩ := hr; exact absurd rfl hnr
        · simp only [execInstrBr, setReg_x0]
          have hrs := h.1 rs
          split at hstp
          · rename_i c hc'
            cases hstp
            rw [hc'] at hrs; simp only [AVal.Holds] at hrs
            exact target_sound hok (AState.holds_setPC h) (by rw [hrs]; rfl)
          · cases hstp
            exact anywhere_sound (hok _ (List.mem_singleton_self _)) (AState.holds_setPC h)
              (fun ts hts hin => hcfi ts hts i _ _ hi hins
                ⟨rs, off, rfl, by rintro ⟨rfl, rfl⟩; exact hnr rfl⟩ hst hin)
      · split at hstp
        · rename_i h1; subst h1; exact absurd (Or.inr ⟨rs, off, rfl⟩) hnc
        · split at hstp
          · rename_i h5; obtain ⟨rfl, rfl⟩ := h5; exact absurd ⟨off, rfl⟩ hno
          · cases hstp
    · -- A straight-line instruction.
      cases ht : transfer s.pc A ins with
      | none => rw [ht] at hstp; cases hstp
      | some o =>
        rw [ht] at hstp
        cases hstp
        obtain ⟨he, hb, hcs⟩ := transfer_some_plain ht
        have hex := stepSp1_exec hfetch he hb hcs hst
        subst hex
        obtain ⟨hH, hp⟩ := transfer_sound rfl h ht hreq' (fun hne => hres' hne)
        exact ⟨target_sound hok hH hp, by simp⟩

/-! ## `ret`, calls, outlined fragments -/

/-- The checked edges of a reachable instruction. -/
theorem edges_ok {f : Fn} {anno} {i : Nat} {A : AState} {st : Step}
    (hv : f.valid anno = true) (hi : i < f.prog.length) (hA : Fn.annoAt anno i = some A)
    (hstp : f.step i A = some st) : ∀ e ∈ st.edges, f.edgeOk anno e = true := by
  have hok := instrOk_of_valid hv hi
  unfold Fn.instrOk at hok
  simp only [hA, hstp, List.all_eq_true] at hok
  exact hok

theorem ret_sound {f : Fn} {anno} {E} {s s' : MachineState} {i : Nat} {A : AState}
    (hv : f.valid anno = true) (hi : f.idx? s.pc = some i) (hA : Fn.annoAt anno i = some A)
    (h : A.Holds E s) (hc : CodeOk f s) (hins : f.instrAt? i = some (.JALR .x0 .x1 0))
    (hst : stepSp1 s = some s') : s'.getReg .x1 = E .x1 ∧ s'.getReg .x2 = E .x2 := by
  have hpc := (Fn.idx?_some hi).1
  have hfetch : s.code s.pc = some (.JALR .x0 .x1 0) := by rw [hpc]; exact hc.1 i _ hins
  have hstp : f.step i A = some { edges := [.exit A] } := by
    rw [Fn.step_of_instrAt hins]; simp [Fn.stepAt, branchOff?]
  have hok := edges_ok hv (Fn.idx?_some hi).2 hA hstp (.exit A) (List.mem_singleton_self _)
  have hex := stepSp1_exec hfetch (by simp) (by simp) (by simp) hst
  subst hex
  simp only [execInstrBr, setReg_x0, MachineState.getReg_setPC]
  exact okExit_holds hok h

theorem afterCall_holds {E} {A : AState} {s s' : MachineState} (h : A.Holds E s)
    (hret : CallRet E A s s') : A.afterCall.Holds E s' := by
  obtain ⟨_, _, hregs, hmem⟩ := hret
  refine ⟨fun r => ?_, fun p hp => ?_⟩
  · by_cases h0 : r = .x0
    · subst h0; simp [AState.get, AVal.Holds, MachineState.getReg]
    · simp only [AState.get, h0, ite_false, AState.afterCall, getD_map_allRegs]
      split
      · rename_i hcs; rw [hregs r hcs]; have := h.1 r; simpa [AState.get, h0] using this
      · trivial
  · simp only [AState.afterCall, List.mem_filter] at hp
    rw [hmem p hp.1 hp.2]; exact h.2 p hp.1

theorem call_step {f : Fn} {i : Nat} {A : AState} {ins : Instr}
    (hins : f.instrAt? i = some ins) (hcall : IsCall ins) :
    f.step i A = some (f.callStep (f.pcOf i) A) := by
  rw [Fn.step_of_instrAt hins]
  rcases hcall with ⟨off, rfl⟩ | ⟨rs, off, rfl⟩ <;> simp [Fn.stepAt, branchOff?]

def Inv (f : Fn) (anno : Array (Option AState)) (E : Ent) (s : MachineState) : Prop :=
  ∃ i A, f.idx? s.pc = some i ∧ Fn.annoAt anno i = some A ∧ A.Holds E s ∧ CodeOk f s

theorem call_sound {f : Fn} {anno} {E} {s s' : MachineState} {i : Nat} {A : AState} {ins : Instr}
    (hv : f.valid anno = true) (hi : f.idx? s.pc = some i) (hA : Fn.annoAt anno i = some A)
    (h : A.Holds E s) (hc : CodeOk f s) (hins : f.instrAt? i = some ins) (hcall : IsCall ins)
    (hin : (f.idx? (s.pc + 4)).isSome) (hret : CallRet E A s s') : Inv f anno E s' := by
  have hpc := (Fn.idx?_some hi).1
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp hin
  have hstp := call_step (A := A) hins hcall
  have hok := edges_ok hv (Fn.idx?_some hi).2 hA hstp
  rw [← hpc] at hok
  simp only [Fn.callStep, hj, List.mem_singleton, forall_eq, Fn.edgeOk] at hok
  cases hC : Fn.annoAt anno j with
  | none => rw [hC] at hok; cases hok
  | some C =>
    rw [hC] at hok
    refine ⟨j, C, by rw [hret.1]; exact hj, hC,
      AState.holds_of_le hok (afterCall_holds h hret), hc.of_code hret.2.1⟩

theorem ofNat_four_mul_succ (n : Nat) :
    BitVec.ofNat 64 (4 * (n + 1)) = BitVec.ofNat 64 (4 * n) + 4 := by
  rw [Nat.mul_succ, BitVec.ofNat_add]; rfl

/-- An outlined fragment, executed for real from instruction `n` to its closing
    `jalr zero, 0(t0)`, ends in the state `runFrag` computed. -/
theorem runFrag_sound {E} {fb : Word} :
    ∀ (fp : List (Option Instr)) (n : Nat) {A B : AState} {k : Nat} {s s' : MachineState},
    runFrag A fb fp n = some B → fragLen fp = some k →
    (∀ m ins, fp[m]? = some (some ins) → s.code (fb + BitVec.ofNat 64 (4 * (n + m))) = some ins) →
    s.pc = fb + BitVec.ofNat 64 (4 * n) → A.Holds E s →
    stepsSp1 (k + 1) s = some s' →
    B.Holds E s' ∧ s'.code = s.code ∧ s'.pc = s'.getReg .x5 &&& ~~~1#64
  | [], _, _, _, _, _, _, hr, _, _, _, _, _ => by simp [runFrag] at hr
  | none :: _, _, _, _, _, _, _, hr, _, _, _, _, _ => by simp [runFrag] at hr
  | some i :: rest, n, A, B, k, s, s', hr, hk, hcode, hpc, h, hsteps => by
    have hfetch : s.code s.pc = some i := by
      rw [hpc]; simpa using hcode 0 i rfl
    by_cases hj : i = .JALR .x0 .x5 0
    · subst hj
      simp only [runFrag, ite_true, Option.some.injEq] at hr; subst hr
      simp only [fragLen, ite_true, Option.some.injEq] at hk; subst hk
      obtain ⟨s1, hs1, hrest⟩ := stepsSp1_succ hsteps
      simp only [stepsSp1_zero, Option.some.injEq] at hrest; subst hrest
      have hex := stepSp1_exec hfetch (by simp) (by simp) (by simp) hs1
      subst hex
      refine ⟨?_, by simp, ?_⟩
      · simp only [execInstrBr, setReg_x0]; exact AState.holds_setPC h
      · simp [execInstrBr, setReg_x0, signExtend12] <;> rfl
    · simp only [runFrag, hj, ite_false] at hr
      cases ht : transfer (fb + BitVec.ofNat 64 (4 * n)) A i with
      | none => rw [ht] at hr; cases hr
      | some o =>
        rw [ht] at hr
        simp only [Bool.and_eq_true, List.isEmpty_iff] at hr
        split at hr
        · rename_i hemp
          simp only [fragLen, hj, ite_false] at hk
          cases hk' : fragLen rest with
          | none => rw [hk'] at hk; cases hk
          | some k' =>
            rw [hk'] at hk; simp only [Option.map_some, Option.some.injEq] at hk; subst hk
            obtain ⟨s1, hs1, hrest⟩ := stepsSp1_succ hsteps
            obtain ⟨he, hb, hcs⟩ := transfer_some_plain ht
            have hex := stepSp1_exec hfetch he hb hcs hs1
            subst hex
            obtain ⟨hH, hp⟩ := transfer_sound hpc h ht (by simp [hemp.1]) (by simp [hemp.2])
            have ih := runFrag_sound rest (n + 1) hr hk'
              (fun m ins hm => by
                have := hcode (m + 1) ins (by simpa using hm)
                rw [show n + (m + 1) = n + 1 + m by omega] at this
                simpa using this)
              (by rw [hp, hpc, ofNat_four_mul_succ, BitVec.add_assoc]) hH hrest
            exact ⟨ih.1, by rw [ih.2.1]; simp, ih.2.2⟩
        · cases hr

theorem outlined_sound {f : Fn} {anno} {E} {s s' : MachineState} {i k : Nat} {A : AState}
    {off : BitVec 12} {fp : List (Option Instr)}
    (hv : f.valid anno = true) (hi : f.idx? s.pc = some i) (hA : Fn.annoAt anno i = some A)
    (h : A.Holds E s) (hc : CodeOk f s) (hins : f.instrAt? i = some (.JALR .x5 .x5 off))
    (hfp : f.frags.lookup ((s.getReg .x5 + signExtend12 off) &&& ~~~1#64) = some fp)
    (hk : fragLen fp = some k) (hsteps : stepsSp1 (k + 2) s = some s') : Inv f anno E s' := by
  have hpc := (Fn.idx?_some hi).1
  have hfetch : s.code s.pc = some (.JALR .x5 .x5 off) := by rw [hpc]; exact hc.1 i _ hins
  have hstp0 : f.step i A = f.outlinedStep (f.pcOf i) A off := by
    rw [Fn.step_of_instrAt hins]; simp [Fn.stepAt, branchOff?]
  have hok0 := instrOk_of_valid hv (Fn.idx?_some hi).2
  unfold Fn.instrOk at hok0
  simp only [hA, hstp0] at hok0
  rw [← hpc] at hok0
  unfold Fn.outlinedStep at hok0
  have h5 := h.1 .x5
  cases hx5 : A.get .x5 with
  | lin r k0 => rw [hx5] at hok0; cases hok0
  | top => rw [hx5] at hok0; cases hok0
  | oneOf => rw [hx5] at hok0; cases hok0
  | cell => rw [hx5] at hok0; cases hok0
  | sym => rw [hx5] at hok0; cases hok0
  | const c =>
    rw [hx5] at hok0 h5
    simp only [AVal.Holds] at h5
    rw [h5] at hfp
    simp only [hfp] at hok0
    cases hj : f.idx? (s.pc + 4) with
    | none => simp only [hj] at hok0; cases hok0
    | some j =>
      simp only [hj] at hok0
      cases hB : runFrag (A.set .x5 (.const (s.pc + 4))) ((c + signExtend12 off) &&& ~~~1#64) fp 0 with
      | none => simp only [hB] at hok0; cases hok0
      | some B =>
        simp only [hB] at hok0
        by_cases hcond : B.get .x5 = .const (s.pc + 4) ∧ (s.pc + 4) &&& ~~~1#64 = s.pc + 4
        · simp only [hcond, and_self, ite_true, List.all_cons, List.all_nil, Bool.and_true,
            Fn.edgeOk] at hok0
          cases hC : Fn.annoAt anno j with
          | none => rw [hC] at hok0; cases hok0
          | some C =>
            rw [hC] at hok0
            obtain ⟨s1, hs1, hrest⟩ := stepsSp1_succ hsteps
            have hex := stepSp1_exec hfetch (by simp) (by simp) (by simp) hs1
            subst hex
            have hH1 : (A.set .x5 (.const (s.pc + 4))).Holds E
                (execInstrBr s (.JALR .x5 .x5 off)) := by
              simp only [execInstrBr]
              exact AState.holds_setPC (AState.holds_set h rfl)
            have hpc1 : (execInstrBr s (.JALR .x5 .x5 off)).pc =
                ((c + signExtend12 off) &&& ~~~1#64) + BitVec.ofNat 64 (4 * 0) := by
              have : (execInstrBr s (.JALR .x5 .x5 off)).pc =
                  (s.getReg .x5 + signExtend12 off) &&& ~~~1#64 := rfl
              rw [this, h5]; simp
            obtain ⟨hHB, hcode', hpc'⟩ := runFrag_sound fp 0 hB hk
              (fun m ins hm => by
                have := hc.2 _ fp hfp m ins hm
                simpa [execInstrBr] using this)
              hpc1 hH1 hrest
            have hx5' := hHB.1 .x5
            rw [hcond.1] at hx5'
            simp only [AVal.Holds] at hx5'
            have hpcs : s'.pc = s.pc + 4 := by rw [hpc', hx5', hcond.2]
            refine ⟨j, C, by rw [hpcs]; exact hj, hC, AState.holds_of_le hok0 hHB,
              hc.of_code (by rw [hcode']; simp [execInstrBr])⟩
        · exfalso
          split at hok0 <;> simp_all

/-! ## The run theorem -/

theorem entry_inv {f : Fn} {anno} {E} {s0 : MachineState} (hv : f.valid anno = true)
    (hne : 0 < f.prog.length) (hpc : s0.pc = f.base) (hE : ∀ r, r ≠ .x0 → s0.getReg r = E r)
    (hc : CodeOk f s0) : Inv f anno E s0 := by
  have hv0 := hv
  simp only [Fn.valid, Bool.and_eq_true] at hv0
  cases hA : Fn.annoAt anno 0 with
  | none => rw [hA] at hv0; simp at hv0
  | some A =>
    rw [hA] at hv0
    refine ⟨0, A, ?_, hA, AState.holds_of_le hv0.1 (AState.holds_entry hE), hc⟩
    simp [Fn.idx?, hpc, hne]

theorem run_inv {f : Fn} {anno} {E} {s0 : MachineState} (hv : f.valid anno = true)
    (hreq : ReqOk f anno E) (hres : ∀ s, Run f anno E s0 s → ResOk f anno E s)
    (hcfi : ∀ s, Run f anno E s0 s → CfiOk f s)
    (h0 : Inv f anno E s0) : ∀ s, Run f anno E s0 s → Inv f anno E s := by
  intro s hr
  induction hr with
  | start => exact h0
  | step hr hi hins hnc hno hnr hst hin ih =>
    obtain ⟨i', A, hi', hA, hH, hc⟩ := ih
    rw [hi] at hi'; cases hi'
    obtain ⟨hl, hcode⟩ := step_sound hv hreq (hres _ hr) (hcfi _ hr) hi hA hH hc hins hnc hno hnr hst
    rcases hl with ⟨j, C, hj, hC, hHC⟩ | ⟨hn, _⟩
    · exact ⟨j, C, hj, hC, hHC, hc.of_code hcode⟩
    · rw [hn] at hin; cases hin
  | call hr hi hins hcall hA hin hret ih =>
    obtain ⟨i', A', hi', hA', hH, hc⟩ := ih
    rw [hi] at hi'; cases hi'
    rw [hA] at hA'; cases hA'
    exact call_sound hv hi hA hH hc hins hcall hin hret
  | outlined hr hi hins hfp hk hsteps ih =>
    obtain ⟨i', A, hi', hA, hH, hc⟩ := ih
    rw [hi] at hi'; cases hi'
    exact outlined_sound hv hi hA hH hc hins hfp hk hsteps

/-- **Return-address integrity.** Along any run of one activation of `f`, a step that
    leaves the function -- a `ret`, or any other non-call step whose target lies outside
    `f` -- ends with `ra` and `sp` at their entry values.

    It rests on: the checker accepting (`hv`); the premises over the entry registers
    (`hreq`); the residual premise at stores through unknown pointers (`hres`); the
    control-flow premise at indirect jumps (`hcfi`, vacuous unless `f.jumps` is given); and,
    inside `Run`, the call contract `CallRet` for every call whose return address is in `f`. -/
theorem integrity {f : Fn} {anno} {E} {s0 : MachineState} (hv : f.valid anno = true)
    (hreq : ReqOk f anno E) (hres : ∀ s, Run f anno E s0 s → ResOk f anno E s)
    (hcfi : ∀ s, Run f anno E s0 s → CfiOk f s)
    (h0 : Inv f anno E s0) {s s' : MachineState} (hr : Run f anno E s0 s) {i : Nat} {ins : Instr}
    (hi : f.idx? s.pc = some i) (hins : f.instrAt? i = some ins)
    (hleave : ins = .JALR .x0 .x1 0 ∨ (¬ IsCall ins ∧ ¬ IsOutlined ins ∧ f.idx? s'.pc = none))
    (hst : stepSp1 s = some s') : s'.getReg .x1 = E .x1 ∧ s'.getReg .x2 = E .x2 := by
  obtain ⟨i', A, hi', hA, hH, hc⟩ := run_inv hv hreq hres hcfi h0 s hr
  rw [hi] at hi'; cases hi'
  rcases hleave with rfl | ⟨hnc, hno, hout⟩
  · exact ret_sound hv hi hA hH hc hins hst
  · by_cases hnr : ins = .JALR .x0 .x1 0
    · subst hnr; exact ret_sound hv hi hA hH hc hins hst
    · obtain ⟨hl, _⟩ := step_sound hv hreq (hres _ hr) (hcfi _ hr) hi hA hH hc hins hnc hno hnr hst
      rcases hl with ⟨j, _, hj, _⟩ | ⟨_, h1, h2⟩
      · rw [hout] at hj; cases hj
      · exact ⟨h1, h2⟩

/-! ## The one-pass check implies the indexed one -/

theorem Fn.annoAt_eq (anno : Array (Option AState)) (i : Nat) :
    Fn.annoAt anno i = (anno.toList[i]?).join := by
  simp [Fn.annoAt]

theorem Fn.edgeOkAt_eq {f : Fn} {anno : Array (Option AState)} {i : Nat} {e : Edge}
    (hsize : anno.size = f.prog.length) :
    f.edgeOkAt anno i (anno.toList[i + 1]?) e = f.edgeOk anno e := by
  cases e with
  | goto j B =>
    simp only [Fn.edgeOkAt]
    split
    · rename_i hj; subst hj
      simp only [Fn.edgeOk, Fn.annoAt_eq]
      cases anno.toList[i + 1]? with
      | none => rfl
      | some x => cases x <;> rfl
    · rfl
  | exit B => rfl
  | anywhere B =>
    cases hjs : f.jumps with
    | some ts =>
      simp only [Fn.edgeOkAt, Fn.edgeOk, hjs]
      cases okExit B <;> rfl
    | none =>
    simp only [Fn.edgeOkAt, Fn.edgeOk, hjs]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [List.all_eq_true, List.mem_range, Fn.annoAt_eq]
    constructor
    · intro h j hj
      have hj' : j < anno.toList.length := by simpa [hsize] using hj
      rw [List.getElem?_eq_getElem hj']
      exact h _ (List.getElem_mem hj')
    · intro h x hx
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      have := h j (by simpa [hsize] using hj)
      rwa [List.getElem?_eq_getElem hj] at this

theorem Fn.walk_sound {f : Fn} {anno : Array (Option AState)}
    (hsize : anno.size = f.prog.length) :
    ∀ (ps : List (Option Instr)) (as : List (Option AState)) (i : Nat),
      f.walk anno i ps as = true → ps = f.prog.drop i → as = anno.toList.drop i →
      ∀ k, i ≤ k → k < f.prog.length → f.instrOk anno k = true
  | [], _, i, _, hps, _, k, hik, hk => by
    have : f.prog.length ≤ i := by simpa using hps.symm
    omega
  | _ :: _, [], i, _, hps, has, k, hik, hk => by
    have h1 : anno.toList.length ≤ i := by simpa using has.symm
    have h2 : i < f.prog.length := by
      have := congrArg List.length hps; simp at this; omega
    simp at h1; omega
  | oi :: ps, a :: as, i, hw, hps, has, k, hik, hk => by
    simp only [Fn.walk, Bool.and_eq_true] at hw
    have hpi : f.prog[i]? = some oi := by
      have := congrArg (·[0]?) hps; simpa using this.symm
    have hai : anno.toList[i]? = some a := by
      have := congrArg (·[0]?) has; simpa using this.symm
    have hps' : ps = f.prog.drop (i + 1) := by
      have := congrArg List.tail hps; simpa [List.tail_drop] using this
    have has' : as = anno.toList.drop (i + 1) := by
      have := congrArg List.tail has; simpa [List.tail_drop] using this
    rcases Nat.eq_or_lt_of_le hik with rfl | hlt
    · unfold Fn.instrOk
      rw [Fn.annoAt_eq, hai]
      have hnext : as.head? = anno.toList[i + 1]? := by
        rw [has']; simp
      cases a with
      | none => rfl
      | some A =>
        have hw1 := hw.1
        simp only [Option.join] at hw1 ⊢
        simp only [Fn.step, hpi]
        cases hst : f.stepAt (f.pcOf i) oi A with
        | none => rw [hst] at hw1; cases hw1
        | some st =>
          rw [hst] at hw1
          simp only [List.all_eq_true] at hw1
          simp only [Option.bind_some, id_eq, hst, List.all_eq_true]
          intro e he
          have := hw1 e he
          rwa [hnext, Fn.edgeOkAt_eq hsize] at this
    · exact Fn.walk_sound hsize ps as (i + 1) hw.2 hps' has' k hlt hk

/-- **The one-pass check suffices.** -/
theorem Fn.validFast_sound {f : Fn} {anno : Array (Option AState)}
    (h : f.validFast anno = true) : f.valid anno = true := by
  simp only [Fn.validFast, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h0, hsize⟩, hw⟩ := h
  simp only [Fn.valid, Bool.and_eq_true, List.all_eq_true, List.mem_range]
  exact ⟨h0, fun k hk => Fn.walk_sound hsize _ _ 0 hw (by simp) (by simp) k (Nat.zero_le _) hk⟩

/-! ## From the report to the premises -/

theorem step_lt {f : Fn} {i : Nat} {A : AState} {st : Step} (h : f.step i A = some st) :
    i < f.prog.length := by
  unfold Fn.step at h
  cases hi : f.prog[i]? with
  | none => rw [hi] at h; cases h
  | some _ => exact (List.getElem?_eq_some_iff.mp hi).1

theorem mem_collectFrom {f : Fn} {g : Step → List α} :
    ∀ (ps : List (Option Instr)) (as : List (Option AState)) (i : Nat) {k : Nat} {A : AState}
      {oi : Option Instr} {st : Step} {x : α},
      ps[k - i]? = some oi → as[k - i]? = some (some A) → i ≤ k →
      f.stepAt (f.pcOf k) oi A = some st → x ∈ g st → x ∈ f.collectFrom g i ps as
  | [], _, _, _, _, _, _, _, hp, _, _, _, _ => by simp at hp
  | _ :: _, [], _, _, _, _, _, _, _, ha, _, _, _ => by simp at ha
  | oi' :: ps, a :: as, i, k, A, oi, st, x, hp, ha, hik, hst, hx => by
    simp only [Fn.collectFrom, List.mem_append]
    rcases Nat.eq_or_lt_of_le hik with rfl | hlt
    · simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at hp ha
      subst hp; subst ha
      left; simp only [hst]; exact hx
    · right
      refine mem_collectFrom ps as (i + 1) ?_ ?_ hlt hst hx
      · have : k - i = (k - (i + 1)) + 1 := by omega
        rw [this] at hp; simpa using hp
      · have : k - i = (k - (i + 1)) + 1 := by omega
        rw [this] at ha; simpa using ha

theorem mem_collect {f : Fn} {anno} {g : Step → List α} {i : Nat} {A : AState} {st : Step}
    (hA : Fn.annoAt anno i = some A) (hst : f.step i A = some st) {x : α} (hx : x ∈ g st) :
    x ∈ f.collect anno g := by
  unfold Fn.step at hst
  cases hp : f.prog[i]? with
  | none => rw [hp] at hst; cases hst
  | some oi =>
    rw [hp] at hst
    rw [Fn.annoAt_eq] at hA
    have ha : anno.toList[i]? = some (some A) := by
      cases h : anno.toList[i]? with
      | none => rw [h] at hA; cases hA
      | some y => rw [h] at hA; cases y <;> simp_all
    exact mem_collectFrom f.prog anno.toList 0 (by simpa using hp) (by simpa using ha)
      (Nat.zero_le _) hst hx

/-- The premises over the entry registers are exactly the report's `reqs`. -/
theorem reqOk_of_report {f : Fn} {anno} {E} (h : ∀ q ∈ f.collect anno (·.reqs), q.Holds E) :
    ReqOk f anno E :=
  fun _ _ _ hA hst q hq => h q (mem_collect hA hst hq)

/-- With no residual in the report, the residual premise holds of every state. -/
theorem resOk_of_report {f : Fn} {anno} {E} (h : f.collect anno (·.residual) = [])
    (s : MachineState) : ResOk f anno E s := by
  intro i A st ins _ hA hst _ hne
  exfalso
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ hne
  have := mem_collect (g := (·.residual)) hA hst hx
  rw [h] at this; cases this

end MachineChecked.RiscV.Frame
