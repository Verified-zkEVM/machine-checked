/-
  MachineChecked.RiscV.Check.Ecall

  What `ecall` does under `stepSp1`, in the shape the checker's soundness needs: for each
  class `sysStep` distinguishes, either no successor (and not accepting), or a successor
  at `pc + 4` with the same code, the registers other than `t0` unchanged, and memory
  unchanged outside the items `sysStep` lists.
-/

import MachineChecked.RiscV.Check.Spec

namespace MachineChecked.RiscV.Check

open RiscvZkvm.Rv64 MachineChecked.RiscV.Frame

/-! ## Writing doublewords -/

theorem getMem_writeBytesAsWords_of :
    ∀ (bs : List (BitVec 8)) {s : MachineState} {base a : Word},
      (∀ i, 8 * i < bs.length → a ≠ base + BitVec.ofNat 64 (8 * i)) →
      (s.writeBytesAsWords base bs).getMem a = s.getMem a
  | [], _, _, _, _ => by simp
  | b :: bs', s, base, a, ha => by
    rw [MachineState.writeBytesAsWords]
    rw [getMem_writeBytesAsWords_of ((b :: bs').drop 8)
      (fun i hi => by
        have := ha (i + 1) (by simp at hi ⊢; omega)
        rw [show 8 * (i + 1) = 8 * i + 8 by omega, BitVec.ofNat_add] at this
        intro he; apply this; rw [he, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 (8 * i))]; rfl)]
    rw [getMem_setMem, ite_eq_right (by simpa using ha 0 (by simp))]
termination_by bs => bs.length
decreasing_by simp; omega

theorem regs_writeBytesAsWords :
    ∀ (bs : List (BitVec 8)) {s : MachineState} {base : Word}, (s.writeBytesAsWords base bs).regs = s.regs
  | [], _, _ => by simp
  | b :: bs', s, base => by
    rw [MachineState.writeBytesAsWords, regs_writeBytesAsWords ((b :: bs').drop 8)]
    rfl
termination_by bs => bs.length
decreasing_by simp; omega

/-- A key `base + 8 i` with `8 i < l` is hit by `[base, base + l)`. -/
theorem hits_dword {base : Word} {l i : Nat} (hi : 8 * i < l) (hl : l < 2 ^ 64) :
    Hits base l (base + BitVec.ofNat 64 (8 * i)) := by
  left
  have : base + BitVec.ofNat 64 (8 * i) - base = BitVec.ofNat 64 (8 * i) := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel]
  rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hi

/-! ## The precompiles -/

theorem accel_payload {s : MachineState} {t : Word} {L : Nat} (hL : accelLen t = some L) :
    (s.sp1AccelWrite t).1 = s.getReg .x10 ∧ (s.sp1AccelWrite t).2.length = L := by
  unfold accelLen at hL
  split at hL
  · rename_i h
    cases hL
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [MachineState.sp1AccelWrite, Sp1.SECP256K1_ADD, Sp1.SECP256K1_DOUBLE, Sp1.PALLAS_ADD,
        Sp1.PALLAS_DOUBLE, Sp1.BN254_ADD, Sp1.BN254_DOUBLE, Sp1.BN254_FP2_ADD, Sp1.BN254_FP2_SUB,
        Sp1.BN254_FP2_MUL, Sp1.KECCAK_PERMUTE, Sp1.BLS12381_ADD, Sp1.BLS12381_DOUBLE,
        Sp1.BLS12381_FP2_ADD, Sp1.BLS12381_FP2_SUB, Sp1.BLS12381_FP2_MUL,
        Accel.curveAddL, Accel.curveDblL, Accel.complexAddL, Accel.complexSubL,
        Accel.complexMulL, Accel.natToLeLimbs]
  · split at hL
    · rename_i h
      cases hL
      rcases h with rfl | rfl | rfl | rfl | rfl <;>
        simp [MachineState.sp1AccelWrite, Sp1.SECP256K1_ADD, Sp1.SECP256K1_DOUBLE, Sp1.PALLAS_ADD,
          Sp1.PALLAS_DOUBLE, Sp1.BN254_ADD, Sp1.BN254_DOUBLE, Sp1.KECCAK_PERMUTE, Sp1.BLS12381_ADD,
          Sp1.BLS12381_DOUBLE, Sp1.BLS12381_FP2_ADD, Sp1.BLS12381_FP2_SUB, Sp1.BLS12381_FP2_MUL,
          Accel.curveAddL, Accel.curveDblL, Accel.complexAddL, Accel.complexSubL,
          Accel.complexMulL, Accel.natToLeLimbs]
    · split at hL
      · rename_i h
        cases hL; subst h
        simp [MachineState.sp1AccelWrite, Sp1.SECP256K1_ADD, Sp1.SECP256K1_DOUBLE, Sp1.PALLAS_ADD,
          Sp1.PALLAS_DOUBLE, Sp1.BN254_ADD, Sp1.BN254_DOUBLE, Sp1.BN254_FP2_ADD, Sp1.BN254_FP2_SUB,
          Sp1.BN254_FP2_MUL, Sp1.KECCAK_PERMUTE, Sp1.BLS12381_ADD, Sp1.BLS12381_DOUBLE,
          Sp1.BLS12381_FP2_ADD, Sp1.BLS12381_FP2_SUB, Sp1.BLS12381_FP2_MUL, Sp1.UINT256_MUL,
          Accel.natToLeLimbs]
      · cases hL

/-! ## The effect of one `ecall` -/

/-- A successor of an `ecall` that `sysStep` lets continue: at `pc + 4`, same code, the
    registers other than `t0` unchanged (and `t0` too, unless it is `HINT_LEN`), memory
    unchanged outside the listed byte ranges. -/
structure SysNext (x y : MachineState) (t0kept : Bool) (rs : List (Word × Nat)) : Prop where
  pc : y.pc = x.pc + 4
  code : y.code = x.code
  regs : ∀ r, r ≠ .x5 → y.getReg r = x.getReg r
  t0 : t0kept = true → y.getReg .x5 = x.getReg .x5
  mem : ∀ a, (∀ R ∈ rs, ¬ Hits R.1 R.2 a) → y.getMem a = x.getMem a

theorem stepSp1_ecall_fetch {s : MachineState} (h : s.code s.pc = some .ECALL) :
    stepSp1 s = sp1Ecall s := by
  simp [stepSp1, h]

theorem accelLen_le {t : Word} {L : Nat} (h : accelLen t = some L) : L ≤ 12 := by
  unfold accelLen at h
  split at h
  · cases h; decide
  · split at h
    · cases h; decide
    · split at h
      · cases h; decide
      · cases h

theorem sys_accel {x y : MachineState} {L : Nat} (hf : x.code x.pc = some .ECALL)
    (hid : Sp1.isAccelId (x.getReg .x5) = true) (hL : accelLen (x.getReg .x5) = some L)
    (hs : stepSp1 x = some y) : SysNext x y true [(x.getReg .x10, 8 * L)] := by
  cases hv : x.sp1AccelValid (x.getReg .x5) with
  | false => rw [stepSp1_accel_trap hf hid hv] at hs; cases hs
  | true =>
    rw [stepSp1_accel hf hid hv] at hs
    cases hs
    obtain ⟨h1, h2⟩ := accel_payload (s := x) hL
    have hL8 : 8 * L ≤ 96 := by have := accelLen_le hL; omega
    refine ⟨rfl, by simp [MachineState.execSp1Accel], fun r _ => by simp [MachineState.execSp1Accel],
      fun _ => by simp [MachineState.execSp1Accel], fun a ha => ?_⟩
    simp only [MachineState.execSp1Accel, MachineState.getMem_setPC]
    rw [h1]
    apply getMem_writeWords_of_ne
    intro i hi he
    have := ha _ (List.mem_singleton_self _)
    rw [he] at this
    exact this (hits_dword (by rw [h2] at hi; omega) (by omega))

theorem sys_hintLen {x y : MachineState} (hf : x.code x.pc = some .ECALL)
    (ht : x.getReg .x5 = Sp1.HINT_LEN) (hs : stepSp1 x = some y) : SysNext x y false [] := by
  rw [stepSp1_ecall_fetch hf] at hs
  have hacc : Sp1.isAccelId Sp1.HINT_LEN = false := by decide
  simp only [sp1Ecall, ht, hacc, Bool.false_eq_true, ite_false, ite_true, Option.some.injEq] at hs
  subst hs
  refine ⟨rfl, by simp [hintLen], fun r hr => ?_, (fun h => by cases h), fun a _ => by simp [hintLen]⟩
  simp only [hintLen, MachineState.getReg_setPC]
  rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]

theorem sys_hintRead {x y : MachineState} (hf : x.code x.pc = some .ECALL)
    (ht : x.getReg .x5 = Sp1.HINT_READ) (hs : stepSp1 x = some y) :
    SysNext x y true [(x.getReg .x10, (x.getReg .x11).toNat + 8)] := by
  rw [stepSp1_ecall_fetch hf] at hs
  have hacc : Sp1.isAccelId Sp1.HINT_READ = false := by decide
  have hne : Sp1.HINT_READ ≠ Sp1.HINT_LEN := by decide
  simp only [sp1Ecall, ht, hacc, hne, Bool.false_eq_true, ite_false, ite_true] at hs
  unfold hintRead at hs
  cases hn : frontHintLen x with
  | none => rw [hn] at hs; cases hs
  | some n =>
  rw [hn] at hs
  simp only [Bool.not_eq_true'] at hs
  split at hs
  · cases hs
  · rename_i hal
    split at hs
    · cases hs
    · rename_i hwin
      split at hs
      · cases hs
      · rename_i hlen
        split at hs
        · cases hs
        · simp only [Option.some.injEq] at hs
          subst hs
          have hw : (x.getReg .x10).toNat + 8 * (n / 8 + 1) ≤ SP1_MAX_MEMORY := by
            simp only [hintWindowOk, Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hwin
            exact hwin.1
          have hn' : (x.getReg .x11).toNat = n := by simpa using hlen
          have hbound : n + 8 < 2 ^ 64 := by simp [SP1_MAX_MEMORY] at hw; omega
          refine ⟨by simp [MachineState.setPC, MachineState.setMem],
            by simp [MachineState.setPC, MachineState.setMem],
            fun r _ => by
              simp [MachineState.getReg, MachineState.setPC, MachineState.setMem,
                regs_writeBytesAsWords],
            fun _ => by
              simp [MachineState.getReg, MachineState.setPC, MachineState.setMem,
                regs_writeBytesAsWords],
            fun a ha => ?_⟩
          have hR := ha _ (List.mem_singleton_self _)
          simp only at hR
          rw [hn'] at hR
          simp only [MachineState.getMem_setPC]
          show (MachineState.setMem _ _ _).getMem a = _
          rw [getMem_setMem, ite_eq_right ?_]
          · apply getMem_writeBytesAsWords_of
            intro i hi he
            apply hR; rw [he]
            apply hits_dword _ hbound
            have : (List.take n (List.drop 8 x.privateInput)).length ≤ n := by
              simp only [List.length_take]; exact Nat.min_le_left _ _
            omega
          · intro he; apply hR; rw [he]
            exact hits_dword (by omega) hbound

theorem sys_commit {x y : MachineState} (hf : x.code x.pc = some .ECALL)
    (ht : x.getReg .x5 = Sp1.COMMIT ∨ x.getReg .x5 = Sp1.COMMIT_DEFERRED_PROOFS)
    (hs : stepSp1 x = some y) : SysNext x y true [] := by
  rw [stepSp1_ecall_fetch hf] at hs
  rcases ht with ht | ht
  · have hacc : Sp1.isAccelId Sp1.COMMIT = false := by decide
    have h1 : Sp1.COMMIT ≠ Sp1.HINT_LEN := by decide
    have h2 : Sp1.COMMIT ≠ Sp1.HINT_READ := by decide
    simp only [sp1Ecall, ht, hacc, h1, h2, Bool.false_eq_true, ite_false, ite_true,
      Option.some.injEq] at hs
    subst hs
    exact ⟨rfl, rfl, fun r _ => by cases r <;> rfl, fun _ => rfl, fun a _ => rfl⟩
  · have hacc : Sp1.isAccelId Sp1.COMMIT_DEFERRED_PROOFS = false := by decide
    have h1 : Sp1.COMMIT_DEFERRED_PROOFS ≠ Sp1.HINT_LEN := by decide
    have h2 : Sp1.COMMIT_DEFERRED_PROOFS ≠ Sp1.HINT_READ := by decide
    have h3 : Sp1.COMMIT_DEFERRED_PROOFS ≠ Sp1.COMMIT := by decide
    simp only [sp1Ecall, ht, hacc, h1, h2, h3, Bool.false_eq_true, ite_false, ite_true,
      Option.some.injEq] at hs
    subst hs
    exact ⟨rfl, by simp, fun r _ => by simp, fun _ => by simp, fun a _ => by simp⟩

theorem sys_host {x : MachineState} (hf : x.code x.pc = some .ECALL)
    (hh : Sp1.isHostId (x.getReg .x5) = true) : stepSp1 x = step x :=
  stepSp1_ecall_host hf hh

theorem sys_write {x y : MachineState} (hf : x.code x.pc = some .ECALL) (ht : x.getReg .x5 = 2)
    (hs : stepSp1 x = some y) : SysNext x y true [] := by
  rw [sys_host hf (by rw [ht]; decide)] at hs
  simp only [step, hf, ht] at hs
  simp only [show ((2 : Word) == 0) = false by decide, Bool.false_eq_true, ite_false,
    show ((2 : Word) == 2) = true by decide, ite_true] at hs
  split at hs
  · split at hs
    · simp only [Option.some.injEq] at hs; subst hs
      exact ⟨rfl, rfl, fun r _ => by cases r <;> rfl, fun _ => rfl, fun a _ => rfl⟩
    · cases hs
  · simp only [Option.some.injEq] at hs; subst hs
    exact ⟨rfl, by simp, fun r _ => by simp, fun _ => by simp, fun a _ => by simp⟩

theorem sys_readInput {x y : MachineState} (hf : x.code x.pc = some .ECALL)
    (ht : x.getReg .x5 = 0xF2) (hs : stepSp1 x = some y) :
    SysNext x y true [(x.getReg .x10, 8), (x.getReg .x11, 8)] := by
  rw [sys_host hf (by rw [ht]; decide)] at hs
  simp only [step, hf, ht] at hs
  simp only [show ((0xF2 : Word) == 0) = false by decide, Bool.false_eq_true, ite_false,
    show ((0xF2 : Word) == 2) = false by decide, show ((0xF2 : Word) == 0x10) = false by decide,
    show ((0xF2 : Word) == 0xF2) = true by decide, ite_true] at hs
  split at hs
  · simp only [Option.some.injEq] at hs; subst hs
    refine ⟨rfl, by simp, fun r _ => by simp [getReg_setMem], fun _ => by simp [getReg_setMem],
      fun a ha => ?_⟩
    have h0 := ha _ (List.mem_cons_self ..)
    have h1 := ha _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    simp only at h0 h1
    simp only [MachineState.getMem_setPC]
    rw [getMem_setMem, ite_eq_right (fun he => h1 (by rw [he]; exact Or.inl (by simp))),
      getMem_setMem, ite_eq_right (fun he => h0 (by rw [he]; exact Or.inl (by simp)))]
  · cases hs

theorem sys_halt {x : MachineState} (hf : x.code x.pc = some .ECALL) (ht : x.getReg .x5 = 0)
    (ha0 : x.getReg .x10 ≠ 0) : stepSp1 x = none ∧ ¬ Accepted x :=
  ⟨stepSp1_halt hf ht, fun h => ha0 h.2.2⟩

theorem sys_trap {x : MachineState} (hf : x.code x.pc = some .ECALL)
    (hacc : Sp1.isAccelId (x.getReg .x5) = false) (h1 : x.getReg .x5 ≠ Sp1.HINT_LEN)
    (h2 : x.getReg .x5 ≠ Sp1.HINT_READ) (h3 : x.getReg .x5 ≠ Sp1.COMMIT)
    (h4 : x.getReg .x5 ≠ Sp1.COMMIT_DEFERRED_PROOFS) (h5 : x.getReg .x5 ≠ 0)
    (h6 : x.getReg .x5 ≠ 2) (h7 : x.getReg .x5 ≠ 0xF2) : stepSp1 x = none ∧ ¬ Accepted x := by
  refine ⟨stepSp1_ecall_unknown_trap hf hacc ?_ h3 h4 ?_, fun h => h5 h.2.1⟩
  · simp [Sp1.isHintId, h1, h2]
  · simp only [Sp1.isHostId, Bool.or_eq_false_iff, decide_eq_false_iff_not]
    exact ⟨⟨h5, h6⟩, h7⟩

/-! ## `sysStep` is sound -/

theorem holds_eval {E : Ent} {v : AVal} {w : Word} (h : v.Holds E w)
    (hv : v.isPtr = true) : v.eval E = w := by
  cases v with
  | lin r k => simp only [AVal.Holds] at h; simp [AVal.eval, h]
  | const c => simp only [AVal.Holds] at h; simp [AVal.eval, h]
  | top => simp [AVal.isPtr] at hv
  | oneOf _ => simp [AVal.isPtr] at hv
  | cell r ks k => simp only [AVal.Holds] at h; simp [AVal.eval, h]
  | sym i j k => simp only [AVal.Holds] at h; simp [AVal.eval, h]

theorem lenPlus_eval {E : Ent} {v : AVal} {w : Word} {c : Nat} {l : Len}
    (h : v.Holds E w) (hl : lenPlus v c = some l) : l.eval E = w.toNat + c := by
  cases v with
  | const n =>
    simp only [lenPlus, Option.some.injEq] at hl; subst hl
    simp only [AVal.Holds] at h; simp [Len.eval, h]
  | lin r k =>
    simp only [lenPlus] at hl
    split at hl
    · rename_i hk; subst hk
      simp only [Option.some.injEq] at hl; subst hl
      simp only [AVal.Holds] at h; simp [Len.eval, h]
    · cases hl
  | top => simp [lenPlus] at hl
  | oneOf _ => simp [lenPlus] at hl
  | cell _ _ _ => simp [lenPlus] at hl
  | sym _ _ _ => simp [lenPlus] at hl

/-- A value `nzVal` accepts is nonzero, whatever it denotes. -/
theorem nzVal_holds {σ : Iface} {E : Ent} (hnz : ∀ v ∈ σ.nz, v.eval E ≠ 0) {v : AVal}
    {w : Word} (h : v.Holds E w) (hok : nzVal σ v = true) : w ≠ 0 := by
  cases v with
  | const c => simp only [AVal.Holds] at h; subst h; simpa [nzVal] using hok
  | lin r k =>
    simp only [AVal.Holds] at h; subst h
    exact hnz _ (List.contains_iff_mem.mp hok)
  | top => simp [nzVal] at hok
  | oneOf cs =>
    simp only [AVal.Holds] at h
    simp only [nzVal, List.all_eq_true, bne_iff_ne, ne_eq] at hok
    exact hok w h
  | cell r ks k =>
    simp only [AVal.Holds] at h; subst h
    exact hnz _ (List.contains_iff_mem.mp hok)
  | sym _ _ _ => simp [nzVal] at hok

/-- What `sysStep` promises about an `ecall` in a state its abstract registers describe. -/
theorem sysStep_sound {σ : Iface} {E : Ent} {A : AState} {x : MachineState} {out : SysOut}
    (h : sysStep σ A = some out) (hr : ∀ r, (A.get r).Holds E (x.getReg r))
    (hnz : ∀ v ∈ σ.nz, v.eval E ≠ 0) (hf : x.code x.pc = some .ECALL) :
    (out = .stop → stepSp1 x = none ∧ ¬ Accepted x) ∧
    (∀ B its, out = .next B its → (∀ it ∈ its, it.base.isPtr = true) → ¬ Accepted x ∧
      ∀ y, stepSp1 x = some y →
      y.pc = x.pc + 4 ∧ y.code = x.code ∧ (∀ r, (B.get r).Holds E (y.getReg r)) ∧
      B.slots = A.slots ∧ ∀ a, (∀ it ∈ its, ¬ it.Hits E a) → y.getMem a = x.getMem a) := by
  unfold sysStep at h
  have h5 := hr .x5
  cases ht : A.get .x5 with
  | lin _ _ => rw [ht] at h; cases h
  | top => rw [ht] at h; cases h
  | oneOf _ => rw [ht] at h; cases h
  | cell _ _ _ => rw [ht] at h; cases h
  | sym _ _ _ => rw [ht] at h; cases h
  | const t =>
  rw [ht] at h h5
  simp only [AVal.Holds] at h5
  simp only at h
  -- A continuing class: from `SysNext` to the conclusion.
  have fin : ∀ (B : AState) (its : List Item) (kept : Bool) (rs : List (Word × Nat)),
      t ≠ 0 → (B = A ∨ (B = A.set .x5 .top ∧ kept = false)) → (B = A → kept = true) →
      (∀ a, (∀ it ∈ its, ¬ it.Hits E a) → ∀ R ∈ rs, ¬ Hits R.1 R.2 a) →
      (∀ y, stepSp1 x = some y → SysNext x y kept rs) →
      ¬ Accepted x ∧ (∀ y, stepSp1 x = some y →
        y.pc = x.pc + 4 ∧ y.code = x.code ∧ (∀ r, (B.get r).Holds E (y.getReg r)) ∧
        B.slots = A.slots ∧ ∀ a, (∀ it ∈ its, ¬ it.Hits E a) → y.getMem a = x.getMem a) := by
    intro B its kept rs ht0 hB hk hrs hsn
    refine ⟨fun hacc => ht0 (h5 ▸ hacc.2.1), fun y hs => ?_⟩
    have hy := hsn y hs
    refine ⟨hy.pc, hy.code, fun r => ?_, ?_, fun a ha => hy.mem a (hrs a ha)⟩
    · rcases hB with rfl | ⟨rfl, _⟩
      · by_cases h5' : r = .x5
        · subst h5'; rw [hy.t0 (hk rfl)]; exact hr .x5
        · rw [hy.regs r h5']; exact hr r
      · by_cases h5' : r = .x5
        · subst h5'
          rcases AState.get_set_eq_or (A := A) (r := .x5) (v := .top) with h1 | h1 | h1
          · rw [h1]; trivial
          · rw [h1]; trivial
          · cases h1
        · rw [AState.get_set_ne h5', hy.regs r h5']; exact hr r
    · rcases hB with rfl | ⟨rfl, _⟩ <;> rfl
  split at h
  · -- A precompile.
    rename_i hacc
    cases hL : accelLen t with
    | none => rw [hL] at h; cases h
    | some L =>
    rw [hL] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    refine ⟨(fun h => by cases h), fun B its he hnt => ?_⟩
    cases he
    refine fin A _ true _ (by rintro rfl; exact absurd hacc (by decide)) (Or.inl rfl) (fun _ => rfl) (fun a ha R hR => ?_)
      (fun y hs => sys_accel hf (by rw [h5]; exact hacc) (by rw [h5]; exact hL) hs)
    simp only [List.mem_singleton] at hR; subst hR
    have := ha _ (List.mem_singleton_self _)
    unfold Item.Hits at this
    rwa [holds_eval (hr .x10) (hnt _ (List.mem_singleton_self _))] at this
  · split at h
    · rename_i hl
      cases h
      refine ⟨(fun h => by cases h), fun B its he _ => ?_⟩
      cases he
      have h1 : (A.set .x5 .top).get .x5 = .top := by
        rcases AState.get_set_eq_or (A := A) (r := .x5) (v := .top) with h1 | h1 | h1
        · exact h1
        · exact h1
        · cases h1
      exact fin _ [] false [] (by rw [hl]; decide) (Or.inr ⟨rfl, rfl⟩)
        (fun he => by exfalso; rw [he, ht] at h1; cases h1)
        (fun _ _ R hR => by cases hR) (fun y hs => sys_hintLen hf (by rw [h5]; exact hl) hs)
    · split at h
      · rename_i hl
        cases hlp : lenPlus (A.get .x11) 8 with
        | none => rw [hlp] at h; cases h
        | some l =>
        rw [hlp] at h
        simp only [Option.map_some, Option.some.injEq] at h
        subst h
        refine ⟨(fun h => by cases h), fun B its he hnt => ?_⟩
        cases he
        refine fin A _ true _ (by rw [hl]; decide) (Or.inl rfl) (fun _ => rfl) (fun a ha R hR => ?_)
          (fun y hs => sys_hintRead hf (by rw [h5]; exact hl) hs)
        simp only [List.mem_singleton] at hR; subst hR
        have := ha _ (List.mem_singleton_self _)
        unfold Item.Hits at this
        simp only at this
        rwa [holds_eval (hr .x10) (hnt _ (List.mem_singleton_self _)),
          lenPlus_eval (hr .x11) hlp] at this
      · split at h
        · rename_i hc
          cases h
          refine ⟨(fun h => by cases h), fun B its he _ => ?_⟩
          cases he
          exact fin A [] true [] (by rcases hc with rfl | rfl <;> decide) (Or.inl rfl) (fun _ => rfl)
            (fun _ _ R hR => by cases hR) (fun y hs => sys_commit hf (by rw [h5]; exact hc) hs)
        · split at h
          · rename_i h0
            split at h
            · rename_i hnzv
              cases h
              refine ⟨fun _ => ?_, fun B its he => by cases he⟩
              exact sys_halt hf (by rw [h5, h0]) (nzVal_holds hnz (hr .x10) hnzv)
            · cases h
          · split at h
            · rename_i h2
              cases h
              refine ⟨(fun h => by cases h), fun B its he _ => ?_⟩
              cases he
              exact fin A [] true [] (by rw [h2]; decide) (Or.inl rfl) (fun _ => rfl)
                (fun _ _ R hR => by cases hR) (fun y hs => sys_write hf (by rw [h5, h2]) hs)
            · split at h
              · rename_i hf2
                cases h
                refine ⟨(fun h => by cases h), fun B its he hnt => ?_⟩
                cases he
                refine fin A _ true _ (by rw [hf2]; decide) (Or.inl rfl) (fun _ => rfl)
                  (fun a ha R hR => ?_) (fun y hs => sys_readInput hf (by rw [h5, hf2]) hs)
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
                rcases hR with rfl | rfl
                · have := ha _ (List.mem_cons_self ..)
                  unfold Item.Hits at this
                  rwa [holds_eval (hr .x10) (hnt _ (List.mem_cons_self ..))] at this
                · have := ha _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
                  unfold Item.Hits at this
                  rwa [holds_eval (hr .x11)
                    (hnt _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)))] at this
              · rename_i hacc hl1 hl2 hc h0 h2 hf2
                cases h
                refine ⟨fun _ => ?_, fun B its he => by cases he⟩
                simp only [not_or] at hc
                rw [← h5] at hacc hl1 hl2 hc h0 h2 hf2
                exact sys_trap hf (by simpa using hacc) hl1 hl2 hc.1 hc.2 h0 h2 hf2

end MachineChecked.RiscV.Check
