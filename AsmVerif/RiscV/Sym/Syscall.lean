/-
  AsmVerif.RiscV.Sym.Syscall

  The `ECALL`s the guest makes, stated over regions so the executor can apply
  them: the three accelerators (`UINT256_MUL`, `PALLAS_ADD`, `PALLAS_DOUBLE`),
  the two hint syscalls, `COMMIT`, `COMMIT_DEFERRED_PROOFS` and `HALT`.

  An accelerator writes one contiguous block with `writeWords`, so its effect on
  a tracked region is `Region.writeWords` (the target block) or
  `Region.frame_writeWords` (any disjoint region), and `Unchanged.writeWords`.

  ## The operand zone

  `sp1AccelValid` range-checks the operand blocks with `validDwordRange`, which
  reuses `riscv-zkvm`'s `isValidDwordAccess`: the zone `[0x20, 0x78000000]`, which
  is where SP1's stack lives, plus two zones the guest never touches. So an
  accelerator operand on the SP1 *heap* (`≥ 0x78040618`) traps in the model. The
  interpreter steps with the same `stepOn`, and the guest's run halts accepting, so
  every one of its 68,330 accelerator calls had its operands on the stack; `ZiskOk`
  (named after the zone's origin) is the fact a region needs to pass the check.
  A model trap where SP1 would proceed is a fidelity question: `docs/AUDIT.md`.
-/

import AsmVerif.RiscV.Sym.Mem
import AsmVerif.RiscV.Sym.Core
import Precompile.Sp1

namespace AsmVerif.RiscV.Sym

open RiscvZkvm.Rv64

/-! ## `getMem` through `writeWords` -/

/-- The next cell: `writeWords`' `base + 8` in region-index form. -/
theorem add8_cell (base : Word) (i : Nat) :
    base + 8 + BitVec.ofNat 64 (8 * i) = base + BitVec.ofNat 64 (8 * (i + 1)) := by
  rw [BitVec.add_assoc]
  congr 1
  rw [show (8 : Word) = BitVec.ofNat 64 8 from rfl, ← BitVec.ofNat_add]
  congr 1; omega

theorem toNat_add8 {base : Word} {n : Nat} (hnw : base.toNat + 8 * (n + 1) ≤ 2 ^ 64) (hn : 0 < n) :
    (base + 8).toNat = base.toNat + 8 := by
  have h8 : (8 : Word).toNat = 8 := rfl
  rw [BitVec.toNat_add, h8]
  exact Nat.mod_eq_of_lt (by omega)

theorem getMem_writeWords_of_ne {s : MachineState} {base a : Word} {ws : List Word}
    (h : ∀ i, i < ws.length → a ≠ base + BitVec.ofNat 64 (8 * i)) :
    (s.writeWords base ws).getMem a = s.getMem a := by
  induction ws generalizing s base with
  | nil => rfl
  | cons w ws ih =>
    simp only [MachineState.writeWords]
    rw [ih, MachineState.getMem_setMem_ne]
    · have := h 0 (by simp); simpa using this
    · intro i hi
      rw [add8_cell]
      exact h (i + 1) (by simp; omega)

theorem getMem_writeWords_at {s : MachineState} {base : Word} {ws : List Word}
    (hnw : base.toNat + 8 * ws.length ≤ 2 ^ 64) {i : Nat} (hi : i < ws.length) :
    (s.writeWords base ws).getMem (base + BitVec.ofNat 64 (8 * i)) = ws[i]! := by
  induction ws generalizing s base i with
  | nil => simp at hi
  | cons w ws ih =>
    simp only [MachineState.writeWords, List.length_cons] at hnw ⊢
    cases i with
    | zero =>
      have h0 : base + BitVec.ofNat 64 (8 * 0) = base := by simp
      rw [h0, getMem_writeWords_of_ne]
      · simp
      · intro j hj heq
        rw [add8_cell] at heq
        have := congrArg BitVec.toNat heq
        rw [toNat_addr (n := ws.length + 1) (by omega) hnw] at this
        omega
    | succ i =>
      have hi' : i < ws.length := by simp at hi; omega
      have hnw' : (base + 8).toNat + 8 * ws.length ≤ 2 ^ 64 := by
        rw [toNat_add8 hnw (by omega)]; omega
      have := ih (s := s.setMem base w) hnw' hi'
      rw [add8_cell] at this
      rw [this, getBang hi', getBang hi]
      simp

/-! ## Regions and `readWords` / `writeWords` -/

theorem Region.readWords {base : Word} {vs : List Word} {s : MachineState} (h : Region base vs s) :
    s.readWords base vs.length = vs := by
  induction vs generalizing base with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.length_cons, MachineState.readWords, List.cons.injEq]
    refine ⟨?_, ?_⟩
    · have := h 0 (by simp); simpa using this
    · apply ih
      intro i hi
      have := h (i + 1) (by simp; omega)
      rw [add8_cell, this, getBang (by simp; omega), getBang hi]
      simp

theorem Region.readWords' {base : Word} {vs : List Word} {s : MachineState} (h : Region base vs s)
    {n : Nat} (hn : vs.length = n) : s.readWords base n = vs := by
  subst hn; exact h.readWords

/-- After `writeWords base ws`, the block holds `ws`. -/
theorem Region.writeWords {base : Word} {s : MachineState} (ws : List Word)
    (hnw : base.toNat + 8 * ws.length ≤ 2 ^ 64)
    {p : Word} {s' : MachineState} (hs' : (s.writeWords base ws).setPC p = s') :
    Region base ws s' := by
  subst hs'
  intro i hi
  rw [pcShape_getMem, getMem_writeWords_at hnw hi]

/-- A region disjoint from the written block is untouched. -/
theorem Region.frame_writeWords {base : Word} {vs : List Word} {s : MachineState}
    (h : Region base vs s) {b₂ : Word} {ws : List Word} (hd : Disjoint base vs.length b₂ ws.length)
    {p : Word} {s' : MachineState} (hs' : (s.writeWords b₂ ws).setPC p = s') :
    Region base vs s' := by
  subst hs'
  intro i hi
  rw [pcShape_getMem, getMem_writeWords_of_ne, h i hi]
  intro j hj
  exact addr_ne_of_disjoint hd hi hj

theorem Unchanged.writeWords {W : List (Word × Nat)} {s s' s'' : MachineState}
    (h : Unchanged W s s') {b : Word} {n : Nat} (hW : (b, n) ∈ W) {ws : List Word}
    (hlen : ws.length = n) (hnw : b.toNat + 8 * n ≤ 2 ^ 64) {p : Word}
    (hs'' : (s'.writeWords b ws).setPC p = s'') : Unchanged W s s'' := by
  intro x hx
  subst hs''
  rw [pcShape_getMem, getMem_writeWords_of_ne]
  · exact h x hx
  · intro i hi heq
    apply hx (b, n) hW
    show InRegion x b n
    unfold InRegion
    rw [heq, toNat_addr (by omega) hnw]
    exact ⟨by omega, by omega⟩

/-! ## The operand zone check -/

/-- The block `[base, base + 8n)` lies in the zone `[0x20, 0x78000000]` and is
    8-aligned: what `validDwordRange` asks. -/
structure ZiskOk (base : Word) (n : Nat) : Prop where
  aligned : base.toNat % 8 = 0
  lo : 0x20 ≤ base.toNat
  hi : base.toNat + 8 * n ≤ 0x78000000

theorem ZiskOk.validDwordRange {base : Word} {n : Nat} (h : ZiskOk base n) :
    MachineState.validDwordRange base n = true := by
  unfold MachineState.validDwordRange
  simp only [List.all_eq_true, List.mem_range]
  intro i hi
  have ht : (base + BitVec.ofNat 64 (8 * i)).toNat = base.toNat + 8 * i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * i) (by have := h.hi; omega)]
    exact Nat.mod_eq_of_lt (by have := h.hi; omega)
  simp only [isValidDwordAccess, isValidMemAddr, isAligned8, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · left; rw [ht]; have := h.lo; have := h.hi; simp only [MEM_START, MEM_END]; omega
  · rw [ht]; have := h.aligned; omega

theorem ZiskOk.sub {base : Word} {n : Nat} (h : ZiskOk base n) (k m : Nat) (hkm : k + m ≤ n) :
    ZiskOk (base + BitVec.ofNat 64 (8 * k)) m := by
  have ht : (base + BitVec.ofNat 64 (8 * k)).toNat = base.toNat + 8 * k := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * k) (by have := h.hi; omega)]
    exact Nat.mod_eq_of_lt (by have := h.hi; omega)
  refine ⟨?_, ?_, ?_⟩ <;> rw [ht]
  · have := h.aligned; omega
  · have := h.lo; omega
  · have := h.hi; omega

/-! ## The accelerator step, over regions -/

/-- `UINT256_MUL`: with `x` at `a0` (4 cells) and `y ‖ m` at `a1` (8 cells), the
    step writes `natToLeLimbs 4 (X * Y % M)` at `a0`, given `M ≠ 0`. -/
theorem step_uint256Mul {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.UINT256_MUL) {a0 a1 : Word} (ha0 : s.getReg .x10 = a0)
    (ha1 : s.getReg .x11 = a1) {x ym : List Word} (hx : Region a0 x s) (hxl : x.length = 4)
    (hym : Region a1 ym s) (hyml : ym.length = 8)
    (hz0 : ZiskOk a0 4) (hz1 : ZiskOk a1 8)
    (hm : Accel.leLimbsToNat (ym.drop 4) ≠ 0) :
    stepSp1 s = some ((s.writeWords a0 (Accel.natToLeLimbs 4
      (Accel.leLimbsToNat x * Accel.leLimbsToNat (ym.take 4) % Accel.leLimbsToNat (ym.drop 4)))).setPC
      (s.pc + 4)) := by
  have hy : s.readWords a1 4 = ym.take 4 := by
    have := (hym.take 4).readWords
    rwa [List.length_take, hyml] at this
  have hmod : s.readWords (a1 + 32) 4 = ym.drop 4 := by
    have := (hym.shift 4).readWords
    rw [List.length_drop, hyml] at this
    simpa using this
  have hxr : s.readWords a0 4 = x := hx.readWords' hxl
  have hvalid : s.sp1AccelValid Sp1.UINT256_MUL = true := by
    rw [Precompile.sp1AccelValid_uint256Mul, ha0, ha1, hmod]
    exact ⟨hz0.validDwordRange, hz1.validDwordRange, hm⟩
  have hid : Sp1.isAccelId (s.getReg .x5) = true := by rw [ht0]; decide
  rw [stepSp1_accel hfetch hid (ht0 ▸ hvalid)]
  congr 2
  unfold MachineState.execSp1Accel
  rw [ht0, Precompile.sp1AccelWrite_uint256Mul, ha0, ha1, hxr, hy, hmod]
  rfl

/-- `PALLAS_ADD`: `P` at `a0`, `Q` at `a1`, both 8 cells; writes `P + Q` at `a0`. -/
theorem step_pallasAdd {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.PALLAS_ADD) {a0 a1 : Word} (ha0 : s.getReg .x10 = a0)
    (ha1 : s.getReg .x11 = a1) {P Q : List Word} (hP : Region a0 P s) (hPl : P.length = 8)
    (hQ : Region a1 Q s) (hQl : Q.length = 8) (hz0 : ZiskOk a0 8) (hz1 : ZiskOk a1 8)
    (hPv : Accel.ptValid Sp1.pallasP 4 P = true) (hQv : Accel.ptValid Sp1.pallasP 4 Q = true)
    (hne : Precompile.Pallas.xOf P ≠ Precompile.Pallas.xOf Q) :
    stepSp1 s = some ((s.writeWords a0 (Accel.curveAddL Sp1.pallasP 4 P Q)).setPC (s.pc + 4)) := by
  have hPr : s.readWords a0 8 = P := hP.readWords' hPl
  have hQr : s.readWords a1 8 = Q := hQ.readWords' hQl
  have hvalid : s.sp1AccelValid Sp1.PALLAS_ADD = true := by
    rw [Precompile.sp1AccelValid_pallasAdd, ha0, ha1, hPr, hQr]
    exact ⟨hz0.validDwordRange, hz1.validDwordRange, hPv, hQv, hne⟩
  have hid : Sp1.isAccelId (s.getReg .x5) = true := by rw [ht0]; decide
  rw [stepSp1_accel hfetch hid (ht0 ▸ hvalid)]
  congr 2
  unfold MachineState.execSp1Accel
  rw [ht0, Precompile.sp1AccelWrite_pallasAdd, ha0, ha1, hPr, hQr]

/-- `PALLAS_DOUBLE`: `P` at `a0`, 8 cells; writes `2P` at `a0`. -/
theorem step_pallasDouble {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.PALLAS_DOUBLE) {a0 : Word} (ha0 : s.getReg .x10 = a0)
    {P : List Word} (hP : Region a0 P s) (hPl : P.length = 8) (hz0 : ZiskOk a0 8)
    (hPv : Accel.ptValid Sp1.pallasP 4 P = true) (hy : Precompile.Pallas.yOf P ≠ 0) :
    stepSp1 s = some ((s.writeWords a0 (Accel.curveDblL Sp1.pallasP 4 P)).setPC (s.pc + 4)) := by
  have hPr : s.readWords a0 8 = P := hP.readWords' hPl
  have hvalid : s.sp1AccelValid Sp1.PALLAS_DOUBLE = true := by
    rw [Precompile.sp1AccelValid_pallasDouble, ha0, hPr]
    exact ⟨hz0.validDwordRange, hPv, hy⟩
  have hid : Sp1.isAccelId (s.getReg .x5) = true := by rw [ht0]; decide
  rw [stepSp1_accel hfetch hid (ht0 ▸ hvalid)]
  congr 2
  unfold MachineState.execSp1Accel
  rw [ht0, Precompile.sp1AccelWrite_pallasDouble, ha0, hPr]

/-! ## Shape projections for `(s.writeWords b ws).setPC p` -/

theorem wwShape_getReg {s : MachineState} {b p : Word} {ws : List Word} {r : Reg} :
    ((s.writeWords b ws).setPC p).getReg r = s.getReg r := by
  rw [pcShape_getReg, MachineState.getReg_writeWords]
theorem wwShape_pc {s : MachineState} {b p : Word} {ws : List Word} :
    ((s.writeWords b ws).setPC p).pc = p := rfl
theorem wwShape_privateInput {s : MachineState} {b p : Word} {ws : List Word} :
    ((s.writeWords b ws).setPC p).privateInput = s.privateInput := by
  rw [pcShape_privateInput, MachineState.privateInput_writeWords]
theorem wwShape_code {s : MachineState} {b p : Word} {ws : List Word} :
    ((s.writeWords b ws).setPC p).code = s.code := by
  rw [MachineState.code_setPC, MachineState.code_writeWords]

/-! ## The other syscalls -/

/-- `COMMIT` changes no register, no memory and no pc other than `+4`. -/
theorem commitShape_getReg {s : MachineState} {p : Word} {r : Reg} :
    ((s.sp1Commit).setPC p).getReg r = s.getReg r := by
  rw [pcShape_getReg]; cases r <;> rfl
theorem commitShape_getMem {s : MachineState} {p a : Word} :
    ((s.sp1Commit).setPC p).getMem a = s.getMem a := rfl
theorem commitShape_mem {s : MachineState} {p : Word} : ((s.sp1Commit).setPC p).mem = s.mem := rfl
theorem commitShape_pc {s : MachineState} {p : Word} : ((s.sp1Commit).setPC p).pc = p := rfl
theorem commitShape_privateInput {s : MachineState} {p : Word} :
    ((s.sp1Commit).setPC p).privateInput = s.privateInput := rfl
theorem commitShape_code {s : MachineState} {p : Word} : ((s.sp1Commit).setPC p).code = s.code := rfl

/-! ## Syscalls in `Safe` form

An accelerator whose operands fail the model's check traps, and a trap is not
an accepting halt, so in `SafeN` form the operand checks cost nothing: the
continuation is only asked for on the path where the model continues. -/

theorem SafeN.accel {G : MachineState → Prop} {n : Nat} {P : Prop} {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (hid : Sp1.isAccelId (s.getReg .x5) = true) (hne : s.getReg .x5 ≠ 0)
    (h : s.sp1AccelValid (s.getReg .x5) = true →
      SafeN G n P ((s.execSp1Accel (s.getReg .x5)).setPC (s.pc + 4))) : SafeN G n P s := by
  cases hv : s.sp1AccelValid (s.getReg .x5) with
  | false => exact SafeN.stuck (stepSp1_accel_trap hfetch hid hv) (fun ha => absurd ha.2.1 hne)
  | true => exact SafeN.step_of (stepSp1_accel hfetch hid hv) (h hv)

theorem SafeN.uint256Mul {G : MachineState → Prop} {n : Nat} {P : Prop} {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.UINT256_MUL) {a0 a1 : Word} (ha0 : s.getReg .x10 = a0)
    (ha1 : s.getReg .x11 = a1) {x ym : List Word} (hx : Region a0 x s) (hxl : x.length = 4)
    (hym : Region a1 ym s) (hyml : ym.length = 8)
    (k : ∀ s', (s.writeWords a0 (Accel.natToLeLimbs 4
      (Accel.leLimbsToNat x * Accel.leLimbsToNat (ym.take 4) % Accel.leLimbsToNat (ym.drop 4)))).setPC
      (s.pc + 4) = s' → SafeN G n P s') : SafeN G n P s := by
  have hy : s.readWords a1 4 = ym.take 4 := by
    have := (hym.take 4).readWords
    rwa [List.length_take, hyml] at this
  have hmod : s.readWords (a1 + 32) 4 = ym.drop 4 := by
    have := (hym.shift 4).readWords
    rw [List.length_drop, hyml] at this
    simpa using this
  have hxr : s.readWords a0 4 = x := hx.readWords' hxl
  refine SafeN.accel (P := P) hfetch (by rw [ht0]; decide) (by rw [ht0]; decide) ?_
  intro _
  apply k
  unfold MachineState.execSp1Accel
  rw [ht0, Precompile.sp1AccelWrite_uint256Mul, ha0, ha1, hxr, hy, hmod]
  rfl

theorem SafeN.pallasAdd {G : MachineState → Prop} {n : Nat} {P : Prop} {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.PALLAS_ADD) {a0 a1 : Word} (ha0 : s.getReg .x10 = a0)
    (ha1 : s.getReg .x11 = a1) {p q : List Word} (hp : Region a0 p s) (hpl : p.length = 8)
    (hq : Region a1 q s) (hql : q.length = 8)
    (k : ∀ s', (s.writeWords a0 (Accel.curveAddL Sp1.pallasP 4 p q)).setPC (s.pc + 4) = s' →
      SafeN G n P s') : SafeN G n P s := by
  have hpr : s.readWords a0 8 = p := hp.readWords' hpl
  have hqr : s.readWords a1 8 = q := hq.readWords' hql
  refine SafeN.accel (P := P) hfetch (by rw [ht0]; decide) (by rw [ht0]; decide) ?_
  intro _
  apply k
  unfold MachineState.execSp1Accel
  rw [ht0, Precompile.sp1AccelWrite_pallasAdd, ha0, ha1, hpr, hqr]

theorem SafeN.pallasDouble {G : MachineState → Prop} {n : Nat} {P : Prop} {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.PALLAS_DOUBLE) {a0 : Word} (ha0 : s.getReg .x10 = a0)
    {p : List Word} (hp : Region a0 p s) (hpl : p.length = 8)
    (k : ∀ s', (s.writeWords a0 (Accel.curveDblL Sp1.pallasP 4 p)).setPC (s.pc + 4) = s' →
      SafeN G n P s') : SafeN G n P s := by
  have hpr : s.readWords a0 8 = p := hp.readWords' hpl
  refine SafeN.accel (P := P) hfetch (by rw [ht0]; decide) (by rw [ht0]; decide) ?_
  intro _
  apply k
  unfold MachineState.execSp1Accel
  rw [ht0, Precompile.sp1AccelWrite_pallasDouble, ha0, hpr]

theorem SafeN.commit {G : MachineState → Prop} {n : Nat} {P : Prop} {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.COMMIT)
    (k : ∀ s', (s.sp1Commit).setPC (s.pc + 4) = s' → SafeN G n P s') : SafeN G n P s :=
  SafeN.step_gen (stepSp1_commit hfetch ht0) k

theorem SafeN.commitDeferred {G : MachineState → Prop} {n : Nat} {P : Prop} {s : MachineState} (hfetch : s.code s.pc = some .ECALL)
    (ht0 : s.getReg .x5 = Sp1.COMMIT_DEFERRED_PROOFS)
    (k : ∀ s', s.setPC (s.pc + 4) = s' → SafeN G n P s') : SafeN G n P s :=
  SafeN.step_gen (stepSp1_commit_deferred hfetch ht0) k

/-! ## Writing a block inside a region -/

theorem Region.writeWords_sub {base : Word} {vs : List Word} {s : MachineState}
    (h : Region base vs s) (hnw : base.toNat + 8 * vs.length ≤ 2 ^ 64) {i : Nat} (ws : List Word)
    (hi : i + ws.length ≤ vs.length) {a p : Word} (ha : a = base + BitVec.ofNat 64 (8 * i))
    {s' : MachineState} (hs' : (s.writeWords a ws).setPC p = s') {vs' : List Word}
    (hvs : vs.take i ++ ws ++ vs.drop (i + ws.length) = vs') : Region base vs' s' := by
  subst ha hs' hvs
  intro j hj
  simp only [List.length_append, List.length_take, List.length_drop] at hj
  rw [pcShape_getMem]
  by_cases hlo : j < i
  · rw [getMem_writeWords_of_ne, h j (by omega)]
    · rw [getBang (by omega), getBang (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_append_left (by simp; omega), List.getElem_take]
    · intro k hk heq
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add] at heq
      have := congrArg BitVec.toNat heq
      rw [toNat_addr (n := vs.length) (by omega) hnw, toNat_addr (n := vs.length) (by omega) hnw] at this
      omega
  · by_cases hhi : j < i + ws.length
    · have hk : j - i < ws.length := by omega
      have := getMem_writeWords_at (s := s) (base := base + BitVec.ofNat 64 (8 * i)) (ws := ws)
        (by rw [toNat_addr (n := vs.length) (by omega) hnw]; omega) hk
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add, Nat.add_sub_cancel' (by omega)] at this
      rw [this, getBang hk, getBang (by simp; omega), List.getElem_append_left (by simp; omega),
        List.getElem_append_right (by simp; omega)]
      congr 1; simp; omega
    · rw [getMem_writeWords_of_ne, h j (by omega)]
      · rw [getBang (by omega), getBang (by simp; omega), List.getElem_append_right (by simp; omega),
          List.getElem_drop]
        congr 1; simp; omega
      · intro k hk heq
        rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add] at heq
        have := congrArg BitVec.toNat heq
        rw [toNat_addr (n := vs.length) (by omega) hnw, toNat_addr (n := vs.length) (by omega) hnw] at this
        omega

theorem Unchanged.writeWords_at {W : List (Word × Nat)} {s s' s'' : MachineState}
    (h : Unchanged W s s') {b : Word} {n : Nat} (hW : (b, n) ∈ W) (o : Nat) {ws : List Word}
    (hlen : o + ws.length ≤ n) (hnw : b.toNat + 8 * n ≤ 2 ^ 64) {a p : Word}
    (ha : a = b + BitVec.ofNat 64 (8 * o))
    (hs'' : (s'.writeWords a ws).setPC p = s'') : Unchanged W s s'' := by
  intro x hx
  subst hs'' ha
  rw [pcShape_getMem, getMem_writeWords_of_ne]
  · exact h x hx
  · intro i hi heq
    apply hx (b, n) hW
    show InRegion x b n
    unfold InRegion
    rw [heq, BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add, toNat_addr (by omega) hnw]
    exact ⟨by omega, by omega⟩

theorem Region.frame_writeWords_sub {base : Word} {vs : List Word} {s : MachineState}
    (h : Region base vs s) {b₂ : Word} {n₂ : Nat} (hd : Disjoint base vs.length b₂ n₂)
    {o : Nat} {ws : List Word} (hlen : o + ws.length ≤ n₂) {a p : Word}
    (ha : a = b₂ + BitVec.ofNat 64 (8 * o))
    {s' : MachineState} (hs' : (s.writeWords a ws).setPC p = s') : Region base vs s' := by
  subst hs' ha
  intro i hi
  rw [pcShape_getMem, getMem_writeWords_of_ne, h i hi]
  intro j hj heq
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← Nat.mul_add] at heq
  exact addr_ne_of_disjoint hd hi (by omega) heq

end AsmVerif.RiscV.Sym

namespace AsmVerif.RiscV.Sym

open RiscvZkvm.Rv64

theorem length_curveAddL (P Q : List Word) : (Accel.curveAddL Sp1.pallasP 4 P Q).length = 8 := by
  simp [Accel.curveAddL, Accel.natToLeLimbs]

theorem length_curveDblL (P : List Word) : (Accel.curveDblL Sp1.pallasP 4 P).length = 8 := by
  simp [Accel.curveDblL, Accel.natToLeLimbs]

end AsmVerif.RiscV.Sym
