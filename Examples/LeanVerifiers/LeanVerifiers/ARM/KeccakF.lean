/-
  LeanVerifiers.ARM.KeccakF

  rustc's `keccak_f` of the AArch64 signature image (`Examples/elf/lean_signatures_a64.elf`):
  its contract at Lprog against the model of leanEthereum/leanVM#837 (`keccakF1600`), proved
  with `lsym` on the lift.

  The code keeps the 25 lanes and θ's five column parities in registers and frame slots across
  the 24 rounds of one loop (`At`, the layout #837 found). A round is one call of `lsym`
  (`round_step`); what it leaves in each register and slot is the model's lane or parity
  (`lane_round`, `par_round`) as an identity of 64-bit vectors, decided by `bv_decide`. The
  prologue reads the lanes from the buffer (`prologue`), the epilogue writes them back and
  restores the callee-saved registers (`epilogue`).

  The round constants are not assumed: the precondition is that memory holds the image
  (`Holds program.memory`), whose words are checked against the ELF, and the table's are among
  them by evaluation (`rc_in_image`). The lift of AArch64 is not proved yet, so nothing follows
  about the machine.
-/

import LeanVerifiers.ARM.Bytes
import LeanVerifiers.ARM.Signatures.F10
import NativeRustc.Keccak.Permute

namespace LeanVerifiers.ARM

open Lprog Lprog.ARM LeanVerifiers.ARM.Signatures
open NativeRustc.Keccak LeanVM.Semantics LeanVM.Parameters

/-- Lane `j` of a state, as a register holds it. -/
def lanes (A : KeccakState) (j : Nat) : BitVec 64 := (Keccak.lane A j).toBitVec

/-- θ's parity of column `x`, as a register holds it. -/
def pars (A : KeccakState) (x : Nat) : BitVec 64 := (par A x).toBitVec

/-- Round constant `i`, as the table holds it. -/
def rcAt (i : Nat) : BitVec 64 := (keccakRC.getD i 0).toBitVec

/-- The registers that hold lanes at the loop head, with the lanes' indices. -/
def laneRegs : List (Reg × Nat) :=
  [(.x22, 4), (.x4, 6), (.x12, 8), (.x6, 9), (.x2, 11), (.x1, 12), (.x7, 13), (.x5, 14),
    (.x19, 16), (.x3, 17), (.x25, 18), (.x21, 19), (.x23, 20), (.x18, 21), (.x16, 22),
    (.x20, 23), (.x14, 24)]

/-- The frame slots that hold lanes at the loop head. -/
def laneSlots : List (BitVec 64 × Nat) :=
  [(56#64, 0), (104#64, 1), (88#64, 2), (64#64, 3), (80#64, 5), (72#64, 7), (48#64, 10),
    (40#64, 15)]

/-- The registers that hold the column parities at the loop head. -/
def parRegs : List (Reg × Nat) := [(.x28, 0), (.x30, 1), (.x8, 2), (.x15, 3), (.x0, 4)]

/-- The frame slots that hold the entry's registers. -/
def savedSlots : List (BitVec 64 × Reg) :=
  [(8#64, .x0), (96#64, .x30), (112#64, .x28), (120#64, .x27), (128#64, .x26), (136#64, .x25),
    (144#64, .x24), (152#64, .x23), (160#64, .x22), (168#64, .x21), (176#64, .x20),
    (184#64, .x19)]

/-- **The loop invariant** after `i` rounds from the state `A`: `r0` and `m0` are the entry's
    registers and memory, `fp` the frame's base. -/
structure At (A : KeccakState) (r0 : Reg → BitVec 64) (m0 : Bytes) (fp : BitVec 64) (i : Nat)
    (regs : Reg → BitVec 64) (m : Bytes) : Prop where
  sp : regs .sp = fp
  ctr : regs .x27 = BitVec.ofNat 64 (8 * i)
  lanes : ∀ p ∈ laneRegs, regs p.1 = lanes (roundsTo A i) p.2
  slots : ∀ p ∈ laneSlots, loadLE m (fp + p.1) 8 = ARM.lanes (roundsTo A i) p.2
  par : ∀ p ∈ parRegs, regs p.1 = pars (roundsTo A i) p.2
  saved : ∀ p ∈ savedSlots, loadLE m (fp + p.1) 8 = r0 p.2
  x29 : regs .x29 = r0 .x29
  same : ∀ x, 192 ≤ (x - fp).toNat → m x = m0 x

theorem Out.load_eq {p q : BitVec 64} {n : Nat} (hq : Out p n q) {m m0 : Bytes}
    (h : ∀ x, n ≤ (x - p).toNat → m x = m0 x) : loadLE m q 8 = loadLE m0 q 8 := by
  obtain ⟨h1, h2⟩ := hq
  exact loadLE_congr fun i hi => h _ (by bv_omega)

theorem ctr_more {i : Nat} (hi : i < 24)
    (h : ¬BitVec.ofNat 64 (8 * i) + 18446744073709551432#64 = 0#64) : i + 1 < 24 := by
  bv_omega

theorem ctr_last {i : Nat} (hi : i < 24)
    (h : BitVec.ofNat 64 (8 * i) + 18446744073709551432#64 = 0#64) : i + 1 = 24 := by
  bv_omega

theorem ctr_next (i : Nat) : BitVec.ofNat 64 (8 * i) + 8#64 = BitVec.ofNat 64 (8 * (i + 1)) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.mul_add]

/-- A register or a slot after a round is the model's lane or parity: unfold both, and decide
    the identity of 64-bit vectors. -/
local macro "kf_bits" A:ident hi:ident : tactic => `(tactic|
  (simp [lsym_simp, lanes, pars, rcAt, roundsTo_succ $A $hi, lane_round, par_round, newPar,
      roundCL, chi, bC, tC, thetaD, toBitVec_rot, rot_zero, loadLE_storeLE_same,
      loadLE_storeLE_off, *]
   try bv_decide))

/-- The invariant after a round, from the state `lsym` leaves. -/
local macro "kf_fields" A:ident hi:ident hsame:ident : tactic => `(tactic|
  (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
   · simp [lsym_simp, *]
   · simp [lsym_simp, ctr_next]
   · simp only [laneRegs, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
       and_true]
     refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
       kf_bits $A $hi
   · simp only [laneSlots, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
       and_true]
     refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> kf_bits $A $hi
   · simp only [parRegs, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
       and_true]
     refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> kf_bits $A $hi
   · simp [savedSlots, loadLE_storeLE_off, *]
   · simp [lsym_simp, *]
   · intro x hx
     simp only [storeLE_out hx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd,
       Nat.reduceLeDiff]
     exact $hsame x hx))

set_option maxHeartbeats 4000000 in
/-- **A round**: from the loop head after `i < 24` rounds to the loop head after `i + 1`, or
    past the loop after the last. -/
theorem round_step {G : State armIsa → Prop} {N : Nat} {Q : State armIsa → Prop}
    {ret top : BitVec 64} {rest : List Frame} (A : KeccakState) (r0 : Reg → BitVec 64)
    (m0 : Bytes) (fp : BitVec 64) (i : Nat) (hi : i < 24)
    (hT : Out fp 192 (2097840#64 + BitVec.ofNat 64 (8 * i)))
    (hrc0 : loadLE m0 (2097840#64 + BitVec.ofNat 64 (8 * i)) 8 = rcAt i)
    (regs : Reg → BitVec 64) (m : Bytes) (hAt : At A r0 m0 fp i regs m)
    (hnext : i + 1 < 24 → ∀ r' m', At A r0 m0 fp (i + 1) r' m' →
      armIsa.SafeN program.lifted ctx G N Q ⟨⟨10, 146, ret, top⟩ :: rest, r', m'⟩)
    (hexit : i + 1 = 24 → ∀ r' m', At A r0 m0 fp (i + 1) r' m' →
      armIsa.SafeN program.lifted ctx G N Q ⟨⟨10, 470, ret, top⟩ :: rest, r', m'⟩) :
    armIsa.SafeN program.lifted ctx G N Q ⟨⟨10, 146, ret, top⟩ :: rest, regs, m⟩ := by
  obtain ⟨hsp, h27, hl, hs, hp, hsv, h29, hsame⟩ := hAt
  have hrc := (hT.load_eq hsame).trans hrc0
  simp only [laneRegs, laneSlots, parRegs, savedSlots, List.forall_mem_cons, List.not_mem_nil,
    false_imp_iff, implies_true, and_true] at hl hs hp hsv
  lsym f10_eq stop [146, 470] with [hsp, h27, hl, hs, hp, hrc, loadLE_storeLE_same,
    loadLE_storeLE_off, loadLE_storeLE_out hT]
  · exact hnext (ctr_more hi hc) _ _ (by kf_fields A hi hsame)
  · exact hexit (ctr_last hi hc) _ _ (by kf_fields A hi hsame)

/-! ## The state's buffer -/

/-- The buffer's words after the first, with the lanes' indices. -/
def bufSlots : List (BitVec 64 × Nat) :=
  [(8#64, 1), (16#64, 2), (24#64, 3), (32#64, 4), (40#64, 5), (48#64, 6), (56#64, 7),
    (64#64, 8), (72#64, 9), (80#64, 10), (88#64, 11), (96#64, 12), (104#64, 13), (112#64, 14),
    (120#64, 15), (128#64, 16), (136#64, 17), (144#64, 18), (152#64, 19), (160#64, 20),
    (168#64, 21), (176#64, 22), (184#64, 23), (192#64, 24)]

/-- The 25 lanes of `A` are the words at `buf`. -/
def StateAt (m : Bytes) (buf : BitVec 64) (A : KeccakState) : Prop :=
  loadLE m buf 8 = lanes A 0 ∧ ∀ p ∈ bufSlots, loadLE m (buf + p.1) 8 = lanes A p.2

/-- The buffer's 200 bytes are outside the frame's 192. -/
def Apart (fp buf : BitVec 64) : Prop := ∀ b : BitVec 64, b.toNat ≤ 192 → Out fp 192 (buf + b)

theorem Apart.zero {fp buf : BitVec 64} (h : Apart fp buf) : Out fp 192 buf := by
  simpa using h 0#64 (by decide)

set_option maxHeartbeats 2000000 in
/-- **The prologue**: from the frame set up to the loop head before the first round. -/
theorem prologue {G : State armIsa → Prop} {N : Nat} {Q : State armIsa → Prop}
    {ret top : BitVec 64} {rest : List Frame} (A : KeccakState) (fp : BitVec 64)
    (regs : Reg → BitVec 64) (m : Bytes) (hsp : regs .sp = fp) (hA : StateAt m (regs .x0) A)
    (hap : Apart fp (regs .x0))
    (hk : ∀ r' m', At A regs m fp 0 r' m' →
      armIsa.SafeN program.lifted ctx G N Q ⟨⟨10, 146, ret, top⟩ :: rest, r', m'⟩) :
    armIsa.SafeN program.lifted ctx G N Q ⟨⟨10, 4, ret, top⟩ :: rest, regs, m⟩ := by
  obtain ⟨hA0, hA⟩ := hA
  simp only [bufSlots, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
    and_true] at hA
  lsym f10_eq stop [146] with [hsp, hA0, hA, loadLE_storeLE_same, loadLE_storeLE_off,
    loadLE_storeLE_out hap.zero, fun b hb => loadLE_storeLE_out (hap b hb)]
  refine hk _ _ ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [lsym_simp, hsp]
  · simp [lsym_simp]
  · simp [laneRegs, lsym_simp, roundsTo_zero]
  · simp [laneSlots, roundsTo_zero, loadLE_storeLE_same, loadLE_storeLE_off]
  · simp only [parRegs, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
      and_true]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      (simp [lsym_simp, pars, par, lanes, roundsTo_zero]; bv_decide)
  · simp [savedSlots, lsym_simp, loadLE_storeLE_same, loadLE_storeLE_off]
  · simp [lsym_simp]
  · intro x hx
    simp only [storeLE_out hx, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd,
      Nat.reduceLeDiff]

/-- **The rounds**: from the loop head after `i < 24` rounds to past the loop after the 24. -/
theorem rounds {G : State armIsa → Prop} {N : Nat} {Q : State armIsa → Prop}
    {ret top : BitVec 64} {rest : List Frame} (A : KeccakState) (r0 : Reg → BitVec 64)
    (m0 : Bytes) (fp : BitVec 64)
    (hT : ∀ i < 24, Out fp 192 (2097840#64 + BitVec.ofNat 64 (8 * i)))
    (hrc : ∀ i < 24, loadLE m0 (2097840#64 + BitVec.ofNat 64 (8 * i)) 8 = rcAt i)
    (hexit : ∀ r' m', At A r0 m0 fp 24 r' m' →
      armIsa.SafeN program.lifted ctx G N Q ⟨⟨10, 470, ret, top⟩ :: rest, r', m'⟩) :
    ∀ k i (regs : Reg → BitVec 64) (m : Bytes), 24 - i = k → i < 24 →
      At A r0 m0 fp i regs m →
      armIsa.SafeN program.lifted ctx G N Q ⟨⟨10, 146, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro i _ _ hk hi; omega
  | succ k ih =>
    intro i regs m hk hi hAt
    exact round_step A r0 m0 fp i hi (hT i hi) (hrc i hi) regs m hAt
      (fun h r' m' h' => ih (i + 1) r' m' (by omega) h h')
      (fun h r' m' h' => hexit r' m' (h ▸ h'))

/-- The registers `keccak_f` restores. -/
def calleeSaved : List Reg := [.x19, .x20, .x21, .x22, .x23, .x24, .x25, .x26, .x27, .x28, .x29]

set_option maxHeartbeats 2000000 in
/-- **The epilogue**: from past the loop after the 24 rounds to the return. -/
theorem epilogue {G : State armIsa → Prop} {N : Nat} {Q : State armIsa → Prop}
    {ret top : BitVec 64} {rest : List Frame} (A : KeccakState) (r0 : Reg → BitVec 64)
    (m0 : Bytes) (fp : BitVec 64) (hra : r0 .x30 = ret) (hfp : fp + 192#64 = top)
    (htop : top &&& 15#64 = 0#64)
    (hap : Apart fp (r0 .x0)) (regs : Reg → BitVec 64) (m : Bytes)
    (hAt : At A r0 m0 fp 24 regs m)
    (hk : ∀ r' m', StateAt m' (r0 .x0) (keccakF1600 A) →
      (∀ x, 192 ≤ (x - fp).toNat → 200 ≤ (x - r0 .x0).toNat → m' x = m0 x) →
      (∀ r ∈ calleeSaved, r' r = r0 r) →
      armIsa.SafeN program.lifted ctx G N Q ⟨rest, r', m'⟩) :
    armIsa.SafeN program.lifted ctx G N Q ⟨⟨10, 470, ret, top⟩ :: rest, regs, m⟩ := by
  obtain ⟨hsp, h27, hl, hs, hp, hsv, h29, hsame⟩ := hAt
  simp only [laneRegs, laneSlots, parRegs, savedSlots, List.forall_mem_cons, List.not_mem_nil,
    false_imp_iff, implies_true, and_true] at hl hs hp hsv
  lsym f10_eq with [hsp, hl, hs, hsv, hra, hfp, htop, loadLE_storeLE_same, loadLE_storeLE_off,
    loadLE_storeLE_in hap.zero, fun b hb => loadLE_storeLE_in (hap b hb)]
  refine hk _ _ ⟨?_, ?_⟩ ?_ ?_
  · simp [← roundsTo_24, loadLE_storeLE_same, loadLE_storeLE_0off]
  · simp [bufSlots, ← roundsTo_24, loadLE_storeLE_same, loadLE_storeLE_off]
  · intro x hx hb
    simp only [storeLE_out hb, storeLE_out0 hb, BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod, Nat.reduceAdd, Nat.reduceLeDiff]
    exact hsame x hx
  · simp [calleeSaved, lsym_simp, h29]

/-- **The round constants are in the image**: the 24 words at `0x2002b0`, by evaluation. -/
theorem rc_in_image : ∀ i < 24,
    (2097840#64 + BitVec.ofNat 64 (8 * i), rcAt i) ∈ program.memory := by
  decide +kernel

/-- `top - 192`, as `lsym` writes it. -/
theorem frame_eq (top : BitVec 64) : top + 18446744073709551424#64 = top - 192#64 := by
  bv_omega

/-- **`keccak_f(buf)`**: the 25 lanes at `buf` become Keccak-f[1600] of them. Memory changes
    only there and in the 192 bytes below the stack pointer, and the callee-saved registers are
    as they were. The stack pointer is a multiple of 16, as the machine requires of it. Memory holds the image, the buffer is outside the frame, and so is the image's
    table of round constants at `0x2002b0`. -/
theorem keccak_f_contract (A : KeccakState) : armIsa.Contract program.lifted ctx 10
    (fun ret top regs m => regs .x30 = ret ∧ regs .sp = top ∧ top &&& 15#64 = 0#64 ∧
      StateAt m (regs .x0) A ∧
      Apart (top - 192#64) (regs .x0) ∧
      Holds program.memory m ∧
      ∀ i < 24, Out (top - 192#64) 192 (2097840#64 + BitVec.ofNat 64 (8 * i)))
    (fun _ top regs m r' m' => StateAt m' (regs .x0) (keccakF1600 A) ∧
      (∀ x, 192 ≤ (x - (top - 192#64)).toNat → 200 ≤ (x - regs .x0).toNat →
        m' x = m x) ∧
      ∀ r ∈ calleeSaved, r' r = regs r) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, htop, hA, hap, hH, hT⟩ hk
  have hal : (top + 18446744073709551424#64) &&& 15#64 = 0#64 := by bv_decide
  lsym f10_eq stop [4] with [hra, hsp, hal]
  rw [frame_eq]
  refine prologue A (top - 192#64) _ m (by simp [lsym_simp]) (by simpa [lsym_simp] using hA)
    (by simpa [lsym_simp] using hap) fun r1 m1 h1 => ?_
  refine rounds A _ m (top - 192#64) hT (fun i hi => hH _ (rc_in_image i hi))
    (fun r2 m2 h2 => ?_) 24 0 r1 m1 rfl (by decide) h1
  refine epilogue A _ m (top - 192#64) (by simp [lsym_simp, hra]) (by bv_omega) htop
    (by simpa [lsym_simp] using hap) r2 m2 h2 fun r' m' h h' h'' => ?_
  refine hk r' m' ⟨by simpa [lsym_simp] using h, by simpa [lsym_simp] using h', ?_⟩
  simpa [calleeSaved, lsym_simp] using h''

end LeanVerifiers.ARM
