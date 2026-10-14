import AsmVerif.RiscV.Sym
import Cases.Zip2005.Image.F_7801beb0
import Cases.Zip2005.Image.Ro

/-!
# SP1's hint syscalls, over regions

`HINT_READ` writes the front hint vector `P` as `P.length / 8 + 1` little-endian doublewords
(`hintWords P`, the last zero-padded) at an aligned pointer. These are the memory facts the input
path (`read_vec_raw`) needs: the written words, and everything else left alone.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- The doublewords a `HINT_READ` of the bytes `P` writes. -/
def hintWords (P : List (BitVec 8)) : List Word :=
  (List.range (P.length / 8 + 1)).map (fun i => bytesToWordLE ((P.drop (8 * i)).take 8))

@[simp] theorem hintWords_length (P : List (BitVec 8)) : (hintWords P).length = P.length / 8 + 1 := by
  simp [hintWords]

/-- The next doubleword's address. -/
theorem addr8_succ (base : Word) (i : Nat) :
    base + BitVec.ofNat 64 (8 * (i + 1)) = base + 8 + BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have : (8 : Word).toNat = 8 := rfl
  rw [this]
  omega

/-- `writeBytesAsWords` leaves every word it does not write. -/
theorem getMem_writeBytesAsWords_ne (s : MachineState) (base a : Word) (bytes : List (BitVec 8))
    (h : ∀ i, 8 * i < bytes.length → a ≠ base + BitVec.ofNat 64 (8 * i)) :
    (s.writeBytesAsWords base bytes).getMem a = s.getMem a := by
  match bytes with
  | [] => simp
  | b :: bs =>
    unfold MachineState.writeBytesAsWords
    rw [getMem_writeBytesAsWords_ne _ (base + 8) a _ ?_]
    · have h0 : a ≠ base := by simpa using h 0 (by simp)
      exact MachineState.getMem_setMem_ne h0
    · intro i hi
      have := h (i + 1) (by simp only [List.length_drop, List.length_cons] at hi ⊢; omega)
      rwa [addr8_succ] at this
termination_by bytes.length
decreasing_by simp [List.length_drop]

/-- The word `writeBytesAsWords` writes at `base + 8 j`. -/
theorem getMem_writeBytesAsWords_at (s : MachineState) (base : Word) (bytes : List (BitVec 8)) (j : Nat)
    (hj : 8 * j < bytes.length) (hnw : base.toNat + bytes.length + 8 ≤ 2 ^ 64) :
    (s.writeBytesAsWords base bytes).getMem (base + BitVec.ofNat 64 (8 * j)) =
      bytesToWordLE ((bytes.drop (8 * j)).take 8) := by
  match bytes, j with
  | [], _ => simp at hj
  | b :: bs, 0 =>
    unfold MachineState.writeBytesAsWords
    rw [getMem_writeBytesAsWords_ne _ (base + 8) _ _ ?_]
    · simp
    · intro i hi
      simp only [List.length_drop, List.length_cons] at hi
      intro heq
      have h1 := congrArg BitVec.toNat heq
      have h8 : (8 : Word).toNat = 8 := rfl
      simp only [Nat.mul_zero, BitVec.toNat_add, BitVec.toNat_ofNat, h8] at h1
      have := base.isLt
      simp only [List.length_cons] at hnw
      omega
  | b :: bs, j + 1 =>
    unfold MachineState.writeBytesAsWords
    rw [addr8_succ]
    rw [getMem_writeBytesAsWords_at _ (base + 8) _ j ?_ ?_]
    · rw [List.drop_drop, show 8 + 8 * j = 8 * (j + 1) by omega]
    · simp only [List.length_drop, List.length_cons] at hj ⊢; omega
    · simp only [List.length_drop, List.length_cons] at hj hnw ⊢
      have h8 : (8 : Word).toNat = 8 := rfl
      rw [BitVec.toNat_add, h8]
      omega
termination_by bytes.length
decreasing_by all_goals simp [List.length_drop]

/-- `HINT_LEN`'s answer on the stream `I`: the front vector's length, or `u64::MAX` when fewer than
eight bytes are left. -/
def hlenW (I : List (BitVec 8)) : Word := if I.length < 8 then -1#64 else bytesToWordLE (I.take 8)

/-- `read_vec_raw`'s `HINT_LEN` (`0x7801bebc`). -/
theorem hint_len_spec {G : MachineState → Prop} {n : Nat} {P : Prop} (u : MachineState) (I : List (BitVec 8)) (r1 r10 r12 : Word)
    (hpc : u.pc = 0x7801bebc#64) (hcode : CodeAt F_7801beb0.base F_7801beb0.prog u)
    (ht0 : u.getReg .x5 = 0xf0#64) (hI : u.privateInput = I)
    (h1 : u.getReg .x1 = r1) (h10 : u.getReg .x10 = r10) (h12 : u.getReg .x12 = r12)
    (hk : ∀ t, t.pc = 0x7801bec0#64 → t.code = u.code → CalleeSaved u t → Unchanged [] u t →
      t.privateInput = u.privateInput → t.getReg .x1 = r1 → t.getReg .x10 = r10 →
      t.getReg .x12 = r12 → t.getReg .x5 = hlenW I → SafeN G n P t) :
    SafeN G n P u := by
  have hf : u.code u.pc = some .ECALL := by rw [hpc]; exact hcode 3 (by decide)
  refine AsmVerif.RiscV.SafeN.step_of (stepSp1_hintLen hf (by rw [ht0]; rfl)) (hk _ ?_ rfl ?_ ?_ rfl ?_ ?_ ?_ ?_)
  · show u.pc + 4 = _; rw [hpc]; decide
  · intro r hr
    simp only [hintLen, MachineState.getReg_setPC]
    exact MachineState.getReg_setReg_ne _ _ _ _ (by intro h; subst h; simp [calleeSavedRegs] at hr)
  · intro a _; simp [hintLen]
  · simp only [hintLen, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide)]; exact h1
  · simp only [hintLen, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide)]; exact h10
  · simp only [hintLen, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_ne _ _ _ _ (by decide)]; exact h12
  · simp only [hintLen, MachineState.getReg_setPC]
    rw [MachineState.getReg_setReg_eq (by decide), hlenW, frontHintLen, hI]
    split_ifs
    · rfl
    · simp

/-- `HINT_READ` writes `hintWords payload` at `ptr`: every word of it. -/
theorem region_hintRead (s : MachineState) (ptr : Word) (payload : List (BitVec 8))
    (hnw : ptr.toNat + 8 * (payload.length / 8 + 2) ≤ 2 ^ 64) :
    Region ptr (hintWords payload)
      ((s.writeBytesAsWords ptr payload).setMem (ptr + BitVec.ofNat 64 (8 * (payload.length / 8)))
        (bytesToWordLE (payload.drop (8 * (payload.length / 8))))) := by
  intro i hi
  rw [hintWords_length] at hi
  have hget : (hintWords payload)[i]! = bytesToWordLE ((payload.drop (8 * i)).take 8) := by
    simp [hintWords, hi]
  rw [hget]
  by_cases hlast : i = payload.length / 8
  · subst hlast
    rw [MachineState.getMem_setMem_eq, List.take_of_length_le (by simp; omega)]
  · rw [MachineState.getMem_setMem_ne, getMem_writeBytesAsWords_at _ _ _ _ (by omega) (by omega)]
    intro heq
    have h1 := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h1
    omega

/-- ... and nothing outside its `payload.length / 8 + 1` words. -/
theorem unchanged_hintRead (s : MachineState) (ptr : Word) (payload : List (BitVec 8))
    (hnw : ptr.toNat + 8 * (payload.length / 8 + 2) ≤ 2 ^ 64) :
    Unchanged [(ptr, payload.length / 8 + 1)] s
      ((s.writeBytesAsWords ptr payload).setMem (ptr + BitVec.ofNat 64 (8 * (payload.length / 8)))
        (bytesToWordLE (payload.drop (8 * (payload.length / 8))))) := by
  intro a ha
  have hn := ha _ (List.mem_singleton_self _)
  simp only [InRegion, not_and_or, Nat.not_le, Nat.not_lt] at hn
  have key : ∀ i, i ≤ payload.length / 8 → a ≠ ptr + BitVec.ofNat 64 (8 * i) := by
    intro i hi heq
    have h1 := congrArg BitVec.toNat heq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
    omega
  rw [MachineState.getMem_setMem_ne (key _ le_rfl), getMem_writeBytesAsWords_ne]
  intro i hi
  exact key i (by omega)

/-- `writeBytesAsWords` touches only memory. -/
theorem frame_writeBytesAsWords (s : MachineState) (base : Word) (bytes : List (BitVec 8)) :
    (s.writeBytesAsWords base bytes).regs = s.regs ∧ (s.writeBytesAsWords base bytes).pc = s.pc ∧
      (s.writeBytesAsWords base bytes).code = s.code := by
  match bytes with
  | [] => unfold MachineState.writeBytesAsWords; exact ⟨rfl, rfl, rfl⟩
  | b :: bs =>
    unfold MachineState.writeBytesAsWords
    obtain ⟨h1, h2, h3⟩ := frame_writeBytesAsWords
      (s.setMem base (bytesToWordLE ((b :: bs).take 8))) (base + 8) ((b :: bs).drop 8)
    exact ⟨h1, h2, h3⟩
termination_by bytes.length
decreasing_by simp [List.length_drop]

/-- The words `B` written over the start of the block `J`, at `J`'s length: a fixed-size window on
a write of symbolic size. -/
def overlay (B J : List Word) : List Word :=
  (List.range J.length).map (fun i => if i < B.length then B[i]! else J[i]!)

@[simp] theorem overlay_length (B J : List Word) : (overlay B J).length = J.length := by
  simp [overlay]

/-- A block written over the start of a region, the rest of it unchanged. -/
theorem region_overlay {ptr : Word} {B J : List Word} {u t : MachineState} (hB : Region ptr B t)
    (hJ : Region ptr J u) (hU : Unchanged [(ptr, B.length)] u t)
    (hnw : ptr.toNat + 8 * J.length ≤ 2 ^ 64) : Region ptr (overlay B J) t := by
  intro i hi
  rw [overlay_length] at hi
  have hget : (overlay B J)[i]! = if i < B.length then B[i]! else J[i]! := by
    simp [overlay, hi]
  rw [hget]
  split
  · exact hB i (by assumption)
  · rw [hU _ ?_]
    · exact hJ i hi
    · intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      simp only [InRegion, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

/-- `read_vec_raw`'s `HINT_READ` (`0x7801befc`). A trap (an exhausted stream, a length or alignment
mismatch, a window past SP1's memory) is not an accepting halt, so the continuation is only asked
for when the read goes through. -/
theorem hint_read_spec {G : MachineState → Prop} {nb : Nat} {P : Prop} (u : MachineState) (I : List (BitVec 8)) (r1 ptr len r12 r13 : Word)
    (J : List Word)
    (hpc : u.pc = 0x7801befc#64) (hcode : CodeAt F_7801beb0.base F_7801beb0.prog u)
    (ht0 : u.getReg .x5 = 0xf1#64) (hI : u.privateInput = I)
    (h1 : u.getReg .x1 = r1) (h10 : u.getReg .x10 = ptr) (h11 : u.getReg .x11 = len)
    (h12 : u.getReg .x12 = r12) (h13 : u.getReg .x13 = r13)
    (hJ : Region ptr J u) (hokJ : RegionOk Ro.layout.textLo Ro.layout.textHi ptr J.length)
    (hk : ∀ (t : MachineState) (B : List Word), t.pc = 0x7801bf00#64 → t.code = u.code →
      CalleeSaved u t → t.getReg .x1 = r1 → t.getReg .x10 = ptr → t.getReg .x11 = len →
      t.getReg .x12 = r12 → t.getReg .x13 = r13 → t.privateInput = I.drop (8 + len.toNat) →
      bytesToWordLE (I.take 8) = len → 8 + len.toNat ≤ I.length →
      ptr.toNat + 8 * (len.toNat / 8 + 1) ≤ 0x2000000000 →
      hintWords ((I.drop 8).take len.toNat) = B → B.length = len.toNat / 8 + 1 →
      Region ptr (overlay B J) t →
      Unchanged [(ptr, len.toNat / 8 + 1)] u t → SafeN G nb P t) :
    SafeN G nb P u := by
  subst hI
  have hf : u.code u.pc = some .ECALL := by rw [hpc]; exact hcode 19 (by decide)
  have hstep := stepSp1_hintRead hf (by rw [ht0]; rfl)
  cases h : hintRead u with
  | none =>
    rw [h] at hstep
    exact AsmVerif.RiscV.SafeN.stuck hstep (fun ha => absurd (ha.2.1.symm.trans ht0) (by decide))
  | some t =>
    rw [h] at hstep
    refine AsmVerif.RiscV.SafeN.step_of hstep ?_
    unfold hintRead at h
    rcases hfl : frontHintLen u with _ | n
    · rw [hfl] at h; exact absurd h (by simp)
    rw [hfl] at h
    simp only [h10, h11] at h
    split_ifs at h with ha hw hl hp
    simp only [Option.some.injEq] at h
    subst h
    have hn : (bytesToWordLE (u.privateInput.take 8)).toNat = n := by
      unfold frontHintLen at hfl; split_ifs at hfl; simpa using hfl
    have hlen : len.toNat = n := by simpa using hl
    have hlv : bytesToWordLE (u.privateInput.take 8) = len := BitVec.eq_of_toNat_eq (by omega)
    have hwin : ptr.toNat + 8 * (n / 8 + 1) ≤ SP1_MAX_MEMORY := by
      have hw' : hintWindowOk u ptr n = true := by simpa using hw
      unfold hintWindowOk at hw'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hw'
      exact hw'.1
    have hpl : ((u.privateInput.drop 8).take n).length = n := by simp; omega
    have hnw : ptr.toNat + 8 * (((u.privateInput.drop 8).take n).length / 8 + 2) ≤ 2 ^ 64 := by
      rw [hpl]; unfold SP1_MAX_MEMORY at hwin; omega
    obtain ⟨hR, hP, hC⟩ := frame_writeBytesAsWords u ptr ((u.privateInput.drop 8).take n)
    have hreg : ∀ (X : List (BitVec 8)) (p : Word) (r : Reg) (tl w : Word),
        ({ ((u.writeBytesAsWords ptr ((u.privateInput.drop 8).take n)).setMem tl w) with
            privateInput := X }.setPC p : MachineState).getReg r = u.getReg r := by
      intro X p r tl w
      unfold MachineState.getReg
      split
      · rfl
      · exact congrFun hR _
    refine hk _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hlv (by omega) (by rw [hlen]; exact hwin) rfl
      (by rw [hintWords_length, hlen, hpl]) ?_ ?_
    · show (u.writeBytesAsWords ptr ((u.privateInput.drop 8).take n)).pc + 4 = _
      rw [hP, hpc]; decide
    · exact hC
    · intro r _; exact hreg _ _ _ _ _
    · exact (hreg _ _ _ _ _).trans h1
    · exact (hreg _ _ _ _ _).trans h10
    · exact (hreg _ _ _ _ _).trans h11
    · exact (hreg _ _ _ _ _).trans h12
    · exact (hreg _ _ _ _ _).trans h13
    · show List.drop (8 + n) u.privateInput = _; rw [hlen]
    · have hR := region_hintRead u ptr ((u.privateInput.drop 8).take n) hnw
      have hU := unchanged_hintRead u ptr ((u.privateInput.drop 8).take n) hnw
      rw [hpl] at hR hU
      rw [hlen]
      have hJn := hokJ.inMem
      unfold SP1_MAX_MEMORY at hJn
      refine region_overlay ?_ hJ ?_ (by omega)
      · exact hR
      · rw [hintWords_length, hpl]; exact hU
    · have := unchanged_hintRead u ptr ((u.privateInput.drop 8).take n) hnw
      rw [hpl] at this
      rw [hlen]
      exact this

end Cases.Zip2005
