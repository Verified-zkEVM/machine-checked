/-
  Examples.Crc32

  `crc32(crc, p, n)` of `src/c/crc32.c`, compiled by clang: CRC-32 four bits at a time, with a
  table of sixteen 32-bit words in `.rodata` at `0x1005c`. Its contract at Lprog, proved with
  `lsym`, and the same statement over riscv-zkvm's machine (`crc32_correct`).

  The specification is a fold over the bytes (`crc32Spec`). The table is read from memory, so
  the precondition says memory holds it (`TableAt`); that the table's addresses are valid and
  aligned is proved, not assumed. The loop ends when the pointer equals `p + n`, and with `n`
  below `2 ^ 64` that happens after exactly `n` bytes, so nothing is asked of `p + n` beyond the
  bytes being readable.

  The result is a 32-bit value in a 64-bit register. With `n ≠ 0` it is sign-extended (`lw` and
  `srliw` sign-extend, `not` flips all 64 bits); with `n = 0` the function returns its first
  argument untouched, upper bits included. So the statement for every `n` is about the low 32
  bits, with the sign extension for `n ≠ 0` beside it.
-/

import Examples.Gen.Crc32
import Examples.Kit

namespace Examples.Crc32

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog MachineChecked.RiscV.Lift
open Lprog.RiscV Lprog.RiscV.Machine Examples.Gen.Crc32

/-- The functions' entries are aligned. -/
theorem hok : ProgOk fns := by decide

/-- The table of the reflected polynomial `0xEDB88320`, for four bits at a time. -/
def table : List (BitVec 32) :=
  [0x00000000, 0x1db71064, 0x3b6e20c8, 0x26d930ac, 0x76dc4190, 0x6b6b51f4, 0x4db26158, 0x5005713c,
   0xedb88320, 0xf00f9344, 0xd6d6a3e8, 0xcb61b38c, 0x9b64c2b0, 0x86d3d2d4, 0xa00ae278, 0xbdbdf21c]

/-- The table's entry for a nibble. -/
def tbl (i : BitVec 4) : BitVec 32 := table.getD i.toNat 0

/-- Four bits of the CRC. -/
def nib (c : BitVec 32) : BitVec 32 := (c >>> 4) ^^^ tbl (c.setWidth 4)

/-- One byte of the CRC. -/
def crcStep (c : BitVec 32) (b : BitVec 8) : BitVec 32 := nib (nib (c ^^^ b.zeroExtend 32))

/-- CRC-32 of `bytes`, continuing from `crc`. -/
def crc32Spec (crc : BitVec 32) (bytes : List (BitVec 8)) : BitVec 32 :=
  ~~~ (bytes.foldl crcStep (~~~ crc))

/-- The check value of CRC-32: that of the ASCII digits `123456789`. -/
example : crc32Spec 0 [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38, 0x39] = 0xcbf43926 := by
  decide

/-- Memory holds the table at `0x1005c`. -/
def TableAt (m : MachineState) : Prop :=
  ∀ i : BitVec 4, m.getWord32 (0x1005c#64 + 4#64 * i.zeroExtend 64) = tbl i

/-- A table index as the code computes it, and as `TableAt` writes it. -/
theorem tbl_addr (x : Word) : (x &&& 15#64) <<< 2 = 4#64 * (x.setWidth 4).zeroExtend 64 := by
  bv_decide

/-- The table is in SP1's memory. -/
theorem tbl_valid (x : Word) : isValidMemAddrSp1 (65628#64 + (x &&& 15#64) <<< 2) = true := by
  rw [tbl_addr]
  simp [isValidMemAddrSp1, SP1_MAX_MEMORY]
  bv_omega

/-- The table's words are aligned. -/
theorem tbl_aligned (x : Word) : alignedFor 4 (65628#64 + (x &&& 15#64) <<< 2) = true := by
  rw [tbl_addr]
  simp [alignedFor, isAligned4]

/-- A load from the table. -/
theorem tbl_load {m : MachineState} (h : TableAt m) (x : Word) :
    m.getWord32 (65628#64 + (x &&& 15#64) <<< 2) = tbl (x.setWidth 4) := by
  rw [tbl_addr]; exact h _

/-- One iteration's `x13`, as `lsym` leaves it, is `crcStep` of its low 32 bits, sign-extended. -/
theorem step_eq (c : Word) (b : BitVec 8) :
    BitVec.signExtend 64
              (BitVec.setWidth 32
                ((BitVec.setWidth 64
                      (BitVec.setWidth 32
                        (BitVec.signExtend 64
                          (BitVec.setWidth 32
                            ((BitVec.setWidth 64 (BitVec.setWidth 32 c) ^^^ BitVec.setWidth 64 b) >>>
                              4)))) ^^^
                    BitVec.setWidth 64
                      (BitVec.setWidth 32
                        (BitVec.signExtend 64 (tbl (BitVec.setWidth 4 c ^^^ BitVec.setWidth 4 b))))) >>>
                  4)) ^^^
            BitVec.signExtend 64
              (tbl
                (BitVec.setWidth 4
                    (BitVec.signExtend 64
                      (BitVec.setWidth 32
                        ((BitVec.setWidth 64 (BitVec.setWidth 32 c) ^^^ BitVec.setWidth 64 b) >>> 4))) ^^^
                  BitVec.setWidth 4
                    (BitVec.signExtend 64 (tbl (BitVec.setWidth 4 c ^^^ BitVec.setWidth 4 b))))) =
      BitVec.signExtend 64 (crcStep (c.setWidth 32) b) := by
  simp only [crcStep, nib]
  have e1 : BitVec.setWidth 4 (BitVec.setWidth 32 c ^^^ BitVec.zeroExtend 32 b) =
      BitVec.setWidth 4 c ^^^ BitVec.setWidth 4 b := by bv_decide
  rw [e1]
  generalize tbl (BitVec.setWidth 4 c ^^^ BitVec.setWidth 4 b) = t1
  have e2 : BitVec.setWidth 4 ((BitVec.setWidth 32 c ^^^ BitVec.zeroExtend 32 b) >>> 4 ^^^ t1) =
      BitVec.setWidth 4
                    (BitVec.signExtend 64
                      (BitVec.setWidth 32
                        ((BitVec.setWidth 64 (BitVec.setWidth 32 c) ^^^ BitVec.setWidth 64 b) >>> 4))) ^^^
                  BitVec.setWidth 4 (BitVec.signExtend 64 t1) := by bv_decide
  rw [e2]
  generalize tbl _ = t2
  bv_decide

/-- The registers `crc32` may change. -/
def clobbered : List Reg := [.x10, .x11, .x12, .x13, .x14]

theorem bytesAt_succ (m : MachineState) (p : Word) (j : Nat) :
    bytesAt m p (j + 1) = bytesAt m p j ++ [m.getByte (p + BitVec.ofNat 64 j)] := by
  simp [bytesAt, List.range_succ]

theorem last_byte {j n : Nat} (hj : j < n) (hn : n < 2 ^ 64)
    (h : BitVec.ofNat 64 j + 1#64 = BitVec.ofNat 64 n) : j + 1 = n := by
  bv_omega

/-- **The byte loop**, at its head with `j < n` bytes done: `x13` holds the running CRC in its
    low 32 bits, and the loop leaves the complement of the CRC of all `n` bytes, sign-extended. -/
theorem loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m : MachineState) (regs0 : Reg → Word) (p : Word) (n : Nat) (c0 : BitVec 32)
    (hn : n < 2 ^ 64) (htbl : TableAt m)
    (hv : ∀ i < n, isValidMemAddrSp1 (p + BitVec.ofNat 64 i) = true)
    (hpost : ∀ r', r' .x10 = BitVec.signExtend 64 (~~~ ((bytesAt m p n).foldl crcStep c0)) →
      (∀ r, r ∉ clobbered → r' r = regs0 r) → LSafeN fns G N Q ⟨rest, r', m⟩) :
    ∀ k j (regs : Reg → Word), n - j = k → j < n →
      regs .x10 = 0x1005c#64 → regs .x11 = p + BitVec.ofNat 64 j →
      regs .x12 = p + BitVec.ofNat 64 n →
      (regs .x13).setWidth 32 = (bytesAt m p j).foldl crcStep c0 →
      regs .x1 = ret → regs .x2 = top → (∀ r, r ∉ clobbered → regs r = regs0 r) →
      LSafeN fns G N Q ⟨⟨0, 10, ret, top⟩ :: rest, regs, m⟩ := by
  intro k
  induction k with
  | zero => intro j _ hk hj; omega
  | succ k ih =>
    intro j regs hk hj h10 h11 h12 h13 hra hsp hkept
    lsym f0_eq stop [10] with [h10, h11, h12, hra, hsp, tbl_valid, tbl_aligned, tbl_load htbl, hv j hj]
    · -- more bytes: the back edge
      have hlt : j + 1 < n := by
        rcases Nat.lt_or_ge (j + 1) n with h | h
        · exact h
        · exact absurd (by rw [ofNat_succ]; congr 1; omega) hc
      apply ih (j + 1) _ (by omega) hlt
      · simp [lsym_simp, h10]
      · simp [lsym_simp, ofNat_succ]
      · simp [lsym_simp, h12]
      · rw [bytesAt_succ, List.foldl_append, ← h13]
        simp only [lsym_simp, List.foldl, step_eq]
        generalize crcStep _ _ = v
        bv_decide
      · simp [lsym_simp, hra]
      · simp [lsym_simp, hsp]
      · intro r hr
        rw [← hkept r hr]
        simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [lsym_simp, hr]
    · -- the last byte
      obtain rfl := last_byte hj hn hc
      apply hpost
      · rw [bytesAt_succ, List.foldl_append, ← h13]
        simp only [lsym_simp, List.foldl, step_eq]
        generalize crcStep _ _ = v
        bv_decide
      · intro r hr
        rw [← hkept r hr]
        simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        simp [lsym_simp, hr]

/-- `crc32(crc, p, n)`: the low 32 bits of the result are the CRC-32 of the `n` bytes at `p`
    continuing from the low 32 bits of `crc`; with `n ≠ 0` the result is that value sign-extended
    (with `n = 0` the register is returned as it came, upper bits included). The table must be
    in memory and the bytes readable. Memory and the registers outside `x10`..`x14` are kept. -/
theorem crc32_contract : rvIsa.Contract (liftProg fns) sp1Ctx 0
    (fun ret top regs m => regs .x1 = ret ∧ regs .x2 = top ∧ TableAt m ∧
      ∀ i < (regs .x12).toNat, isValidMemAddrSp1 (regs .x11 + BitVec.ofNat 64 i) = true)
    (fun _ _ regs m r' m' =>
      (r' .x10).setWidth 32 =
        crc32Spec ((regs .x10).setWidth 32) (bytesAt m (regs .x11) (regs .x12).toNat) ∧
      (regs .x12 ≠ 0 → r' .x10 = BitVec.signExtend 64
        (crc32Spec ((regs .x10).setWidth 32) (bytesAt m (regs .x11) (regs .x12).toNat))) ∧
      (∀ r, r ∉ clobbered → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp, htbl, hv⟩ hk
  lsym f0_eq stop [10] with [hra, hsp]
  · -- no bytes
    apply hk
    refine ⟨?_, fun h => absurd hc h, fun _ _ => rfl, rfl⟩
    simp [hc, bytesAt, crc32Spec]
  · -- some bytes: the loop
    have hpos : 0 < (regs .x12).toNat := by
      rcases Nat.eq_zero_or_pos (regs .x12).toNat with h | h
      · exact absurd (BitVec.eq_of_toNat_eq h) hc
      · exact h
    refine loop m regs (regs .x11) (regs .x12).toNat (~~~ (regs .x10).setWidth 32) (regs .x12).isLt
      htbl hv (fun r' h10 hkept => hk r' m ⟨?_, fun _ => h10, hkept, rfl⟩) _ 0 _ rfl hpos ?_ ?_ ?_ ?_
      ?_ ?_ ?_
    · rw [h10]; unfold crc32Spec; generalize List.foldl _ _ _ = v; bv_decide
    · simp [lsym_simp]
    · simp [lsym_simp]
    · simp [lsym_simp]
    · simp only [lsym_simp, bytesAt, List.range_zero, List.map_nil, List.foldl_nil]
      bv_decide
    · simp [lsym_simp, hra]
    · simp [lsym_simp, hsp]
    · intro r hr
      simp only [clobbered, List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      simp [lsym_simp, hr]

/-- **`crc32` on the machine.** -/
theorem crc32_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10000#64) (hcode : Loaded fns s) (htbl : TableAt s)
    (hv : ∀ i < (s.getReg .x12).toNat,
      isValidMemAddrSp1 (s.getReg .x11 + BitVec.ofNat 64 i) = true)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      (t.getReg .x10).setWidth 32 = crc32Spec ((s.getReg .x10).setWidth 32)
        (bytesAt s (s.getReg .x11) (s.getReg .x12).toNat) →
      (s.getReg .x12 ≠ 0 → t.getReg .x10 = BitVec.signExtend 64
        (crc32Spec ((s.getReg .x10).setWidth 32)
          (bytesAt s (s.getReg .x11) (s.getReg .x12).toNat))) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[0]? = some fn ∧ fn.base = 0x10000#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode crc32_contract ⟨rfl, rfl, htbl, hv⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, h10', -, rfl⟩
  have e : t.getReg .x10 = r' .x10 := by
    rw [← hag.regs, getReg_ofParts]; simp
  refine hk t hpc' ?_ ?_ fun a => (hag.mem a).symm
  · rw [e]; exact h10
  · rw [e]; exact h10'

end Examples.Crc32
