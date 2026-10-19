/-
  MachineChecked.RiscV.Exec.Hint

  SP1's input path, exactly. `Check.Ecall` gives the checker what a hint `ecall` may write
  (`SysNext`); a hand proof that reads input needs what it *does*: `HINT_LEN` sets `t0` to
  the front hint's length (`lenW`, `u64::MAX` for none) and consumes nothing; a `HINT_READ`
  that does not trap pops the hint and writes its payload at `a0` as little-endian
  doublewords plus SP1's zero-padded last one (`readMem`, through `bytesMem`, `writeBytesAsWords`
  on memory alone). `safe_hintLen`/`safe_hintRead` are the executor's steps over them.
-/

import MachineChecked.RiscV.Exec.Basic
import MachineChecked.RiscV.Check.Ecall

namespace MachineChecked.RiscV.Exec

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Frame MachineChecked.RiscV.Check

variable {G : MachineState → Prop} {k : Nat} {P : Prop}

/-- What `HINT_LEN` answers: the front hint's length, or `u64::MAX` for none. -/
def lenW (s : MachineState) : Word :=
  match frontHintLen s with
  | some n => BitVec.ofNat 64 n
  | none => -1#64

@[simp] theorem lenW_setReg (s : MachineState) (r : Reg) (v : Word) : lenW (s.setReg r v) = lenW s := by
  simp [lenW, frontHintLen]
@[simp] theorem lenW_setPC (s : MachineState) (v : Word) : lenW (s.setPC v) = lenW s := rfl
@[simp] theorem lenW_setMem (s : MachineState) (a v : Word) : lenW (s.setMem a v) = lenW s := rfl

theorem hintLen_eq (s : MachineState) : hintLen s = (s.setReg .x5 (lenW s)).setPC (s.pc + 4) := by
  unfold hintLen lenW; rfl

theorem safe_hintLen {x : MachineState} (hf : x.code x.pc = some .ECALL)
    (ht : x.getReg .x5 = 0xF0#64) (h : SafeN G k P (hintLen x)) : SafeN G k P x := by
  have hacc : Sp1.isAccelId 0xF0#64 = false := by decide
  refine SafeN.of_step (fun ha => by rw [ha.2.1] at ht; exact absurd ht (by decide)) ?_ h
  rw [stepSp1_ecall_fetch hf]
  simp [sp1Ecall, ht, hacc, Sp1.HINT_LEN]

theorem safe_hintRead {x : MachineState} (hf : x.code x.pc = some .ECALL)
    (ht : x.getReg .x5 = 0xF1#64) (h : ∀ y, hintRead x = some y → SafeN G k P y) :
    SafeN G k P x := by
  have hacc : Sp1.isAccelId 0xF1#64 = false := by decide
  have hs : stepSp1 x = hintRead x := by
    rw [stepSp1_ecall_fetch hf]
    simp [sp1Ecall, ht, hacc, Sp1.HINT_LEN, Sp1.HINT_READ]
  cases hy : hintRead x with
  | none => exact SafeN.stuck (hs.trans hy) (fun ha => by rw [ha.2.1] at ht; exact absurd ht (by decide))
  | some y =>
    exact SafeN.of_step (fun ha => by rw [ha.2.1] at ht; exact absurd ht (by decide)) (hs.trans hy) (h y hy)

/-- `writeBytesAsWords`, on memory alone. -/
def bytesMem (m : Word → Word) (base : Word) : List (BitVec 8) → Word → Word
  | [] => m
  | b :: bs => bytesMem (fun a => if a = base then bytesToWordLE ((b :: bs).take 8) else m a) (base + 8#64)
      ((b :: bs).drop 8)
termination_by l => l.length
decreasing_by simp; omega

theorem mem_writeBytesAsWords : ∀ (bs : List (BitVec 8)) (s : MachineState) (base : Word),
    (s.writeBytesAsWords base bs).getMem = bytesMem s.getMem base bs
  | [], _, _ => by simp [bytesMem]
  | b :: bs', s, base => by
    rw [MachineState.writeBytesAsWords, bytesMem, mem_writeBytesAsWords ((b :: bs').drop 8)]
    congr 1
    funext a
    simp only [getMem_setMem]
termination_by bs => bs.length
decreasing_by simp; omega

/-- What `HINT_READ` of the front `n`-byte hint leaves in memory at `p`: the payload as
    little-endian doublewords, and the zero-padded last one. -/
def readMem (m : Word → Word) (p : Word) (input : List (BitVec 8)) (n : Nat) : Word → Word :=
  fun a => if a = p + BitVec.ofNat 64 (8 * (n / 8)) then
      bytesToWordLE (((input.drop 8).take n).drop (8 * (n / 8)))
    else bytesMem m p ((input.drop 8).take n) a

/-- **`HINT_READ`, exactly**: the next state of a read that does not trap. -/
theorem hintRead_eq {x y : MachineState} {n : Nat} (hn : frontHintLen x = some n)
    (h : hintRead x = some y) :
    y.pc = x.pc + 4 ∧ y.code = x.code ∧ (∀ r, y.getReg r = x.getReg r) ∧
    y.privateInput = x.privateInput.drop (8 + n) ∧
    y.getMem = readMem x.getMem (x.getReg .x10) x.privateInput n := by
  unfold hintRead at h
  rw [hn] at h
  simp only [Bool.not_eq_true'] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  simp only [Option.some.injEq] at h
  subst h
  refine ⟨by simp [MachineState.setPC, MachineState.setMem], by simp [MachineState.setPC, MachineState.setMem],
    fun r => by simp [MachineState.getReg, MachineState.setPC, MachineState.setMem, regs_writeBytesAsWords],
    by simp [MachineState.setPC], ?_⟩
  funext a
  show (MachineState.setMem _ _ _).getMem a = _
  rw [getMem_setMem, readMem, mem_writeBytesAsWords]

/-- `getMem` as a function, through register, pc and memory writes. -/
theorem gm_setReg (s : MachineState) (r : Reg) (v : Word) : (s.setReg r v).getMem = s.getMem :=
  funext fun _ => by simp
theorem gm_setPC (s : MachineState) (v : Word) : (s.setPC v).getMem = s.getMem := rfl
theorem gm_setMem (s : MachineState) (a v : Word) :
    (s.setMem a v).getMem = fun x => if x = a then v else s.getMem x := funext fun _ => getMem_setMem

end MachineChecked.RiscV.Exec
