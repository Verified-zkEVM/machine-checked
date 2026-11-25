/-
  MachineChecked.ARM.Lift.Sound.Reverse

  The lift of AArch64 against arm64-semantics: the reversals of bytes and of bits (`rev`,
  `rev16`, `rev32`, `rbit`). The lift reverses by swapping halves of ever wider runs in `t0`;
  the machine reverses bytes by taking them apart, and bits in a loop.

  The counts of leading zeros and signs (`clz`, `cls`) are not proved yet.

  ## Main results

  * `reverseBits_foldl`: the machine's loop as a fold
  * `rev_sound`: the four instructions
-/

import MachineChecked.ARM.Lift.Sound.Basic

namespace MachineChecked.ARM.Lift

open Lprog Lprog.ARM Lprog.Build
open Arm64 (Instr RegWidth MemWidth)

variable {regs : Reg → BitVec 64} {m : Arm64.Memory} {s : Arm64.State}

/-- The machine's reversal of bits, as a fold. -/
theorem reverseBits_foldl {n : Nat} (v : BitVec n) :
    Arm64.reverseBits v = (List.range' 0 n).foldl
      (fun acc i => if v.getLsbD i then acc ||| (BitVec.ofNat n 1 <<< (n - 1 - i)) else acc) 0 := by
  have key : ∀ (l : List Nat) (init : BitVec n),
      (forIn (m := Id) l init fun i acc =>
        if v.getLsbD i = true then pure (ForInStep.yield (acc ||| BitVec.ofNat n 1 <<< (n - 1 - i)))
        else pure (ForInStep.yield acc)) =
      pure (l.foldl (fun acc i => if v.getLsbD i then acc ||| (BitVec.ofNat n 1 <<< (n - 1 - i))
        else acc) init) := by
    intro l
    induction l with
    | nil => intro init; rfl
    | cons a l ih =>
      intro init
      simp only [List.forIn_cons, List.foldl_cons]
      split <;> simp [*]
  simp only [Arm64.reverseBits, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have e : (n - 0 + 1 - 1) / 1 = n := by simp
  rw [e]
  exact key _ _

/-- Each run of `k` bits swapped with the next; `mk` masks the lower of each pair. -/
def sw (k : Nat) (mk : Nat) (v : BitVec 64) : BitVec 64 :=
  (v &&& BitVec.ofNat 64 mk) <<< k ||| (v >>> k) &&& BitVec.ofNat 64 mk

/-- The reversal of the bits of 64, by six swaps. -/
def rbits (x : BitVec 64) : BitVec 64 :=
  sw 32 0x00000000ffffffff (sw 16 0x0000ffff0000ffff (sw 8 0x00ff00ff00ff00ff
    (sw 4 0x0f0f0f0f0f0f0f0f (sw 2 0x3333333333333333 (sw 1 0x5555555555555555 x)))))

theorem rev16_eq (x : BitVec 64) : sw 8 0x00ff00ff00ff00ff x = Arm64.rev16_64 x := by
  simp only [sw, Arm64.rev16_64]; bv_decide

theorem rev32_eq (x : BitVec 64) :
    sw 16 0x0000ffff0000ffff (sw 8 0x00ff00ff00ff00ff x) = Arm64.rev32_64 x := by
  simp only [sw, Arm64.rev32_64]; bv_decide

theorem rev64_eq (x : BitVec 64) :
    sw 32 0x00000000ffffffff (sw 16 0x0000ffff0000ffff (sw 8 0x00ff00ff00ff00ff x)) =
      Arm64.rev64 x := by
  simp only [sw, Arm64.rev64]; bv_decide

set_option maxRecDepth 8000 in
theorem rbit64_eq (x : BitVec 64) : rbits x = Arm64.reverseBits x := by
  rw [reverseBits_foldl]
  simp only [rbits, sw, List.range', List.foldl, Nat.reduceAdd, Nat.reduceSub]
  bv_decide

set_option maxRecDepth 8000 in
theorem rbit32_eq (x : BitVec 64) (hx : x = (x.setWidth 32).setWidth 64) :
    rbits x >>> 32 = (Arm64.reverseBits (x.truncate 32)).zeroExtend 64 := by
  rw [reverseBits_foldl]
  simp only [rbits, sw, List.range', List.foldl, Nat.reduceAdd, Nat.reduceSub]
  bv_decide

theorem rev16_32_eq (x : BitVec 64) (hx : x = (x.setWidth 32).setWidth 64) :
    sw 8 0x00ff00ff00ff00ff x = ((Arm64.rev16_64 x).truncate 32).zeroExtend 64 := by
  simp only [sw, Arm64.rev16_64]; bv_decide

theorem rev32_32_eq (x : BitVec 64) (hx : x = (x.setWidth 32).setWidth 64) :
    sw 16 0x0000ffff0000ffff (sw 8 0x00ff00ff00ff00ff x) =
      ((Arm64.rev32_64 x).truncate 32).zeroExtend 64 := by
  simp only [sw, Arm64.rev32_64]; bv_decide

/-- A value computed in `t0` and written to a register. -/
theorem t0_run (h : Agree regs m s) {dst : Arm64.Reg} (hd : Wf dst) (V : BitVec 64) (e : E) :
    ∃ r', run (wr dst e) (updReg regs .t0 V) m = some (r', m) ∧
      Agree r' m (s.writeReg64 dst (e.eval (updReg regs .t0 V))).advancePC := by
  obtain ⟨r', h1, h2, -⟩ := wr_run (h.scratch (.inl rfl) V) hd e
  exact ⟨r', h1, h2.advancePC⟩

theorem run_swap_t0 (R : Reg → BitVec 64) (V : BitVec 64) (k mk : Nat) (hk : k < 2 ^ 64)
    (os : List O) :
    run (swap .t0 k mk :: os) (updReg R .t0 V) m = run os (updReg R .t0 (sw k mk V)) m := by
  simp [swap, sw, updReg_updReg, updReg, Nat.mod_eq_of_lt hk]

/-- The operations of a reversal run to `t0` holding `V`. -/
theorem rev_run (h : Agree regs m s) {dst : Arm64.Reg} (hd : Wf dst) {os : List O} {e : E}
    {V : BitVec 64} (ho : run (os ++ wr dst e) regs m = run (wr dst e) (updReg regs .t0 V) m)
    {s' : Arm64.State} (hs : s' = (s.writeReg64 dst (e.eval (updReg regs .t0 V))).advancePC) :
    ∃ r', run (os ++ wr dst e) regs m = some (r', m) ∧ Agree r' m s' := by
  rw [ho, hs]
  exact t0_run h hd V e

/-- **`rev`, `rev16`, `rev32`, `rbit`.** -/
theorem rev_sound (h : Agree regs m s) (pc : BitVec 64) (w : RegWidth)
    (op : Arm64.DataProc1Op) {dst rn : Arm64.Reg} (hd : Wf dst) (hn : Wf rn)
    (hop : op ≠ .CLZ ∧ op ≠ .CLS) {os : List O}
    (ho : ops pc (.dataProc1 w op dst rn) = some os) :
    ∃ r', run os regs m = some (r', m) ∧ Agree r' m (Arm64.execDataProc1 w op dst rn s) := by
  have ex := rdw_eval h w hn
  have wx := rdw_width (regs := regs) w rn
  rw [ex] at wx
  cases w <;> cases op <;> simp only [ops] at ho <;> cases ho
  case W32.CLZ | W64.CLZ => exact absurd rfl hop.1
  case W32.CLS | W64.CLS => exact absurd rfl hop.2
  case W32.RBIT =>
    refine rev_run h hd (V := (rbits (s.readReg .W32 rn))) ?_ ?_
    · simp only [List.cons_append, List.nil_append, run_set, ex, reverseBits, Build.reverseBits, Build.reverseBytes, List.take, List.map, run_swap_t0, rbits,
        Nat.reducePow, Nat.reduceLT]
    · rw [show ((lshr (.reg .t0) (64 - RegWidth.W32.bits) : E).eval (updReg regs .t0 (rbits (s.readReg .W32 rn)))) = _ from (rbit32_eq _ (wx rfl))]
      simp [Arm64.execDataProc1, Arm64.State.writeReg]
  case W32.REV16 =>
    refine rev_run h hd (V := (sw 8 0x00ff00ff00ff00ff (s.readReg .W32 rn))) ?_ ?_
    · simp only [List.cons_append, List.nil_append, run_set, ex, reverseBytes, Build.reverseBytes, List.take, List.map, run_swap_t0, Nat.reducePow,
        Nat.reduceLT]
    · rw [show ((.reg .t0 : E).eval (updReg regs .t0 (sw 8 0x00ff00ff00ff00ff (s.readReg .W32 rn)))) = _ from (rev16_32_eq _ (wx rfl))]
      simp [Arm64.execDataProc1, Arm64.State.writeReg]
  case W32.REV32 =>
    refine rev_run h hd (V := (sw 16 0x0000ffff0000ffff (sw 8 0x00ff00ff00ff00ff (s.readReg .W32 rn)))) ?_ ?_
    · simp only [List.cons_append, List.nil_append, run_set, ex, reverseBytes, Build.reverseBytes, List.take, List.map, run_swap_t0, Nat.reducePow,
        Nat.reduceLT]
    · rw [show ((.reg .t0 : E).eval (updReg regs .t0 (sw 16 0x0000ffff0000ffff (sw 8 0x00ff00ff00ff00ff (s.readReg .W32 rn))))) = _ from (rev32_32_eq _ (wx rfl))]
      simp [Arm64.execDataProc1, Arm64.State.writeReg]
  case W32.REV =>
    refine rev_run h hd (V := (sw 16 0x0000ffff0000ffff (sw 8 0x00ff00ff00ff00ff (s.readReg .W32 rn)))) ?_ ?_
    · simp only [List.cons_append, List.nil_append, run_set, ex, reverseBytes, Build.reverseBytes, List.take, List.map, run_swap_t0, Nat.reducePow,
        Nat.reduceLT, ↓reduceIte]
    · rw [show ((.reg .t0 : E).eval (updReg regs .t0 (sw 16 0x0000ffff0000ffff (sw 8 0x00ff00ff00ff00ff (s.readReg .W32 rn))))) = _ from (rev32_32_eq _ (wx rfl))]
      simp [Arm64.execDataProc1, Arm64.State.writeReg]
  case W64.RBIT =>
    refine rev_run h hd (V := (rbits (s.readReg .W64 rn))) ?_ ?_
    · simp only [List.cons_append, List.nil_append, run_set, ex, reverseBits, Build.reverseBits, Build.reverseBytes, List.take, List.map, run_swap_t0, rbits,
        Nat.reducePow, Nat.reduceLT]
    · rw [show ((lshr (.reg .t0) (64 - RegWidth.W64.bits) : E).eval (updReg regs .t0 (rbits (s.readReg .W64 rn)))) = _ from (rbit64_eq _)]
      rfl
  case W64.REV16 =>
    refine rev_run h hd (V := (sw 8 0x00ff00ff00ff00ff (s.readReg .W64 rn))) ?_ ?_
    · simp only [List.cons_append, List.nil_append, run_set, ex, reverseBytes, Build.reverseBytes, List.take, List.map, run_swap_t0, Nat.reducePow,
        Nat.reduceLT]
    · rw [show ((.reg .t0 : E).eval (updReg regs .t0 (sw 8 0x00ff00ff00ff00ff (s.readReg .W64 rn)))) = _ from (rev16_eq _)]
      rfl
  case W64.REV32 =>
    refine rev_run h hd (V := (sw 16 0x0000ffff0000ffff (sw 8 0x00ff00ff00ff00ff (s.readReg .W64 rn)))) ?_ ?_
    · simp only [List.cons_append, List.nil_append, run_set, ex, reverseBytes, Build.reverseBytes, List.take, List.map, run_swap_t0, Nat.reducePow,
        Nat.reduceLT]
    · rw [show ((.reg .t0 : E).eval (updReg regs .t0 (sw 16 0x0000ffff0000ffff (sw 8 0x00ff00ff00ff00ff (s.readReg .W64 rn))))) = _ from (rev32_eq _)]
      rfl
  case W64.REV =>
    refine rev_run h hd (V := (sw 32 0x00000000ffffffff (sw 16 0x0000ffff0000ffff (sw 8 0x00ff00ff00ff00ff (s.readReg .W64 rn))))) ?_ ?_
    · simp only [List.cons_append, List.nil_append, run_set, ex, reverseBytes, Build.reverseBytes, List.take, List.map, run_swap_t0, Nat.reducePow,
        Nat.reduceLT, reduceCtorEq, ↓reduceIte]
    · rw [show ((.reg .t0 : E).eval (updReg regs .t0 (sw 32 0x00000000ffffffff (sw 16 0x0000ffff0000ffff (sw 8 0x00ff00ff00ff00ff (s.readReg .W64 rn)))))) = _ from (rev64_eq _)]
      rfl

end MachineChecked.ARM.Lift
