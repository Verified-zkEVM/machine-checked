import Cases.CatCrypt.Fe
import Cases.CatCrypt.Image.FeAdd

/-!
# CatCrypt's RV64 field addition mod `2^255 - 19`, on riscv-zkvm

Ported from catcrypt-compiler's `feAddBytes_correct` (`RiscvBytesProof`, rv64 stack). The 186
instructions, decoded by riscv-zkvm, take any `x` in `a0..a3` and `y` in `a4..a7` to
`(x + y) mod p25519` in `a0..a3`.

`bv_decide` checks that the block's result `r` is below `p25519` and that
`x + y = r + k·p25519` for some `k ≤ 4`.
-/

namespace Cases.CatCrypt.FeAdd

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Lprog Cases.CatCrypt.Image.FeAdd

/-- What the block's registers `ρ` satisfy, from inputs in `m`: the result `r` in `a0..a3` is
    below `p25519` and `x + y = r + k·p25519` for some `k ≤ 4`. -/
def Spec (m : MachineState) (ρ : Reg → Word) : Prop :=
  let X := (cat4 (m.getReg .x10) (m.getReg .x11) (m.getReg .x12) (m.getReg .x13)).zeroExtend 258
  let Y := (cat4 (m.getReg .x14) (m.getReg .x15) (m.getReg .x16) (m.getReg .x17)).zeroExtend 258
  let R := cat4 (ρ .x10) (ρ .x11) (ρ .x12) (ρ .x13)
  R < BitVec.ofNat 256 p25519 ∧
    (X + Y = R.zeroExtend 258 + BitVec.ofNat 258 (0 * p25519) ∨
      X + Y = R.zeroExtend 258 + BitVec.ofNat 258 (1 * p25519) ∨
      X + Y = R.zeroExtend 258 + BitVec.ofNat 258 (2 * p25519) ∨
      X + Y = R.zeroExtend 258 + BitVec.ofNat 258 (3 * p25519) ∨
      X + Y = R.zeroExtend 258 + BitVec.ofNat 258 (4 * p25519))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem bv (m : MachineState) : Spec m (prog.foldl stepRegs m.getReg) := by
  simp only [prog]
  regs_run
  simp only [Spec, cat4, p25519, upd, reduceCtorEq, if_false, if_true]
  bv_decide (config := { timeout := 1200, enums := false })

set_option maxRecDepth 100000 in
/-- **Field addition on riscv-zkvm.** -/
theorem corres (base : Word) :
    CorresSp1 (KSR base prog) (KPre fun _ _ => True) (KSpec fun x y => (x + y) % p25519) := by
  refine kernel_corres base prog (by decide) _ _ ?_
  intro m _
  have hp : (BitVec.ofNat 256 p25519).toNat = p25519 := by simp [p25519]
  obtain ⟨hR, hsum⟩ := bv m
  rw [regA_eq, regA_eq, regB_eq]
  simp only [getReg_foldl prog m (by decide)]
  generalize prog.foldl stepRegs m.getReg = ρ at hR hsum ⊢
  rw [BitVec.lt_def, hp] at hR
  rcases hsum with h | h | h | h | h <;>
    exact eq_mod_of_eq_add_mul hR (sum_of_zext (by decide) h)

end Cases.CatCrypt.FeAdd
