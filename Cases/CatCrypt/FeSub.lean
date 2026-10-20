import Cases.CatCrypt.Fe
import MachineChecked.RiscV.Corres.Regs
import Cases.CatCrypt.Image.FeSub

/-!
# CatCrypt's RV64 field subtraction mod `2^255 - 19`, on riscv-zkvm

Ported from catcrypt-compiler's `feSubBytes_correct` (`RiscvBytesProof`, rv64 stack). The 216
instructions, decoded by riscv-zkvm, take `x` in `a0..a3` and `y ≤ x + 2·p25519` in `a4..a7`
to `(x + 2·p25519 - y) mod p25519` in `a0..a3`.

`bv_decide` checks that the block's result `r` is below `p25519` and that
`x + 2·p25519 = y + r + k·p25519` for some `k ≤ 4`.
-/

namespace Cases.CatCrypt.FeSub

open RiscvZkvm.Rv64 MachineChecked.RiscV Cases.CatCrypt.Image.FeSub

/-- What the block's registers `ρ` satisfy, from inputs in `m`. -/
def Spec (m : MachineState) (ρ : Reg → Word) : Prop :=
  let X := (cat4 (m.getReg .x10) (m.getReg .x11) (m.getReg .x12) (m.getReg .x13)).zeroExtend 258
  let Y := (cat4 (m.getReg .x14) (m.getReg .x15) (m.getReg .x16) (m.getReg .x17)).zeroExtend 258
  let R := cat4 (ρ .x10) (ρ .x11) (ρ .x12) (ρ .x13)
  let P2 := BitVec.ofNat 258 (2 * p25519)
  Y ≤ X + P2 →
  R < BitVec.ofNat 256 p25519 ∧
    (X + P2 = Y + R.zeroExtend 258 + BitVec.ofNat 258 (0 * p25519) ∨
      X + P2 = Y + R.zeroExtend 258 + BitVec.ofNat 258 (1 * p25519) ∨
      X + P2 = Y + R.zeroExtend 258 + BitVec.ofNat 258 (2 * p25519) ∨
      X + P2 = Y + R.zeroExtend 258 + BitVec.ofNat 258 (3 * p25519) ∨
      X + P2 = Y + R.zeroExtend 258 + BitVec.ofNat 258 (4 * p25519))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem bv (m : MachineState) : Spec m (prog.foldl stepRegs m.getReg) := by
  simp only [prog]
  regs_run
  simp only [Spec, cat4, p25519, upd, reduceCtorEq, if_false, if_true]
  bv_decide (config := { timeout := 1200 })

set_option maxRecDepth 100000 in
/-- **Field subtraction on riscv-zkvm.** -/
theorem corres (base : Word) :
    Corres (KSR base prog) (KPre fun x y => y ≤ x + 2 * p25519)
      (KSpec fun x y => (x + 2 * p25519 - y) % p25519) 216 := by
  rw [← show prog.length = 216 from rfl]
  refine kernel_corres base prog (by decide) _ _ ?_
  intro m hy
  rw [regA_eq, regB_eq] at hy
  have hp : (BitVec.ofNat 256 p25519).toNat = p25519 := by simp [p25519]
  have hp2 : 2 * p25519 < 2 ^ 256 := by decide
  have hle := zext_le_add hp2 hy
  obtain ⟨hR, hsum⟩ := bv m hle
  rw [regA_eq, regA_eq, regB_eq]
  simp only [getReg_foldl prog m (by decide)]
  generalize prog.foldl stepRegs m.getReg = ρ at hR hsum ⊢
  rw [BitVec.lt_def, hp] at hR
  rcases hsum with h | h | h | h | h <;>
    exact eq_sub_mod_of_eq hR (sum3_of_zext hp2 (by decide) h)

end Cases.CatCrypt.FeSub
