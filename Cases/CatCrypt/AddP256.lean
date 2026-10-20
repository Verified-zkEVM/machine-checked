import Cases.CatCrypt.Fe
import Cases.CatCrypt.Image.AddP256

/-!
# CatCrypt's RV64 `bignum_add_p256`, on riscv-zkvm

Ported from catcrypt-compiler's `addp256Bytes_correct` (`RiscvBytesProof`, rv64 stack). The
83 instructions, decoded by riscv-zkvm, take `x` in `a0..a3` and `y` in `a4..a7`, both below
`p256`, to `(x + y) mod p256` in `a0..a3`.

The block's effect is computed by unfolding the fold of `execInstrBr`; `bv_decide` checks
that its result `r` satisfies `x + y = r + c·p256` with `r < p256` and `c ∈ {0, 1}`.
-/

namespace Cases.CatCrypt.AddP256

open RiscvZkvm.Rv64 MachineChecked.RiscV Cases.CatCrypt.Image.AddP256

/-- The NIST P-256 prime. -/
def p256 : Nat := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

/-- The block's result, as a 256-bit identity. -/
theorem bv (m : MachineState)
    (hx : cat4 (m.getReg .x10) (m.getReg .x11) (m.getReg .x12) (m.getReg .x13) < BitVec.ofNat 256 p256)
    (hy : cat4 (m.getReg .x14) (m.getReg .x15) (m.getReg .x16) (m.getReg .x17) < BitVec.ofNat 256 p256) :
    let m' := prog.foldl execInstrBr m
    let X := (cat4 (m.getReg .x10) (m.getReg .x11) (m.getReg .x12) (m.getReg .x13)).zeroExtend 258
    let Y := (cat4 (m.getReg .x14) (m.getReg .x15) (m.getReg .x16) (m.getReg .x17)).zeroExtend 258
    let R := cat4 (m'.getReg .x10) (m'.getReg .x11) (m'.getReg .x12) (m'.getReg .x13)
    R < BitVec.ofNat 256 p256 ∧
      (X + Y = R.zeroExtend 258 + BitVec.ofNat 258 (0 * p256) ∨
        X + Y = R.zeroExtend 258 + BitVec.ofNat 258 (1 * p256)) := by
  intro m' X Y R
  simp only [m', X, Y, R, cat4, prog, List.foldl_cons, List.foldl_nil, execInstrBr,
    getReg_setReg_ite, getReg_x0', MachineState.getReg_setPC, signExtend12, p256] at hx hy ⊢
  bv_decide

/-- **`bignum_add_p256` on riscv-zkvm.** -/
theorem corres (base : Word) :
    Corres (KSR base prog) (KPre fun x y => x < p256 ∧ y < p256)
      (KSpec fun x y => (x + y) % p256) 83 := by
  rw [← show prog.length = 83 from rfl]
  refine kernel_corres base prog (by decide) _ _ ?_
  rintro m ⟨hx, hy⟩
  rw [regA_eq] at hx; rw [regB_eq] at hy
  have hp : (BitVec.ofNat 256 p256).toNat = p256 := by simp [p256]
  obtain ⟨hR, hsum⟩ := bv m (by rw [BitVec.lt_def, hp]; exact hx) (by rw [BitVec.lt_def, hp]; exact hy)
  generalize prog.foldl execInstrBr m = m' at hR hsum ⊢
  rw [BitVec.lt_def, hp] at hR
  rw [regA_eq, regA_eq, regB_eq]
  rcases hsum with h | h
  · exact eq_mod_of_eq_add_mul hR (sum_of_zext (by decide) h)
  · exact eq_mod_of_eq_add_mul hR (sum_of_zext (by decide) h)

end Cases.CatCrypt.AddP256
