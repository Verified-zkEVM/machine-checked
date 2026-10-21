import MachineChecked.RiscV.Lprog.Block
import Cases.CatCrypt.Image.Cswap

/-!
# CatCrypt's RV64 `cswap`, on riscv-zkvm

Ported from catcrypt-compiler's `cswapBytes_correct` (`RiscvBytesProof`, rv64 stack), which
states the kernel over catcrypt-compiler's own RV64 model. Here the same bytes, decoded by
riscv-zkvm's `decode`, run under `stepSp1`, through the lift (`corres_block`): from a state holding two field elements in
`a0..a3` and `a4..a7` and a swap word `t0 ∈ {0, 1}`, the 52 instructions swap the two
elements exactly when `t0 = 1`, and leave `t0` and the code alone.
-/

namespace Cases.CatCrypt

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.RiscV.Lprog
open MachineChecked.Ascent (Corres)

/-- The abstract state of `cswap`: the pc, two four-limb values and the swap word. -/
structure SwapState where
  pc : Word
  a0 : Word
  a1 : Word
  a2 : Word
  a3 : Word
  b0 : Word
  b1 : Word
  b2 : Word
  b3 : Word
  sw : Word

namespace Cswap

open Cases.CatCrypt.Image.Cswap

/-- The machine holds the kernel at `base`, and `x` in its pc, `a0..a7` and `t0`. -/
def SR (base : Word) (m : MachineState) (x : SwapState) : Prop :=
  CodeAt base (prog.map some) m ∧ m.pc = x.pc ∧
  m.getReg .x10 = x.a0 ∧ m.getReg .x11 = x.a1 ∧ m.getReg .x12 = x.a2 ∧ m.getReg .x13 = x.a3 ∧
  m.getReg .x14 = x.b0 ∧ m.getReg .x15 = x.b1 ∧ m.getReg .x16 = x.b2 ∧ m.getReg .x17 = x.b3 ∧
  m.getReg .x5 = x.sw

/-- At the entry, with a swap word of `0` or `1`. -/
def Pre (base : Word) (x : SwapState) : Prop := x.pc = base ∧ x.sw.toNat ≤ 1

/-- The specification: past the block, the two values swapped exactly when `sw = 1`. -/
def spec (x : SwapState) : SwapState :=
  if x.sw = 1 then
    { x with pc := x.pc + 208, a0 := x.b0, a1 := x.b1, a2 := x.b2, a3 := x.b3,
             b0 := x.a0, b1 := x.a1, b2 := x.a2, b3 := x.a3 }
  else { x with pc := x.pc + 208 }

/-- A select by a 0/1 word, as the kernel computes it. -/
theorem sel (sw a b : Word) (h : sw.toNat ≤ 1) :
    (b &&& (0 - sw) ||| (a ^^^ (a &&& (0 - sw)))) = if sw = 1 then b else a := by
  have : sw = 0 ∨ sw = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h
    · exact Or.inl (BitVec.eq_of_toNat_eq (by simpa using h))
    · exact Or.inr (BitVec.eq_of_toNat_eq (by simpa using h))
  rcases this with rfl | rfl <;> simp <;> bv_decide (config := { enums := false })

/-- **`cswap` on riscv-zkvm.** -/
theorem corres (base : Word) : Corres stepSp1 (SR base) (Pre base) spec := by
  apply corres_block base prog (by decide)
  · rintro m x ⟨hc, hpc, -⟩ ⟨hb, -⟩
    exact ⟨hc, hpc.trans hb⟩
  · rintro m x t ⟨-, hpc, h0, h1, h2, h3, h4, h5, h6, h7, hsw⟩ ⟨hb, hle⟩ hag htpc htc
    have key := sel x.sw
    simp only [SR, hag.regs, htc, htpc, true_and]
    simp only [prog, List.foldl_cons, List.foldl_nil, execInstrBr, List.length_cons,
      List.length_nil]
    unfold spec
    split <;>
      simp_all [getReg_setReg, getReg_x0, signExtend12] <;>
      bv_decide (config := { enums := false })
end Cswap

end Cases.CatCrypt
