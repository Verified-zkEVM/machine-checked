import Cases.Hardening.Gen.Mem
import LprogRiscV.Lsym

/-!
  # Loads and stores of every width

  A signed load sign-extends, an unsigned one zero-extends, and a store then a load of another
  cell reads the old value: each against what C says, through `lsym`. Nothing is assumed of the
  addresses: a load whose address is not valid traps, and a trap is safe (`SafeN.fault`), so its
  check is a hypothesis (`hm`) and not a goal.
-/

namespace Cases.Hardening.Mem

open RiscvZkvm.Rv64 Lprog Lprog.RiscV Lprog.RiscV.Machine MachineChecked.RiscV.Lift
open Cases.Hardening.Gen.Mem

/-- A function at index `i` returns `f m a0` in `a0`, the memory unchanged. -/
def Loads (i : Nat) (f : MachineState → Word → Word) : Prop :=
  ∀ {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word} {rest : List Frame}
    (regs : Reg → BitVec 64) (m : MachineState), regs .x1 = ret → regs .x2 = top →
    (∀ r' m', r' .x10 = f m (regs .x10) → m' = m → LSafeN fns G N Q ⟨rest, r', m'⟩) →
    LSafeN fns G N Q ⟨⟨i, 0, ret, top⟩ :: rest, regs, m⟩

theorem load_s8_spec : Loads 3 fun m a => (m.getByte a).signExtend 64 := by
  intro G N Q ret top rest regs m hra hsp hpost
  lsym f3_eq with [hra, hsp]
  exact hpost _ _ (by simp [lsym_simp]) rfl

theorem load_u8_spec : Loads 4 fun m a => (m.getByte a).zeroExtend 64 := by
  intro G N Q ret top rest regs m hra hsp hpost
  lsym f4_eq with [hra, hsp]
  exact hpost _ _ (by simp [lsym_simp]) rfl

theorem load_s16_spec : Loads 5 fun m a => (m.getHalfword a).signExtend 64 := by
  intro G N Q ret top rest regs m hra hsp hpost
  lsym f5_eq with [hra, hsp]
  exact hpost _ _ (by simp [lsym_simp]) rfl

theorem load_u16_spec : Loads 6 fun m a => (m.getHalfword a).zeroExtend 64 := by
  intro G N Q ret top rest regs m hra hsp hpost
  lsym f6_eq with [hra, hsp]
  exact hpost _ _ (by simp [lsym_simp]) rfl

theorem load_s32_spec : Loads 7 fun m a => (m.getWord32 a).signExtend 64 := by
  intro G N Q ret top rest regs m hra hsp hpost
  lsym f7_eq with [hra, hsp]
  exact hpost _ _ (by simp [lsym_simp]) rfl

theorem load_u32_spec : Loads 8 fun m a => (m.getWord32 a).zeroExtend 64 := by
  intro G N Q ret top rest regs m hra hsp hpost
  lsym f8_eq with [hra, hsp]
  exact hpost _ _ (by simp [lsym_simp]) rfl

end Cases.Hardening.Mem
