import MachineChecked.RiscV.Sym
import Cases.Zip2005.Image.Ro

/-!
# A byte store at a computed offset

The executor stores only into a cell it can name. `safe_sb_region` steps one `sb` whose address
is `base + (8 i + k)` inside a region held as a list: afterwards the region holds *some* list of
the same length, every register and every other cell as before. For tables whose contents the
proof does not track (`SqrtTables::new`'s `inv`, ledger A3).
-/

namespace Cases.Zip2005

open Cases.Zip2005.Image

open RiscvZkvm.Rv64 MachineChecked.RiscV.Sym

set_option autoImplicit false

theorem safe_sb_region {G : MachineState → Prop} {nb : Nat} {P : Prop} {u : MachineState} {rs1 rs2 : Reg} {off : BitVec 12}
    {base : Word} {L : List Word} {n i k : Nat}
    (hfetch : u.code u.pc = some (.SB rs1 rs2 off))
    (haddr : u.getReg rs1 + signExtend12 off = base + BitVec.ofNat 64 (8 * i + k))
    (hi : i < n) (hk : k < 8) (hL : L.length = n) (hR : Region base L u)
    (hok : RegionOk Ro.layout.textLo Ro.layout.textHi base n) (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi u)
    (hnext : ∀ t : MachineState, t.pc = u.pc + 4#64 → (∀ r, t.getReg r = u.getReg r) →
      t.code = u.code → Unchanged [(base, n)] u t → ∀ L' : List Word, L'.length = n →
      Region base L' t → SafeN G nb P t) :
    SafeN G nb P u := by
  have hmem : memOkSp1 u (.SB rs1 rs2 off) = true :=
    memOk_SB (by rw [haddr]; exact addrOk hok hi hk)
      (by rw [haddr]; exact noCodeOk hok hcw hi hk (by decide) (by omega))
  refine MachineChecked.RiscV.SafeN.step_of (stepSp1_mem hfetch rfl rfl hmem) ?_
  rw [exec_SB, haddr, setByte_cell hok hi hk u _ rfl]
  have hnw : base.toNat + 8 * L.length ≤ 2 ^ 64 := by rw [hL]; exact hok.nowrap
  refine hnext _ memShape_pc (fun r => memShape_getReg) memShape_code ?_ _ (by simp [hL])
    (Region.set hR (by omega) hnw _ rfl)
  intro a ha
  have hne : a ≠ base + BitVec.ofNat 64 (8 * i) := by
    intro heq
    apply ha (base, n) (by simp)
    unfold InRegion
    dsimp only
    rw [heq, toNat_addr hi (by rw [← hL]; exact hnw)]
    omega
  exact memShape_getMem_ne hne

end Cases.Zip2005
