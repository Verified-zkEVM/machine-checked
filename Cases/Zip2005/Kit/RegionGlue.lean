import MachineChecked.RiscV.Sym.Frame

/-!
# Re-partitioning regions between two executor runs

A caller's frame is cut into the pieces its callees' specifications name. When two callees need
different cuts (`prf_nf`: `constants()`'s output pieces, then the sponge's input, state and matrix
regions over the same cells), the proof stops between the calls and re-derives the region facts:
`Region.sub` for a piece of one region, `Region.append'` for the join of two adjacent ones.
-/

namespace MachineChecked.RiscV.Sym

open RiscvZkvm.Rv64

/-- `Region.append` with the second base given by an equation. -/
theorem Region.append' {b b' : Word} {vs ws : List Word} {s : MachineState}
    (h₁ : Region b vs s) (h₂ : Region b' ws s) (hb : b' = b + BitVec.ofNat 64 (8 * vs.length)) :
    Region b (vs ++ ws) s :=
  Region.append h₁ (hb ▸ h₂)

end MachineChecked.RiscV.Sym
