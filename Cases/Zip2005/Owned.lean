/-
  Cases.Zip2005.Owned

  zip-2005's owned statics: the public-values hasher's state that only `syscall_write` and
  `syscall_halt` touch.

  `PUBLIC_VALUES_HASHER` (`0x78048830`, `0x78` bytes) is an `Option<Sha256>`: a tag word
  (`1` once `__start` sets it up, `0` after `syscall_halt` takes it), the SHA-256 state, a
  block counter, a 64-byte buffer and the buffer position, one byte at `0x780488a0`.
  `syscall_write` on the public-values descriptor reads the tag (panicking on `None`) and
  appends to the buffer at the position; it must be below 64 or the append leaves the hasher.
  So the invariant: the tag is `Some`, the position is below 64. The tag's and the
  position's doublewords are owned: no footprint names them. The state, counter and buffer
  stay ordinary memory, in `syscall_write`'s footprint, so `memcpy` and `compress256` can be
  called on them with their plain interfaces.

  Every interface of the checked table is lifted to this `Env` (`tbl_holds`): none of them
  reaches the owned doublewords.
-/

import Cases.Zip2005.Contract.All
import AsmVerif.RiscV.Check.Statics
import Cases.Zip2005.Runtime.Entry

namespace Cases.Zip2005.Owned

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Frame AsmVerif.RiscV.Check

/-- The hasher's tag, and the doubleword holding its buffer position (the low byte). -/
def tagKey : Word := 0x78048830#64
def posKey : Word := 0x780488a0#64

/-- The hasher is `Some` and its buffer position is below 64. -/
def HasherOk (m : Word → Word) : Prop := m tagKey = 1#64 ∧ (m posKey &&& 0xff#64).toNat < 64

noncomputable def env : Env :=
  { Contract.env with own := [(tagKey, 8), (posKey, 8)], inv := HasherOk }

theorem env_wf : env.wf = true := by decide +kernel

theorem env_plain : env.plain = Contract.env := rfl

theorem tag_own : env.InOwn tagKey := ⟨(tagKey, 8), by simp [env], Or.inl (by decide)⟩
theorem pos_own : env.InOwn posKey := ⟨(posKey, 8), by simp [env], Or.inl (by decide)⟩

/-- The invariant of a memory, through the owned keys. -/
theorem inv_iff {m : Word → Word} : env.Inv m ↔ HasherOk m := by
  have ht : env.ownPart m tagKey = m tagKey := by
    simp only [Env.ownPart]; rw [if_pos ⟨by unfold Aligned; decide, tag_own⟩]
  have hp : env.ownPart m posKey = m posKey := by
    simp only [Env.ownPart]; rw [if_pos ⟨by unfold Aligned; decide, pos_own⟩]
  show HasherOk (env.ownPart m) ↔ HasherOk m
  simp only [HasherOk, ht, hp]

/-- **The checked table, with the hasher owned.** -/
theorem tbl_holds : ∀ g ∈ Contract.tbl, g.Holds env Image.Layout.image.codeAt :=
  fun g hg n => Iface.HoldsN.lift env_wf (by rw [env_plain]; exact Contract.all g hg n)

/-- At `main`'s entry the hasher is set up: the invariant holds. -/
theorem mainEntry_inv {input : List (BitVec 8)} {t : MachineState}
    (h : Runtime.Entry.MainEntry input t) : env.Inv t.getMem := by
  rw [inv_iff]
  have hm := h.2.2.2.2.2.1
  refine ⟨?_, ?_⟩
  · rw [tagKey, hm]; rfl
  · rw [posKey, hm]; decide

end Cases.Zip2005.Owned
