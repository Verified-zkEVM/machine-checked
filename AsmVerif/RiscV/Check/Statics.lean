/-
  AsmVerif.RiscV.Check.Statics

  Read-only data and protected statics stay put (phase C3).

  The `Env`'s protected regions are where a program's constants live: `.rodata`, and the
  statics no function writes (a hook that is never set). The precondition of every
  interface says the protected keys hold their load values and that nothing the function may
  write (its window, its footprint) reaches them. So a verified call returns with them
  unchanged, and a region that the `Env` protects holds its load values at every call
  boundary: the protected part of `StaticsOk` is preserved by every specification in the
  table, with no per-function work.

  At load, memory *is* the image's (`Image.state`), so a region holds its load values there
  by definition. What remains for an image is the choice of what to protect: a static is
  protected only if no specification's footprint writes it (`Infer` refuses a footprint
  that would, since such a precondition would be unsatisfiable).
-/

import AsmVerif.RiscV.Check.Arith
import AsmVerif.RiscV.Check.Region
import AsmVerif.RiscV.Load

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Frame

variable {env : Env} {C : Word → Option Instr} {σ : Iface} {s t : MachineState}

/-- The precondition puts every protected key outside what the function may write. -/
theorem Pre.not_written_prot (hwf : env.wf = true) (h : Pre env C σ s) {a : Word}
    (ha : Aligned a) (hp : env.InProt a) : ¬ Written σ (regsOf s) a := by
  rintro (hw | ⟨it, hit, hh⟩)
  · exact not_prot_of_inWin hwf h.2.2.1 h.2.1 hw hp
  · exact (h.2.2.2.2.2.1 it hit a ha hh).2 hp

/-- **A verified call leaves protected memory as it found it.** -/
theorem Post.keeps_prot (hwf : env.wf = true) (hpre : Pre env C σ s) (hpost : Post σ s t)
    {a : Word} (ha : Aligned a) (hp : env.InProt a) : t.getMem a = s.getMem a :=
  hpost.2.2.2.1 a ha (Pre.not_written_prot hwf hpre ha hp)

/-- Protected memory holds its load values at a verified call's return. -/
theorem Post.prot_init (hwf : env.wf = true) (hpre : Pre env C σ s) (hpost : Post σ s t)
    {a : Word} (ha : Aligned a) (hp : env.InProt a) : t.getMem a = env.init a := by
  rw [Post.keeps_prot hwf hpre hpost ha hp]
  exact hpre.2.2.2.2.1 a ha hp

/-- The aligned keys of a region hold the values `M` gives them. -/
def RegionOk (R : Region) (M : Word → Word) (s : MachineState) : Prop :=
  ∀ a, Aligned a → R.Mem a → s.getMem a = M a

/-- A key of a region the `Env` protects is a protected key. -/
theorem Env.inProt_of_mem {R : Region} (hR : (R.base, R.len) ∈ env.prot) {a : Word}
    (h : R.Mem a) : env.InProt a :=
  ⟨(R.base, R.len), hR, Region.mem_hits h⟩

/-- At load, every region holds the image's values. -/
theorem Image.state_regionOk (img : Image) (input : List (BitVec 8)) (R : Region) :
    RegionOk R img.memAt (img.state input) :=
  fun _ _ _ => rfl

/-- **C3, preserved:** a region the `Env` protects holds its load values at the return of
    every verified call, whatever the function. -/
theorem Post.regionOk (hwf : env.wf = true) {R : Region} (hR : (R.base, R.len) ∈ env.prot)
    (hpre : Pre env C σ s) (hpost : Post σ s t) : RegionOk R env.init t :=
  fun _ ha hm => Post.prot_init hwf hpre hpost ha (Env.inProt_of_mem hR hm)

/-- And at the entry of every verified call: the precondition says so. -/
theorem Pre.regionOk {R : Region} (hR : (R.base, R.len) ∈ env.prot) (hpre : Pre env C σ s) :
    RegionOk R env.init s :=
  fun a ha hm => hpre.2.2.2.2.1 a ha (Env.inProt_of_mem hR hm)

end AsmVerif.RiscV.Check
