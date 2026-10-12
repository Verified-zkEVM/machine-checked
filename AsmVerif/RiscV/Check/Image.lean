/-
  AsmVerif.RiscV.Check.Image

  The checker's code premise (`CodeAt`), discharged from a loaded image: every word of the
  function, decodable or not, is what the image's code map holds.
-/

import AsmVerif.RiscV.Load
import AsmVerif.RiscV.Check.Sound

namespace AsmVerif.RiscV.Check

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Frame

theorem codeAt_of_image {img : Image} {f : Fn} (hwf : img.codeWF = true) {k : Nat}
    {ws : List (BitVec 32)} (hk : img.code[k]? = some (CodeChunk.mk f.base ws))
    (hdec : decodeWords ws = f.prog)
    (hfr : ∀ fb fp, f.frags.lookup fb = some fp →
      ∃ (k' : Nat) (ws' : List (BitVec 32)), img.code[k']? = some (CodeChunk.mk fb ws') ∧
        decodeWords ws' = fp) :
    CodeAt f img.codeAt := by
  refine ⟨fun j oi hj => ?_, fun fb fp hfp m ins hm => ?_⟩
  · rw [← hdec] at hj
    simp only [decodeWords, List.getElem?_map, Option.map_eq_some_iff] at hj
    obtain ⟨w, hw, rfl⟩ := hj
    have hlt : j < ws.length := (List.getElem?_eq_some_iff.mp hw).1
    unfold Fn.pcOf
    rw [Image.codeAt_chunk (c := ⟨f.base, ws⟩) hwf hk hlt]
    rw [List.getElem?_eq_some_iff] at hw
    obtain ⟨_, rfl⟩ := hw
    rfl
  · obtain ⟨k', ws', hk', hdec'⟩ := hfr fb fp hfp
    exact Image.codeAt_prog hwf hk' hdec' hm

/-- The fragment premise of `codeAt_of_image`, from one fact per fragment. -/
theorem frags_of_image {img : Image} {l : List (Word × List (Option Instr))}
    (h : ∀ p ∈ l, ∃ (k : Nat) (ws : List (BitVec 32)), img.code[k]? = some (CodeChunk.mk p.1 ws) ∧
      decodeWords ws = p.2) :
    ∀ fb fp, l.lookup fb = some fp →
      ∃ (k' : Nat) (ws' : List (BitVec 32)), img.code[k']? = some (CodeChunk.mk fb ws') ∧
        decodeWords ws' = fp :=
  fun fb fp hl => h (fb, fp) (lookup_mem hl)

end AsmVerif.RiscV.Check
