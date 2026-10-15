/-
  Cases.Zip2005.Run.ReallocContracts

  `__rust_realloc`'s contract at `MerklePath` parsing (`ReallocMp`, its `Vec<Fp>`), discharged
  (milestone M1) from `heap_realloc` with `realloc_copy`; `from_iter`'s (`ReallocOrFi`,
  `ReallocOrNc`) are in `Run/ReallocOr`.
-/

import Cases.Zip2005.Run.Realloc
import Cases.Zip2005.Runtime.ReserveMp

set_option maxRecDepth 100000

namespace Cases.Zip2005.Run

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Sym Cases.Zip2005 Cases.Zip2005.Image
  Cases.Zip2005.Runtime

/-- A live buffer's pointer, null or not, is a readable and writable block of `k` doublewords,
    and of `k + 1`. -/
theorem regionOk_live {L : List (Word × Nat)} {s : MachineState} (h : HeapAt L s)
    {p : Word} {k : Nat} (hm : (p, k) ∈ L) (hp : p.toNat = 0 ∨ 0x78048980 ≤ p.toNat)
    (hk : 8 * k + 8 ≤ 0x78000000) :
    RegionOk Ro.layout.roBase Ro.layout.textHi p (k + 1) := by
  have ha := h.aligned hm
  rcases hp with hp | hp
  · refine RegionOk.of_nat ha ?_ (.inl ?_) <;> simp only [SP1_MAX_MEMORY, Ro.layout_roBase] <;> omega
  · have hb := h.bound_ne hm (fun e => by dsimp only at e; rw [e] at hp; simp at hp)
    simp only [TOP] at hb
    refine RegionOk.of_nat ha ?_ (.inr ?_) <;> simp only [SP1_MAX_MEMORY, Ro.layout_textHi] <;> omega

/-- `__rust_realloc(p0, 32 n, 8, 64 n)` at `reserve`'s `finish_grow` (`MerklePath` parsing). -/
theorem realloc_mp_ok {G : MachineState → Prop} {n : Nat} {P : Prop} : ReallocMp G n P C := by
  intro u sp' p0 nn B L' h4 h16 hpc hcode hx1 hsp hstk hx10 hx11 hx12 hx13 hBl hB hlo _ hro hh k
  have hsz : (4 * nn, 8 * nn, 4 * nn) ∈ reallocSizes := by
    simp only [reallocSizes]; interval_cases nn <;> decide
  have hb := hh.bound (List.mem_cons_self ..)
  simp only [TOP] at hb
  have hokP : RegionOk Ro.layout.textLo Ro.layout.textHi p0 (4 * nn) :=
    RegionOk.of_nat (hh.aligned (List.mem_cons_self ..)) (by simp only [SP1_MAX_MEMORY]; omega)
      (.inr (by simp only [Ro.layout_textHi]; omega))
  refine heap_realloc u _ sp' p0 8#64 (4 * nn) (8 * nn) (4 * nn) B hpc hcode hx1 (by decide) hsp hstk hx10
    (by rw [hx11]; congr 1; omega) hx12 (by rw [hx13]; congr 1; omega) (.inr rfl) hsz hB hBl hlo hro
    hh (realloc_copy (c := u.code) hcode (.inr (.inr ⟨⟨nn, rfl⟩, by omega⟩)) hBl hokP) ?_
  intro t hpc' hcs hcode' _ hun hro' hh' hres
  obtain ⟨B', hB', hB'l⟩ := Region.exists_junk (t.getReg .x10 + BitVec.ofNat 64 (8 * B.length)) (4 * nn) t
  have hok := regionOk_live hh' (List.mem_cons_self ..) (hres.imp id fun h => h.1) (by omega)
  refine k t _ B' hpc' hcs hcode' hun rfl hB'l
    ⟨hok.aligned, by have := hok.inMem; omega, hok.offCode.imp (fun h => by omega) id⟩ ?_ ?_ hh'
  · rcases hres with h | ⟨_, h, _⟩ <;> omega
  · rcases hres with h | ⟨h1, _, _, hR⟩
    · exact .inl h
    · exact .inr ⟨h1, Region.append hR hB'⟩

end Cases.Zip2005.Run
