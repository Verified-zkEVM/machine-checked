/-
  Cases.Zip2005.Run.SqContracts

  The heap contracts of the `FP_TABLES` build (`Fp::sqrt`'s tables), discharged (milestone M1):
  `SqAlloc` and `SqAllocInv` from `alloc_at`, `SqReallocG` (`from_iter`'s growth) and `SqRealloc`
  (the last table shrunk) from `heap_realloc` with `realloc_copy`.
-/

import Cases.Zip2005.Run.ReallocContracts
import Cases.Zip2005.Field.SqTablesNew
import Cases.Zip2005.Field.SqIterPro
import Cases.Zip2005.Field.SqReserve

set_option maxRecDepth 100000

namespace Cases.Zip2005.Run

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Cases.Zip2005 Cases.Zip2005.Image

/-- `__rust_alloc(0x80, 8)` at `from_iter`'s call. -/
theorem sq_alloc_ok {G : MachineState → Prop} {n : Nat} {P : Prop} : SqAlloc G n P C := by
  intro u sp' L' hpc hcode hr hsp hstk hsz hal hro hh k
  exact alloc_at 16 hpc hcode hr (by decide) hsp hstk hsz (Nat.le_refl _) (by omega) (by decide)
    (.inr hal) hro hh fun t ptr B a1 a2 a3 _ a5 a6 a7 a8 a9 a10 a11 a12 _ => k t ptr B a1 a2 a3 a5 a6 a7 a8
      a9 a10 a11 a12

/-- `__rust_alloc(1098, 1)` at `new`'s call: the `inv` table, 138 doublewords. -/
theorem sq_alloc_inv_ok {G : MachineState → Prop} {n : Nat} {P : Prop} : SqAllocInv G n P C := by
  intro u sp' L' hpc hcode hr hsp hstk hsz hal hro hh k
  exact alloc_at 138 hpc hcode hr (by decide) hsp hstk hsz (by omega) (by omega) (by decide)
    (.inl hal) hro hh fun t ptr B a1 a2 a3 _ a5 a6 a7 a8 a9 a10 a11 a12 _ => k t ptr B a1 a2 a3 a5 a6 a7 a8
      a9 a10 a11 a12

/-- `__rust_realloc(p0, 32 n, 8, 64 n)` at `finish_grow` (`from_iter`'s growth). -/
theorem sq_realloc_g_ok {G : MachineState → Prop} {nb : Nat} {P : Prop} : SqReallocG G nb P C := by
  intro u sp' p0 nn L' hn hpc hcode hx1 hsp hstk hx10 hx11 hx12 hx13 hlo hro hh k
  have hsz : (4 * nn, 8 * nn, 4 * nn) ∈ reallocSizes := by
    simp only [reallocSizes]; rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hn128 : nn ≤ 128 := by omega
  have hb := hh.bound (List.mem_cons_self ..)
  simp only [TOP] at hb
  obtain ⟨B, hB, hBl⟩ := Region.exists_junk p0 (4 * nn) u
  have hokP : RegionOk Ro.layout.textLo Ro.layout.textHi p0 (4 * nn) :=
    RegionOk.of_nat (hh.aligned (List.mem_cons_self ..)) (by simp only [SP1_MAX_MEMORY]; omega)
      (.inr (by simp only [Ro.layout_textHi]; omega))
  refine heap_realloc u _ sp' p0 8#64 (4 * nn) (8 * nn) (4 * nn) B hpc hcode hx1 (by decide) hsp hstk
    hx10 (by rw [hx11]; congr 1; omega) hx12 (by rw [hx13]; congr 1; omega) (.inr rfl) hsz hB hBl hlo
    hro hh (realloc_copy (c := u.code) hcode (.inr (.inr ⟨⟨nn, rfl⟩, by omega⟩)) hBl hokP) ?_
  intro t hpc' hcs hcode' _ hun _ hh' hres
  have hok := regionOk_live hh' (List.mem_cons_self ..) (hres.imp id fun h => h.1) (by omega)
  refine k t _ hpc' hcs hcode' hun rfl ⟨hok.aligned, by have := hok.inMem; omega,
    hok.offCode.imp (fun h => by omega) id⟩ (hres.imp id fun h => h.1) ?_ hh'
  rcases hres with h | ⟨_, h, _⟩ <;> omega

/-- `__rust_realloc(p, 0x2000, 8, 0x1020)` at `new`'s call: the last table shrunk to 516
    doublewords, the first 516 copied. -/
theorem sq_realloc_ok {G : MachineState → Prop} {nb : Nat} {P : Prop} : SqRealloc G nb P C := by
  intro u sp' p0 L' hpc hcode hx1 hsp hstk hx10 hx11 hx12 hx13 hlo hro hh k
  have hb := hh.bound (List.mem_cons_self ..)
  simp only [TOP] at hb
  obtain ⟨B, hB, hBl⟩ := Region.exists_junk p0 516 u
  have hokP : RegionOk Ro.layout.textLo Ro.layout.textHi p0 516 :=
    RegionOk.of_nat (hh.aligned (List.mem_cons_self ..)) (by simp only [SP1_MAX_MEMORY]; omega)
      (.inr (by simp only [Ro.layout_textHi]; omega))
  refine heap_realloc u _ sp' p0 8#64 1024 516 516 B hpc hcode hx1 (by decide) hsp (hstk.mono (by decide))
    hx10 (by rw [hx11]) hx12 (by rw [hx13]) (.inr rfl) (by simp [reallocSizes]) hB hBl hlo
    hro hh (realloc_copy (c := u.code) hcode (.inr (.inr ⟨⟨129, rfl⟩, by omega⟩)) hBl hokP) ?_
  intro t hpc' hcs hcode' _ hun _ hh' hres
  have hok := regionOk_live hh' (List.mem_cons_self ..) (hres.imp id fun h => h.1) (by omega)
  have hs := hstk.lo
  have hun' : Unchanged [(sp' - 0x100#64, 32), (0x78040620#64, 4162), (0x78048980#64, 14780690128)]
      u t := fun a ha => hun a fun r hr => by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · intro hin
      refine ha _ (List.mem_cons_self ..) ?_
      simp only [InRegion] at hin ⊢
      have e1 : (sp' - 0x60#64).toNat = sp'.toNat - 0x60 := by rw [BitVec.toNat_sub]; simp; omega
      have e2 : (sp' - 0x100#64).toNat = sp'.toNat - 0x100 := by rw [BitVec.toNat_sub]; simp; omega
      rw [e1] at hin; rw [e2]; omega
    · exact ha _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact ha _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine k t _ hpc' hcs hcode' hun' rfl ⟨hok.aligned, by have := hok.inMem; omega,
    hok.offCode.imp (fun h => by omega) id⟩ (hres.imp id fun h => h.1) ?_ hh'
  rcases hres with h | ⟨_, h, _⟩ <;> omega

end Cases.Zip2005.Run
