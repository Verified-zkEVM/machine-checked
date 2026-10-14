import AsmVerif.RiscV.Sym
import Cases.Zip2005.Image.F_7801bf5c
import Cases.Zip2005.Image.F_7801bf3c
import Cases.Zip2005.Image.F_7801bf4c
import Cases.Zip2005.Image.Ro

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- `syscall_uint256_mulmod(x, y‖m)`: `x := x * y mod m`. -/
theorem uint256_mulmod_spec {P : Prop} (s : MachineState) (ra a0 a1 : Word)
    (x0 x1 x2 x3 y0 y1 y2 y3 m0 m1 m2 m3 : Word)
    (hpc : s.pc = 0x7801bf5c#64) (hcode : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hx : Region a0 [x0, x1, x2, x3] s) (hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi a0 4)
    (hy : Region a1 [y0, y1, y2, y3, m0, m1, m2, m3] s)
    (hd : Disjoint a0 4 a1 8)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(a0, 4)] s t →
      Region a0 (Accel.natToLeLimbs 4 (Accel.leLimbsToNat [x0, x1, x2, x3] *
        Accel.leLimbsToNat [y0, y1, y2, y3] % Accel.leLimbsToNat [m0, m1, m2, m3])) t → Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl [(a0, 4)] s
  sym_exec
  sym_close hk

end Cases.Zip2005

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- `syscall_pallas_add(p, q)`: `p := p + q` (the precompile's chord formula). -/
theorem pallas_add_spec {P : Prop} (s : MachineState) (ra a0 a1 : Word) (p q : List Word)
    (hpl : p.length = 8) (hql : q.length = 8)
    (hpc : s.pc = 0x7801bf3c#64) (hcode : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1)
    (hp : Region a0 p s) (hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi a0 8)
    (hq : Region a1 q s) (hd : Disjoint a0 8 a1 8)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(a0, 8)] s t →
      Region a0 (Accel.curveAddL Sp1.pallasP 4 p q) t → Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl [(a0, 8)] s
  sym_exec
  sym_close hk

/-- `syscall_pallas_double(p)`: `p := 2p`. -/
theorem pallas_double_spec {P : Prop} (s : MachineState) (ra a0 : Word) (p : List Word)
    (hpl : p.length = 8)
    (hpc : s.pc = 0x7801bf4c#64) (hcode : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (ha0 : s.getReg .x10 = a0)
    (hp : Region a0 p s) (hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi a0 8)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code → Unchanged [(a0, 8)] s t →
      Region a0 (Accel.curveDblL Sp1.pallasP 4 p) t → Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl [(a0, 8)] s
  sym_exec
  sym_close hk

end Cases.Zip2005
