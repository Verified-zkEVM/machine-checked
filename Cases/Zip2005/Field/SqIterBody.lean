import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Image.F_780326cc
import Cases.Zip2005.Image.Ro

/-!
# `Vec<Fp>::from_iter` of `SqrtTables::new`'s power sequence: one iteration (0x7803292c)

The loop of `(0..256).map(|_| { let r = gp; gp *= g; r }).collect()`: from the loop head with
`m` elements stored (`1 ≤ m < 256`), `gp * g` by two `mulmod` calls (the product and its
Montgomery reduction), then the old `gp` stored as element `m` at `p + 32 m`. Nothing is
claimed about the values: the tables are only ever read by `sqrt_alt`, which checks its own
result (ledger A3).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image MachineChecked.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem sq_iter_body {Gd : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (sp out g p k c o q : Word)
    (q0 q1 q2 q3 : Word) (G J : List Word) (hGl : G.length = 4) (hJl : J.length = 20)
    (hkc : (k == c) = false) (hq : p + o = q)
    (hpc : s.pc = 0x7803292c#64) (hcode : CodeAt F_780326cc.base F_780326cc.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hsp : s.getReg .x2 = sp)
    (hs0 : s.getReg .x8 = o) (hs1 : s.getReg .x9 = p)
    (hs3 : s.getReg .x19 = g) (hs4 : s.getReg .x20 = 0x224698fc094cf91b#64)
    (hs5 : s.getReg .x21 = 0x992d30ed00000001#64) (hs6 : s.getReg .x22 = 0x4000000000000000#64)
    (hs7 : s.getReg .x23 = 0x70cb2996efc89a65#64) (hs8 : s.getReg .x24 = 0x21f1c4ff1e2278d5#64)
    (hs9 : s.getReg .x25 = 257#64) (hs10 : s.getReg .x26 = k + 1#64)
    (hs11 : s.getReg .x27 = sp + 0xb8#64)
    (hH : Region (sp + 8#64) [out, 0xac9fba6a4077fc57#64, 0xcf3f8e8753a769a9#64, c, p, k] s)
    (hokF : RegionOk Ro.layout.roBase Ro.layout.textHi sp 27) (hokH : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 8#64) 6)
    (hJ : Region (sp + 0x38#64) J s) (hokJ : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x38#64) 20)
    (hG : Region g G s) (hokG : RegionOk Ro.layout.roBase Ro.layout.textHi g 4)
    (hQ : Region q [q0, q1, q2, q3] s) (hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi q 4)
    (hsplo : 0x10000 ≤ sp.toNat) (hsphi : sp.toNat + 0x140 ≤ 0x78000000)
    (hglo : sp.toNat + 0x140 ≤ g.toNat) (hghi : g.toNat + 32 ≤ 0x78000000)
    (hdQF : Disjoint q 4 sp 27) (hdQG : Disjoint q 4 g 4)
    (hk : ∀ (t : MachineState) (J' Q' : List Word), t.pc = 0x7803292c#64 → t.code = s.code →
      Unchanged [(sp, 27), (q, 4)] s t →
      t.getReg .x2 = sp → t.getReg .x8 = o + 32#64 → t.getReg .x9 = p →
      t.getReg .x19 = g → t.getReg .x20 = 0x224698fc094cf91b#64 →
      t.getReg .x21 = 0x992d30ed00000001#64 → t.getReg .x22 = 0x4000000000000000#64 →
      t.getReg .x23 = 0x70cb2996efc89a65#64 → t.getReg .x24 = 0x21f1c4ff1e2278d5#64 →
      t.getReg .x25 = 257#64 → t.getReg .x26 = k + 2#64 →
      t.getReg .x27 = sp + 0xb8#64 → t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      Region (sp + 8#64) [out, 0xac9fba6a4077fc57#64, 0xcf3f8e8753a769a9#64, c, p, k + 1#64] t →
      J'.length = 20 → Region (sp + 0x38#64) J' t → Q'.length = 4 → Region q Q' t →
      (k + 2#64 == 257#64) = false → SafeN Gd n P t)
    (hx : ∀ (t : MachineState) (J' Q' : List Word), t.pc = 0x78032a40#64 → t.code = s.code →
      Unchanged [(sp, 27), (q, 4)] s t →
      t.getReg .x2 = sp → t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      Region (sp + 8#64) [out, 0xac9fba6a4077fc57#64, 0xcf3f8e8753a769a9#64, c, p, k + 1#64] t →
      J'.length = 20 → Region (sp + 0x38#64) J' t → Q'.length = 4 → Region q Q' t →
      (k + 2#64 == 257#64) = true → SafeN Gd n P t) :
    SafeN Gd n P s := by
  have hu := Unchanged.refl [(sp, 27), (q, 4)] s
  sym_exec [uint256_mulmod_spec] stop [0x7803292c, 0x78032a40]
  · sym_close hx <;> rfl
  · sym_close hk <;> rfl

end Cases.Zip2005
