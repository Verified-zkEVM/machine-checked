import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Image.F_780326cc
import Cases.Zip2005.Image.Ro

/-!
# `Vec<Fp>::from_iter` of `SqrtTables::new`: the exit (0x78032a40)

The `Vec` header `(cap, ptr, len)` copied to the output, the callee-saved registers restored
from the frame, and the return.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem sq_iter_tail {P : Prop} (s : MachineState) (sp out c p l : Word) (O : List Word)
    (hOl : O.length = 3)
    (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v rav : Word) (hra1 : rav &&& ~~~1#64 = rav)
    (hpc : s.pc = 0x78032a40#64) (hcode : CodeAt F_780326cc.base F_780326cc.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hsp : s.getReg .x2 = sp)
    (hH : Region (sp + 8#64) [out, 0xac9fba6a4077fc57#64, 0xcf3f8e8753a769a9#64, c, p, l] s)
    (hokH : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 8#64) 6)
    (hS : Region (sp + 0xd8#64) [s11v, s10v, s9v, s8v, s7v, s6v, s5v, s4v, s3v, s2v, s1v, s0v, rav] s)
    (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0xd8#64) 13)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 3)
    (hdOH : Disjoint out 3 (sp + 8#64) 6) (hdOS : Disjoint out 3 (sp + 0xd8#64) 13)
    (hk : ∀ t : MachineState, t.pc = rav → t.code = s.code → Unchanged [(out, 3)] s t →
      t.getReg .x2 = sp + 0x140#64 → t.getReg .x8 = s0v → t.getReg .x9 = s1v →
      t.getReg .x18 = s2v → t.getReg .x19 = s3v → t.getReg .x20 = s4v → t.getReg .x21 = s5v →
      t.getReg .x22 = s6v → t.getReg .x23 = s7v → t.getReg .x24 = s8v → t.getReg .x25 = s9v →
      t.getReg .x26 = s10v → t.getReg .x27 = s11v →
      t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      Region out [c, p, l] t → Safe P t) :
    Safe P s := by
  have hu := Unchanged.refl [(out, 3)] s
  sym_exec
  sym_close hk

end Cases.Zip2005
