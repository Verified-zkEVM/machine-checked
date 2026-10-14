import Cases.Zip2005.Runtime.Stubs
import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Image.F_780326cc
import Cases.Zip2005.Image.Ro

/-!
# `Vec<Fp>::from_iter` of `SqrtTables::new`: the growing iteration (0x7803292c, `len = cap`)

As `sq_iter_body`, but the vector is full (`len = cap = C`, `C ∈ {4, …, 128}`): the element is
stored after `RawVec::reserve` (`do_reserve_and_handle`, `0x78032560`) has moved the buffer to a
block of `2C` elements, the contract `hres` (ledger A5).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- `do_reserve_and_handle` at `from_iter`'s call (`0x78032a24`): the full buffer of `n` elements
moves to a block of `2 n` in the heap. -/
def SqReserve (G : MachineState → Prop) (nb : Nat) (P : Prop) (code : Word → Option Instr) : Prop :=
  ∀ (u : MachineState) (sp' p0 n : Word), u.pc = 0x78032560#64 → u.code = code →
    u.getReg .x1 = 0x78032a24#64 → u.getReg .x2 = sp' → StackOk Ro.layout 0x100 sp' →
    u.getReg .x10 = sp' + 0x20#64 → u.getReg .x11 = n → u.getReg .x12 = 1#64 →
    Region (sp' + 0x20#64) [n, p0, n] u → RegionOk Ro.layout.roBase Ro.layout.textHi (sp' + 0x20#64) 3 →
    (n.toNat = 4 ∨ n.toNat = 8 ∨ n.toNat = 16 ∨ n.toNat = 32 ∨ n.toNat = 64 ∨ n.toNat = 128) →
    0x78048980 ≤ p0.toNat → p0.toNat + 32 * n.toNat ≤ 0x1c00000000 →
    (∀ (t : MachineState) (p' : Word), t.pc = 0x78032a24#64 → CalleeSaved u t → t.code = u.code →
      Unchanged [(sp' - 0x100#64, 32), (sp' + 0x20#64, 2), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
      Region (sp' + 0x20#64) [n + n, p'] t → RegionOk Ro.layout.roBase Ro.layout.textHi p' (8 * n.toNat) →
      0x78048980 ≤ p'.toNat → p'.toNat + 64 * n.toNat ≤ 0x1c00000000 → SafeN G nb P t) →
    SafeN G nb P u

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem sq_iter_grow {Gd : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (sp out g p k o : Word)
    (G J : List Word) (hGl : G.length = 4) (hJl : J.length = 20)
    (hkC : k.toNat = 4 ∨ k.toNat = 8 ∨ k.toNat = 16 ∨ k.toNat = 32 ∨ k.toNat = 64 ∨ k.toNat = 128)
    (ho : o.toNat = 32 * k.toNat)
    (hpc : s.pc = 0x7803292c#64) (hcode : CodeAt F_780326cc.base F_780326cc.prog s)
    (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x100 sp)
    (hs0 : s.getReg .x8 = o) (hs1 : s.getReg .x9 = p)
    (hs3 : s.getReg .x19 = g) (hs4 : s.getReg .x20 = 0x224698fc094cf91b#64)
    (hs5 : s.getReg .x21 = 0x992d30ed00000001#64) (hs6 : s.getReg .x22 = 0x4000000000000000#64)
    (hs7 : s.getReg .x23 = 0x70cb2996efc89a65#64) (hs8 : s.getReg .x24 = 0x21f1c4ff1e2278d5#64)
    (hs9 : s.getReg .x25 = 257#64) (hs10 : s.getReg .x26 = k + 1#64)
    (hs11 : s.getReg .x27 = sp + 0xb8#64)
    (hH : Region (sp + 8#64) [out, 0xac9fba6a4077fc57#64, 0xcf3f8e8753a769a9#64, k, p, k] s)
    (hokF : RegionOk Ro.layout.roBase Ro.layout.textHi sp 27) (hokH : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 8#64) 6)
    (hJ : Region (sp + 0x38#64) J s) (hokJ : RegionOk Ro.layout.roBase Ro.layout.textHi (sp + 0x38#64) 20)
    (hG : Region g G s) (hokG : RegionOk Ro.layout.roBase Ro.layout.textHi g 4)
    (hsphi : sp.toNat + 0x140 ≤ 0x78000000)
    (hglo : sp.toNat + 0x140 ≤ g.toNat) (hghi : g.toNat + 32 ≤ 0x78000000)
    (hplo : 0x78048980 ≤ p.toNat) (hphi : p.toNat + 32 * k.toNat ≤ 0x1c00000000)
    (hres : SqReserve Gd n P s.code)
    (hk : ∀ (t : MachineState) (p' : Word) (J' : List Word), t.pc = 0x7803292c#64 → t.code = s.code →
      Unchanged [(sp - 0x100#64, 32), (sp, 27), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      t.getReg .x2 = sp → t.getReg .x8 = o + 32#64 → t.getReg .x9 = p' →
      t.getReg .x19 = g → t.getReg .x20 = 0x224698fc094cf91b#64 →
      t.getReg .x21 = 0x992d30ed00000001#64 → t.getReg .x22 = 0x4000000000000000#64 →
      t.getReg .x23 = 0x70cb2996efc89a65#64 → t.getReg .x24 = 0x21f1c4ff1e2278d5#64 →
      t.getReg .x25 = 257#64 → t.getReg .x26 = k + 2#64 →
      t.getReg .x27 = sp + 0xb8#64 → t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      Region (sp + 8#64) [out, 0xac9fba6a4077fc57#64, 0xcf3f8e8753a769a9#64, k + k, p', k + 1#64] t →
      J'.length = 20 → Region (sp + 0x38#64) J' t →
      RegionOk Ro.layout.roBase Ro.layout.textHi p' (8 * k.toNat) → 0x78048980 ≤ p'.toNat →
      p'.toNat + 64 * k.toNat ≤ 0x1c00000000 → SafeN Gd n P t) :
    SafeN Gd n P s := by
  have hu := Unchanged.refl [(sp - 0x100#64, 32), (sp, 27), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x100#64) 32 := hstk.frame 32 (by decide)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  unfold SqReserve at hres
  have hkk : (k == k) = true := beq_self_eq_true k
  sym_exec [uint256_mulmod_spec, hres] stop [0x78032a24]
  -- the new buffer's slot `k`, a block of its own
  have hoe : o = BitVec.ofNat 64 (8 * (4 * k.toNat)) := by
    apply BitVec.eq_of_toNat_eq; rw [ho, BitVec.toNat_ofNat]; omega
  have hqn : (post64_0 + o).toNat = post64_0.toNat + 32 * k.toNat := by
    rw [BitVec.toNat_add, ho]; omega
  obtain ⟨q, hq⟩ : ∃ q, post64_0 + o = q := ⟨_, rfl⟩
  rw [hq] at hqn
  have hokQ : RegionOk Ro.layout.roBase Ro.layout.textHi q 4 :=
    post64_6.sub' (4 * k.toNat) 4 (by omega) (by rw [← hq, hoe])
  obtain ⟨Q, hQ, hQl⟩ := Region.exists_junk q 4 t
  have hdQF : AsmVerif.RiscV.Sym.Disjoint q 4 sp 27 := by unfold AsmVerif.RiscV.Sym.Disjoint; omega
  have hdQS : AsmVerif.RiscV.Sym.Disjoint q 4 (sp - 0x100#64) 32 := by
    have := hstk.lo
    unfold AsmVerif.RiscV.Sym.Disjoint; rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hdQG : AsmVerif.RiscV.Sym.Disjoint q 4 g 4 := by unfold AsmVerif.RiscV.Sym.Disjoint; omega
  have hqlo : 0x78040620 ≤ q.toNat := by omega
  have hqhi : q.toNat + 32 ≤ 0x1c00000000 := by omega
  have hne : (k + 2#64 == 257#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_add] at this; simp only [BitVec.toNat_ofNat] at this; omega
  clear hoe
  sym_reframe
  sym_exec stop [0x7803292c, 0x78032a40]
  sym_close hk
  rfl

end Cases.Zip2005
