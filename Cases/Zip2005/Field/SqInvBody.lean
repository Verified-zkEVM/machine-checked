import Cases.Zip2005.Field.GetLower32
import Cases.Zip2005.Image.F_78030a94
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `SqrtTables::new`'s `inv` loop: from one store to the next (0x78031280 → 0x7803127c)

`for (j, x) in gtab[3].iter().enumerate() { let h = hash(x); assert!(inv[h] == 1); inv[h] = … }`
over the 256 elements of the last power table: after the store for element `i`, the iterator
steps to element `i + 1`, `get_lower_32` hashes it, and the `inv` entry is read (a collision
panics). Values are not tracked (ledger A3).
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

theorem remu1098_lt (x : Word) : (rv64_remu x 1098#64).toNat < 1098 := by
  unfold rv64_remu
  rw [if_neg (by decide), BitVec.toNat_umod]
  exact Nat.mod_lt _ (by decide)

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem sq_inv_step {G : MachineState → Prop} {nb : Nat} {P : Prop} {L : List (Word × Nat)} {sp0 : Word} (s : MachineState) (inv hx e f n j : Word) (x0 x1 x2 x3 : Word)
    (IV : List Word) (hIVl : IV.length = 138) (hn : (n + 18446744073709551615#64 != 0#64) = true)
    (hpc : s.pc = 0x78031280#64) (hcode : CodeAt F_78030a94.base F_78030a94.prog s)
    (hcodeL : CodeAt F_78029b64.base F_78029b64.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hsp0 : s.getReg .x2 = sp0) (hstk0 : StackOk Ro.layout 0 sp0)
    (hs0 : s.getReg .x8 = 1098#64) (hs2 : s.getReg .x18 = hx) (hs3 : s.getReg .x19 = 1#64)
    (hs4 : s.getReg .x20 = f) (hs5 : s.getReg .x21 = n) (hs7 : s.getReg .x23 = e)
    (hs8 : s.getReg .x24 = j) (hs11 : s.getReg .x27 = inv)
    (hIV : Region inv IV s) (hokIV : RegionOk Ro.layout.roBase Ro.layout.textHi inv 138)
    (hE : Region e [x0, x1, x2, x3] s) (hokE : RegionOk Ro.layout.roBase Ro.layout.textHi e 4)
    (hpp : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de20#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_de20 → SafeN G nb P u)
    (hk : ∀ (t : MachineState) (d e' : Word), t.pc = 0x7803127c#64 → t.code = s.code →
      Unchanged [] s t → t.getReg .x10 = inv + d → d.toNat < 1098 →
      t.getReg .x21 = n + 18446744073709551615#64 → t.getReg .x22 = -j → t.getReg .x23 = e' →
      e + ((if (0#64).ult (e ^^^ f) = true then 1#64 else 0#64) <<< 5) = e' →
      t.getReg .x24 = j + 1#64 →
      t.getReg .x2 = s.getReg .x2 → t.getReg .x3 = s.getReg .x3 → t.getReg .x4 = s.getReg .x4 →
      t.getReg .x8 = 1098#64 → t.getReg .x9 = s.getReg .x9 → t.getReg .x18 = hx →
      t.getReg .x19 = 1#64 → t.getReg .x20 = f → t.getReg .x25 = s.getReg .x25 →
      t.getReg .x26 = s.getReg .x26 → t.getReg .x27 = inv →
      Region inv IV t → SafeN G nb P t) :
    SafeN G nb P s := by
  have hu := Unchanged.refl [] s
  sym_exec [fp_get_lower_32_spec] stop [0x78031274, 0x780312a0]
  pick_goal 2
  · exact absurd hn hbr7
  have hb : v16.toNat < 1098 := by rw [← v16_def]; exact remu1098_lt _
  sym_reframe
  sym_exec [hpp] stop [0x7803127c]
  sym_close hk _ v16 v6

end Cases.Zip2005
