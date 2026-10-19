import Cases.Zip2005.Sinsemilla.CachedCommitDomain
import Cases.Zip2005.Field.ToLeBits
import Cases.Zip2005.Image.F_7801fbcc
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `orchard::note::commitment::NoteCommitment::derive` (`0x7801fbcc`)

`derive(out, g_d, pk_d, v, rho, psi, rcm)`: the two generators by `cached_commit_domain`
(their raw coordinates in the read-only segment), the message words — `g★_d` and `pk★_d`
reassembled from their 32 bytes, `v`, `ρ` and `ψ` as `to_le_bits` lays them out
(`to_repr`) — then the `Chain`/`Take` iterator over them (its 120 bytes built in the frame),
`CommitDomain::commit`, and `conditional_select` against the identity on the `is_some` flag,
stored as the result's last byte.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image MachineChecked.RiscV.Sym

/-! ## The model -/

/-- `Q^Orchard-NoteCommit`'s raw `x`, the read-only words at `0x78001828`. -/
def qNoteX : List Word :=
  [0x320eba0940a8745d#64, 0xc5960f5afd46dd2a#64, 0xf79ff2b479b0ed5d#64, 0x178007a056fbcd0d#64]

/-- … its raw `y`, at `0x78001848`. -/
def qNoteY : List Word :=
  [0x87270a5a7349ac63#64, 0x8822128881db5e9e#64, 0x4ebec2d96ef4c92c#64, 0x32a058938ac67083#64]

/-- `R^Orchard-NoteCommit`'s raw `x`, at `0x78001868`. -/
def rNoteX : List Word :=
  [0x2c022c480ffc6e13#64, 0x239ec55cfc14a47c#64, 0xcd239fab936f3df2#64, 0x26b206c328a94533#64]

/-- … its raw `y`, at `0x78001888`. -/
def rNoteY : List Word :=
  [0xc34153c622cf37e3#64, 0x79c7c07823e0dcf6#64, 0xa9541a2f2366e1c6#64, 0x3cde564b686dc04c#64]

/-- `Q` as the guest holds it (Jacobian Montgomery limbs, `Z = R`). -/
def qNoteW : List Word := domainPtW qNoteX qNoteY

/-- `R` as the guest holds it. -/
def rNoteW : List Word := domainPtW rNoteX rNoteY

/-- `Fp::to_repr` / `to_le_bits` of Montgomery limbs: the canonical value's bytes as words. -/
def reprW (x : List Word) : List Word := natToLeLimbs 4 (leLimbsToNat x * Fp.rInv % Fp.p)

/-- The message bytes of the note commitment of `(g★_d, pk★_d, v, ρ, ψ)`, `ρ` and `ψ` given
as Montgomery limbs. -/
def noteMsgW (gd pkd : List Word) (v : Word) (rho psi : List Word) : List Word :=
  noteBitsW gd pkd v (reprW rho) (reprW psi)

theorem noteMsgW_eq (gd pkd : List Word) (v : Word) (rho psi : List Word) :
    noteMsgW gd pkd v rho psi = boolBytesToWords (noteBit gd pkd v (reprW rho) (reprW psi)) 137 := rfl

/-- `conditional_select` on `commit`'s flag: the commitment when the hash is defined, the
identity `(0, 0, 0)` otherwise. -/
def cmSel (Q R B k : List Word) : List Word :=
  cond (commitFold Q B).isSome (commitW Q R B k)
    [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64]

theorem cmSel_none {Q R B k : List Word} (h : commitFold Q B = none) :
    cmSel Q R B k = [0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64, 0#64] := by
  rw [cmSel, h]; rfl

theorem cmSel_some {Q R B k L : List Word} (h : commitFold Q B = some L) :
    cmSel Q R B k = commitW Q R B k := by
  rw [cmSel, h]; rfl

/-- A twelve-element list is its cells. -/
theorem cells12_eq (L : List Word) (h : L.length = 12) :
    [L[0]!, L[1]!, L[2]!, L[3]!, L[4]!, L[5]!, L[6]!, L[7]!, L[8]!, L[9]!, L[10]!, L[11]!] = L :=
  ((List.eq_map_range L h).trans rfl).symm

/-- The cells `conditional_select` leaves, as the model. -/
theorem cmSel_cells (Q R B k : List Word) :
    [if (commitFold Q B).isSome = true then (commitW Q R B k)[0]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[1]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[2]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[3]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[4]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[5]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[6]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[7]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[8]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[9]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[10]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[11]! else 0#64] = cmSel Q R B k := by
  unfold cmSel
  generalize (commitFold Q B).isSome = c
  cases c
  · rfl
  · simp only [if_true]
    exact cells12_eq _ (commitW_length _ _ _ _)

theorem cmSel_length (Q R B k : List Word) : (cmSel Q R B k).length = 12 := by
  unfold cmSel
  generalize (commitFold Q B).isSome = c
  cases c
  · rfl
  · exact commitW_length _ _ _ _

/-- The thirteen cells `derive` leaves at `out`: the selected point, then the flag cell. -/
theorem cmSel_cells13 (Q R B k : List Word) (f : Word) :
    [if (commitFold Q B).isSome = true then (commitW Q R B k)[0]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[1]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[2]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[3]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[4]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[5]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[6]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[7]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[8]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[9]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[10]! else 0#64,
      if (commitFold Q B).isSome = true then (commitW Q R B k)[11]! else 0#64, f] =
    cmSel Q R B k ++ [f] := by
  rw [← cmSel_cells]; rfl

-- the executor sizes a post region stated over a model by `simp`: its length lemmas
attribute [simp] domainPtW_length boolBytesToWords_length noteBitsW_length

/-- `conditional_select` on `commit`'s flag byte, read back zero-extended. -/
theorem conditional_select_spec_flag {G : MachineState → Prop} {n : Nat} {P : Prop} (s : MachineState) (ra sp a0 a1 a2 : Word)
    (Q Bv : List Word)
    (p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 : Word)
    (O : List Word) (hOl : O.length = 12)
    (hpc : s.pc = 0x78023d7c#64) (hcode : CodeAt F_78023d7c.base F_78023d7c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x20 sp)
    (ha0 : s.getReg .x10 = a0) (ha1 : s.getReg .x11 = a1) (ha2 : s.getReg .x12 = a2)
    (ha3 : s.getReg .x13 = BitVec.zeroExtend 64 (commitFlag Q Bv))
    (hA : Region a1 [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11] s)
    (hok1 : RegionOk Ro.layout.roBase Ro.layout.textHi a1 12)
    (hB : Region a2 [q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11] s)
    (hok2 : RegionOk Ro.layout.roBase Ro.layout.textHi a2 12)
    (hO : Region a0 O s) (hok0 : RegionOk Ro.layout.roBase Ro.layout.textHi a0 12)
    (hd0 : Disjoint (sp - 0x20#64) 4 a0 12) (hd1 : Disjoint (sp - 0x20#64) 4 a1 12)
    (hd2 : Disjoint (sp - 0x20#64) 4 a2 12)
    (he1 : Disjoint a0 12 a1 12) (he2 : Disjoint a0 12 a2 12)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0x20#64, 4), (a0, 12)] s t →
      Region a0 [if (commitFold Q Bv).isSome then q0 else p0, if (commitFold Q Bv).isSome then q1 else p1,
        if (commitFold Q Bv).isSome then q2 else p2, if (commitFold Q Bv).isSome then q3 else p3,
        if (commitFold Q Bv).isSome then q4 else p4, if (commitFold Q Bv).isSome then q5 else p5,
        if (commitFold Q Bv).isSome then q6 else p6, if (commitFold Q Bv).isSome then q7 else p7,
        if (commitFold Q Bv).isSome then q8 else p8, if (commitFold Q Bv).isSome then q9 else p9,
        if (commitFold Q Bv).isSome then q10 else p10, if (commitFold Q Bv).isSome then q11 else p11] t →
      SafeN G n P t) :
    SafeN G n P s :=
  conditional_select_spec s ra sp a0 a1 a2 (commitFold Q Bv).isSome p0 p1 p2 p3 p4 p5 p6 p7 p8 p9
    p10 p11 q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 O hOl hpc hcode hcw hra hra1 hsp hstk ha0 ha1 ha2
    (by rw [ha3]; unfold commitFlag bw; split <;> rfl) hA hok1 hB hok2 hO hok0 hd0 hd1 hd2 he1 he2 hk

/-- The padded-bit iterator (`Pad<Chain<…>>`, 120 bytes) as `derive` lays it out in its frame
at `sp - 0x148`: the tags, lengths and pointers (`ρ`'s bits at `sp - 0x88`, `ψ`'s at `sp - 0x68`,
`g★_d` at `sp - 0xd0`, `pk★_d` at `sp - 0xb0`, `v` at `sp - 0x90`), stored by the compiler's
schedule of sub-word stores over the block's previous contents `J` (whose padding bytes survive).
Reducible: a `from_iter` contract stated over it is matched against the executor's cells. -/
@[reducible] def iterW (sp : Word) (J : List Word) : List Word :=
  [255#64,
   sp + 18446744073709551480#64,
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[2]! 3 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 40))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551512#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 48))),
   (replaceByte (replaceByte J[3]! 0 (BitVec.truncate 8 ((sp + 18446744073709551512#64) >>> 56))) 1 (BitVec.truncate 8 0#64)),
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[4]! 3 (BitVec.truncate 8 ((sp + 18446744073709551408#64) >>> 16))) 4 (BitVec.truncate 8 ((sp + 18446744073709551408#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551408#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551408#64) >>> 40))) 0 (BitVec.truncate 8 1#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551408#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551408#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551408#64) >>> 48))),
   (replaceHalfword (replaceHalfword (replaceHalfword (replaceByte (replaceByte J[5]! 0 (BitVec.truncate 8 ((sp + 18446744073709551408#64) >>> 56))) 1 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 16 (sp + 18446744073709551440#64))) 2 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 16))) 3 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 32))),
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceHalfword J[6]! 0 (BitVec.truncate 16 ((sp + 18446744073709551440#64) >>> 48))) 2 (BitVec.truncate 8 0#64)) 7 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 32))) 3 (BitVec.truncate 8 (sp + 18446744073709551440#64))) 4 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 8))) 5 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 16))) 6 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 24))),
   (replaceWord32 (replaceByte (replaceByte (replaceByte (replaceByte J[7]! 0 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 40))) 1 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 48))) 2 (BitVec.truncate 8 ((sp + 18446744073709551440#64) >>> 56))) 3 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 32 (sp + 18446744073709551472#64))),
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceWord32 J[8]! 0 (BitVec.truncate 32 ((sp + 18446744073709551472#64) >>> 32))) 4 (BitVec.truncate 8 0#64)) 5 (BitVec.truncate 8 (sp + 18446744073709551472#64))) 6 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 8))) 7 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 16))),
   (replaceHalfword (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[9]! 1 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 32))) 2 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 40))) 3 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 48))) 4 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 56))) 0 (BitVec.truncate 8 ((sp + 18446744073709551472#64) >>> 24))) 5 (BitVec.truncate 8 0#64)) 3 (BitVec.truncate 16 (sp + 18446744073709551480#64))),
   (replaceHalfword (replaceHalfword (replaceByte (replaceHalfword J[10]! 2 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 48))) 6 (BitVec.truncate 8 0#64)) 0 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 16))) 1 (BitVec.truncate 16 ((sp + 18446744073709551480#64) >>> 32))),
   255#64,
   sp + 18446744073709551512#64,
   (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte (replaceByte J[13]! 4 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 24))) 5 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 32))) 6 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 40))) 7 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 48))) 0 (BitVec.truncate 8 0#64)) 1 (BitVec.truncate 8 (sp + 18446744073709551544#64))) 2 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 8))) 3 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 16))),
   (replaceByte (replaceByte J[14]! 0 (BitVec.truncate 8 ((sp + 18446744073709551544#64) >>> 56))) 1 (BitVec.truncate 8 0#64))]

/-! ## The specification -/

set_option maxHeartbeats 1000000000 in
set_option maxRecDepth 200000 in
set_option machineChecked.sym.foldBytes true in
theorem note_commitment_derive_spec {G : MachineState → Prop} {nb : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState)
    (ra sp out gd pkd v rho psi rcm : Word)
    (g0 g1 g2 g3 p0 p1 p2 p3 r0 r1 r2 r3 q0 q1 q2 q3 k0 k1 k2 k3 : Word)
    (O J : List Word) (hOl : O.length = 13) (hJl : J.length = 15)
    (hpaf : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803a110#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x15 ∈ Run.vals_a110 → SafeN G nb P u)
    (hpanic : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803de40#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → SafeN G nb P u)
    (hunwrap : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dc7c#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x10 ∈ Run.vals_dc7c_10 → u.getReg .x13 ∈ Run.vals_dc7c_13 → u.getReg .x14 ∈ Run.vals_dc7c_14 → SafeN G nb P u)
    (hbounds : ∀ (u : MachineState) (sp' : Word) (L' : List (Word × Nat)), u.pc = 0x7803dcdc#64 → u.code = s.code →
      u.getReg .x2 = sp' → StackOk Ro.layout 0 sp' → RoImage Ro.layout u → Run.HeapAt L' u → u.getReg .x12 ∈ Run.vals_dcdc → SafeN G nb P u)
    (hpc : s.pc = 0x7801fbcc#64) (hcode : CodeAt F_7801fbcc.base F_7801fbcc.prog s)
    -- callees: cached_commit_domain (+ from_raw, from_xy, is_on_curve, mulmod, black_box,
    -- to_curve), to_le_bits (+ to_repr), commit and its callees, memset, conditional_select
    (hcodeCD : CodeAt F_78020548.base F_78020548.prog s) (hcodeLB : CodeAt F_78029b18.base F_78029b18.prog s)
    (hcodeCm : CodeAt F_78020d50.base F_78020d50.prog s)
    (hcodeC : CodeAt F_7801b4d8.base F_7801b4d8.prog s) (hcodeTA : CodeAt F_78025164.base F_78025164.prog s)
    (hcodeI : CodeAt F_78028d04.base F_78028d04.prog s) (hcodeM : CodeAt F_7801bf5c.base F_7801bf5c.prog s)
    (hcodeBB : CodeAt F_7803a0fc.base F_7803a0fc.prog s) (hcodeCo : CodeAt F_78023f64.base F_78023f64.prog s)
    (hcodeP : CodeAt F_780237dc.base F_780237dc.prog s) (hcodeRp : CodeAt F_78029468.base F_78029468.prog s)
    (hcodeL : CodeAt F_780234cc.base F_780234cc.prog s) (hcodeIA : CodeAt F_780235e8.base F_780235e8.prog s)
    (hcodeCmp : CodeAt F_7803f54c.base F_7803f54c.prog s) (hcodeAA : CodeAt F_78035f88.base F_78035f88.prog s)
    (hcodeLR : CodeAt F_780360e0.base F_780360e0.prog s) (hcodeAdd : CodeAt F_7801bf3c.base F_7801bf3c.prog s)
    (hcodeU : CodeAt F_78023864.base F_78023864.prog s) (hcodeR : CodeAt F_780297c0.base F_780297c0.prog s)
    (hcodeXY : CodeAt F_78026878.base F_78026878.prog s) (hcodeOC : CodeAt F_78026258.base F_78026258.prog s)
    (hcodeFR : CodeAt F_78028298.base F_78028298.prog s) (hcodeTC : CodeAt F_78025854.base F_78025854.prog s)
    (hcodeF : CodeAt F_780239bc.base F_780239bc.prog s) (hcodeBt : CodeAt F_78023544.base F_78023544.prog s)
    (hcodeS : CodeAt F_7803f57c.base F_7803f57c.prog s) (hcodeCS : CodeAt F_78023d7c.base F_78023d7c.prog s)
    (hcodeB : CodeAt F_78023594.base F_78023594.prog s) (hcodeW : CodeAt F_7802827c.base F_7802827c.prog s)
    (hcodeMul : CodeAt F_78031be8.base F_78031be8.prog s) (hcodeRq : CodeAt F_7802e9b8.base F_7802e9b8.prog s)
    (hcodeA : CodeAt F_78035fe0.base F_78035fe0.prog s) (hcodeDbl : CodeAt F_7801bf4c.base F_7801bf4c.prog s)
    (hcodeD : CodeAt F_780360c8.base F_780360c8.prog s) (hcodeAF : CodeAt F_7803a110.base F_7803a110.prog s)
    (hcodeAFI : CodeAt F_7803dd28.base F_7803dd28.prog s) (hcodeEA : CodeAt F_78026b44.base F_78026b44.prog s)
    (hcodeED : CodeAt F_7802413c.base F_7802413c.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s) (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hra : s.getReg .x1 = ra) (hra1 : ra &&& ~~~1#64 = ra)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0xb50 sp)
    (ha0 : s.getReg .x10 = out) (ha1 : s.getReg .x11 = gd) (ha2 : s.getReg .x12 = pkd)
    (ha3 : s.getReg .x13 = v) (ha4 : s.getReg .x14 = rho) (ha5 : s.getReg .x15 = psi)
    (ha6 : s.getReg .x16 = rcm)
    (hG : Region gd [g0, g1, g2, g3] s) (hokG : RegionOk Ro.layout.textLo Ro.layout.textHi gd 4)
    (hP : Region pkd [p0, p1, p2, p3] s) (hokP : RegionOk Ro.layout.textLo Ro.layout.textHi pkd 4)
    (hR : Region rho [r0, r1, r2, r3] s) (hokR : RegionOk Ro.layout.roBase Ro.layout.textHi rho 4)
    (hS : Region psi [q0, q1, q2, q3] s) (hokS : RegionOk Ro.layout.roBase Ro.layout.textHi psi 4)
    (hK : Region rcm [k0, k1, k2, k3] s) (hokK : RegionOk Ro.layout.roBase Ro.layout.textHi rcm 4)
    (hO : Region out O s) (hokO : RegionOk Ro.layout.roBase Ro.layout.textHi out 13)
    (hbelow_out : out.toNat + 8 * 13 ≤ 0x78040620)
    -- the frame's iterator block before the call: the struct's padding bytes keep these
    (hJ : Region (sp - 0xb50#64 + 0xa08#64) J s)
    (hd0 : Disjoint (sp - 0xb50#64) 362 out 13) (hd1 : Disjoint (sp - 0xb50#64) 362 gd 4)
    (hd2 : Disjoint (sp - 0xb50#64) 362 pkd 4) (hd3 : Disjoint (sp - 0xb50#64) 362 rho 4)
    (hd4 : Disjoint (sp - 0xb50#64) 362 psi 4) (hd5 : Disjoint (sp - 0xb50#64) 362 rcm 4)
    (he0 : Disjoint out 13 gd 4) (he1 : Disjoint out 13 pkd 4) (he2 : Disjoint out 13 rho 4)
    (he3 : Disjoint out 13 psi 4) (he4 : Disjoint out 13 rcm 4)
    (hh0 : Disjoint 0x78040620#64 14780694332 out 13) (hh1 : Disjoint 0x78040620#64 14780694332 rcm 4)
    -- `Vec<bool>::from_iter` of the padded bit iterator (ledger T2): the iterator block as
    -- `derive` builds it (ITER_CELLS: tags, lengths and pointers into this frame — `ρ`'s bits at
    -- `+0x1e8`, `ψ`'s at `+0x208`, `g★_d` at `+0x1a0`, `pk★_d` at `+0x1c0`, `v` at `+0x1e0` —
    -- with the struct's padding bytes `J` left as they were) over the message words at
    -- `+0x1a0` yields 1090 bytes, byte `o` the message bit `o`
    (hfrom : ∀ (u : MachineState) (sp' a0' a1' j : Word) (O1 : List Word) (L' : List (Word × Nat)), O1.length = 3 →
      u.pc = 0x7801dfb4#64 → u.code = s.code → u.getReg .x1 = 0x78020dc4#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x260 sp' → u.getReg .x10 = a0' → u.getReg .x11 = a1' →
      Region a0' O1 u → Region a1' [0#64, j] u →
      Region (a1' + 0x10#64) (iterW sp J) u →
      Region (a1' + 0x88#64) [0#64] u →
      Region (sp - 0xb50#64 + 0xa80#64) ([g0, g1, g2, g3, p0, p1, p2, p3, v] ++
        reprW [r0, r1, r2, r3] ++ reprW [q0, q1, q2, q3]) u →
      RegionOk Ro.layout.roBase Ro.layout.textHi a0' 3 → RegionOk Ro.layout.roBase Ro.layout.textHi a1' 18 →
      Disjoint (sp' - 0x260#64) 76 a0' 3 → Disjoint (sp' - 0x260#64) 76 a1' 18 →
      Disjoint a0' 3 a1' 18 →
      StackOk Ro.layout 0xb50 sp →
      Disjoint (sp' - 0x260#64) 76 (sp - 0xb50#64 + 0xa80#64) 17 → Disjoint a0' 3 (sp - 0xb50#64 + 0xa80#64) 17 → Disjoint a1' 18 (sp - 0xb50#64 + 0xa80#64) 17 →
      Disjoint 0x78040620#64 14780694332 a0' 3 → Disjoint 0x78040620#64 14780694332 a1' 18 →
      a0'.toNat + 8 * 3 ≤ 0x78040620 → a1'.toNat + 8 * 18 ≤ 0x78040620 →
      RoImage Ro.layout u → Run.HeapAt L' u →
      (∀ (t : MachineState) (cap ptr : Word) (J Bv : List Word), t.pc = 0x78020dc4#64 →
        CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x260#64, 76), (a0', 3), (a1', 18), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t →
        J.length = 18 → Region a0' [cap, ptr, 1090#64] t → cap ≠ 0#64 → Region a1' J t →
        Bv.length = 137 →
        (∀ o, o < 1090 → byteAt Bv o = bw (noteBit [g0, g1, g2, g3] [p0, p1, p2, p3] v
          (reprW [r0, r1, r2, r3]) (reprW [q0, q1, q2, q3]) o)) →
        Region ptr Bv t → RegionOk Ro.layout.roBase Ro.layout.textHi ptr 137 →
        0x78048980 ≤ ptr.toNat → ptr.toNat + 8 * 137 ≤ 0x1c00000000 → Run.HeapAt ((ptr, 256) :: L') t → SafeN G nb P t) → SafeN G nb P u)
    -- `__rust_dealloc` of that `Vec` (ledger T2)
    (hdealloc : ∀ (u : MachineState) (sp' ptr cap : Word) (C : List Word) (k : Nat) (L' : List (Word × Nat)), C.length = 137 →
      u.pc = 0x7801bd08#64 → u.code = s.code → u.getReg .x1 = 0x780210f0#64 →
      u.getReg .x2 = sp' → StackOk Ro.layout 0x20 sp' → u.getReg .x10 = ptr → u.getReg .x11 = cap →
      u.getReg .x12 = 1#64 → Region ptr C u → 0x78048980 ≤ ptr.toNat →
      ptr.toNat + 8 * 137 ≤ 0x1c00000000 →
      RoImage Ro.layout u → Run.HeapAt ((ptr, k) :: L') u →
      (∀ t, t.pc = 0x780210f0#64 → CalleeSaved u t → t.code = u.code →
        Unchanged [(sp' - 0x20#64, 4), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] u t → Run.HeapAt L' t → SafeN G nb P t) → SafeN G nb P u)
    (hk : ∀ t, t.pc = ra → CalleeSaved s t → t.code = s.code →
      Unchanged [(sp - 0xb50#64, 362), (out, 13), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s t →
      Region out (cmSel qNoteW rNoteW (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3]
        [q0, q1, q2, q3]) [k0, k1, k2, k3]) t →
      Region (out + 0x60#64) [replaceByte O[12]! 0 (commitFlag qNoteW
        (noteMsgW [g0, g1, g2, g3] [p0, p1, p2, p3] v [r0, r1, r2, r3] [q0, q1, q2, q3]))] t →
      mulFacts rNoteW [k0, k1, k2, k3] → Run.HeapAt L t → SafeN G nb P t) :
    SafeN G nb P s := by
  have hokW : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb50#64) 362 := hstk.frame 362 (by decide)
  -- the frame (below it 0x8e0 bytes for `commit`): the domain `[Q, R]`, `commit`'s output,
  -- the iterator, the message words, the save area
  have hokA : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb50#64 + 0x8e0#64) 24 := hokW.sub' 284 24 (by decide) (by bv_omega)
  have hokB : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb50#64 + 0x9a0#64) 13 := hokW.sub' 308 13 (by decide) (by bv_omega)
  have hokC : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb50#64 + 0xa08#64) 15 := hokW.sub' 321 15 (by decide) (by bv_omega)
  have hokD : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb50#64 + 0xa80#64) 17 := hokW.sub' 336 17 (by decide) (by bv_omega)
  have hokE : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xb50#64 + 0xb08#64) 9 := hokW.sub' 353 9 (by decide) (by bv_omega)
  obtain ⟨A, hA, hAl⟩ := Region.exists_junk (sp - 0xb50#64 + 0x8e0#64) 24 s
  obtain ⟨B, hB, hBl⟩ := Region.exists_junk (sp - 0xb50#64 + 0x9a0#64) 13 s
  obtain ⟨D, hD, hDl⟩ := Region.exists_junk (sp - 0xb50#64 + 0xa80#64) 17 s
  obtain ⟨E, hE, hEl⟩ := Region.exists_junk (sp - 0xb50#64 + 0xb08#64) 9 s
  -- the generators' raw coordinates in the read-only segment
  have hQx : Region 0x78001828#64 qNoteX s := (hro.get 12 (by decide)).sub 5 4 (by decide) rfl
  have hokQx : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001828#64 4 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 12 (by decide)).sub' 5 4 (by decide) (by decide)
  have hQy : Region 0x78001848#64 qNoteY s := (hro.get 12 (by decide)).sub 9 4 (by decide) rfl
  have hokQy : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001848#64 4 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 12 (by decide)).sub' 9 4 (by decide) (by decide)
  have hRx : Region 0x78001868#64 rNoteX s := (hro.get 12 (by decide)).sub 13 4 (by decide) rfl
  have hokRx : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001868#64 4 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 12 (by decide)).sub' 13 4 (by decide) (by decide)
  have hRy : Region 0x78001888#64 rNoteY s := (hro.get 12 (by decide)).sub 17 4 (by decide) rfl
  have hokRy : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001888#64 4 :=
    (RoImage.ok Ro.layout Ro.layout.textLo Ro.layout.textHi (by decide) 12 (by decide)).sub' 17 4 (by decide) (by decide)
  have hhF : Disjoint 0x78040620#64 14780694332 (sp - 0xb50#64) 362 := Disjoint.heap_frame (n := 362) hstk (by decide)
  have hokH : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 14780694332 := heapOk
  have hokHc : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78040620#64 4162 := ctlOk
  have hokHa : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78048980#64 14780690128 := arenaOk
  have hlo := hstk.lo
  have hhi := (Nat.le_trans hstk.hi (Nat.le_of_eq Ro.layout_stackTop))
  have hu := Unchanged.refl [(sp - 0xb50#64, 362), (out, 13), (0x78040620#64, 4162), (0x78048980#64, 14780690128)] s
  sym_exec [cached_commit_domain_spec, to_le_bits_spec, hpaf] stop [0x78020124]
  -- the message words `g★_d`, `pk★_d` were reassembled from their bytes
  have hg0 : v114 = g0 := by
    simp only [← v93_def, ← v94_def, ← v95_def, ← v96_def, ← v97_def, ← v98_def, ← v99_def, ← v100_def, ← v101_def, ← v102_def, ← v103_def, ← v104_def, ← v105_def, ← v106_def, ← v107_def, ← v108_def, ← v109_def, ← v110_def, ← v111_def, ← v112_def, ← v113_def, ← v114_def]
    exact bytes_word g0
  have hg1 : v92 = g1 := by
    simp only [← v71_def, ← v72_def, ← v73_def, ← v74_def, ← v75_def, ← v76_def, ← v77_def, ← v78_def, ← v79_def, ← v80_def, ← v81_def, ← v82_def, ← v83_def, ← v84_def, ← v85_def, ← v86_def, ← v87_def, ← v88_def, ← v89_def, ← v90_def, ← v91_def, ← v92_def]
    exact bytes_word g1
  have hg2 : v70 = g2 := by
    simp only [← v49_def, ← v50_def, ← v51_def, ← v52_def, ← v53_def, ← v54_def, ← v55_def, ← v56_def, ← v57_def, ← v58_def, ← v59_def, ← v60_def, ← v61_def, ← v62_def, ← v63_def, ← v64_def, ← v65_def, ← v66_def, ← v67_def, ← v68_def, ← v69_def, ← v70_def]
    exact bytes_word g2
  have hg3 : v48 = g3 := by
    simp only [← v27_def, ← v28_def, ← v29_def, ← v30_def, ← v31_def, ← v32_def, ← v33_def, ← v34_def, ← v35_def, ← v36_def, ← v37_def, ← v38_def, ← v39_def, ← v40_def, ← v41_def, ← v42_def, ← v43_def, ← v44_def, ← v45_def, ← v46_def, ← v47_def, ← v48_def]
    exact bytes_word g3
  have hp0 : v207 = p0 := by
    simp only [← v185_def, ← v186_def, ← v187_def, ← v188_def, ← v189_def, ← v190_def, ← v191_def, ← v192_def, ← v193_def, ← v194_def, ← v195_def, ← v196_def, ← v197_def, ← v198_def, ← v199_def, ← v200_def, ← v201_def, ← v202_def, ← v203_def, ← v204_def, ← v206_def, ← v207_def]
    exact bytes_word p0
  have hp1 : v184 = p1 := by
    simp only [← v163_def, ← v164_def, ← v165_def, ← v166_def, ← v167_def, ← v168_def, ← v169_def, ← v170_def, ← v171_def, ← v172_def, ← v173_def, ← v174_def, ← v175_def, ← v176_def, ← v177_def, ← v178_def, ← v179_def, ← v180_def, ← v181_def, ← v182_def, ← v183_def, ← v184_def]
    exact bytes_word p1
  have hp2 : v162 = p2 := by
    simp only [← v141_def, ← v142_def, ← v143_def, ← v144_def, ← v145_def, ← v146_def, ← v147_def, ← v148_def, ← v149_def, ← v150_def, ← v151_def, ← v152_def, ← v153_def, ← v154_def, ← v155_def, ← v156_def, ← v157_def, ← v158_def, ← v159_def, ← v160_def, ← v161_def, ← v162_def]
    exact bytes_word p2
  have hp3 : v140 = p3 := by
    simp only [← v119_def, ← v120_def, ← v121_def, ← v122_def, ← v123_def, ← v124_def, ← v125_def, ← v126_def, ← v127_def, ← v128_def, ← v129_def, ← v130_def, ← v131_def, ← v132_def, ← v133_def, ← v134_def, ← v135_def, ← v136_def, ← v137_def, ← v138_def, ← v139_def, ← v140_def]
    exact bytes_word p3
  rw [hg0, hg1, hg2, hg3, hp0, hp1, hp2, hp3, ← acc220_0_def, ← acc245_0_def] at hR8
  have eM : [g0, g1, g2, g3, p0, p1, p2, p3, v,
      BitVec.ofNat 64 ((leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p) >>> (64 * 0)),
      BitVec.ofNat 64 ((leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p) >>> (64 * 1)),
      BitVec.ofNat 64 ((leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p) >>> (64 * 2)),
      BitVec.ofNat 64 ((leLimbsToNat [r0, r1, r2, r3] * Fp.rInv % Fp.p) >>> (64 * 3)),
      BitVec.ofNat 64 ((leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p) >>> (64 * 0)),
      BitVec.ofNat 64 ((leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p) >>> (64 * 1)),
      BitVec.ofNat 64 ((leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p) >>> (64 * 2)),
      BitVec.ofNat 64 ((leLimbsToNat [q0, q1, q2, q3] * Fp.rInv % Fp.p) >>> (64 * 3))] =
      [g0, g1, g2, g3, p0, p1, p2, p3, v] ++ reprW [r0, r1, r2, r3] ++ reprW [q0, q1, q2, q3] := by
    simp only [reprW, natToLeLimbs_cells4, List.cons_append, List.nil_append, Nat.reduceMul,
      Nat.shiftRight_zero]
  have hR8' := Eq.mp (congrArg (fun L => Region (sp - 0xb50#64 + 0xa80#64) L s_345) eM) hR8
  clear hR8
  -- the iterator block's cells, atom-free, so that `commit`'s contract matches `hfrom`
  simp only [← v222_def, ← v223_def, ← v224_def, ← v225_def, ← v226_def, ← v227_def, ← v228_def, ← v229_def, ← v230_def, ← v232_def, ← v233_def, ← v234_def, ← v235_def, ← v236_def, ← v237_def, ← v238_def, ← v239_def, ← v248_def, ← v249_def, ← v250_def, ← v253_def, ← v254_def, ← v255_def, ← v256_def, ← v257_def, ← v258_def, ← v259_def, ← v260_def, ← v261_def, ← v262_def, ← v263_def, ← v264_def, ← v265_def, ← v266_def, ← v267_def, ← v268_def, ← v269_def, ← v272_def, ← v273_def, ← v274_def, ← v275_def, ← v276_def, ← v277_def, ← v278_def, ← v279_def, ← v280_def, ← v281_def, ← v282_def, ← v284_def, ← v285_def, ← v286_def, ← v287_def, ← v288_def, ← v289_def, ← v290_def, ← v291_def, ← v292_def, ← v293_def, ← v294_def, ← v295_def, ← v296_def, ← v297_def, ← v299_def, ← v300_def, ← v301_def, ← v302_def, ← v303_def, ← v304_def, ← v305_def, ← v306_def, ← v307_def, ← v308_def, ← v309_def, ← v310_def, ← v311_def, ← v312_def, ← v313_def, ← v314_def, ← v315_def, ← v316_def, ← v317_def, ← v318_def, ← v320_def, ← v321_def, ← v322_def, ← v323_def, ← v324_def, ← v325_def, ← v326_def, ← v327_def, ← v328_def, ← v329_def, ← v330_def, ← v331_def, ← v332_def, ← v333_def, ← v334_def, ← v335_def, ← v336_def, ← v337_def, ← v338_def, ← v339_def, ← v340_def] at hR6
  sym_reframe
  have hcommit := sinsemilla_commit_spec (L := L) (G := G) (n := nb) (P := P) (M := sp - 0xb50#64 + 0xa80#64)
    (Mw := [g0, g1, g2, g3, p0, p1, p2, p3, v] ++ reprW [r0, r1, r2, r3] ++ reprW [q0, q1, q2, q3])
    (bit := noteBit [g0, g1, g2, g3] [p0, p1, p2, p3] v (reprW [r0, r1, r2, r3]) (reprW [q0, q1, q2, q3]))
    (hMl := by simp [reprW])
    (Mok := StackOk Ro.layout 0xb50 sp) (hMok := hstk)
  sym_exec [hcommit, memset96_spec', conditional_select_spec_flag, hpaf, hpanic, hunwrap, hbounds]
  -- the generators are the models' `Q` and `R`
  have hQ : [acc26_0[0]!, acc26_0[1]!, acc26_0[2]!, acc26_0[3]!, acc26_0[4]!, acc26_0[5]!, acc26_0[6]!,
      acc26_0[7]!, acc26_0[8]!, acc26_0[9]!, acc26_0[10]!, acc26_0[11]!] = qNoteW :=
    (cells12_eq _ (acc26_0_def ▸ domainPtW_length _ _)).trans acc26_0_def.symm
  have hR : [acc26_1[0]!, acc26_1[1]!, acc26_1[2]!, acc26_1[3]!, acc26_1[4]!, acc26_1[5]!, acc26_1[6]!,
      acc26_1[7]!, acc26_1[8]!, acc26_1[9]!, acc26_1[10]!, acc26_1[11]!] = rNoteW :=
    (cells12_eq _ (acc26_1_def ▸ domainPtW_length _ _)).trans acc26_1_def.symm
  rw [hR] at post2_6
  have hRo := hR5
  rw [← v17_def, ← v9_def, ← acc2_0_def, hQ, hR, cmSel_cells13, trunc8_zext, ← noteMsgW_eq] at hRo
  have hRoP := hRo.sub 0 12 (a := out) (ws := cmSel _ _ _ _) (by simp)
    (by rw [List.drop_zero, List.take_left' (cmSel_length _ _ _ _)])
  have hRoF := hRo.sub 12 1 (a := out + 0x60#64) (ws := [replaceByte _ 0 (commitFlag _ _)]) rfl
    (by rw [List.drop_left' (cmSel_length _ _ _ _)]; rfl)
  sym_close hk

end Cases.Zip2005
