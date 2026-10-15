import Cases.Zip2005.Runtime.Heap
import Cases.Zip2005.Runtime.MemcpySpec
import Cases.Zip2005.Runtime.MemsetPad
import Cases.Zip2005.Sha256.Sha256Compress
import Cases.Zip2005.Image.F_7801afc0
import Cases.Zip2005.Image.F_7801b4d8
import Cases.Zip2005.Image.F_7803f57c
import Cases.Zip2005.Image.F_78035e44
import Cases.Zip2005.Image.Ro
import Cases.Zip2005.Run.Heap
import Cases.Zip2005.Run.Vals

/-!
# `syscall_halt` (0x7801afc0) with a nonzero exit code

SP1's halt: `PUBLIC_VALUES_HASHER.take().unwrap()` (the static at `0x78048830`: an `Option<Sha256>`,
its tag word then the 0x70-byte hasher state, the buffer position as the last byte), the hasher
finalised (the `0x80` pad byte, `memset` of the rest of the block, the bit length, one or two
`compress256`), the eight digest words byte-swapped and `COMMIT`ed, eight
`COMMIT_DEFERRED_PROOFS`, then `HALT` with the exit code. A nonzero code never accepts
(`AsmVerif.RiscV.SafeN.reject`), so `Safe P` for every `P`.

The static is taken **fresh**: its buffer position byte is zero, as `__start` leaves it
(`Some(Sha256::new())`) and nothing in the guest writes to it (the only `syscall_write` reachable
from `main` is `empty_input_stream_halt`'s, to fd 2, which does not touch the hasher). The tag and
the other fourteen words are arbitrary: a tag with bit 0 clear is the `None` arm, `unwrap_failed`.
With position 0 the pad byte lands at the block's start, the length word at its end, and one
`compress256` finishes the hash.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 Cases.Zip2005.Image AsmVerif.RiscV.Sym

set_option autoImplicit false

/-- The hasher static's region, off the code window. -/
theorem hasherOk : RegionOk Ro.layout.roBase Ro.layout.textHi 0x78048830#64 15 :=
  ⟨by decide, by decide, Or.inr (by decide)⟩

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
theorem syscall_halt_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (sp c : Word)
    (f h0 h1 h2 h3 cnt b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (hpc : s.pc = 0x7801afc0#64) (hcode : CodeAt F_7801afc0.base F_7801afc0.prog s)
    (hcodeCpy : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSet : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeSha : CodeAt F_780361e0.base F_780361e0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x470 sp)
    (ha0 : s.getReg .x10 = c) (hc : c ≠ 0#64)
    (hST : Region 0x78048830#64 [f, h0, h1, h2, h3, cnt, b0, b1, b2, b3, b4, b5, b6, b7, 0#64] s) :
    SafeN G n P s := by
  have hokS : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x470#64) 142 := hstk.frame 142 (by decide)
  have hu := Unchanged.refl [(sp - 0x470#64, 142), (0x78048830#64, 15)] s
  have hlo := hstk.lo
  have hokST := hasherOk
  -- the hasher is `Some` (the run's invariant): the `None` arm is dead
  have hf : f = 1#64 := by
    have h := hST 0 (by simp)
    simp only [Nat.mul_zero, BitVec.add_zero] at h
    exact h.symm.trans (Run.HeapAt.tag hheap)
  subst hf
  -- the frame (`sp' = sp - 0xe0`): [0, 8) the first slot, the hasher copy [8, 0x78), the
  -- second block [0x78, 0xb8), the save area [0xb8, 0xe0)
  have hok0 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xe0#64) 1 := hokS.sub' 114 1 (by decide) (by bv_omega)
  have hok1 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0xd8#64) 14 := hokS.sub' 115 14 (by decide) (by bv_omega)
  have hok2 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x68#64) 8 := hokS.sub' 129 8 (by decide) (by bv_omega)
  have hok3 : RegionOk Ro.layout.textLo Ro.layout.textHi (sp - 0x28#64) 5 := hokS.sub' 137 5 (by decide) (by bv_omega)
  obtain ⟨F0, hF0, hF0l⟩ := Region.exists_junk (sp - 0xe0#64) 1 s
  obtain ⟨F1, hF1, hF1l⟩ := Region.exists_junk (sp - 0xd8#64) 14 s
  obtain ⟨F2, hF2, hF2l⟩ := Region.exists_junk (sp - 0x68#64) 8 s
  obtain ⟨F3, hF3, hF3l⟩ := Region.exists_junk (sp - 0x28#64) 5 s
  -- the `HALT`'s fetch, through the code map (the executor renames the `CodeAt` facts)
  have hfetch : s.code 0x7801b380#64 = some .ECALL := hcode 240 (by decide)
  sym_exec [memcpy112_spec, memset63_pad_spec, compress256_spec]
  -- the `HALT` with the symbolic exit code
  refine AsmVerif.RiscV.SafeN.reject ?_ ?_ ?_
  · rw [hpc, hcode]; exact hfetch
  · rw [hx5]; rfl
  · rw [hx10]; exact hc

set_option maxHeartbeats 400000000 in
set_option maxRecDepth 20000 in
/-- `halt_invalid_hint` (0x78035e44): `syscall_halt(3)`. -/
theorem halt_invalid_hint_spec {G : MachineState → Prop} {n : Nat} {P : Prop} {L : List (Word × Nat)} (s : MachineState) (sp : Word)
    (f h0 h1 h2 h3 cnt b0 b1 b2 b3 b4 b5 b6 b7 : Word)
    (hpc : s.pc = 0x78035e44#64) (hcode : CodeAt F_78035e44.base F_78035e44.prog s)
    (hcodeHalt : CodeAt F_7801afc0.base F_7801afc0.prog s)
    (hcodeCpy : CodeAt F_7801b4d8.base F_7801b4d8.prog s)
    (hcodeSet : CodeAt F_7803f57c.base F_7803f57c.prog s)
    (hcodeSha : CodeAt F_780361e0.base F_780361e0.prog s)
    (hcw : CodeWithin Ro.layout.textLo Ro.layout.textHi s)
    (hro : RoImage Ro.layout s) (hheap : Run.HeapAt L s)
    (hsp : s.getReg .x2 = sp) (hstk : StackOk Ro.layout 0x470 sp)
    (hST : Region 0x78048830#64 [f, h0, h1, h2, h3, cnt, b0, b1, b2, b3, b4, b5, b6, b7, 0#64] s) :
    SafeN G n P s := by
  have hu := Unchanged.refl [(0x78048830#64, 15)] s
  have hlo := hstk.lo
  have hokST := hasherOk
  sym_exec stop [0x7801afc0] 10
  -- `syscall_halt(3)` never returns: its spec has no continuation, so it is applied by hand at
  -- the call, the code facts carried over the code map
  have hcE : ∀ {b : Word} {p : List (Option Instr)}, CodeAt b p s → CodeAt b p s_3 :=
    fun h i hi => (congrFun hcode _).trans (h i hi)
  exact syscall_halt_spec s_3 sp 3#64 f h0 h1 h2 h3 cnt b0 b1 b2 b3 b4 b5 b6 b7 hpc (hcE hcodeHalt)
    (hcE hcodeCpy) (hcE hcodeSet) (hcE hcodeSha) hcw hro hcarry hx2 hstk hx10 (by decide) hR0

end Cases.Zip2005
