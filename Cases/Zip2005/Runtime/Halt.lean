/-
  Cases.Zip2005.Runtime.Halt

  `syscall_halt(code)` (phase D2), against the hasher invariant of `Owned.env`: with a
  nonzero code it never accepts.

  It takes the hasher (`Option::take`: the invariant says `Some`, so the `unwrap` panic is
  unreachable), copies it into its frame, pads the last block (`0x80`, zeros, the bit
  length), compresses once or twice, commits the eight digest words and eight zero
  deferred-proof words, and halts with `code`. It never returns, so its interface has no
  postcondition to keep: what the proof tracks (`H`) is only what the remaining calls and
  the halt need — the code, its stack pointer, the exit code in `s0`, and the protected
  regions (`ProtOk`), which every store and call leaves alone. The position byte it reads
  back from the frame copy is not known (`memcpy`'s interface states no contents); it is a
  byte, and that bound is enough to keep the padding store and `memset` below `.rodata`.
-/

import MachineChecked.RiscV.Exec.Tactic
import MachineChecked.RiscV.Check.Image
import Cases.Zip2005.Runtime.SysWrite

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Cases.Zip2005.Runtime.Halt

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Frame MachineChecked.RiscV.Check
  MachineChecked.RiscV.Exec Cases.Zip2005.Image

noncomputable abbrev C : Word → Option Instr := Layout.image.codeAt

def fn : Fn := { base := F_7801afc0.base, prog := F_7801afc0.prog }

theorem code : CodeAt fn C :=
  codeAt_of_image (k := 23) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn] at h)

/-- `syscall_halt(code)`: commits the public values' digest and halts with `code`. It does
    not return, and with a nonzero code it does not accept. -/
def iface : Iface :=
  { entry := 0x7801afc0#64, depth := 0xe0 + 912, returns := false, nz := [.lin .x10 0] }

/-- The protected regions hold their contents. -/
def ProtOk (y : MachineState) : Prop :=
  ∀ a, Aligned a → Contract.env.InProt a → y.getMem a = Contract.env.init a

namespace ProtOk

variable {y : MachineState}

theorem setPC (h : ProtOk y) (v : Word) : ProtOk (y.setPC v) := fun a ha hp => by
  simpa using h a ha hp

theorem setReg (h : ProtOk y) (r : Reg) (v : Word) : ProtOk (y.setReg r v) := fun a ha hp => by
  simpa using h a ha hp

theorem setMem (h : ProtOk y) {w : Word} (hw : ¬ Contract.env.InProt w) (v : Word) :
    ProtOk (y.setMem w v) := fun a ha hp => by
  rw [getMem_setMem, if_neg (fun e => hw (by rw [← e]; exact hp))]
  exact h a ha hp

theorem setByte (h : ProtOk y) {w : Word} (hw : ¬ Contract.env.InProt (alignToDword w))
    (b : BitVec 8) : ProtOk (y.setByte w b) :=
  h.setMem hw _

end ProtOk

/-- Below the protected regions. -/
theorem not_prot_low {w : Word} (h : w.toNat + 8 ≤ 0x78000190) : ¬ Contract.env.InProt w := by
  intro hp
  have := Runtime.Entry.prot_range hp
  omega

/-- Away from the protected regions, by evaluation. -/
theorem not_prot_far {w : Word} (h : Runtime.Entry.nearProt w = false) :
    ¬ Contract.env.InProt w := by
  intro hp
  have := Runtime.Entry.prot_range hp
  simp only [Runtime.Entry.nearProt, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at h
  omega

/-- `ProtOk` through register writes, `pc` updates and stores, down to a hypothesis. Each
    store is below the protected regions (`bv_omega`) or at a literal away from them. -/
macro "xprot" : tactic => `(tactic|
  repeat (first | with_reducible assumption | with_reducible refine ProtOk.setPC ?_ _ |
    with_reducible refine ProtOk.setReg ?_ _ _ |
    (with_reducible refine ProtOk.setMem ?_ (not_prot_low ?_) _; rotate_left; bv_omega) |
    (with_reducible refine ProtOk.setMem ?_ ?_ _; rotate_left; exact not_prot_far (by decide))))

/-- A byte store below the protected regions. -/
theorem not_prot_byte {w : Word} (h : w.toNat + 8 ≤ 0x78000190) :
    ¬ Contract.env.InProt (alignToDword w) :=
  not_prot_low (by rw [alignToDword_toNat]; omega)

/-- After `syscall_halt`'s prologue: the code, its stack pointer `sp`, the exit code `e` in
    `s0`, and the protected regions. -/
structure H (sp e : Word) (y : MachineState) : Prop where
  code : y.code = C
  sp : y.getReg .x2 = sp
  e : y.getReg .x8 = e
  prot : ProtOk y

theorem H.setPC {sp e : Word} {y : MachineState} (h : H sp e y) (v : Word) :
    H sp e (y.setPC v) :=
  ⟨by simp [h.code], by simp [h.sp], by simp [h.e], h.prot.setPC v⟩

theorem H.setReg {sp e : Word} {y : MachineState} (h : H sp e y) {r : Reg} (h2 : r ≠ .x2)
    (h8 : r ≠ .x8) (v : Word) : H sp e (y.setReg r v) :=
  ⟨by simp [h.code], by rw [MachineState.getReg_setReg_ne _ _ _ _ h2]; exact h.sp,
    by rw [MachineState.getReg_setReg_ne _ _ _ _ h8]; exact h.e, h.prot.setReg r v⟩

theorem H.setMem {sp e : Word} {y : MachineState} (h : H sp e y) {w : Word}
    (hw : w.toNat + 8 ≤ 0x78000190) (v : Word) : H sp e (y.setMem w v) :=
  ⟨by simp [h.code], by rw [getReg_setMem]; exact h.sp, by rw [getReg_setMem]; exact h.e,
    h.prot.setMem (not_prot_low hw) v⟩

theorem H.setByte {sp e : Word} {y : MachineState} (h : H sp e y) {w : Word}
    (hw : w.toNat + 8 ≤ 0x78000190) (b : BitVec 8) : H sp e (y.setByte w b) :=
  h.setMem (by rw [alignToDword_toNat]; omega) _

/-- `H` through register writes, `pc` updates and stores below the protected regions, down
    to a hypothesis; each store leaves its address bound as a goal. -/
macro "xh" : tactic => `(tactic|
  repeat (first | with_reducible assumption | with_reducible refine H.setPC ?_ _ |
    with_reducible refine H.setReg ?_ (by decide) (by decide) _ |
    with_reducible refine H.setMem ?_ ?_ _ | with_reducible refine H.setByte ?_ ?_ _))

/-- A callee's precondition, from `H`, for a callee with only footprint premises. -/
theorem H.pre {sp e : Word} {y : MachineState} {g : Iface} (h : H sp e y)
    (hal : Aligned sp) (hd : g.depth ≤ sp.toNat) (ht : sp.toNat ≤ 0x78000000)
    (hnz : g.nz = []) (hvals : g.vals = []) (hcells : g.cells = []) (hstrs : g.strs = [])
    (hpre : g.pre = [])
    (hfoot : ∀ it ∈ g.foot, ∀ a, Aligned a → it.Hits (regsOf y) a →
      ¬ InWin sp g.depth a ∧ a.toNat + 8 ≤ 0x78000190) : Pre Contract.env C g y := by
  refine ⟨h.code, by rw [h.sp]; exact hd, by rw [h.sp]; exact ht, by rw [h.sp]; exact hal,
    h.prot, fun it hit a ha hh => ?_, by simp [hnz], by simp [hvals], by simp [hcells], trivial,
    StrsPre.trivial rfl hstrs, by simp [hpre]⟩
  have := hfoot it hit a ha hh
  exact ⟨by rw [h.sp]; exact this.1, not_prot_low this.2,
    fun ⟨_, hR, _⟩ => by simp [Contract.env] at hR⟩

/-- A callee returns with `H`. -/
theorem H.post {sp e : Word} {y t : MachineState} {g : Iface} (h : H sp e y)
    (hpre : Pre Contract.env C g y) (hpost : Post Contract.env g y t) : H sp e t :=
  ⟨hpost.2.2.2.2.1.trans h.code, (hpost.2.2.1 .x2 (by decide)).trans h.sp,
    (hpost.2.2.1 .x8 (by decide)).trans h.e,
    fun _ ha hp => Post.prot_init Contract.env_wf hpre hpost ha hp⟩

/-- A commit `ecall`: the run goes on with the code, and every register but `t0`. -/
theorem step_commit {G : MachineState → Prop} {P : Prop} {n : Nat} {y : MachineState}
    (hcode : y.code = C) (hf : y.code y.pc = some .ECALL)
    (h5 : y.getReg .x5 = Sp1.COMMIT ∨ y.getReg .x5 = Sp1.COMMIT_DEFERRED_PROOFS)
    (k : ∀ z, z.code = C → z.pc = y.pc + 4 → z.getReg .x8 = y.getReg .x8 → SafeN G n P z) :
    SafeN G n P y :=
  safe_ecall (by rcases h5 with h | h <;> rw [h] <;> decide)
    (fun z hs => sys_commit hf h5 hs)
    (fun z hz => k z (hz.code.trans hcode) hz.pc (hz.regs .x8 (by decide)))

/-- From `0x7801b110` (the digest computed): sixteen commits, then the halt with exit code
    `e`, which is nonzero, so the run does not accept. -/
theorem tail {G : MachineState → Prop} {P : Prop} {n : Nat} {e : Word} (he0 : e ≠ 0)
    {y : MachineState} (hcode : y.code = C) (hpc : y.pc = 0x7801b110#64)
    (he : y.getReg .x8 = e) : SafeN G n P y := by
  rw [← setPC_self hpc]
  iterate 16 (
    xrun code
    refine step_commit ?_ ?_ ?_ (fun z hzc hzpc hz8 => ?_)
    · (try simp only [MachineState.code_setReg, MachineState.code_setPC]); assumption
    · exact fetchLit code (by (try simp only [MachineState.code_setReg, MachineState.code_setPC]); assumption) (pc_setPC _ _) rfl (by decide)
    · xregs; first | exact Or.inl rfl | exact Or.inr rfl
    replace he : z.getReg .x8 = e := hz8.trans (by xregs; exact he)
    simp only [pc_setPC, BitVec.reduceAdd] at hzpc
    rw [← setPC_self hzpc])
  xrun code
  refine safe_halt ?_ ?_ ?_
  · exact fetchLit code (by (try simp only [MachineState.code_setReg, MachineState.code_setPC]); assumption) (pc_setPC _ _) rfl (by decide)
  · xregs
  · xregs
    rw [he]
    exact he0

/-- Bounds on `syscall_halt`'s stack pointer, from its precondition. -/
structure SpOk (sp : Word) : Prop where
  al : Aligned sp
  lo : 912 ≤ sp.toNat
  hi : sp.toNat + 0xe0 ≤ 0x78000000

/-- `compress256` on the frame's state copy at `sp + 8`. -/
theorem call_compress {G : MachineState → Prop} (hG : ∀ x, G x → Owned.env.Cfi x) {P : Prop}
    {n : Nat} {sp e : Word} (hs : SpOk sp) {y : MachineState} (h : H sp e y)
    (hpc : y.pc = 0x780361e0#64) (h10 : y.getReg .x10 = sp + 8#64)
    (k : ∀ t, H sp e t → t.pc = y.getReg .x1 &&& ~~~1#64 → SafeN G n P t) : SafeN G n P y := by
  have hpre : Pre Contract.env C Contract.A_780361e0.iface y := by
    refine h.pre hs.al (by simp [Contract.A_780361e0.iface]; exact hs.lo) (by have := hs.hi; omega)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) ?_
    intro it hit a _ hh
    simp only [Contract.A_780361e0.iface, List.mem_singleton] at hit
    subst hit
    have hh : Hits (sp + 8#64) 29 a := by simpa [Item.Hits, AVal.eval, Len.eval, regsOf, h10] using hh
    have := hs.hi
    have := sp.isLt
    unfold Hits at hh
    unfold InWin Hits
    simp only [Contract.A_780361e0.iface]
    constructor
    · rcases hh with hh | ⟨_, hh⟩ <;> bv_omega
    · rcases hh with hh | ⟨_, hh⟩ <;> bv_omega
  exact SysWrite.compress_holds n G (SysWrite.cfi_plain hG) P y hpc hpre
    (fun t ht => k t (h.post hpre ht) ht.2.1)

/-- `memcpy` of the hasher into the frame at `sp + 8`, `0x70` bytes. -/
theorem call_memcpy {G : MachineState → Prop} (hG : ∀ x, G x → Owned.env.Cfi x) {P : Prop}
    {n : Nat} {sp e : Word} (hs : SpOk sp) {y : MachineState} (h : H sp e y)
    (hpc : y.pc = 0x7801b4d8#64) (h10 : y.getReg .x10 = sp + 8#64)
    (h12 : y.getReg .x12 = 0x70#64)
    (k : ∀ t, H sp e t → t.pc = y.getReg .x1 &&& ~~~1#64 → SafeN G n P t) : SafeN G n P y := by
  have hpre : Pre Contract.env C Memcpy.iface y := by
    refine h.pre hs.al (by simp [Memcpy.iface]) (by have := hs.hi; omega) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) ?_
    intro it hit a _ hh
    simp only [Memcpy.iface, List.mem_singleton] at hit
    subst hit
    have hh : Hits (sp + 8#64) 0x70 a := by
      simpa [Item.Hits, AVal.eval, Len.eval, regsOf, h10, h12] using hh
    have := hs.hi
    have := sp.isLt
    refine ⟨by simp [InWin, Hits, Memcpy.iface], ?_⟩
    unfold Hits at hh
    rcases hh with hh | ⟨_, hh⟩ <;> bv_omega
  exact Runtime.Memcpy.holds Contract.env Contract.env_ok rfl (by decide) n G (SysWrite.cfi_plain hG)
    P y hpc hpre
    (fun t ht => k t (h.post hpre ht) ht.2.1)

/-- `memset` of the rest of the last block: from `sp + 0x31 + b`, `b ^^^ 63` bytes, `b < 256`. -/
theorem call_memset {G : MachineState → Prop} (hG : ∀ x, G x → Owned.env.Cfi x) {P : Prop}
    {n : Nat} {sp e : Word} (hs : SpOk sp) {y : MachineState} (h : H sp e y)
    (hpc : y.pc = 0x7803f57c#64) {b : Word} (hb : b.toNat < 256)
    (h10 : y.getReg .x10 = sp + 0x30#64 + b + 1#64) (h12 : y.getReg .x12 = b ^^^ 0x3f#64)
    (k : ∀ t, H sp e t → t.pc = y.getReg .x1 &&& ~~~1#64 → SafeN G n P t) : SafeN G n P y := by
  have hx : (b ^^^ 0x3f#64).toNat < 256 := by
    rw [BitVec.toNat_xor]
    exact Nat.xor_lt_two_pow (n := 8) hb (by decide)
  have hpre : Pre Contract.env C Memset.iface y := by
    refine h.pre hs.al (by simp [Memset.iface]) (by have := hs.hi; omega) (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) ?_
    intro it hit a _ hh
    simp only [Memset.iface, List.mem_singleton] at hit
    subst hit
    have hh : Hits (sp + 0x30#64 + b + 1#64) (b ^^^ 0x3f#64).toNat a := by
      simpa [Item.Hits, AVal.eval, Len.eval, regsOf, h10, h12] using hh
    have := hs.hi
    have := sp.isLt
    refine ⟨by simp [InWin, Hits, Memset.iface], ?_⟩
    unfold Hits at hh
    rcases hh with hh | ⟨_, hh⟩ <;> bv_omega
  exact Runtime.Memset.holds Contract.env Contract.env_ok n G (SysWrite.cfi_plain hG) P y hpc hpre
    (fun t ht => k t (h.post hpre ht) ht.2.1)

/-- At `0x7801b108`: the last block's compression, then the commits and the halt. -/
theorem at_b108 {G : MachineState → Prop} (hG : ∀ x, G x → Owned.env.Cfi x) {P : Prop}
    {n : Nat} {sp e : Word} (he0 : e ≠ 0) (hs : SpOk sp) {y : MachineState} (h : H sp e y)
    (hpc : y.pc = 0x7801b108#64) (h10 : y.getReg .x10 = sp + 8#64) : SafeN G n P y := by
  have hcode := h.code
  rw [← setPC_self hpc]
  iterate 2 xstep code
  xa
  refine call_compress (e := e) hG hs (by xh) rfl (by xregs; exact h10) (fun t ht htpc => ?_)
  exact tail he0 ht.code (by rw [htpc]; xregs; decide) ht.e

/-- At `0x7801b0f8`: the length fits in the last block. -/
theorem at_b0f8 {G : MachineState → Prop} (hG : ∀ x, G x → Owned.env.Cfi x) {P : Prop}
    {n : Nat} {sp e : Word} (he0 : e ≠ 0) (hs : SpOk sp) {y : MachineState} (h : H sp e y)
    (hpc : y.pc = 0x7801b0f8#64) : SafeN G n P y := by
  have hcode := h.code
  rw [← setPC_self hpc]
  iterate 4 xstep code
  simp only [h.sp]
  xa
  have := hs.hi
  exact at_b108 hG he0 hs (by xh <;> bv_omega) rfl (by xregs)

/-- At `0x7801b0b4`: the length needs a block of its own. -/
theorem at_b0b4 {G : MachineState → Prop} (hG : ∀ x, G x → Owned.env.Cfi x) {P : Prop}
    {n : Nat} {sp e : Word} (he0 : e ≠ 0) (hs : SpOk sp) {y : MachineState} (h : H sp e y)
    (hpc : y.pc = 0x7801b0b4#64) : SafeN G n P y := by
  have hcode := h.code
  rw [← setPC_self hpc]
  iterate 5 xstep code
  simp only [h.sp]
  xa
  refine call_compress (e := e) hG hs (by xh) rfl (by xregs) (fun t ht htpc => ?_)
  have htcode := ht.code
  rw [← setPC_self (show t.pc = 0x7801b0c8#64 by rw [htpc]; xregs; decide)]
  iterate 12 xstep code
  simp only [ht.sp]
  xa
  have := hs.hi
  exact at_b108 hG he0 hs (by xh <;> bv_omega) rfl (by xregs)

/-- At `0x7801b0a8`, after the padding: does the length fit in this block? -/
theorem at_b0a8 {G : MachineState → Prop} (hG : ∀ x, G x → Owned.env.Cfi x) {P : Prop}
    {n : Nat} {sp e : Word} (he0 : e ≠ 0) (hs : SpOk sp) {y : MachineState} (h : H sp e y)
    (hpc : y.pc = 0x7801b0a8#64) : SafeN G n P y := by
  have hcode := h.code
  rw [← setPC_self hpc]
  iterate 3 xstep code
  · exact at_b0f8 hG he0 hs (by xh) rfl
  · exact at_b0b4 hG he0 hs (by xh) rfl

/-- At `0x7801b008`, the hasher copied into the frame: the final block's padding. -/
theorem at_b008 {G : MachineState → Prop} (hG : ∀ x, G x → Owned.env.Cfi x) {P : Prop}
    {n : Nat} {sp e : Word} (he0 : e ≠ 0) (hs : SpOk sp) {y : MachineState} (h : H sp e y)
    (hpc : y.pc = 0x7801b008#64) : SafeN G n P y := by
  have hcode := h.code
  rw [← setPC_self hpc]
  iterate 3 xstep code
  simp only [h.sp]
  xa
  simp only [MachineState.getByte, MachineState.getMem_setReg, MachineState.getMem_setPC] at *
  have hb8 : (BitVec.zeroExtend 64 (extractByte (y.getMem (alignToDword
      (sp + 112#64))) (byteOffset (sp + 112#64)))).toNat
      < 256 := by simp; omega
  generalize BitVec.zeroExtend 64 (extractByte (y.getMem (alignToDword
      (sp + 112#64))) (byteOffset (sp + 112#64))) = b at *
  iterate 32 xstep code
  xa
  have := hs.hi
  have := hs.lo
  xstep code
  · -- the length needs no zero padding
    refine at_b0b4 hG he0 hs ?_ rfl
    xh
    all_goals (simp only [BitVec.toNat_add, BitVec.reduceToNat]; omega)
  · iterate 4 xstep code
    xa
    refine call_memset (e := e) hG hs ?_ rfl hb8 (by xregs; bv_omega) (by xregs)
      (fun t2 hH2 ht2pc => ?_)
    · xh
      all_goals (simp only [BitVec.toNat_add, BitVec.reduceToNat]; omega)
    exact at_b0a8 hG he0 hs hH2 (by rw [ht2pc]; xregs; decide)


/-- **`syscall_halt`**, under the hasher invariant: with a nonzero exit code it never
    accepts. It takes the hasher (`Some`, by the invariant), finishes the digest in its
    frame, commits it, and halts. -/
theorem holds : iface.Holds Owned.env C := by
  intro n G hG P s hpc hpre _
  replace hpc : s.pc = 0x7801afc0#64 := hpc
  have hcode := hpre.1
  have hd : 0xe0 + 912 ≤ (s.getReg .x2).toNat := hpre.2.1
  have ht : (s.getReg .x2).toNat ≤ 0x78000000 := hpre.2.2.1
  have htag : s.getMem 0x78048830#64 = 1#64 := ((Owned.inv_iff).mp hpre.2.2.2.2.2.2.2.2.2.1).1
  have he0 : s.getReg .x10 ≠ 0 := by
    have := hpre.2.2.2.2.2.2.1 _ (List.mem_singleton_self _)
    simpa [AVal.eval, regsOf] using this
  rw [← setPC_self hpc]
  iterate 9 xstep code
  xa
  simp only [MachineState.getMem_setReg, MachineState.getMem_setPC]
  repeat (rw [getMem_setMem, if_neg (SysWrite.frame_ne ht (by simp <;> omega) (by decide))])
  simp only [MachineState.getMem_setReg, htag]
  iterate 3 xstep code
  · simp at hb
  xa
  iterate 6 xstep code
  xa
  generalize hsp : s.getReg .x2 = sp0 at *
  have hs : SpOk (sp0 + 0xffffffffffffff20#64) := by
    have hal : Aligned sp0 := hsp ▸ hpre.2.2.2.1
    rw [aligned_iff] at hal
    refine ⟨(aligned_iff _).mpr (by bv_omega), by bv_omega, by bv_omega⟩
  have hp0 : ProtOk s := fun a ha hp => hpre.2.2.2.2.1 a ha hp
  -- `memcpy` the hasher into the frame
  refine call_memcpy (e := s.getReg .x10) hG hs ⟨by simp [hcode], by xregs, by xregs, ?_⟩ rfl
    (by xregs; bv_omega) (by xregs) (fun t1 hH1 ht1pc => ?_)
  · xprot
  exact at_b008 hG he0 hs hH1 (by rw [ht1pc]; xregs; decide)

end Cases.Zip2005.Runtime.Halt
