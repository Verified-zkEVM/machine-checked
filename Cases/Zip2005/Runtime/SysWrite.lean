/-
  Cases.Zip2005.Runtime.SysWrite

  `syscall_write(fd, buf, len)` (phase D2), against the hasher invariant of `Owned.env`.

  It writes `[buf, buf + len)` to `fd` (an `ecall` that changes no memory). On the
  public-values descriptor (13) it also absorbs the bytes into `PUBLIC_VALUES_HASHER`: if
  they fit, appended to the buffer at the position; otherwise the buffer is filled and
  compressed, whole 64-byte blocks are compressed straight from `buf`, and the rest starts a
  new buffer. The tag must be `Some` (else it panics) and the position below 64 (else the
  append leaves the hasher, into `std::alloc::HOOK`): the invariant gives both, and every
  path stores a new position below 64.

  The proof: `Mid` is what holds between the prologue and the epilogue (frame slots, the
  untouched callee-saved registers, memory outside the footprint, the invariant). It
  survives register writes, the counter and position stores, and the calls (`memcpy` into
  the buffer, `compress256` on the state, both with their plain interfaces). The executor
  runs the straight-line pieces between them.
-/

import AsmVerif.RiscV.Exec.Tactic
import AsmVerif.RiscV.Check.Image
import Cases.Zip2005.Owned

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Cases.Zip2005.Runtime.SysWrite

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Frame AsmVerif.RiscV.Check
  AsmVerif.RiscV.Exec Cases.Zip2005.Image

noncomputable abbrev C : Word → Option Instr := Layout.image.codeAt

def fn : Fn := { base := F_7801b3b0.base, prog := F_7801b3b0.prog }

theorem code : CodeAt fn C :=
  codeAt_of_image (k := 24) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [fn] at h)

/-- `syscall_write(fd, buf, len)`: writes to `fd`; on the public-values descriptor, also
    absorbs the bytes into the hasher (its state, counter and buffer). -/
def iface : Iface :=
  { entry := 0x7801b3b0#64, depth := 0x30 + 912, foot := [⟨.const 0x78048838#64, .n 0x68⟩] }

/-- Fold literal offsets on a symbolic base. -/
macro "xa" : tactic => `(tactic| (
  try simp only [BitVec.add_assoc, BitVec.add_zero, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceNeg,
    signExtend12, BitVec.reduceSignExtend, BitVec.reduceZeroExtend, BitVec.reduceHShiftLeft,
    BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceNot, BitVec.reduceToNat,
    BitVec.reduceUShiftRight, BitVec.reduceHShiftRight] at *))

/-- The callee-saved registers `syscall_write` does not save. -/
def untouched : List Reg := [.x3, .x4, .x21, .x22, .x23, .x24, .x25, .x26, .x27]

/-- Inside `syscall_write`, after its prologue: its frame holds the saved registers, the
    rest of memory is the entry's outside what it may write, and the hasher is fine. -/
structure Mid (s0 y : MachineState) : Prop where
  code0 : s0.code = C
  code : y.code = C
  sp : y.getReg .x2 = s0.getReg .x2 + 0xffffffffffffffd0#64
  regs : ∀ r ∈ untouched, y.getReg r = s0.getReg r
  fra : y.getMem (s0.getReg .x2 + 0xfffffffffffffff8#64) = s0.getReg .x1
  fs0 : y.getMem (s0.getReg .x2 + 0xfffffffffffffff0#64) = s0.getReg .x8
  fs1 : y.getMem (s0.getReg .x2 + 0xffffffffffffffe8#64) = s0.getReg .x9
  fs2 : y.getMem (s0.getReg .x2 + 0xffffffffffffffe0#64) = s0.getReg .x18
  fs3 : y.getMem (s0.getReg .x2 + 0xffffffffffffffd8#64) = s0.getReg .x19
  fs4 : y.getMem (s0.getReg .x2 + 0xffffffffffffffd0#64) = s0.getReg .x20
  mem : ∀ a, Aligned a → ¬ Written iface (regsOf s0) a → ¬ Owned.env.InOwn a →
    y.getMem a = s0.getMem a
  ok : Owned.HasherOk y.getMem

/-- The frame lies below the stack top, so below every static. -/
theorem frame_ne {sp a c : Word} (hsp : sp.toNat ≤ 0x78000000) (hc : 2 ^ 64 - sp.toNat ≤ c.toNat)
    (ha : 0x78000000 ≤ a.toNat) : a ≠ sp + c := by
  intro h
  have := sp.isLt
  have := c.isLt
  subst h
  rw [BitVec.toNat_add] at ha
  omega

/-- The written window of `syscall_write`. -/
theorem inWin_frame {sp a c : Word} (hc : 2 ^ 64 - 960 ≤ c.toNat)
    (ha : a = sp + c) : InWin sp iface.depth a := by
  subst ha
  have := sp.isLt
  have := c.isLt
  unfold InWin Hits iface
  left
  simp only
  bv_omega

/-- A key outside the window (`hw`) is none of the frame slots. -/
macro "xnf" hw:term:max : tactic => `(tactic|
  repeat (rw [getMem_setMem, if_neg (fun h => $hw (inWin_frame (by decide) h))]))

/-- Replacing the low byte of a doubleword: the low byte is the new one. -/
theorem low_byte (w : Word) (b : BitVec 8) :
    (w &&& ~~~0xff#64 ||| BitVec.zeroExtend 64 b) &&& 0xff#64 = BitVec.zeroExtend 64 b := by
  have hff : ∀ i, (0xff#64).getLsbD i = decide (i < 8) := by
    intro i
    rw [show (0xff#64) = BitVec.ofNat 64 (2 ^ 8 - 1) from rfl, BitVec.getLsbD_ofNat,
      Nat.testBit_two_pow_sub_one]
    by_cases h : i < 8 <;> simp [h] <;> omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, BitVec.getLsbD_setWidth,
    BitVec.truncate_eq_setWidth, hff]
  by_cases h : i < 8
  · simp [h, hi]
  · simp [h, BitVec.getLsbD_of_ge b i (by omega)]

/-- The low byte of a doubleword, as `lbu` reads it. -/
theorem extractByte_zero (w : Word) : (extractByte w 0).toNat = (w &&& 0xff#64).toNat := by
  simp only [extractByte, Nat.zero_mul, BitVec.ushiftRight_zero, BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_and]
  rw [show (0xff#64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

namespace Mid

variable {s0 y : MachineState}

theorem setPC (h : Mid s0 y) (v : Word) : Mid s0 (y.setPC v) := by
  refine ⟨h.code0, by simp [h.code], by simp [h.sp], fun r hr => by simp [h.regs r hr],
    by simp [h.fra], by simp [h.fs0], by simp [h.fs1], by simp [h.fs2], by simp [h.fs3],
    by simp [h.fs4], fun a ha hnw ho => by simp [h.mem a ha hnw ho], ?_⟩
  simpa [Owned.HasherOk] using h.ok

theorem setReg (h : Mid s0 y) {r : Reg} (hr : r ∉ untouched) (h2 : r ≠ .x2) (v : Word) :
    Mid s0 (y.setReg r v) := by
  refine ⟨h.code0, by simp [h.code], ?_, fun r' hr' => ?_,
    by simp [h.fra], by simp [h.fs0], by simp [h.fs1], by simp [h.fs2], by simp [h.fs3],
    by simp [h.fs4], fun a ha hnw ho => by simp [h.mem a ha hnw ho], ?_⟩
  · rw [MachineState.getReg_setReg_ne _ _ _ _ h2]; exact h.sp
  · have : r ≠ r' := fun e => hr (e ▸ hr')
    rw [MachineState.getReg_setReg_ne _ _ _ _ this]; exact h.regs r' hr'
  · simpa [Owned.HasherOk] using h.ok

/-- The hasher's state, counter and buffer: `syscall_write`'s footprint. -/
def InHasher (a : Word) : Prop := 0x78048838 ≤ a.toNat ∧ a.toNat < 0x780488a0

/-- After a call whose writes stay below the frame or in the hasher, `Mid` still holds. -/
theorem post {g : Iface} {x t : MachineState} (h : Mid s0 x)
    (hal : Aligned (s0.getReg .x2)) (hd : 960 ≤ (s0.getReg .x2).toNat)
    (ht : (s0.getReg .x2).toNat ≤ 0x78000000) (hdep : g.depth ≤ 912)
    (hW : ∀ a, Aligned a → Written g (regsOf x) a →
      InWin (x.getReg .x2) g.depth a ∨ InHasher a)
    (hpost : Post Contract.env g x t) : Mid s0 t := by
  obtain ⟨_, _, hsaved, hun, hcode, _⟩ := hpost
  have hno : ∀ a, ¬ Contract.env.InOwn a := fun a ⟨_, hR, _⟩ => by simp [Contract.env] at hR
  have hxsp := h.sp
  -- A key at or above the callee's stack pointer and below the stack top is kept.
  have keep : ∀ a, Aligned a → (s0.getReg .x2).toNat - 0x30 ≤ a.toNat →
      a.toNat < 0x78000000 → t.getMem a = x.getMem a := by
    intro a ha hlo hhi
    refine hun a ha (fun hw => ?_) (hno a) (StrHit.trivial rfl)
    rcases hW a ha hw with hw | hw
    · rw [hxsp] at hw
      unfold InWin Hits at hw
      have := (s0.getReg .x2).isLt
      rcases hw with hw | ⟨_, hw⟩ <;> bv_omega
    · unfold InHasher at hw; omega
  have hslot : ∀ c : Word, 2 ^ 64 - 0x30 ≤ c.toNat → c.toNat % 8 = 0 →
      t.getMem (s0.getReg .x2 + c) = x.getMem (s0.getReg .x2 + c) := by
    intro c hc hc8
    have := (s0.getReg .x2).isLt
    have := c.isLt
    rw [aligned_iff] at hal
    refine keep _ ((aligned_iff _).mpr ?_) ?_ ?_ <;> rw [BitVec.toNat_add] <;> omega
  refine ⟨h.code0, hcode.trans h.code, (hsaved .x2 (by decide)).trans h.sp,
    fun r hr => (hsaved r (by simp [untouched] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> decide)).trans (h.regs r hr),
    (hslot _ (by decide) (by decide)).trans h.fra, (hslot _ (by decide) (by decide)).trans h.fs0,
    (hslot _ (by decide) (by decide)).trans h.fs1, (hslot _ (by decide) (by decide)).trans h.fs2,
    (hslot _ (by decide) (by decide)).trans h.fs3, (hslot _ (by decide) (by decide)).trans h.fs4,
    fun a ha hnw ho => ?_, ?_⟩
  · refine Eq.trans (hun a ha (fun hw => hnw ?_) (hno a) (StrHit.trivial rfl)) (h.mem a ha hnw ho)
    rcases hW a ha hw with hw | hw
    · left
      rw [hxsp] at hw
      have he : s0.getReg .x2 + 0xffffffffffffffd0#64 = s0.getReg .x2 - BitVec.ofNat 64 48 := by
        bv_omega
      rw [he] at hw
      exact inWin_callee hal (by decide) (by simp [iface]; omega) ha hw
    · right
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      unfold InHasher at hw
      simp only [Item.Hits, AVal.eval, Len.eval, Hits]
      left; bv_omega
  · have hk : ∀ a, (a = Owned.tagKey ∨ a = Owned.posKey) → t.getMem a = x.getMem a := by
      rintro a (rfl | rfl) <;>
      · refine hun _ (by unfold Aligned; decide) (fun hw => ?_) (hno _) (StrHit.trivial rfl)
        rcases hW _ (by unfold Aligned; decide) hw with hw | hw
        · rw [hxsp] at hw
          unfold InWin Hits at hw
          have := (s0.getReg .x2).isLt
          simp only [Owned.tagKey, Owned.posKey] at hw
          rcases hw with hw | ⟨_, hw⟩ <;> bv_omega
        · unfold InHasher at hw; simp [Owned.tagKey, Owned.posKey] at hw
    have := h.ok
    simp only [Owned.HasherOk] at this ⊢
    rw [hk _ (Or.inl rfl), hk _ (Or.inr rfl)]
    exact this

/-- Setting the buffer position below 64 keeps `Mid`. -/
theorem setPos (h : Mid s0 y) (hd : 960 ≤ (s0.getReg .x2).toNat)
    (ht : (s0.getReg .x2).toNat ≤ 0x78000000) {b : BitVec 8} (hb : b.toNat < 64) :
    Mid s0 (y.setByte 0x780488a0#64 b) := by
  have hne : ∀ c : Word, 2 ^ 64 - 0x30 ≤ c.toNat → s0.getReg .x2 + c ≠ 0x780488a0#64 := by
    intro c hc he
    have := (frame_ne (a := 0x780488a0#64) ht (by omega) (by decide)) he.symm
    exact this
  have hset : ∀ a, (y.setByte 0x780488a0#64 b).getMem a =
      if a = 0x780488a0#64 then replaceByte (y.getMem 0x780488a0#64) 0 b else y.getMem a := by
    intro a
    simp only [MachineState.setByte, alignToDword, byteOffset, BitVec.reduceAnd, BitVec.reduceNot,
      BitVec.reduceToNat]
    exact getMem_setMem
  refine ⟨h.code0, by simp [MachineState.setByte, h.code], ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, fun a ha hnw ho => ?_, ?_⟩
  · simp only [MachineState.setByte, getReg_setMem]; exact h.sp
  · simp only [MachineState.setByte, getReg_setMem]; exact h.regs r hr
  · rw [hset, if_neg (hne _ (by decide))]; exact h.fra
  · rw [hset, if_neg (hne _ (by decide))]; exact h.fs0
  · rw [hset, if_neg (hne _ (by decide))]; exact h.fs1
  · rw [hset, if_neg (hne _ (by decide))]; exact h.fs2
  · rw [hset, if_neg (hne _ (by decide))]; exact h.fs3
  · rw [hset, if_neg (hne _ (by decide))]; exact h.fs4
  · rw [hset, if_neg (fun he => ho (by rw [he]; exact Owned.pos_own))]
    exact h.mem a ha hnw ho
  · have := h.ok
    simp only [Owned.HasherOk, Owned.tagKey, Owned.posKey] at this ⊢
    rw [hset, hset, if_neg (by decide), if_pos rfl]
    refine ⟨this.1, ?_⟩
    simp only [replaceByte, Nat.zero_mul, BitVec.shiftLeft_zero]
    have : (y.getMem 0x780488a0#64 &&& ~~~0xff#64 ||| BitVec.zeroExtend 64 b) &&& 0xff#64 =
        BitVec.zeroExtend 64 b := by
      exact low_byte _ _
    rw [this, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
    exact hb

/-- A store to the hasher's block counter keeps `Mid`: it is in the footprint. -/
theorem setCounter (h : Mid s0 y) (hd : 960 ≤ (s0.getReg .x2).toNat)
    (ht : (s0.getReg .x2).toNat ≤ 0x78000000) (v : Word) :
    Mid s0 (y.setMem 0x78048858#64 v) := by
  have hne : ∀ c : Word, 2 ^ 64 - 0x30 ≤ c.toNat → s0.getReg .x2 + c ≠ 0x78048858#64 :=
    fun c hc he => (frame_ne (a := 0x78048858#64) ht (by omega) (by decide)) he.symm
  refine ⟨h.code0, by simp [h.code], by rw [getReg_setMem]; exact h.sp,
    fun r hr => by rw [getReg_setMem]; exact h.regs r hr, ?_, ?_, ?_, ?_, ?_, ?_,
    fun a ha hnw ho => ?_, ?_⟩
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fra
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fs0
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fs1
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fs2
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fs3
  · rw [getMem_setMem, if_neg (hne _ (by decide))]; exact h.fs4
  · rw [getMem_setMem, if_neg]
    · exact h.mem a ha hnw ho
    · rintro rfl
      exact hnw (Or.inr ⟨_, List.mem_singleton_self _, by
        simp only [Item.Hits, AVal.eval, Len.eval, Hits]; left; decide⟩)
  · have := h.ok
    simp only [Owned.HasherOk, Owned.tagKey, Owned.posKey] at this ⊢
    rw [getMem_setMem, getMem_setMem, if_neg (by decide), if_neg (by decide)]
    exact this

end Mid

/-! ## Calls -/

section Calls

variable {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 x : MachineState}

theorem cfi_plain (hG : ∀ x, G x → Owned.env.Cfi x) : ∀ x, G x → Contract.env.Cfi x :=
  fun x hx => by simpa [Env.Cfi, Owned.env] using hG x hx

/-- The protected keys still hold their contents inside `syscall_write`. -/
theorem prot_mid (hpre : Pre Owned.env C iface s0) (h : Mid s0 x) {a : Word} (ha : Aligned a)
    (hp : Contract.env.InProt a) : x.getMem a = Contract.env.init a := by
  have hp' : Owned.env.InProt a := hp
  rw [h.mem a ha (Pre.not_written_prot Owned.env_wf hpre ha hp')
    (not_own_of_prot Owned.env_wf hp')]
  exact hpre.2.2.2.2.1 a ha hp'

/-- A range inside the hasher avoids the protected regions. -/
theorem hasher_not_prot {b : Word} {l : Nat} {a : Word} (hb : 0x78048838 ≤ b.toNat)
    (hbl : b.toNat + l ≤ 0x780488a0) (hh : Hits b l a) : ¬ Contract.env.InProt a := by
  intro hp
  have hr := Runtime.Entry.prot_range hp
  unfold Hits at hh
  have := a.isLt
  have := b.isLt
  rcases hh with hh | ⟨_, hh⟩ <;> bv_omega

/-- `memcpy` into the hasher's buffer, from offset `o`, `l` bytes, `o + l ≤ 64`. -/
theorem call_memcpy (hpre : Pre Owned.env C iface s0) (hG : ∀ x, G x → Owned.env.Cfi x)
    (h : Mid s0 x) (hpc : x.pc = 0x7801b4d8#64) {o l : Nat} (hol : o + l ≤ 64)
    (h10 : x.getReg .x10 = 0x78048860#64 + BitVec.ofNat 64 o)
    (h12 : x.getReg .x12 = BitVec.ofNat 64 l)
    (hk : ∀ t, Mid s0 t → t.pc = x.getReg .x1 &&& ~~~1#64 →
      (∀ r ∈ savedRegs, t.getReg r = x.getReg r) → SafeN G n P t) : SafeN G n P x := by
  have hal : Aligned (s0.getReg .x2) := hpre.2.2.2.1
  have hd : 960 ≤ (s0.getReg .x2).toNat := hpre.2.1
  have ht : (s0.getReg .x2).toNat ≤ 0x78000000 := hpre.2.2.1
  have hb : (x.getReg .x10).toNat = 0x78048860 + o := by rw [h10]; bv_omega
  have hl : (x.getReg .x12).toNat = l := by rw [h12]; simp; omega
  have hfoot : ∀ a, Aligned a → Written Memcpy.iface (regsOf x) a →
      Hits (x.getReg .x10) l a := by
    rintro a _ (hw | ⟨it, hit, hh⟩)
    · simp [InWin, Hits, Memcpy.iface] at hw
    · simp only [Memcpy.iface, List.mem_singleton] at hit
      subst hit
      have hz : x.getReg .x10 + 0 = x.getReg .x10 := by bv_omega
      simpa [Item.Hits, AVal.eval, Len.eval, regsOf, hl, hz] using hh
  refine Runtime.Memcpy.holds Contract.env rfl (by decide) n G (cfi_plain hG) P x hpc
    ⟨h.code, Nat.zero_le _, ?_, ?_, fun a ha hp => prot_mid hpre h ha hp, ?_, by simp [Memcpy.iface],
      by simp [Memcpy.iface], by simp [Memcpy.iface], trivial, StrsPre.trivial rfl rfl⟩
    (fun t hp => hk t (Mid.post h hal hd ht (by simp [Memcpy.iface]) (fun a ha hw => Or.inr ?_) hp)
      hp.2.1 hp.2.2.1)
  · rw [h.sp]; have := (s0.getReg .x2).isLt; show _ ≤ 2013265920; bv_omega
  · rw [h.sp]; rw [aligned_iff] at hal ⊢; bv_omega
  · intro it hit a _ hh
    simp only [Memcpy.iface, List.mem_singleton] at hit
    subst hit
    have hz : x.getReg .x10 + 0 = x.getReg .x10 := by bv_omega
    simp only [Item.Hits, AVal.eval, Len.eval, regsOf, hl, hz] at hh
    refine ⟨by simp [InWin, Hits, Memcpy.iface], hasher_not_prot (by omega) (by omega) hh,
      fun ⟨_, hR, _⟩ => by simp [Contract.env] at hR⟩
  · have hh := hfoot a ha hw
    unfold Hits at hh
    rw [aligned_iff] at ha
    unfold Mid.InHasher
    have := a.isLt
    rcases hh with hh | ⟨_, hh⟩ <;> bv_omega

/-- `compress256`'s interface, from the checked table. -/
theorem compress_holds : Contract.A_780361e0.iface.Holds Contract.env C :=
  Contract.all _ (by simp [Contract.tbl])

/-- `compress256` on the hasher's state. -/
theorem call_compress (hpre : Pre Owned.env C iface s0) (hG : ∀ x, G x → Owned.env.Cfi x)
    (h : Mid s0 x) (hpc : x.pc = 0x780361e0#64) (h10 : x.getReg .x10 = 0x78048838#64)
    (hk : ∀ t, Mid s0 t → t.pc = x.getReg .x1 &&& ~~~1#64 →
      (∀ r ∈ savedRegs, t.getReg r = x.getReg r) → SafeN G n P t) : SafeN G n P x := by
  have hal : Aligned (s0.getReg .x2) := hpre.2.2.2.1
  have hd : 960 ≤ (s0.getReg .x2).toNat := hpre.2.1
  have ht : (s0.getReg .x2).toNat ≤ 0x78000000 := hpre.2.2.1
  have hfoot : ∀ a, Aligned a → Written Contract.A_780361e0.iface (regsOf x) a →
      InWin (x.getReg .x2) Contract.A_780361e0.iface.depth a ∨ Hits 0x78048838#64 29 a := by
    rintro a _ (hw | ⟨it, hit, hh⟩)
    · exact Or.inl hw
    · simp only [Contract.A_780361e0.iface, List.mem_singleton] at hit
      subst hit
      exact Or.inr (by simpa [Item.Hits, AVal.eval, Len.eval, regsOf, h10] using hh)
  refine compress_holds n G (cfi_plain hG) P x hpc
    ⟨h.code, ?_, ?_, ?_, fun a ha hp => prot_mid hpre h ha hp, ?_,
      by simp [Contract.A_780361e0.iface], by simp [Contract.A_780361e0.iface],
      by simp [Contract.A_780361e0.iface], trivial, StrsPre.trivial rfl rfl⟩
    (fun t hp => hk t (Mid.post h hal hd ht (by simp [Contract.A_780361e0.iface])
      (fun a ha hw => ?_) hp) hp.2.1 hp.2.2.1)
  · rw [h.sp]; simp only [Contract.A_780361e0.iface]; bv_omega
  · rw [h.sp]; have := (s0.getReg .x2).isLt; show _ ≤ 2013265920; bv_omega
  · rw [h.sp]; rw [aligned_iff] at hal ⊢; bv_omega
  · intro it hit a _ hh
    simp only [Contract.A_780361e0.iface, List.mem_singleton] at hit
    subst hit
    have hh : Hits 0x78048838#64 29 a := by
      simpa [Item.Hits, AVal.eval, Len.eval, regsOf, h10] using hh
    refine ⟨fun hw => ?_, hasher_not_prot (b := 0x78048838#64) (by decide) (by decide) hh,
      fun ⟨_, hR, _⟩ => by simp [Contract.env] at hR⟩
    rw [h.sp] at hw
    unfold InWin Hits at hw hh
    have := (s0.getReg .x2).isLt
    simp only [Contract.A_780361e0.iface] at hw
    rcases hw with hw | ⟨_, hw⟩ <;> rcases hh with hh | ⟨_, hh⟩ <;> bv_omega
  · rcases hfoot a ha hw with hw | hw
    · exact Or.inl hw
    · right
      unfold Hits at hw
      rw [aligned_iff] at ha
      unfold Mid.InHasher
      have := a.isLt
      rcases hw with hw | ⟨_, hw⟩ <;> bv_omega

end Calls

/-- The epilogue at `0x7801b4a8`: restore and return. -/
theorem epilogue {G : MachineState → Prop} {P : Prop} {n : Nat} {s0 y : MachineState}
    (hk : ∀ t, Post Owned.env iface s0 t → SafeN G n P t) (hy : Mid s0 y)
    (hpc : y.pc = 0x7801b4a8#64) : SafeN G n P y := by
  have hcode := hy.code
  rw [← setPC_self hpc]
  iterate 8 xstep code
  xa
  simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, hy.sp]
  xa
  simp only [hy.fra, hy.fs0, hy.fs1, hy.fs2, hy.fs3, hy.fs4]
  apply hk
  refine ⟨rfl, ?_, fun r hr => ?_, fun a ha hnw ho _ => ?_, ?_, ?_, StrsPost.trivial rfl rfl⟩
  · simp only [pc_setPC, BitVec.reduceNot]
  · simp only [savedRegs, List.mem_cons, List.mem_nil_iff, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;> xregs <;> first | rfl | simp | (refine hy.regs _ ?_; simp [untouched])
  · simp only [MachineState.getMem_setReg, MachineState.getMem_setPC]
    exact hy.mem a ha hnw ho
  · simpa using hy.code.trans hy.code0.symm
  · rw [Owned.inv_iff]
    simp only [Owned.HasherOk, MachineState.getMem_setReg, MachineState.getMem_setPC]
    exact hy.ok

/-- `Mid` through register writes and `pc` updates, down to a hypothesis. -/
macro "xmid" : tactic => `(tactic|
  repeat (first | assumption | refine Mid.setPC ?_ _ |
    refine Mid.setReg ?_ (by decide) (by decide) _))

/-- The tail at `0x7801b4a4`: store the new buffer position (below 64), return. -/
theorem finish {G : MachineState → Prop} {P : Prop} {n : Nat}
    {s0 y : MachineState} (hpre : Pre Owned.env C iface s0)
    (hk : ∀ t, Post Owned.env iface s0 t → SafeN G n P t) (h : Mid s0 y)
    (hpc : y.pc = 0x7801b4a4#64) (h18 : y.getReg .x18 = 0x78048830#64)
    (h9 : (y.getReg .x9).toNat < 64) : SafeN G n P y := by
  have hcode := h.code
  rw [← setPC_self hpc]
  xstep code
  rw [h18] at *
  xa
  refine epilogue hk (Mid.setPC (Mid.setPos h hpre.2.1 hpre.2.2.1 ?_) _) rfl
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  omega

/-- The join at `0x7801b45c`: whole blocks into the state, the rest into the buffer. -/
theorem blocks {G : MachineState → Prop} (hG : ∀ x, G x → Owned.env.Cfi x) {P : Prop} {n : Nat}
    {s0 y : MachineState} (hpre : Pre Owned.env C iface s0)
    (hk : ∀ t, Post Owned.env iface s0 t → SafeN G n P t) (h : Mid s0 y)
    (hpc : y.pc = 0x7801b45c#64) (h18 : y.getReg .x18 = 0x78048830#64) : SafeN G n P y := by
  have hcode := h.code
  have hd : 960 ≤ (s0.getReg .x2).toNat := hpre.2.1
  have ht : (s0.getReg .x2).toNat ≤ 0x78000000 := hpre.2.2.1
  rw [← setPC_self hpc]
  iterate 6 xstep code
  xa
  generalize y.getReg .x8 = len at *
  -- The remainder into the buffer, then the new position.
  have rest : ∀ z : MachineState, Mid s0 z → z.pc = 0x7801b490#64 →
      z.getReg .x18 = 0x78048830#64 → z.getReg .x9 = len &&& 0x3f#64 → SafeN G n P z := by
    intro z hz hzpc hz18 hz9
    have hzcode := hz.code
    rw [← setPC_self hzpc]
    iterate 5 xstep code
    xa
    simp only [hz18, hz9]
    xa
    have hl : (len &&& 0x3f#64).toNat < 64 := by
      rw [BitVec.toNat_and, show (0x3f#64).toNat = 2 ^ 6 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]; omega
    refine call_memcpy (o := 0) (l := (len &&& 0x3f#64).toNat) hpre hG (by xmid) rfl (by omega)
      (by xregs; rfl) (by xregs; simp) (fun t ht' htpc hsv => ?_)
    refine finish hpre hk ht' (by rw [htpc]; xregs; decide) ?_ ?_
    · rw [hsv _ (by decide)]; xregs; exact hz18
    · rw [hsv _ (by decide)]; xregs; rw [hz9]; exact hl
  xstep code
  · -- no whole block
    exact rest _ (by xmid) rfl (by xregs; exact h18) (by xregs)
  · iterate 3 xstep code
    xa
    simp only [h18]
    xa
    iterate 3 xstep code
    xa
    refine call_compress hpre hG ?_ rfl (by xregs; rw [h18]; rfl) (fun t ht' htpc hsv => ?_)
    · xmid
      refine Mid.setCounter ?_ hd ht _
      xmid
    · refine rest t ht' (by rw [htpc]; xregs; decide) ?_ ?_
      · rw [hsv _ (by decide)]; xregs; exact h18
      · rw [hsv _ (by decide)]; xregs

theorem body {G : MachineState → Prop} (hG : ∀ x, G x → Owned.env.Cfi x) {P : Prop} {n : Nat}
    {s0 y : MachineState} (hpre : Pre Owned.env C iface s0)
    (hk : ∀ t, Post Owned.env iface s0 t → SafeN G n P t) (h : Mid s0 y)
    (hpc : y.pc = 0x7801b3d8#64) : SafeN G n P y := by
  have hcode := h.code
  rw [← setPC_self hpc]
  xstep code
  xstep code
  · -- not the public-values descriptor: return
    exact epilogue hk ((h.setPC _).setReg (by decide) (by decide) _ |>.setPC _) rfl
  have htag : y.getMem 0x78048830#64 = 1#64 := h.ok.1
  iterate 3 xstep code
  xa
  simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, htag] at *
  xstep code
  · simp at hb
  iterate 2 xstep code
  xa
  simp only [MachineState.getByte, MachineState.getMem_setReg, MachineState.getMem_setPC,
    alignToDword, byteOffset, BitVec.reduceAnd, BitVec.reduceNot, BitVec.reduceToNat] at *
  have hpos : (extractByte (y.getMem 0x780488a0#64) 0).toNat < 64 := by
    rw [extractByte_zero]; exact h.ok.2
  generalize extractByte (y.getMem 0x780488a0#64) 0 = p8 at *
  have hd : 960 ≤ (s0.getReg .x2).toNat := hpre.2.1
  have ht : (s0.getReg .x2).toNat ≤ 0x78000000 := hpre.2.2.1
  have hz : (BitVec.zeroExtend 64 p8).toNat = p8.toNat := by simp; omega
  xstep code
  xstep code
  · -- `len ≥ 64 - pos`: fill the buffer if it has bytes, then whole blocks
    generalize y.getReg .x8 = len at *
    xstep code
    · exact blocks hG hpre hk (by xmid) rfl (by xregs)
    · simp only [beq_iff_eq] at hb
      have hp0 : p8.toNat ≠ 0 := fun h0 => hb (by apply BitVec.eq_of_toNat_eq; rw [hz]; simpa using h0)
      iterate 6 xstep code
      xa
      refine call_memcpy (o := p8.toNat) (l := 64 - p8.toNat) hpre hG (by xmid) rfl (by omega)
        (by xregs; apply BitVec.eq_of_toNat_eq; simp <;> omega)
        (by xregs; apply BitVec.eq_of_toNat_eq; simp <;> omega) (fun t ht' htpc hsv => ?_)
      have htcode := ht'.code
      rw [← setPC_self (show t.pc = 0x7801b438#64 by rw [htpc]; xregs; decide)]
      have h18 : t.getReg .x18 = 0x78048830#64 := by rw [hsv _ (by decide)]; xregs
      iterate 8 xstep code
      xa
      simp only [h18]
      xa
      refine call_compress hpre hG ?_ rfl (by xregs <;> simp [h18]) (fun t2 ht2 ht2pc hsv2 => ?_)
      · xmid
        refine Mid.setCounter ?_ hd ht _
        xmid
      · have ht2code := ht2.code
        rw [← setPC_self (show t2.pc = 0x7801b458#64 by rw [ht2pc]; xregs; decide)]
        xstep code
        exact blocks hG hpre hk (by xmid) rfl (by xregs; rw [hsv2 _ (by decide)]; xregs; exact h18)
  · -- `len < 64 - pos`: append to the buffer
    generalize hlen : y.getReg .x8 = len at *
    simp only [Decidable.not_not, BitVec.ult_iff_lt, BitVec.lt_def] at hb
    have hb' : len.toNat + p8.toNat < 64 := by
      rw [BitVec.toNat_sub, hz] at hb; simp at hb; omega
    iterate 5 xstep code
    xa
    refine call_memcpy (o := p8.toNat) (l := len.toNat) hpre hG (by xmid) rfl (by omega)
      (by xregs; apply BitVec.eq_of_toNat_eq; simp <;> omega) (by xregs; simp [hlen])
      (fun t ht' htpc hsv => ?_)
    have htcode := ht'.code
    rw [← setPC_self (show t.pc = 0x7801b414#64 by rw [htpc]; xregs; decide)]
    iterate 2 xstep code
    refine finish hpre hk (by xmid) rfl (by xregs; rw [hsv _ (by decide)]; xregs) ?_
    xregs
    rw [hsv _ (by decide), hsv _ (by decide)]
    xregs
    rw [hlen, BitVec.toNat_add, hz]
    omega

/-- **`syscall_write`**, under the hasher invariant: it writes only its frame and the hasher's
    state, counter and buffer, keeps the hasher `Some` with its position below 64, and
    returns. On the public-values descriptor it appends to the buffer (compressing whole
    blocks); otherwise it only writes out. -/
theorem holds : iface.Holds Owned.env C := by
  intro n G hG P s hpc hpre hk
  have hcode := hpre.1
  rw [← setPC_self hpc]
  iterate 9 xstep code
  xa
  generalize hsp : s.getReg .x2 = sp at *
  refine safe_ecall (by xregs; decide)
    (fun y hs => sys_write (fetchLit code (by simp only [MachineState.code_setReg,
      MachineState.code_setPC, MachineState.code_setMem]; exact hcode) (pc_setPC _ _) rfl
      (by decide)) (by xregs; rfl) hs) (fun y hy => ?_)
  have hd : 960 ≤ sp.toNat := by have := hpre.2.1; rw [hsp] at this; exact this
  have ht : sp.toNat ≤ 0x78000000 := by have := hpre.2.2.1; rw [hsp] at this; exact this
  have hmid : Mid s y := by
    refine ⟨hcode, hy.code.trans (by simp [hcode]), ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      fun a ha hnw ho => ?_, ?_⟩
    · rw [hy.regs _ (by decide)]; xregs; rw [hsp]
    · simp only [untouched, List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (rw [hy.regs _ (by decide)]; xregs)
    all_goals try (rw [hy.mem _ (by simp), hsp]
                   simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, getMem_setMem,
                     BitVec.add_right_inj, BitVec.reduceEq, if_true, if_false]; done)
    · rw [hy.mem _ (by simp)]
      simp only [MachineState.getMem_setReg, MachineState.getMem_setPC]
      have hw : ¬ InWin sp iface.depth a := fun h => hnw (Or.inl (by simpa [regsOf, hsp] using h))
      xnf hw
      simp only [MachineState.getMem_setReg]
    · have hinv := (Owned.inv_iff).mp hpre.2.2.2.2.2.2.2.2.2.1
      have hm : ∀ a, 0x78000000 ≤ a.toNat → y.getMem a = s.getMem a := by
        intro a ha
        rw [hy.mem _ (by simp)]
        simp only [MachineState.getMem_setReg, MachineState.getMem_setPC]
        repeat (rw [getMem_setMem, if_neg (frame_ne ht (by bv_omega) ha)])
        simp only [MachineState.getMem_setReg]
      simp only [Owned.HasherOk] at hinv ⊢
      rw [hm _ (by decide), hm _ (by decide)]
      exact hinv
  exact body hG hpre hk hmid (by rw [hy.pc]; rfl)

end Cases.Zip2005.Runtime.SysWrite
