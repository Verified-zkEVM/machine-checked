/-
  Cases.Zip2005.Runtime.Memset

  `memset(a0, a1, a2)` for every length: it writes only `[a0, a0 + a2)` and returns.
-/

import AsmVerif.RiscV.Exec.Tactic
import AsmVerif.RiscV.Check.Image
import Cases.Zip2005.Loaded


set_option maxRecDepth 100000

namespace Cases.Zip2005.Runtime.Memset

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Frame AsmVerif.RiscV.Check
  AsmVerif.RiscV.Exec Cases.Zip2005.Image

noncomputable abbrev C : Word → Option Instr := Layout.image.codeAt

def fn : Fn := { base := F_7803f57c.base, prog := F_7803f57c.prog }

def iface : Iface :=
  { entry := 0x7803f57c#64, depth := 0, foot := [⟨.lin .x10 0, .reg .x12⟩] }

theorem decode : decodeWords F_7803f57c.words = F_7803f57c.prog := by decide +kernel

theorem code : CodeAt fn C :=
  codeAt_of_image (k := 306) Loaded.codeWF rfl decode (fun _ _ h => by simp [fn] at h)

theorem written_of {s0 : MachineState} {a : Word}
    (h : Hits (s0.getReg .x10) (s0.getReg .x12).toNat a) : Written iface (regsOf s0) a :=
  Or.inr ⟨_, List.mem_singleton_self _, by simpa [Item.Hits, AVal.eval, Len.eval, regsOf] using h⟩

/-- A store's footprint obligation, at an address `a0 + o` with `o < n`. -/
macro "xw" h:ident : tactic => `(tactic| (
  intro _
  apply written_of
  simp only [$h:ident]
  first | ((with_reducible apply hits_align); bv_omega) | (left; bv_omega)))

/-- The byte loop at `0x7803f5f0`: `r > 0` bytes left, at offset `o`. -/
def Bt (s0 s : MachineState) : Prop :=
  s.pc = 0x7803f5f0#64 ∧ ∃ o r : Nat, 0 < r ∧ o + r ≤ (s0.getReg .x12).toNat ∧
    s.getReg .x13 = s0.getReg .x10 + BitVec.ofNat 64 o ∧ s.getReg .x12 = BitVec.ofNat 64 r

/-- `a2 &&& -8`, the doubleword part of a length. -/
theorem and_neg8 (x : Word) : (x &&& 0xfffffffffffffff8#64).toNat = x.toNat / 8 * 8 := by
  have h := alignToDword_toNat x
  have : alignToDword x = x &&& 0xfffffffffffffff8#64 := by
    unfold alignToDword; congr 1
  rw [← this, h]; omega

theorem and_7 (x : Word) : (x &&& 7#64).toNat = x.toNat % 8 := by
  rw [BitVec.toNat_and]
  have h7 : (7#64).toNat = 2 ^ 3 - 1 := rfl
  rw [h7, Nat.and_two_pow_sub_one_eq_mod]

/-- Where the doubleword loop ends: the head, then whole doublewords. -/
def oe (h n : Nat) : Nat := h + (n - h) / 8 * 8

/-- The head loop at `0x7803f59c`: bytes up to the first aligned address. -/
def Head (s0 s : MachineState) : Prop :=
  s.pc = 0x7803f59c#64 ∧ ∃ h i : Nat, i < h ∧ h < 8 ∧ 16 ≤ (s0.getReg .x12).toNat ∧
    s.getReg .x16 = s0.getReg .x10 + BitVec.ofNat 64 i ∧ s.getReg .x15 = BitVec.ofNat 64 (h - i) ∧
    s.getReg .x14 = s0.getReg .x10 + BitVec.ofNat 64 h ∧ s.getReg .x13 = BitVec.ofNat 64 h ∧
    s.getReg .x12 = s0.getReg .x12

/-- After the head, at `0x7803f5ac`. -/
def Mid (s0 s : MachineState) : Prop :=
  s.pc = 0x7803f5ac#64 ∧ ∃ h : Nat, h < 8 ∧ 16 ≤ (s0.getReg .x12).toNat ∧
    s.getReg .x13 = BitVec.ofNat 64 h ∧ s.getReg .x14 = s0.getReg .x10 + BitVec.ofNat 64 h ∧
    s.getReg .x12 = s0.getReg .x12

/-- The doubleword loop at `0x7803f5d8`, at offset `o`. -/
def Dw (s0 s : MachineState) : Prop :=
  s.pc = 0x7803f5d8#64 ∧ ∃ h o : Nat, h < 8 ∧ 16 ≤ (s0.getReg .x12).toNat ∧
    o < oe h (s0.getReg .x12).toNat ∧ (oe h (s0.getReg .x12).toNat - o) % 8 = 0 ∧
    s.getReg .x14 = s0.getReg .x10 + BitVec.ofNat 64 o ∧
    s.getReg .x13 = s0.getReg .x10 + BitVec.ofNat 64 (oe h (s0.getReg .x12).toNat) ∧
    s.getReg .x12 = BitVec.ofNat 64 ((s0.getReg .x12).toNat - h)

/-- Before the byte tail, at `0x7803f5e4`: `m % 8` bytes left from offset `q`. -/
def Tl (s0 s : MachineState) : Prop :=
  s.pc = 0x7803f5e4#64 ∧ ∃ q m : Nat, q + m % 8 = (s0.getReg .x12).toNat ∧ m < 2 ^ 64 ∧
    s.getReg .x13 = s0.getReg .x10 + BitVec.ofNat 64 q ∧ s.getReg .x12 = BitVec.ofNat 64 m

theorem bt {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s) (h : Bt s0 s)
    (hk : ∀ t, Ret iface s0 t → SafeN G k P t)
    (IH : ∀ t, Frame iface C s0 t → Bt s0 t → SafeN G k P t) : SafeN G (k + 1) P s := by
  obtain ⟨hpc, o, r, hr, hor, h13, h12⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  xstep code
  xstep code
  · rw [h12] at hb
    have hr1 : r - 1 ≠ 0 := by
      simp only [bne_iff_ne, ne_eq] at hb
      intro h0; apply hb; bv_omega
    refine IH _ (by xframe <;> xw h13) ⟨rfl, o + 1, r - 1, by omega, by omega, ?_, ?_⟩
    · simp only [getReg_setReg, MachineState.getReg_setPC, getReg_setByte, reduceCtorEq,
        ne_eq, not_false_eq_true, and_true, if_true, h13]
      bv_omega
    · simp only [getReg_setReg, MachineState.getReg_setPC, getReg_setByte, reduceCtorEq,
        ne_eq, not_false_eq_true, and_true, if_true, if_false, h12]
      bv_omega
  · xret code hk
    xframe <;> xw h13


theorem tl {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s) (h : Tl s0 s)
    (hk : ∀ t, Ret iface s0 t → SafeN G k P t)
    (IH : ∀ t, Frame iface C s0 t → Bt s0 t → SafeN G k P t) : SafeN G (k + 1) P s := by
  obtain ⟨hpc, q, m, hqm, hm64, h13, h12⟩ := h
  have hcode := hF.code
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  xstep code
  · xret code hk
    xframe
  · have h7 := and_7 (s.getReg .x12)
    rw [h12, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm64] at h7
    rw [h12] at hb ⊢
    simp only [Decidable.not_not, BitVec.ult_iff_lt, BitVec.lt_def] at hb
    generalize BitVec.ofNat 64 m &&& 7#64 = y at *
    apply IH _ (by xframe) ⟨rfl, q, m % 8, ?_, by omega, ?_, ?_⟩
    · rw [h13] at hb; bv_omega
    · xregs; exact h13
    · xregs; bv_omega

theorem dw {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s) (h : Dw s0 s)
    (IH : ∀ t, Frame iface C s0 t → (Dw s0 t ∨ Tl s0 t) → SafeN G k P t) : SafeN G (k + 1) P s := by
  obtain ⟨hpc, h, o, hh, hn16, ho, ho8, h14, h13, h12⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  have hoe : oe h (s0.getReg .x12).toNat ≤ (s0.getReg .x12).toNat := by unfold oe; omega
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  xstep code
  · rw [h14, h13] at hb
    simp only [BitVec.ult_iff_lt, BitVec.lt_def] at hb
    have ho' : o + 8 < oe h (s0.getReg .x12).toNat := by
      have : o + 8 ≤ oe h (s0.getReg .x12).toNat := by omega
      rcases Nat.lt_or_eq_of_le this with h' | h'
      · exact h'
      · rw [← h'] at hb; exfalso; bv_omega
    refine IH _ (by xframe <;> xw h14) (Or.inl ⟨rfl, h, o + 8, hh, hn16, ho', by omega, ?_, ?_, ?_⟩)
    · xregs; rw [h14]; bv_omega
    · xregs; exact h13
    · xregs; exact h12
  · refine IH _ (by xframe <;> xw h14) (Or.inr ⟨rfl, oe h (s0.getReg .x12).toNat,
      (s0.getReg .x12).toNat - h, by unfold oe; omega, by omega, ?_, ?_⟩)
    · xregs; exact h13
    · xregs; exact h12

theorem mid {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s) (h : Mid s0 s)
    (IH : ∀ t, Frame iface C s0 t → (Dw s0 t ∨ Tl s0 t) → SafeN G k P t) : SafeN G (k + 1) P s := by
  obtain ⟨hpc, h, hh, hn16, h13, h14, h12⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  have h8 := and_neg8 (s.getReg .x12 - s.getReg .x13)
  have hsub : s.getReg .x12 - s.getReg .x13 = BitVec.ofNat 64 ((s0.getReg .x12).toNat - h) := by
    rw [h12, h13]; bv_omega
  rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h8
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  xstep code
  xstep code
  · rw [hsub] at hb ⊢
    generalize BitVec.ofNat 64 ((s0.getReg .x12).toNat - h) &&& 18446744073709551608#64 = w at *
    refine IH _ (by xframe) (Or.inr ⟨rfl, oe h (s0.getReg .x12).toNat,
      (s0.getReg .x12).toNat - h, by unfold oe; omega, by omega, ?_, ?_⟩)
    · xregs; rw [h14]; unfold oe; bv_omega
    · xregs
  · rw [hsub] at hb ⊢
    xstep code
    xstep code
    xstep code
    xstep code
    xstep code
    xstep code
    xstep code
    generalize BitVec.ofNat 64 ((s0.getReg .x12).toNat - h) &&& 18446744073709551608#64 = w at *
    rw [h14] at hb
    simp only [Decidable.not_not, BitVec.ult_iff_lt, BitVec.lt_def] at hb
    have hw : 0 < w.toNat := by bv_omega
    refine IH _ (by xframe) (Or.inl ⟨rfl, h, h, hh, hn16, by unfold oe; omega,
      by unfold oe; omega, ?_, ?_, ?_⟩)
    · xregs; exact h14
    · xregs; rw [h14]; unfold oe; bv_omega
    · xregs

theorem head {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s) (h : Head s0 s)
    (IH : ∀ t, Frame iface C s0 t → (Head s0 t ∨ Mid s0 t) → SafeN G k P t) :
    SafeN G (k + 1) P s := by
  obtain ⟨hpc, h, i, hi, hh, hn16, h16, h15, h14, h13, h12⟩ := h
  have hcode := hF.code
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  xstep code
  xstep code
  · rw [h15] at hb
    simp only [bne_iff_ne, ne_eq] at hb
    have hi1 : i + 1 < h := by
      have : h - i - 1 ≠ 0 := by intro h0; apply hb; bv_omega
      omega
    refine IH _ (by xframe <;> xw h16) (Or.inl ⟨rfl, h, i + 1, hi1, hh, hn16, ?_, ?_, ?_, ?_, ?_⟩)
    · xregs; rw [h16]; bv_omega
    · xregs; rw [h15]; bv_omega
    · xregs; exact h14
    · xregs; exact h13
    · xregs; exact h12
  · refine IH _ (by xframe <;> xw h16) (Or.inr ⟨rfl, h, hh, hn16, ?_, ?_, ?_⟩)
    · xregs; exact h13
    · xregs; exact h14
    · xregs; exact h12

theorem entry {s0 : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s0)
    (hpc : s0.pc = 0x7803f57c#64) (hk : ∀ t, Ret iface s0 t → SafeN G k P t)
    (IH : ∀ t, Frame iface C s0 t → (Head s0 t ∨ Mid s0 t ∨ Bt s0 t) → SafeN G k P t) :
    SafeN G (k + 1) P s0 := by
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def] at hb
    xstep code
    xstep code
    xstep code
    · refine IH _ (by xframe) (Or.inr (Or.inr ⟨rfl, 0, (s0.getReg .x12).toNat, ?_, by omega, ?_, ?_⟩))
      · simp only [BitVec.ult_iff_lt, BitVec.lt_def] at hb; bv_omega
      · xregs; bv_omega
      · xregs; simp
    · xstep code
      xret code hk
      xframe
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, Nat.not_lt] at hb
    have hn16 : 16 ≤ (s0.getReg .x12).toNat := hb
    clear hb
    xstep code
    xstep code
    xstep code
    xstep code
    · have h7 := and_7 (BitVec.signExtend 64 (BitVec.truncate 32 (0 : Word) -
        BitVec.truncate 32 (s0.getReg .x10)))
      generalize BitVec.signExtend 64 (BitVec.truncate 32 (0 : Word) -
        BitVec.truncate 32 (s0.getReg .x10)) &&& 7#64 = y at *
      refine IH _ (by xframe) (Or.inr (Or.inl ⟨rfl, y.toNat, by omega, hn16, ?_, ?_, ?_⟩))
      · xregs; simp
      · xregs; simp
      · xregs
    · xstep code
      xstep code
      have h7 := and_7 (BitVec.signExtend 64 (BitVec.truncate 32 (0 : Word) -
        BitVec.truncate 32 (s0.getReg .x10)))
      generalize BitVec.signExtend 64 (BitVec.truncate 32 (0 : Word) -
        BitVec.truncate 32 (s0.getReg .x10)) &&& 7#64 = y at *
      simp only [Decidable.not_not, BitVec.ult_iff_lt, BitVec.lt_def] at hb
      have hy : 0 < y.toNat := by bv_omega
      refine IH _ (by xframe) (Or.inl ⟨rfl, y.toNat, 0, hy, by omega, hn16, ?_, ?_, ?_,
        ?_, ?_⟩)
      · xregs; simp
      · xregs; simp
      · xregs; simp
      · xregs; simp
      · xregs

/-- The cut points: the entry, the head loop, after it, the doubleword loop, before the byte
    tail, and the byte loop. -/
def Inv (s0 s : MachineState) : Prop :=
  Frame iface C s0 s ∧
    ((s = s0 ∧ s0.pc = 0x7803f57c#64) ∨ Head s0 s ∨ Mid s0 s ∨ Dw s0 s ∨ Tl s0 s ∨ Bt s0 s)

/-- **memset**, for every length: writes only `[a0, a0 + a2)`, keeps `ra`, `sp` and the
    callee-saved registers, and returns. Under any `Env`: it reads no memory and calls
    nothing. -/
theorem holds (env : Env) (hok : env.Ok) : iface.Holds env C := by
  intro n
  apply holdsN_of_inv Inv hok (fun _ hpre => Pre.own_not_written rfl hpre)
    (fun _ _ _ _ _ h => by simp [iface] at h)
  · intro s0 hpc hpre
    exact ⟨Frame.entry hpre.1, Or.inl ⟨rfl, hpc⟩⟩
  · intro G s0 P k _ _ _ hk IH s ⟨hF, hs⟩
    cases k with
    | zero => exact SafeN.zero
    | succ k =>
      have hk' : ∀ t, Ret iface s0 t → SafeN G k P t :=
        fun t ht => SafeN.mono (Nat.le_succ k) (hk t ht)
      have IH' : ∀ t, Inv s0 t → SafeN G k P t := fun t ht => IH k (Nat.lt_succ_self k) t ht
      rcases hs with ⟨rfl, hpc⟩ | h | h | h | h | h
      · exact entry hF hpc hk' fun t hF h => IH' t ⟨hF, by
          rcases h with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
      · exact head hF h fun t hF h => IH' t ⟨hF, by
          rcases h with h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))⟩
      · exact mid hF h fun t hF h => IH' t ⟨hF, by
          rcases h with h | h
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
      · exact dw hF h fun t hF h => IH' t ⟨hF, by
          rcases h with h | h
          · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))⟩
      · exact tl hF h hk' fun t hF h => IH' t ⟨hF, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩
      · exact bt hF h hk' fun t hF h => IH' t ⟨hF, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))⟩

end Cases.Zip2005.Runtime.Memset
