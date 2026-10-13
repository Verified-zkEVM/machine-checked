/-
  Cases.Zip2005.Runtime.Memcpy

  `memcpy(a0, a1, a2)` for every length: it writes only `[a0, a0 + a2)` and returns.

  compiler-builtins' word-at-a-time copy: a byte loop aligns the source; with the
  destination aligned too, a 32-byte loop and 16/8/4-byte tails; otherwise, from 64 bytes
  on, a jump table on the destination's misalignment selects one of seven loops that
  shift source doublewords into place, and a 32-byte block and 16/8/4/2/1-byte tails take
  the rest. Only where it stores matters here: at the destination cursor `a3 = a0 + o`,
  below `a0 + n`. The values copied are left abstract (`xrun` loads fresh values).

  The jump table is read from `.rodata`, which the precondition protects.
-/

import AsmVerif.RiscV.Exec.Tactic
import AsmVerif.RiscV.Check.Image
import Cases.Zip2005.Loaded

set_option maxRecDepth 100000

namespace Cases.Zip2005.Runtime.Memcpy

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Frame AsmVerif.RiscV.Check
  AsmVerif.RiscV.Exec Cases.Zip2005.Image

noncomputable abbrev C : Word → Option Instr := Layout.image.codeAt

def fn : Fn := { base := F_7801b4d8.base, prog := F_7801b4d8.prog }

def iface : Iface :=
  { entry := 0x7801b4d8#64, depth := 0, foot := [⟨.lin .x10 0, .reg .x12⟩] }

theorem code : CodeAt fn C :=
  codeAt_of_image (k := 25) Loaded.codeWF rfl Loaded.memcpy_decode
    (fun _ _ h => by simp [fn] at h)

theorem written_of {s0 : MachineState} {a : Word}
    (h : Hits (s0.getReg .x10) (s0.getReg .x12).toNat a) : Written iface (regsOf s0) a :=
  Or.inr ⟨_, List.mem_singleton_self _, by simpa [Item.Hits, AVal.eval, Len.eval, regsOf] using h⟩

/-- A store's footprint obligation at the cursor: `x13 = a0 + o`, the store `c` bytes on,
    `o + c < n`. -/
macro "xw" h:ident : tactic => `(tactic| (
  intro _
  apply written_of
  simp only [$h:ident]
  first | ((with_reducible apply hits_align); bv_omega) | (left; bv_omega)))

/-- The tail cut points: `r` bytes left in the low `j` bits, from offset `o`. -/
def Tail (s0 s : MachineState) (p : Word) (j : Nat) (lo : Nat) (hi : Nat := 64) : Prop :=
  s.pc = p ∧ ∃ o r : Nat, r < hi ∧ o + r % 2 ^ j = (s0.getReg .x12).toNat ∧ lo ≤ r % 2 ^ j ∧
    s.getReg .x13 = s0.getReg .x10 + BitVec.ofNat 64 o ∧ s.getReg .x12 = BitVec.ofNat 64 r

/-- `n - o` bytes left from offset `o`, at `p`. -/
def Rest (s0 s : MachineState) (p : Word) (o : Nat) : Prop :=
  s.pc = p ∧ o ≤ (s0.getReg .x12).toNat ∧ s.getReg .x13 = s0.getReg .x10 + BitVec.ofNat 64 o ∧
    s.getReg .x12 = BitVec.ofNat 64 ((s0.getReg .x12).toNat - o)

/-- memcpy's cut points. -/
inductive Pt where
  | t538 | t540 | t548 | bb78 | bc0c | bc60 | bc8c
  | c634 | l640 | a670 | a680 | a6ac | a6c4
  | head | c520 | c528 | gba64
  | v1 | v2 | v3 | v4 | v5 | v6 | v7
  deriving DecidableEq

def At : Pt → MachineState → MachineState → Prop
  | .t538, s0, s => Tail s0 s 0x7801b538#64 5 0
  | .t540, s0, s => Tail s0 s 0x7801b540#64 4 0
  | .t548, s0, s => Tail s0 s 0x7801b548#64 3 0
  | .bb78, s0, s => Tail s0 s 0x7801bb78#64 5 16
  | .bc0c, s0, s => Tail s0 s 0x7801bc0c#64 4 8
  | .bc60, s0, s => Tail s0 s 0x7801bc60#64 3 4
  | .bc8c, s0, s => Tail s0 s 0x7801bc8c#64 2 0
  | .c634, s0, s => ∃ o, Rest s0 s 0x7801b634#64 o
  | .l640, s0, s => ∃ o, Rest s0 s 0x7801b640#64 o ∧ 32 ≤ (s0.getReg .x12).toNat - o ∧
      s.getReg .x14 = 31#64
  | .a670, s0, s => Tail s0 s 0x7801b670#64 5 0 32
  | .a680, s0, s => Tail s0 s 0x7801b680#64 3 0
  | .a6ac, s0, s => Tail s0 s 0x7801b6ac#64 4 8
  | .a6c4, s0, s => Tail s0 s 0x7801b6c4#64 3 4
  | .head, s0, s => ∃ o, Rest s0 s 0x7801b4f0#64 o ∧ o < (s0.getReg .x12).toNat ∧
      s.getReg .x15 = 1#64
  | .c520, s0, s => ∃ o, Rest s0 s 0x7801b520#64 o
  | .c528, s0, s => ∃ o, Rest s0 s 0x7801b528#64 o ∧ s.getReg .x14 = s.getReg .x13 &&& 7#64 ∧
      s.getReg .x14 ≠ 0
  | .gba64, s0, s => ∃ o, Rest s0 s 0x7801ba64#64 o ∧ 32 ≤ (s0.getReg .x12).toNat - o ∧
      (s0.getReg .x12).toNat - o < 64
  | .v1, s0, s => ∃ o, Rest s0 s 0x7801b5b8#64 o ∧ 32 < (s0.getReg .x12).toNat - o ∧
      s.getReg .x15 = 32#64
  | .v2, s0, s => ∃ o, Rest s0 s 0x7801b8e8#64 o ∧ 33 < (s0.getReg .x12).toNat - o ∧
      s.getReg .x15 = 33#64
  | .v3, s0, s => ∃ o, Rest s0 s 0x7801b7a0#64 o ∧ 34 < (s0.getReg .x12).toNat - o ∧
      s.getReg .x15 = 34#64
  | .v4, s0, s => ∃ o, Rest s0 s 0x7801b83c#64 o ∧ 35 < (s0.getReg .x12).toNat - o ∧
      s.getReg .x15 = 35#64
  | .v5, s0, s => ∃ o, Rest s0 s 0x7801b6fc#64 o ∧ 36 < (s0.getReg .x12).toNat - o ∧
      s.getReg .x15 = 36#64
  | .v6, s0, s => ∃ o, Rest s0 s 0x7801b974#64 o ∧ 37 < (s0.getReg .x12).toNat - o ∧
      s.getReg .x15 = 37#64
  | .v7, s0, s => ∃ o, Rest s0 s 0x7801b9f8#64 o ∧ 38 < (s0.getReg .x12).toNat - o ∧
      s.getReg .x15 = 38#64

/-- What a segment may assume: every cut state is safe at the remaining budget. -/
abbrev Next (G : MachineState → Prop) (s0 : MachineState) (k : Nat) (P : Prop) : Prop :=
  ∀ t c, Frame iface C s0 t → At c s0 t → SafeN G k P t

theorem tail_bc8c {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .bc8c s0 s) (hk : ∀ t, Ret iface s0 t → SafeN G k P t) :
    SafeN G (k + 1) P s := by
  obtain ⟨hpc, o, r, hr, hor, -, h13, h12⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  · have h1 := bit_set (b := 1) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h1
    xrun code
    xstep code
    · have h0 := bit_clear' (b := 0) (by omega) hb
      rw [h12, toNat_ofNat_lt (by omega)] at h0
      xret code hk
      xframe <;> xw h13
    · have h0 := bit_set' (b := 0) (by omega) hb
      rw [h12, toNat_ofNat_lt (by omega)] at h0
      xrun code
      xret code hk
      xframe <;> xw h13
  · have h1 := bit_clear (b := 1) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h1
    xrun code
    xstep code
    · have h0 := bit_set (b := 0) (by omega) hb
      rw [h12, toNat_ofNat_lt (by omega)] at h0
      xrun code
      xret code hk
      xframe <;> xw h13
    · xret code hk
      xframe


theorem tail_bc60 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .bc60 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨hpc, o, r, hr, hor, hlo, h13, h12⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code to 0x7801bc8c#64
  refine IH _ .bc8c (by xframe <;> xw h13) ⟨rfl, o + 4, r, hr, by omega, by omega, ?_, ?_⟩
  · xregs; rw [h13]; bv_omega
  · xregs; exact h12

theorem tail_bc0c {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .bc0c s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨hpc, o, r, hr, hor, hlo, h13, h12⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code
  xstep code
  · have h2 := bit_clear' (b := 2) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h2
    refine IH _ .bc8c (by xframe <;> xw h13) ⟨rfl, o + 8, r, hr, by omega, by omega, ?_, ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; exact h12
  · have h2 := bit_set' (b := 2) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h2
    refine IH _ .bc60 (by xframe <;> xw h13) ⟨rfl, o + 8, r, hr, by omega, by omega, ?_, ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; exact h12

theorem tail_bb78 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .bb78 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨hpc, o, r, hr, hor, hlo, h13, h12⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code
  xstep code
  · have h3 := bit_clear' (b := 3) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h3
    refine IH _ .t548 (by xframe <;> xw h13) ⟨rfl, o + 16, r, hr, by omega, by omega, ?_, ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; exact h12
  · have h3 := bit_set' (b := 3) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h3
    refine IH _ .bc0c (by xframe <;> xw h13) ⟨rfl, o + 16, r, hr, by omega, by omega, ?_, ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; exact h12

theorem tail_t548 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .t548 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨hpc, o, r, hr, hor, hlo, h13, h12⟩ := h
  have hcode := hF.code
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  · have h2 := bit_set (b := 2) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h2
    refine IH _ .bc60 (by xframe) ⟨rfl, o, r, hr, hor, by omega, ?_, ?_⟩
    · xregs; exact h13
    · xregs; exact h12
  · have h2 := bit_clear (b := 2) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h2
    xstep code
    refine IH _ .bc8c (by xframe) ⟨rfl, o, r, hr, by omega, by omega, ?_, ?_⟩
    · xregs; exact h13
    · xregs; exact h12

theorem tail_t540 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .t540 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨hpc, o, r, hr, hor, hlo, h13, h12⟩ := h
  have hcode := hF.code
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  · have h3 := bit_set (b := 3) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h3
    refine IH _ .bc0c (by xframe) ⟨rfl, o, r, hr, hor, by omega, ?_, ?_⟩
    · xregs; exact h13
    · xregs; exact h12
  · have h3 := bit_clear (b := 3) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h3
    refine IH _ .t548 (by xframe) ⟨rfl, o, r, hr, by omega, by omega, ?_, ?_⟩
    · xregs; exact h13
    · xregs; exact h12

theorem tail_t538 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .t538 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨hpc, o, r, hr, hor, hlo, h13, h12⟩ := h
  have hcode := hF.code
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  · have h4 := bit_set (b := 4) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h4
    refine IH _ .bb78 (by xframe) ⟨rfl, o, r, hr, hor, by omega, ?_, ?_⟩
    · xregs; exact h13
    · xregs; exact h12
  · have h4 := bit_clear (b := 4) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h4
    refine IH _ .t540 (by xframe) ⟨rfl, o, r, hr, by omega, by omega, ?_, ?_⟩
    · xregs; exact h13
    · xregs; exact h12

theorem aln_6c4 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .a6c4 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨hpc, o, r, hr, hor, hlo, h13, h12⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code
  xstep code
  refine IH _ .bc8c (by xframe <;> xw h13) ⟨rfl, o + 4, r, hr, by omega, by omega, ?_, ?_⟩
  · xregs; rw [h13]; bv_omega
  · xregs; exact h12

theorem aln_6ac {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .a6ac s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨hpc, o, r, hr, hor, hlo, h13, h12⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code
  xstep code
  · have h2 := bit_clear' (b := 2) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h2
    refine IH _ .bc8c (by xframe <;> xw h13) ⟨rfl, o + 8, r, hr, by omega, by omega, ?_, ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; exact h12
  · have h2 := bit_set' (b := 2) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h2
    refine IH _ .a6c4 (by xframe <;> xw h13) ⟨rfl, o + 8, r, hr, by omega, by omega, ?_, ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; exact h12

theorem aln_680 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .a680 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨hpc, o, r, hr, hor, hlo, h13, h12⟩ := h
  have hcode := hF.code
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  · have h2 := bit_set (b := 2) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h2
    refine IH _ .a6c4 (by xframe) ⟨rfl, o, r, hr, hor, by omega, ?_, ?_⟩
    · xregs; exact h13
    · xregs; exact h12
  · have h2 := bit_clear (b := 2) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h2
    xstep code
    refine IH _ .bc8c (by xframe) ⟨rfl, o, r, hr, by omega, by omega, ?_, ?_⟩
    · xregs; exact h13
    · xregs; exact h12

theorem aln_670 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .a670 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨hpc, o, r, hr, hor, hlo, h13, h12⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12,
      toNat_ofNat_lt (show r < 2 ^ 64 by omega), BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod] at hb
    have h16 := hb
    xrun code
    xstep code
    · have h3 := bit_clear' (b := 3) (by omega) hb
      rw [h12, toNat_ofNat_lt (by omega)] at h3
      refine IH _ .a680 (by xframe <;> xw h13) ⟨rfl, o + 16, r, by omega, by omega,
        by omega, ?_, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; exact h12
    · have h3 := bit_set' (b := 3) (by omega) hb
      rw [h12, toNat_ofNat_lt (by omega)] at h3
      refine IH _ .a6ac (by xframe <;> xw h13) ⟨rfl, o + 16, r, ?_, ?_, ?_, ?_, ?_⟩
      · omega
      · omega
      · omega
      · xregs; rw [h13]; bv_omega
      · xregs; exact h12
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12,
      toNat_ofNat_lt (show r < 2 ^ 64 by omega), BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod] at hb
    have h16 := hb
    xstep code
    xstep code
    · have h3 := bit_set (b := 3) (by omega) hb
      rw [h12, toNat_ofNat_lt (by omega)] at h3
      refine IH _ .a6ac (by xframe) ⟨rfl, o, r, by omega, by omega, by omega, ?_, ?_⟩
      · xregs; exact h13
      · xregs; exact h12
    · have h3 := bit_clear (b := 3) (by omega) hb
      rw [h12, toNat_ofNat_lt (by omega)] at h3
      refine IH _ .a680 (by xframe) ⟨rfl, o, r, by omega, by omega, by omega, ?_, ?_⟩
      · xregs; exact h13
      · xregs; exact h12

theorem aln_640 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .l640 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨o, ⟨hpc, ho, h13, h12⟩, h32, h14⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code
  xstep code
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h14, h12] at hb
    have h32' : 32 ≤ (s0.getReg .x12).toNat - (o + 32) := by bv_omega
    refine IH _ .l640 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, h32', ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; rw [h12]; bv_omega
    · xregs; exact h14
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h14, h12] at hb
    have h32' : (s0.getReg .x12).toNat - (o + 32) < 32 := by bv_omega
    refine IH _ .a670 (by xframe <;> xw h13) ⟨rfl, o + 32, (s0.getReg .x12).toNat - (o + 32),
      by omega, by omega, by omega, ?_, ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; rw [h12]; bv_omega

theorem aln_634 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .c634 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨o, hpc, ho, h13, h12⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12, toNat_ofNat_lt (show
      (s0.getReg .x12).toNat - o < 2 ^ 64 by omega), BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod] at hb
    refine IH _ .a670 (by xframe) ⟨rfl, o, (s0.getReg .x12).toNat - o, hb, by omega, by omega,
      ?_, ?_⟩
    · xregs; exact h13
    · xregs; exact h12
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12, toNat_ofNat_lt (show
      (s0.getReg .x12).toNat - o < 2 ^ 64 by omega), BitVec.toNat_ofNat, Nat.reducePow,
      Nat.reduceMod] at hb
    xstep code
    refine IH _ .l640 (by xframe) ⟨o, ⟨rfl, ho, ?_, ?_⟩, by omega, ?_⟩
    · xregs; exact h13
    · xregs; exact h12
    · xregs

theorem seg_c520 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .c520 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨o, hpc, ho, h13, h12⟩ := h
  have hcode := hF.code
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  · refine IH _ .c634 (by xframe) ⟨o, rfl, ho, ?_, ?_⟩
    · xregs; exact h13
    · xregs; exact h12
  · refine IH _ .c528 (by xframe) ⟨o, ⟨rfl, ho, ?_, ?_⟩, ?_, ?_⟩
    · xregs; exact h13
    · xregs; exact h12
    · xregs
    · xregs; simpa using hb

theorem seg_head {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .head s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨o, ⟨hpc, ho, h13, h12⟩, hon, h15⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code
  xstep code
  · refine IH _ .c520 (by xframe <;> xw h13) ⟨o + 1, rfl, by omega, ?_, ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; rw [h12]; bv_omega
  · xstep code
    xstep code
    · simp only [bne_iff_ne, ne_eq, h12, h15] at hb
      have hon' : o + 1 < (s0.getReg .x12).toNat := by
        have : (s0.getReg .x12).toNat - o ≠ 1 := by intro h1; apply hb; rw [h1]
        omega
      refine IH _ .head (by xframe <;> xw h13) ⟨o + 1, ⟨rfl, by omega, ?_, ?_⟩, hon', ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
      · xregs; exact h15
    · xstep code
      refine IH _ .c520 (by xframe <;> xw h13) ⟨o + 1, rfl, by omega, ?_, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega

theorem seg_ba64 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .gba64 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨o, ⟨hpc, ho, h13, h12⟩, h32, h64⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code
  xstep code
  · have h4 := bit_clear' (b := 4) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h4
    refine IH _ .t540 (by xframe <;> xw h13) ⟨rfl, o + 32, (s0.getReg .x12).toNat - o,
      by omega, by omega, by omega, ?_, ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; exact h12
  · have h4 := bit_set' (b := 4) (by omega) hb
    rw [h12, toNat_ofNat_lt (by omega)] at h4
    refine IH _ .bb78 (by xframe <;> xw h13) ⟨rfl, o + 32, (s0.getReg .x12).toNat - o,
      by omega, by omega, by omega, ?_, ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; exact h12

theorem seg_v1 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .v1 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨o, ⟨hpc, ho, h13, h12⟩, hth, h15⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code
  xstep code
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h15, h12] at hb
    have hth' : 32 < (s0.getReg .x12).toNat - (o + 32) := by bv_omega
    refine IH _ .v1 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, hth', ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; rw [h12]; bv_omega
    · xregs; exact h15
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h15, h12] at hb
    have hle : (s0.getReg .x12).toNat - (o + 32) ≤ 32 := by bv_omega
    xrun code
    xstep code
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have hlt : (s0.getReg .x12).toNat - (o + 32) < 32 := by bv_omega
      refine IH _ .t538 (by xframe <;> xw h13) ⟨rfl, o + 32, (s0.getReg .x12).toNat - (o + 32),
        by omega, by omega, by omega, ?_, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have hge : 32 ≤ (s0.getReg .x12).toNat - (o + 32) := by bv_omega
      xstep code
      refine IH _ .gba64 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, hge, by omega⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega

theorem seg_v2 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .v2 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨o, ⟨hpc, ho, h13, h12⟩, hth, h15⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code
  xstep code
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h15, h12] at hb
    have hth' : 33 < (s0.getReg .x12).toNat - (o + 32) := by bv_omega
    refine IH _ .v2 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, hth', ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; rw [h12]; bv_omega
    · xregs; exact h15
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h15, h12] at hb
    have hle : (s0.getReg .x12).toNat - (o + 32) ≤ 33 := by bv_omega
    xrun code
    xstep code
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have hlt : (s0.getReg .x12).toNat - (o + 32) < 32 := by bv_omega
      refine IH _ .t538 (by xframe <;> xw h13) ⟨rfl, o + 32, (s0.getReg .x12).toNat - (o + 32),
        by omega, by omega, by omega, ?_, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have hge : 32 ≤ (s0.getReg .x12).toNat - (o + 32) := by bv_omega
      xstep code
      refine IH _ .gba64 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, hge, by omega⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega

theorem seg_v3 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .v3 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨o, ⟨hpc, ho, h13, h12⟩, hth, h15⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code
  xstep code
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h15, h12] at hb
    have hth' : 34 < (s0.getReg .x12).toNat - (o + 32) := by bv_omega
    refine IH _ .v3 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, hth', ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; rw [h12]; bv_omega
    · xregs; exact h15
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h15, h12] at hb
    have hle : (s0.getReg .x12).toNat - (o + 32) ≤ 34 := by bv_omega
    xrun code
    xstep code
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have hlt : (s0.getReg .x12).toNat - (o + 32) < 32 := by bv_omega
      refine IH _ .t538 (by xframe <;> xw h13) ⟨rfl, o + 32, (s0.getReg .x12).toNat - (o + 32),
        by omega, by omega, by omega, ?_, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have hge : 32 ≤ (s0.getReg .x12).toNat - (o + 32) := by bv_omega
      xstep code
      refine IH _ .gba64 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, hge, by omega⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega

theorem seg_v4 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .v4 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨o, ⟨hpc, ho, h13, h12⟩, hth, h15⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code
  xstep code
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h15, h12] at hb
    have hth' : 35 < (s0.getReg .x12).toNat - (o + 32) := by bv_omega
    refine IH _ .v4 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, hth', ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; rw [h12]; bv_omega
    · xregs; exact h15
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h15, h12] at hb
    have hle : (s0.getReg .x12).toNat - (o + 32) ≤ 35 := by bv_omega
    xrun code
    xstep code
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have hlt : (s0.getReg .x12).toNat - (o + 32) < 32 := by bv_omega
      refine IH _ .t538 (by xframe <;> xw h13) ⟨rfl, o + 32, (s0.getReg .x12).toNat - (o + 32),
        by omega, by omega, by omega, ?_, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have hge : 32 ≤ (s0.getReg .x12).toNat - (o + 32) := by bv_omega
      xstep code
      refine IH _ .gba64 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, hge, by omega⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega

theorem seg_v5 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .v5 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨o, ⟨hpc, ho, h13, h12⟩, hth, h15⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code
  xstep code
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h15, h12] at hb
    have hth' : 36 < (s0.getReg .x12).toNat - (o + 32) := by bv_omega
    refine IH _ .v5 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, hth', ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; rw [h12]; bv_omega
    · xregs; exact h15
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h15, h12] at hb
    have hle : (s0.getReg .x12).toNat - (o + 32) ≤ 36 := by bv_omega
    xrun code
    xstep code
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have hlt : (s0.getReg .x12).toNat - (o + 32) < 32 := by bv_omega
      refine IH _ .t538 (by xframe <;> xw h13) ⟨rfl, o + 32, (s0.getReg .x12).toNat - (o + 32),
        by omega, by omega, by omega, ?_, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have hge : 32 ≤ (s0.getReg .x12).toNat - (o + 32) := by bv_omega
      xstep code
      refine IH _ .gba64 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, hge, by omega⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega

theorem seg_v6 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .v6 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨o, ⟨hpc, ho, h13, h12⟩, hth, h15⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code
  xstep code
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h15, h12] at hb
    have hth' : 37 < (s0.getReg .x12).toNat - (o + 32) := by bv_omega
    refine IH _ .v6 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, hth', ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; rw [h12]; bv_omega
    · xregs; exact h15
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h15, h12] at hb
    have hle : (s0.getReg .x12).toNat - (o + 32) ≤ 37 := by bv_omega
    xrun code
    xstep code
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have hlt : (s0.getReg .x12).toNat - (o + 32) < 32 := by bv_omega
      refine IH _ .t538 (by xframe <;> xw h13) ⟨rfl, o + 32, (s0.getReg .x12).toNat - (o + 32),
        by omega, by omega, by omega, ?_, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have hge : 32 ≤ (s0.getReg .x12).toNat - (o + 32) := by bv_omega
      xstep code
      refine IH _ .gba64 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, hge, by omega⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega

theorem seg_v7 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .v7 s0 s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨o, ⟨hpc, ho, h13, h12⟩, hth, h15⟩ := h
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xrun1 code
  xstep code
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h15, h12] at hb
    have hth' : 38 < (s0.getReg .x12).toNat - (o + 32) := by bv_omega
    refine IH _ .v7 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, hth', ?_⟩
    · xregs; rw [h13]; bv_omega
    · xregs; rw [h12]; bv_omega
    · xregs; exact h15
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h15, h12] at hb
    have hle : (s0.getReg .x12).toNat - (o + 32) ≤ 38 := by bv_omega
    xrun code
    xstep code
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have hlt : (s0.getReg .x12).toNat - (o + 32) < 32 := by bv_omega
      refine IH _ .t538 (by xframe <;> xw h13) ⟨rfl, o + 32, (s0.getReg .x12).toNat - (o + 32),
        by omega, by omega, by omega, ?_, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have hge : 32 ≤ (s0.getReg .x12).toNat - (o + 32) := by bv_omega
      refine IH _ .gba64 (by xframe <;> xw h13) ⟨o + 32, ⟨rfl, by omega, ?_, ?_⟩, hge, by omega⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega

/-- The jump table's doublewords, as the image holds them. -/
def TabOk (s : MachineState) : Prop :=
  s.getMem 0x78001490#64 = 0x7801b8ac7801b574#64 ∧ s.getMem 0x78001498#64 = 0x7801b8107801b76c#64 ∧
  s.getMem 0x780014a0#64 = 0x7801b9587801b6d8#64 ∧ s.getMem 0x780014a8#64 = 0x000000007801b9e4#64

theorem seg_c528 {s0 s : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s)
    (h : At .c528 s0 s) (htab : TabOk s) (IH : Next G s0 k P) : SafeN G (k + 1) P s := by
  obtain ⟨o, ⟨hpc, ho, h13, h12⟩, h14, h14z⟩ := h
  obtain ⟨t0, t1, t2, t3⟩ := htab
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
    have h64 : 64 ≤ (s0.getReg .x12).toNat - o := by bv_omega
    xrun code to 0x7801b568#64
    xstep code
    xload code
    have hk7 : s.getReg .x14 = 1#64 ∨ s.getReg .x14 = 2#64 ∨ s.getReg .x14 = 3#64 ∨
        s.getReg .x14 = 4#64 ∨ s.getReg .x14 = 5#64 ∨ s.getReg .x14 = 6#64 ∨
        s.getReg .x14 = 7#64 := by
      have : (s.getReg .x14).toNat < 8 := by rw [h14, BitVec.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
      have : s.getReg .x14 ≠ 0 := h14z
      bv_omega
    rcases hk7 with hk | hk | hk | hk | hk | hk | hk
    · simp only [hk, MachineState.getWord32, MachineState.getMem_setReg,
        MachineState.getMem_setPC]
      simp only [BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceSignExtend,
        BitVec.reduceToNat, BitVec.reduceHShiftLeft, alignToDword, byteOffset, BitVec.reduceAnd,
        BitVec.reduceNot, Nat.reduceDiv]
      simp only [t0, extractWord32, Nat.reduceMul, BitVec.reduceHShiftRight, BitVec.truncate_eq_setWidth,
        BitVec.reduceSetWidth]
      xstep code
      xrun code to 0x7801b5b8#64
      refine IH _ .v1 (by xframe <;> xw h13) ⟨o + 7, ⟨rfl, by omega, ?_, ?_⟩, by omega, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
      · xregs
    · simp only [hk, MachineState.getWord32, MachineState.getMem_setReg,
        MachineState.getMem_setPC]
      simp only [BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceSignExtend,
        BitVec.reduceToNat, BitVec.reduceHShiftLeft, alignToDword, byteOffset, BitVec.reduceAnd,
        BitVec.reduceNot, Nat.reduceDiv]
      simp only [t0, extractWord32, Nat.reduceMul, BitVec.reduceHShiftRight, BitVec.truncate_eq_setWidth,
        BitVec.reduceSetWidth]
      xstep code
      xrun code to 0x7801b8e8#64
      refine IH _ .v2 (by xframe <;> xw h13) ⟨o + 6, ⟨rfl, by omega, ?_, ?_⟩, by omega, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
      · xregs
    · simp only [hk, MachineState.getWord32, MachineState.getMem_setReg,
        MachineState.getMem_setPC]
      simp only [BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceSignExtend,
        BitVec.reduceToNat, BitVec.reduceHShiftLeft, alignToDword, byteOffset, BitVec.reduceAnd,
        BitVec.reduceNot, Nat.reduceDiv]
      simp only [t1, extractWord32, Nat.reduceMul, BitVec.reduceHShiftRight, BitVec.truncate_eq_setWidth,
        BitVec.reduceSetWidth]
      xstep code
      xrun code to 0x7801b7a0#64
      refine IH _ .v3 (by xframe <;> xw h13) ⟨o + 5, ⟨rfl, by omega, ?_, ?_⟩, by omega, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
      · xregs
    · simp only [hk, MachineState.getWord32, MachineState.getMem_setReg,
        MachineState.getMem_setPC]
      simp only [BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceSignExtend,
        BitVec.reduceToNat, BitVec.reduceHShiftLeft, alignToDword, byteOffset, BitVec.reduceAnd,
        BitVec.reduceNot, Nat.reduceDiv]
      simp only [t1, extractWord32, Nat.reduceMul, BitVec.reduceHShiftRight, BitVec.truncate_eq_setWidth,
        BitVec.reduceSetWidth]
      xstep code
      xrun code to 0x7801b83c#64
      refine IH _ .v4 (by xframe <;> xw h13) ⟨o + 4, ⟨rfl, by omega, ?_, ?_⟩, by omega, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
      · xregs
    · simp only [hk, MachineState.getWord32, MachineState.getMem_setReg,
        MachineState.getMem_setPC]
      simp only [BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceSignExtend,
        BitVec.reduceToNat, BitVec.reduceHShiftLeft, alignToDword, byteOffset, BitVec.reduceAnd,
        BitVec.reduceNot, Nat.reduceDiv]
      simp only [t2, extractWord32, Nat.reduceMul, BitVec.reduceHShiftRight, BitVec.truncate_eq_setWidth,
        BitVec.reduceSetWidth]
      xstep code
      xrun code to 0x7801b6fc#64
      refine IH _ .v5 (by xframe <;> xw h13) ⟨o + 3, ⟨rfl, by omega, ?_, ?_⟩, by omega, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
      · xregs
    · simp only [hk, MachineState.getWord32, MachineState.getMem_setReg,
        MachineState.getMem_setPC]
      simp only [BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceSignExtend,
        BitVec.reduceToNat, BitVec.reduceHShiftLeft, alignToDword, byteOffset, BitVec.reduceAnd,
        BitVec.reduceNot, Nat.reduceDiv]
      simp only [t2, extractWord32, Nat.reduceMul, BitVec.reduceHShiftRight, BitVec.truncate_eq_setWidth,
        BitVec.reduceSetWidth]
      xstep code
      xrun code to 0x7801b974#64
      refine IH _ .v6 (by xframe <;> xw h13) ⟨o + 2, ⟨rfl, by omega, ?_, ?_⟩, by omega, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
      · xregs
    · simp only [hk, MachineState.getWord32, MachineState.getMem_setReg,
        MachineState.getMem_setPC]
      simp only [BitVec.reduceAdd, BitVec.reduceZeroExtend, BitVec.reduceSignExtend,
        BitVec.reduceToNat, BitVec.reduceHShiftLeft, alignToDword, byteOffset, BitVec.reduceAnd,
        BitVec.reduceNot, Nat.reduceDiv]
      simp only [t3, extractWord32, Nat.reduceMul, BitVec.reduceHShiftRight, BitVec.truncate_eq_setWidth,
        BitVec.reduceSetWidth]
      xstep code
      xrun code to 0x7801b9f8#64
      refine IH _ .v7 (by xframe <;> xw h13) ⟨o + 1, ⟨rfl, by omega, ?_, ?_⟩, by omega, ?_⟩
      · xregs; rw [h13]; bv_omega
      · xregs; rw [h12]; bv_omega
      · xregs
  · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
    have h64 : (s0.getReg .x12).toNat - o < 64 := by bv_omega
    xstep code
    xstep code
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have h32 : 32 ≤ (s0.getReg .x12).toNat - o := by bv_omega
      refine IH _ .gba64 (by xframe) ⟨o, ⟨rfl, ho, ?_, ?_⟩, h32, h64⟩
      · xregs; exact h13
      · xregs; exact h12
    · simp only [BitVec.ult_iff_lt, BitVec.lt_def, h12] at hb
      have h32 : (s0.getReg .x12).toNat - o < 32 := by bv_omega
      refine IH _ .t538 (by xframe) ⟨rfl, o, (s0.getReg .x12).toNat - o, by omega, by omega,
        by omega, ?_, ?_⟩
      · xregs; exact h13
      · xregs; exact h12

theorem seg_entry {s0 : MachineState} {G : MachineState → Prop} {k : Nat} {P : Prop} (hF : Frame iface C s0 s0)
    (hpc : s0.pc = 0x7801b4d8#64) (IH : Next G s0 k P) : SafeN G (k + 1) P s0 := by
  have hcode := hF.code
  have hn := (s0.getReg .x12).isLt
  rw [← setPC_self hpc]
  xstep1 code
  xstep code
  · xrun code
    xstep code
    · refine IH _ .c528 (by xframe) ⟨0, ⟨rfl, by omega, ?_, ?_⟩, ?_, ?_⟩
      · xregs; try simp
      · xregs; try simp
      · xregs; try simp
      · xregs; simpa using hb
    · refine IH _ .c634 (by xframe) ⟨0, rfl, by omega, ?_, ?_⟩
      · xregs; try simp
      · xregs; try simp
  · xstep code
    · xstep code
      refine IH _ .c520 (by xframe) ⟨0, rfl, by omega, ?_, ?_⟩
      · xregs; try simp
      · xregs; simp only [beq_iff_eq] at hb; rw [hb]; rfl
    · simp only [beq_iff_eq] at hb
      xrun code to 0x7801b4f0#64
      refine IH _ .head (by xframe) ⟨0, ⟨rfl, by omega, ?_, ?_⟩, ?_, ?_⟩
      · xregs; try simp
      · xregs; try simp
      · have : s0.getReg .x12 ≠ 0 := hb
        have : (s0.getReg .x12).toNat ≠ 0 := fun h => this (BitVec.eq_of_toNat_eq (by simpa using h))
        omega
      · xregs

/-! ## Assembly -/

theorem memAt_word {j : Nat} (hj : j < Data_0.chunk.size) {a v : Word}
    (ha : Data_0.chunk.base + BitVec.ofNat 64 (8 * j) = a) (hv : Data_0.chunk.wordAt j = v) :
    Layout.image.memAt a = v := by
  rw [← ha, ← hv]
  exact Image.memAt_chunk (k := 0) Loaded.dataWF rfl hj

/-- The jump table in the loaded image. -/
theorem tab_image : Layout.image.memAt 0x78001490#64 = 0x7801b8ac7801b574#64 ∧
    Layout.image.memAt 0x78001498#64 = 0x7801b8107801b76c#64 ∧
    Layout.image.memAt 0x780014a0#64 = 0x7801b9587801b6d8#64 ∧
    Layout.image.memAt 0x780014a8#64 = 0x000000007801b9e4#64 :=
  ⟨memAt_word (j := 658) (by decide +kernel) (by decide +kernel) (by decide +kernel),
   memAt_word (j := 659) (by decide +kernel) (by decide +kernel) (by decide +kernel),
   memAt_word (j := 660) (by decide +kernel) (by decide +kernel) (by decide +kernel),
   memAt_word (j := 661) (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩

/-- The table is in `.rodata`, which the precondition protects and memcpy's footprint
    avoids: every state of the activation reads it as the image holds it. -/
theorem tabOk {env : Env} (hinit : env.init = Layout.image.memAt)
    (hprot : (0x78000190#64, 0x157a8) ∈ env.prot) {s0 s : MachineState}
    (hpre : Pre env C iface s0) (hF : Frame iface C s0 s) : TabOk s := by
  have key : ∀ a : Word, a.toNat % 8 = 0 → 0x78000190 ≤ a.toNat → a.toNat + 8 ≤ 0x78015938 →
      s.getMem a = Layout.image.memAt a := by
    intro a ha8 hlo hhi
    have hal : Aligned a := (aligned_iff a).mpr ha8
    have hp : env.InProt a := ⟨_, hprot, Or.inl (by simp only; bv_omega)⟩
    rw [hF.mem a hal, hpre.2.2.2.2.1 a hal hp, hinit]
    rintro (hw | ⟨it, hit, hh⟩)
    · rcases hw with hw | ⟨hw, _⟩ <;> simp [iface] at hw
    · exact (hpre.2.2.2.2.2.1 it hit a hal hh).2.1 hp
  obtain ⟨t0, t1, t2, t3⟩ := tab_image
  exact ⟨(key _ (by decide) (by decide) (by decide)).trans t0,
    (key _ (by decide) (by decide) (by decide)).trans t1,
    (key _ (by decide) (by decide) (by decide)).trans t2,
    (key _ (by decide) (by decide) (by decide)).trans t3⟩

def Inv (s0 s : MachineState) : Prop :=
  Frame iface C s0 s ∧ ((s = s0 ∧ s0.pc = 0x7801b4d8#64) ∨ ∃ c, At c s0 s)

/-- **memcpy**, for every length: writes only `[a0, a0 + a2)`, keeps `ra`, `sp` and the
    callee-saved registers, and returns. It reads its jump table from `.rodata`, so the
    `Env` must protect it with the image's contents. -/
theorem holds (env : Env) (hinit : env.init = Layout.image.memAt)
    (hprot : (0x78000190#64, 0x157a8) ∈ env.prot) : iface.Holds env C := by
  intro n
  apply holdsN_of_inv Inv (fun _ hpre => Pre.own_not_written rfl hpre)
  · intro s0 hpc hpre
    exact ⟨Frame.entry hpre.1, Or.inl ⟨rfl, hpc⟩⟩
  · intro G s0 P k _ hpre _ hk IH s ⟨hF, hs⟩
    cases k with
    | zero => exact SafeN.zero
    | succ k =>
      have hk' : ∀ t, Ret iface s0 t → SafeN G k P t :=
        fun t ht => SafeN.mono (Nat.le_succ k) (hk t ht)
      have IH' : Next G s0 k P := fun t c hF h => IH k (Nat.lt_succ_self k) t ⟨hF, Or.inr ⟨c, h⟩⟩
      rcases hs with ⟨rfl, hpc⟩ | ⟨c, h⟩
      · exact seg_entry hF hpc IH'
      · cases c with
        | t538 => exact tail_t538 hF h IH'
        | t540 => exact tail_t540 hF h IH'
        | t548 => exact tail_t548 hF h IH'
        | bb78 => exact tail_bb78 hF h IH'
        | bc0c => exact tail_bc0c hF h IH'
        | bc60 => exact tail_bc60 hF h IH'
        | bc8c => exact tail_bc8c hF h hk'
        | c634 => exact aln_634 hF h IH'
        | l640 => exact aln_640 hF h IH'
        | a670 => exact aln_670 hF h IH'
        | a680 => exact aln_680 hF h IH'
        | a6ac => exact aln_6ac hF h IH'
        | a6c4 => exact aln_6c4 hF h IH'
        | head => exact seg_head hF h IH'
        | c520 => exact seg_c520 hF h IH'
        | c528 => exact seg_c528 hF h (tabOk hinit hprot hpre hF) IH'
        | gba64 => exact seg_ba64 hF h IH'
        | v1 => exact seg_v1 hF h IH'
        | v2 => exact seg_v2 hF h IH'
        | v3 => exact seg_v3 hF h IH'
        | v4 => exact seg_v4 hF h IH'
        | v5 => exact seg_v5 hF h IH'
        | v6 => exact seg_v6 hF h IH'
        | v7 => exact seg_v7 hF h IH'

end Cases.Zip2005.Runtime.Memcpy
