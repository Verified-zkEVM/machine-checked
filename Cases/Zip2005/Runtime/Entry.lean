/-
  Cases.Zip2005.Runtime.Entry

  Phase D1: the run from the loaded image to `main`'s entry.

  Every value on this path is a constant: `_start` sets `gp` and loads `sp` from the image;
  `__start` runs the allocator's `init`, which checks `_end < 7 << 34` and hands
  `Heap::init` the arena `[_end, 7 << 34)`; `Heap::init` reads `INNER_HEAP`'s zero lock,
  rounds the arena to one free block and links it into its size class (both bitmaps,
  one free-list head); `__start` then sets up the public-values hasher (state `1`, four
  words of `.rodata`, `memset` of the 73-byte buffer) and calls `main`.

  So the proof runs the executor on literal states (`xs`: one step, the untaken side of a
  literal branch discharged by `decide`), reading `.bss` as zero (`bss0`); `memset` too is
  run on its literal arguments. `MainEntry` is what `main` gets: code, `ra`, `sp`, `gp`, and
  all of memory — the image's, with the 31 stores of `stores`. In particular the protected
  statics and `.rodata` hold their load values, the heap is one free block covering the
  arena, and the hasher is `Some`, at position zero.

  The input stream reaches `main` untouched.
-/

import AsmVerif.RiscV.Exec.Tactic
import AsmVerif.RiscV.Check.Image
import Cases.Zip2005.Loaded
import Cases.Zip2005.Runtime.Memset
import Cases.Zip2005.Statics
import Cases.Zip2005.Contract.Table

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Cases.Zip2005.Runtime.Entry

open RiscvZkvm.Rv64 AsmVerif.RiscV AsmVerif.RiscV.Frame AsmVerif.RiscV.Check
  AsmVerif.RiscV.Exec Cases.Zip2005.Image

noncomputable abbrev C : Word → Option Instr := Layout.image.codeAt

def startWords : List (BitVec 32) :=
  [0xfffe5197#32, 0xb3018193#32, 0xfffe5117#32, 0x7d810113#32, 0x00013103#32, 0x00000097#32,
    0x150080e7#32]

def start : Fn := { base := 0x7801bcd0#64, prog := [
  some (.AUIPC .x3 0xfffe5#20), some (.ADDI .x3 .x3 0xb30#12), some (.AUIPC .x2 0xfffe5#20),
  some (.ADDI .x2 .x2 0x7d8#12), some (.LD .x2 .x2 0x000#12), some (.AUIPC .x1 0x00000#20),
  some (.JALR .x1 .x1 0x150#12)] }

theorem start_code : CodeAt start C :=
  codeAt_of_image (k := 26) (ws := startWords) Loaded.codeWF rfl (by decide)
    (fun _ _ h => by simp [start] at h)

def startF : Fn := { base := F_7801be34.base, prog := F_7801be34.prog }
def initF : Fn := { base := F_7801bdec.base, prog := F_7801bdec.prog }
def heapInitF : Fn := { base := F_7801bfac.base, prog := F_7801bfac.prog }
def dumpF : Fn := { base := F_7801beac.base, prog := F_7801beac.prog }

theorem startF_code : CodeAt startF C :=
  codeAt_of_image (k := 31) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [startF] at h)
theorem initF_code : CodeAt initF C :=
  codeAt_of_image (k := 30) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [initF] at h)
theorem heapInitF_code : CodeAt heapInitF C :=
  codeAt_of_image (k := 41) Loaded.codeWF rfl (by decide +kernel)
    (fun _ _ h => by simp [heapInitF] at h)
theorem dumpF_code : CodeAt dumpF C :=
  codeAt_of_image (k := 32) Loaded.codeWF rfl (by decide +kernel) (fun _ _ h => by simp [dumpF] at h)

theorem getMem_load (input : List (BitVec 8)) (a : Word) :
    (Layout.image.state input).getMem a = Layout.image.memAt a := rfl

theorem getReg_load (input : List (BitVec 8)) (r : Reg) :
    (Layout.image.state input).getReg r = 0 := by
  cases r <;> rfl

/-- A doubleword of `.bss` past `.data` reads zero at load. -/
theorem bss0 (a : Word) (h : (a.toNat - 0x78040618) % 8 = 0 ∧ 0x78040620 ≤ a.toNat ∧
    a.toNat < 0x78040618 + 8 * 4205) : Layout.image.memAt a = 0 := by
  obtain ⟨h8, hlo, hhi⟩ := h
  have ha : a = Image.Data_2.chunk.base + BitVec.ofNat 64 (8 * ((a.toNat - 0x78040618) / 8)) := by
    rw [Statics.chunk_base]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have := a.isLt
    omega
  rw [ha]
  exact Statics.memAt_bss (by rw [Statics.words_len]; omega) (by rw [Statics.chunk_size]; omega)

/-- Fold the literal arithmetic of a concrete run and read memory through its stores. -/
macro "xn" : tactic => `(tactic| (
  try simp only [BitVec.reduceZeroExtend, BitVec.reduceShiftLeft, BitVec.reduceSignExtend,
    BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceXOr,
    BitVec.reduceNot, BitVec.reduceHShiftLeft, BitVec.reduceHShiftRight, BitVec.reduceShiftLeft,
    BitVec.reduceUShiftRight, BitVec.reduceSShiftRight, BitVec.reduceMul, BitVec.reduceNeg,
    BitVec.reduceExtractLsb', BitVec.reduceSetWidth, BitVec.reduceShiftLeftZeroExtend,
    BitVec.reduceToNat, BitVec.truncate_eq_setWidth, Nat.reduceMod, Nat.reduceMul,
    signExtend12, signExtend13, rv64_mulhu, MachineState.setByte, replaceByte, alignToDword,
    byteOffset] at *
  try simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, getMem_setMem,
    getMem_load, getReg_load, Loaded.stackTop_word, BitVec.reduceEq, if_true, if_false, reduceIte] at *
  try simp (disch := decide) only [bss0] at *))

set_option hygiene false in
/-- One step of the concrete run: a branch keeps only the side its literal condition takes. -/
macro "xs " c:term:max : tactic => `(tactic| (
  xstep $c <;> (xn; first
    | (exfalso; revert hb; decide)
    | (try clear hb))))

/-! ## What `main` is entered with -/

/-- The doublewords the entry run writes before `main`, latest first: `__start`'s and
    `Heap::init`'s stack slots; `INNER_HEAP`'s lock, its one free-list head and both bitmap
    words; the arena's one free block (header, links, end sentinel); the public-values
    hasher's `Some` tag, its four initial words from `.rodata`, and its zeroed buffer and
    position. -/
noncomputable def stores : List (Word × Word) := [
  (0x780488a0#64, 0x0#64),
  (0x78048898#64, 0x0#64),
  (0x78048890#64, 0x0#64),
  (0x78048888#64, 0x0#64),
  (0x78048880#64, 0x0#64),
  (0x78048878#64, 0x0#64),
  (0x78048870#64, 0x0#64),
  (0x78048868#64, 0x0#64),
  (0x78048860#64, 0x0#64),
  (0x78048858#64, 0x0#64),
  (0x78048850#64, Layout.image.memAt 0x780003d8#64),
  (0x78048848#64, Layout.image.memAt 0x780002c0#64),
  (0x78048840#64, Layout.image.memAt 0x78000318#64),
  (0x78048838#64, Layout.image.memAt 0x780003c8#64),
  (0x78048830#64, 0x1#64),
  (0x78040620#64, 0x0#64),
  (0x78048720#64, 0x400000000000#64),
  (0x78048828#64, 0x80000000#64),
  (0x78048998#64, 0x0#64),
  (0x78048990#64, 0x0#64),
  (0x78044598#64, 0x78048980#64),
  (0x1bffffffe8#64, 0x78048980#64),
  (0x1bffffffe0#64, 0x23#64),
  (0x78048988#64, 0x0#64),
  (0x78048980#64, 0x1b87fb7660#64),
  (0x78040620#64, 0xffffffffffffffff#64),
  (0x77ffffd0#64, 0x0#64),
  (0x77ffffd8#64, 0x0#64),
  (0x77ffffe0#64, 0x0#64),
  (0x77ffffe8#64, 0x7801be44#64),
  (0x77fffff8#64, 0x7801bcec#64)]

/-- Memory at `main`'s entry: the image, with the run's stores. -/
noncomputable def initMem (a : Word) : Word := (stores.lookup a).getD (Layout.image.memAt a)

/-- `main`'s entry state, for input `input`: the code is the image's, `ra` returns into
    `__start` (which halts with `main`'s result), `sp` and `gp` are `_start`'s, memory is
    `initMem`, and the input stream is untouched. -/
def MainEntry (input : List (BitVec 8)) (t : MachineState) : Prop :=
  t.pc = 0x78019ff4#64 ∧ t.code = C ∧ t.getReg .x1 = 0x7801bea0#64 ∧
    t.getReg .x2 = 0x77fffff0#64 ∧ t.getReg .x3 = 0x78000800#64 ∧
    (∀ a, t.getMem a = initMem a) ∧ t.privateInput = input

/-! ## The protected regions are not written -/

/-- A key of a protected region lies near one of the three. -/
theorem prot_range {a : Word} (hp : Contract.env.InProt a) :
    (0x78000190 < a.toNat + 8 ∧ a.toNat < 0x78015938) ∨
      (0x78048920 < a.toNat + 8 ∧ a.toNat < 0x78048928) ∨
      (0x78048948 < a.toNat + 8 ∧ a.toNat < 0x78048960) := by
  obtain ⟨R, hR, hh⟩ := hp
  simp only [Contract.env, List.mem_cons, List.mem_nil_iff, or_false] at hR
  have := a.isLt
  rcases hR with rfl | rfl | rfl <;> simp only [Hits] at hh <;> bv_omega

theorem lookup_cons_getD {a d : Word} {p : Word × Word} {l : List (Word × Word)} :
    ((p :: l).lookup a).getD d = if a = p.1 then p.2 else (l.lookup a).getD d := by
  by_cases h : a = p.1
  · subst h; simp [List.lookup]
  · have hne : (a == p.1) = false := by simpa using h
    simp [List.lookup, hne, h]

theorem lookup_none {a : Word} {l : List (Word × Word)} (h : ∀ p ∈ l, a ≠ p.1) :
    l.lookup a = none := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hne : (a == p.1) = false := by simpa using h p (List.mem_cons_self ..)
    simp only [List.lookup, hne]
    exact ih fun q hq => h q (List.mem_cons_of_mem _ hq)

/-- Near a protected region, as a test. -/
def nearProt (a : Word) : Bool :=
  (decide (0x78000190 < a.toNat + 8) && decide (a.toNat < 0x78015938)) ||
    (decide (0x78048920 < a.toNat + 8) && decide (a.toNat < 0x78048928)) ||
    (decide (0x78048948 < a.toNat + 8) && decide (a.toNat < 0x78048960))

theorem stores_far : (stores.map Prod.fst).all (fun k => !nearProt k) = true := by
  decide +kernel

/-- No store of the run reaches a protected key. -/
theorem stores_not_prot {a : Word} (hp : Contract.env.InProt a) : stores.lookup a = none := by
  have hr : nearProt a = true := by
    have := prot_range hp
    simp only [nearProt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
  apply lookup_none
  intro p hp' he
  have := List.all_eq_true.mp stores_far p.1 (List.mem_map_of_mem hp')
  rw [← he, hr] at this
  cases this

/-! ## D1: from the loaded image to `main` -/

/-- **D1.** The guest, as the zkVM loads it, runs `_start` and `__start` — the allocator
    gets the arena `[_end, 7 << 34)` as one free block, the public-values hasher is set up —
    and enters `main` in `MainEntry`. Whatever is safe from every such entry is safe from
    the load. -/
theorem entry (input : List (BitVec 8)) {G : MachineState → Prop}
    {P : Prop} {n : Nat} (hk : ∀ t, MainEntry input t → SafeN G n P t) : SafeN G n P (Layout.image.state input) := by
  have hcode : (Layout.image.state input).code = C := rfl
  have hpc : (Layout.image.state input).pc = 0x7801bcd0#64 := rfl
  rw [← setPC_self hpc]
  iterate 7 xs start_code
  iterate 4 xs startF_code
  iterate 11 xs initF_code
  repeat (first | xs heapInitF_code | xs dumpF_code | xs startF_code)
  repeat (first | xs Memset.code | xs startF_code)
  refine hk _ ⟨rfl, ?_, ?_, ?_, ?_, fun a => ?_, ?_⟩
  · simp only [MachineState.code_setReg, MachineState.code_setPC, MachineState.code_setMem]
    exact hcode
  all_goals try xregs
  rotate_left
  · simp only [MachineState.privateInput_setReg, MachineState.privateInput_setMem,
      MachineState.privateInput_setPC]
    rfl
  simp only [MachineState.getMem_setReg, MachineState.getMem_setPC, getMem_setMem,
    getMem_load, initMem, stores, lookup_cons_getD, List.lookup_nil, Option.getD_none]
  rfl

/-! ## What `MainEntry` gives -/

/-- `.rodata` and the protected statics hold their load values at `main`'s entry. -/
theorem MainEntry.prot {input : List (BitVec 8)} {t : MachineState} (h : MainEntry input t) {a : Word}
    (hp : Contract.env.InProt a) : t.getMem a = Contract.env.init a := by
  rw [h.2.2.2.2.2.1 a, initMem, stores_not_prot hp]
  rfl

/-- Neither hook is installed at `main`'s entry (C3's `HooksUnset`). -/
theorem MainEntry.hooksUnset {input : List (BitVec 8)} {t : MachineState} (h : MainEntry input t) : Statics.HooksUnset t :=
  ⟨fun _ hal hm => (h.prot (Env.inProt_of_mem Statics.allocHook_prot hm)).trans
      (Statics.allocHook_zero hal hm),
   fun _ hal hm => (h.prot (Env.inProt_of_mem Statics.panicHook_prot hm)).trans
      (Statics.panicHook_zero hal hm)⟩

/-- The arena's one free block: its header holds its size, `0x1b87fb7660` bytes, and the
    end sentinel `0x23` points back at it; its size class's list head is the block. -/
theorem MainEntry.heap {input : List (BitVec 8)} {t : MachineState} (h : MainEntry input t) :
    t.getMem 0x78048980#64 = 0x1b87fb7660#64 ∧ t.getMem 0x1bffffffe0#64 = 0x23#64 ∧
    t.getMem 0x1bffffffe8#64 = 0x78048980#64 ∧ t.getMem 0x78044598#64 = 0x78048980#64 ∧
    t.getMem 0x78040620#64 = 0#64 := by
  have hm := h.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [hm]
    rfl

end Cases.Zip2005.Runtime.Entry
