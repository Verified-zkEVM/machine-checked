/-
  MachineChecked.RiscV.Load

  A total, kernel-evaluable loader: the machine state an SP1 guest starts in, built from an
  image given as data.

  riscv-zkvm's own `Interpreter.load` builds hash maps in an imperative loop, so nothing can
  be proved about its result; zip-2005-asm therefore checked predicates on it with compiled
  code (`check-load`). Here the loader is a definition, facts about the loaded state are
  kernel-checked theorems, and the remaining glue is narrower: `gen-image` checks, entry by
  entry, that this loader and riscv-zkvm's agree on the ELF it read.

  The semantics mirror `Interpreter.load`:
    * code: every 4-aligned word of every executable segment, decoded by
      `Interpreter.decode`; a word that does not decode has no code entry;
    * memory: every doubleword of every segment (from its 8-aligned start to
      `vaddr + memsz`), little-endian; everything else reads as zero;
    * registers zero, `pc` the entry point.
-/

import RiscvZkvm.Rv64
import RiscvZkvm.Interpreter.Decode
import MachineChecked.RiscV.Image

namespace MachineChecked.RiscV

open RiscvZkvm.Rv64

/-- A run of 32-bit code words at `base`. -/
structure CodeChunk where
  base : Word
  words : List (BitVec 32)

/-- A run of doublewords at an 8-aligned `base`, then `zeros` zero doublewords (`.bss`). -/
structure DataChunk where
  base : Word
  words : List Word
  zeros : Nat := 0

/-- A loadable image: entry point, code chunks tiling the executable segments, data chunks
    covering every segment. -/
structure Image where
  entry : Word
  code : List CodeChunk
  data : List DataChunk

namespace CodeChunk

def lo (c : CodeChunk) : Nat := c.base.toNat
def hi (c : CodeChunk) : Nat := c.base.toNat + 4 * c.words.length

def word? (c : CodeChunk) (a : Word) : Option (BitVec 32) :=
  let d := (a - c.base).toNat
  if d % 4 = 0 then c.words[d / 4]? else none

end CodeChunk

def DataChunk.word? (c : DataChunk) (a : Word) : Option Word :=
  let d := (a - c.base).toNat
  if d % 8 = 0 then
    if d / 8 < c.words.length then c.words[d / 8]?
    else if d / 8 < c.words.length + c.zeros then some 0 else none
  else none

namespace Image

def codeAt (img : Image) (a : Word) : Option Instr :=
  (img.code.findSome? (·.word? a)).bind RiscvZkvm.Interpreter.decode

def memAt (img : Image) (a : Word) : Word :=
  (img.data.findSome? (·.word? a)).getD 0

/-- The state the guest starts in. -/
def state (img : Image) (input : List (BitVec 8) := []) : MachineState :=
  { regs := fun _ => 0, mem := img.memAt, code := img.codeAt, pc := img.entry,
    privateInput := input }

end Image

/-- Code chunks in increasing address order and disjoint. -/
def codeChain : List CodeChunk → Bool
  | c :: d :: rest => decide (c.hi ≤ d.lo) && codeChain (d :: rest)
  | _ => true

/-- The code chunks are sorted, disjoint, and below `2^64`: then reading an address finds
    the one chunk that holds it. Checked once per image by `decide`. -/
def Image.codeWF (img : Image) : Bool :=
  codeChain img.code && img.code.all (fun c => decide (c.hi ≤ 2 ^ 64))

/-! ## Reading a chunk back -/

theorem CodeChunk.lo_le_hi (c : CodeChunk) : c.lo ≤ c.hi := by
  simp [CodeChunk.lo, CodeChunk.hi]

theorem codeChain_tail {c : CodeChunk} {l : List CodeChunk} (h : codeChain (c :: l) = true) :
    codeChain l = true := by
  cases l with
  | nil => rfl
  | cons d rest => simp only [codeChain, Bool.and_eq_true] at h; exact h.2

/-- In a chain, every later chunk starts at or after an earlier one ends. -/
theorem codeChain_before {c : CodeChunk} {l : List CodeChunk} (h : codeChain (c :: l) = true) :
    ∀ d ∈ l, c.hi ≤ d.lo := by
  induction l generalizing c with
  | nil => simp
  | cons d rest ih =>
    simp only [codeChain, Bool.and_eq_true, decide_eq_true_eq] at h
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact h.1
    · have := ih h.2 e he
      have := d.lo_le_hi
      omega

/-- The `j`-th word of a chunk is what a sorted chunk list holds at `base + 4 j`. -/
theorem findSome_word {l : List CodeChunk} (hc : codeChain l = true)
    (hb : ∀ d ∈ l, d.hi ≤ 2 ^ 64) {k : Nat} {c : CodeChunk}
    (hk : l[k]? = some c) {j : Nat} (hj : j < c.words.length) :
    l.findSome? (·.word? (c.base + BitVec.ofNat 64 (4 * j))) = some c.words[j] := by
  induction l generalizing k with
  | nil => simp at hk
  | cons e rest ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      have hhi := hb e (List.mem_cons_self ..)
      simp only [CodeChunk.hi] at hhi
      have h4 : (BitVec.ofNat 64 (4 * j)).toNat = 4 * j := by
        rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
      have hd : (e.base + BitVec.ofNat 64 (4 * j) - e.base).toNat = 4 * j := by
        rw [BitVec.add_comm, BitVec.add_sub_cancel, h4]
      have hw : e.word? (e.base + BitVec.ofNat 64 (4 * j)) = some e.words[j] := by
        simp only [CodeChunk.word?]
        rw [hd]
        simp [hj]
      rw [List.findSome?_cons, hw]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      have hcm : c ∈ rest := List.mem_of_getElem? hk
      have hbefore := codeChain_before hc c hcm
      have hhi := hb c (List.mem_cons_of_mem _ hcm)
      simp only [CodeChunk.hi, CodeChunk.lo] at hbefore hhi
      have ha : (c.base + BitVec.ofNat 64 (4 * j)).toNat = c.base.toNat + 4 * j := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (a := 4 * j) (by omega)]
        apply Nat.mod_eq_of_lt; omega
      have hnone : e.word? (c.base + BitVec.ofNat 64 (4 * j)) = none := by
        simp only [CodeChunk.word?]
        split
        · apply List.getElem?_eq_none
          rw [BitVec.toNat_sub, ha]
          have := e.base.isLt
          rw [show 2 ^ 64 - e.base.toNat + (c.base.toNat + 4 * j) =
              2 ^ 64 + (c.base.toNat + 4 * j - e.base.toNat) by omega,
            Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
          omega
        · rfl
      rw [List.findSome?_cons, hnone]
      exact ih (codeChain_tail hc) (fun d hd => hb d (List.mem_cons_of_mem _ hd)) hk

/-- **Code read-back.** In a well-formed image, the code at `base + 4 j` of the `k`-th chunk
    is the decoding of its `j`-th word. -/
theorem Image.codeAt_chunk {img : Image} (hwf : img.codeWF = true) {k : Nat} {c : CodeChunk}
    (hk : img.code[k]? = some c) {j : Nat} (hj : j < c.words.length) :
    img.codeAt (c.base + BitVec.ofNat 64 (4 * j)) = RiscvZkvm.Interpreter.decode c.words[j] := by
  simp only [Image.codeWF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  simp [Image.codeAt, findSome_word hwf.1 hwf.2 hk hj]

/-- A function's decoded program is in the loaded code, given its chunk and the
    kernel-checked decoding of its words. -/
theorem Image.codeAt_prog {img : Image} (hwf : img.codeWF = true) {k : Nat} {base : Word}
    {ws : List (BitVec 32)} (hk : img.code[k]? = some ⟨base, ws⟩) {prog : List (Option Instr)}
    (hdec : decodeWords ws = prog) {j : Nat} {ins : Instr} (hj : prog[j]? = some (some ins)) :
    img.codeAt (base + BitVec.ofNat 64 (4 * j)) = some ins := by
  subst hdec
  simp only [decodeWords, List.getElem?_map, Option.map_eq_some_iff] at hj
  obtain ⟨w, hw, hdw⟩ := hj
  have hlt : j < ws.length := (List.getElem?_eq_some_iff.mp hw).1
  rw [Image.codeAt_chunk (c := ⟨base, ws⟩) hwf hk hlt]
  rw [List.getElem?_eq_some_iff] at hw
  obtain ⟨_, rfl⟩ := hw
  exact hdw

/-! ## Reading data back -/

namespace DataChunk

def lo (c : DataChunk) : Nat := c.base.toNat
/-- Its doublewords, `.bss` included. -/
def size (c : DataChunk) : Nat := c.words.length + c.zeros
def hi (c : DataChunk) : Nat := c.base.toNat + 8 * c.size

/-- The doubleword at `base + 8 j`: a stored word, then zeros. -/
def wordAt (c : DataChunk) (j : Nat) : Word := c.words.getD j 0

theorem word?_outside {c : DataChunk} (hhi : c.hi ≤ 2 ^ 64) {a : Word}
    (h : a.toNat < c.lo ∨ c.hi ≤ a.toNat) : c.word? a = none := by
  simp only [hi, lo, size] at hhi h
  have hd : c.words.length + c.zeros ≤ (a - c.base).toNat / 8 := by
    rw [BitVec.toNat_sub]
    have := c.base.isLt
    have := a.isLt
    rcases h with h | h
    · rw [show 2 ^ 64 - c.base.toNat + a.toNat = 2 ^ 64 - (c.base.toNat - a.toNat) by omega,
        Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [show 2 ^ 64 - c.base.toNat + a.toNat = 2 ^ 64 + (a.toNat - c.base.toNat) by omega,
        Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      omega
  simp only [word?]
  split
  · rw [if_neg (by omega), if_neg (by omega)]
  · rfl

theorem word?_at {c : DataChunk} (hhi : c.hi ≤ 2 ^ 64) {j : Nat} (hj : j < c.size) :
    c.word? (c.base + BitVec.ofNat 64 (8 * j)) = some (c.wordAt j) := by
  simp only [hi, size] at hhi hj
  have h8 : (BitVec.ofNat 64 (8 * j)).toNat = 8 * j := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  have hd : (c.base + BitVec.ofNat 64 (8 * j) - c.base).toNat = 8 * j := by
    rw [BitVec.add_comm, BitVec.add_sub_cancel, h8]
  simp only [word?, hd, wordAt]
  rw [if_pos (by omega), show 8 * j / 8 = j by omega]
  by_cases hw : j < c.words.length
  · rw [if_pos hw, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw]; rfl
  · rw [if_neg hw, if_pos (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega)]; rfl

end DataChunk

/-- Data chunks in increasing address order and disjoint. -/
def dataChain : List DataChunk → Bool
  | c :: d :: rest => decide (c.hi ≤ d.lo) && dataChain (d :: rest)
  | _ => true

/-- The data chunks are sorted, disjoint, 8-aligned and below `2^64`. Checked once per image
    by `decide`. -/
def Image.dataWF (img : Image) : Bool :=
  dataChain img.data && img.data.all (fun c => decide (c.lo % 8 = 0) && decide (c.hi ≤ 2 ^ 64))

theorem DataChunk.lo_le_hi (c : DataChunk) : c.lo ≤ c.hi := by
  simp [DataChunk.lo, DataChunk.hi]

theorem dataChain_tail {c : DataChunk} {l : List DataChunk} (h : dataChain (c :: l) = true) :
    dataChain l = true := by
  cases l with
  | nil => rfl
  | cons d rest => simp only [dataChain, Bool.and_eq_true] at h; exact h.2

theorem dataChain_before {c : DataChunk} {l : List DataChunk} (h : dataChain (c :: l) = true) :
    ∀ d ∈ l, c.hi ≤ d.lo := by
  induction l generalizing c with
  | nil => simp
  | cons d rest ih =>
    simp only [dataChain, Bool.and_eq_true, decide_eq_true_eq] at h
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact h.1
    · have := ih h.2 e he
      have := d.lo_le_hi
      omega

theorem findSome_data {l : List DataChunk} (hc : dataChain l = true)
    (hb : ∀ d ∈ l, d.hi ≤ 2 ^ 64) {k : Nat} {c : DataChunk}
    (hk : l[k]? = some c) {j : Nat} (hj : j < c.size) :
    l.findSome? (·.word? (c.base + BitVec.ofNat 64 (8 * j))) = some (c.wordAt j) := by
  induction l generalizing k with
  | nil => simp at hk
  | cons e rest ih =>
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      rw [List.findSome?_cons, DataChunk.word?_at (hb e (List.mem_cons_self ..)) hj]
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk
      have hcm : c ∈ rest := List.mem_of_getElem? hk
      have hbefore := dataChain_before hc c hcm
      have hhi := hb c (List.mem_cons_of_mem _ hcm)
      simp only [DataChunk.hi, DataChunk.lo, DataChunk.size] at hbefore hhi hj
      have ha : (c.base + BitVec.ofNat 64 (8 * j)).toNat = c.base.toNat + 8 * j := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (a := 8 * j) (by omega)]
        apply Nat.mod_eq_of_lt; omega
      have hnone : e.word? (c.base + BitVec.ofNat 64 (8 * j)) = none := by
        apply DataChunk.word?_outside (hb e (List.mem_cons_self ..))
        right; simp only [DataChunk.hi, DataChunk.size] at hbefore ⊢; omega
      rw [List.findSome?_cons, hnone]
      exact ih (dataChain_tail hc) (fun d hd => hb d (List.mem_cons_of_mem _ hd)) hk

/-- **Data read-back.** In a well-formed image, the doubleword at `base + 8 j` of the `k`-th
    data chunk is its `j`-th word, or zero in its `.bss` tail. -/
theorem Image.memAt_chunk {img : Image} (hwf : img.dataWF = true) {k : Nat} {c : DataChunk}
    (hk : img.data[k]? = some c) {j : Nat} (hj : j < c.size) :
    img.memAt (c.base + BitVec.ofNat 64 (8 * j)) = c.wordAt j := by
  simp only [Image.dataWF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  simp [Image.memAt, findSome_data hwf.1 (fun d hd => (hwf.2 d hd).2) hk hj]

/-- Outside every data chunk, the loaded memory reads zero. -/
theorem Image.memAt_outside {img : Image} (hwf : img.dataWF = true) {a : Word}
    (h : ∀ c ∈ img.data, a.toNat < c.lo ∨ c.hi ≤ a.toNat) : img.memAt a = 0 := by
  simp only [Image.dataWF, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  have : img.data.findSome? (·.word? a) = none := by
    rw [List.findSome?_eq_none_iff]
    intro c hc
    exact DataChunk.word?_outside (hwf.2 c hc).2 (h c hc)
  simp [Image.memAt, this]

end MachineChecked.RiscV
