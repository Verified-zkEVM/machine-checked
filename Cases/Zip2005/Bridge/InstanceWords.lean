import Cases.Zip2005.Bridge.InputBytes
import Cases.Zip2005.Runtime.MemcpyMis
import Cases.Zip2005.Witness.InstanceVisitor

/-!
# The instance's words in `main`'s frame are the input record's

The instance visitor leaves `Ok(instance)` as `instW O W`: a tag byte, then the record's 128
bytes. `main` moves the struct through three `memcpy`s (113 bytes each, destination offsets
0, 0, 7) into its frame, where `rk` and `nf` are read as words 3–6 and 7–10. Byte `p` of that
frame block (24 ≤ p < 88) is byte `p + 8` of the record (`inst_chain_byte`), so those words are
`wordsAt r 32 4` and `wordsAt r 64 4` (`inst_words`).
-/

namespace Cases.Zip2005.Top

open RiscvZkvm.Rv64 Cases.Zip2005

set_option autoImplicit false

/-- Byte `p` of a word list. -/
def byteAt (A : List Word) (p : ℕ) : BitVec 8 := extractByte A[p / 8]! (p % 8)

theorem extractByte_word8_fn (f : ℕ → BitVec 8) (q k : ℕ) (hk : k < 8) :
    extractByte (word8 (f q) (f (q + 1)) (f (q + 2)) (f (q + 3)) (f (q + 4)) (f (q + 5)) (f (q + 6)) (f (q + 7))) k =
      f (q + k) := by
  interval_cases k <;> simp (disch := decide) only [byte_simp, Nat.add_zero]

theorem mcpyW_byte (D S : List Word) (d s n nw i k : ℕ) (hi : i < nw) (hk : k < 8) :
    extractByte (mcpyW D S d s n nw)[i]! k = mcByte D S d s n i k := by
  rw [mcpyW_getElem! D S d s n nw i hi]
  interval_cases k <;> simp (disch := decide) only [byte_simp]

/-- A copy, byte by byte. -/
theorem byteAt_mcpyW (D S : List Word) (d s n nw p : ℕ) (hp : p < 8 * nw) :
    byteAt (mcpyW D S d s n nw) p = if d ≤ p ∧ p < d + n then byteAt S (p - d + s) else byteAt D p := by
  unfold byteAt
  rw [mcpyW_byte D S d s n nw (p / 8) (p % 8) (by omega) (Nat.mod_lt _ (by decide))]
  unfold mcByte
  rw [Nat.div_add_mod p 8]

theorem byteAt_range_map (f : ℕ → Word) (n p : ℕ) (h : p / 8 < n) :
    byteAt ((List.range n).map f) p = extractByte (f (p / 8)) (p % 8) := by
  unfold byteAt
  rw [getElem!_pos _ _ (by simpa using h), List.getElem_map, List.getElem_range]

theorem instW_get (O W : List Word) (m : ℕ) (hm : m < 16) :
    (instW O W)[m]! = word8 (instByte W (8 * m)) (instByte W (8 * m + 1)) (instByte W (8 * m + 2))
      (instByte W (8 * m + 3)) (instByte W (8 * m + 4)) (instByte W (8 * m + 5)) (instByte W (8 * m + 6))
      (instByte W (8 * m + 7)) := by
  unfold instW
  rw [getElem!_pos _ _ (by simp; omega), List.getElem_append_left (by simp; omega), List.getElem_map, List.getElem_range]

/-- The struct's bytes 1..128 are the record's. -/
theorem byteAt_instW (O W : List Word) (p : ℕ) (hp : p < 128) (hp0 : 0 < p) :
    byteAt (instW O W) p = inByte W 0 (p - 1) := by
  unfold byteAt
  rw [instW_get O W (p / 8) (by omega), extractByte_word8_fn (instByte W) (8 * (p / 8)) (p % 8) (Nat.mod_lt _ (by decide)),
    Nat.div_add_mod p 8]
  unfold instByte
  rw [if_neg (by omega)]

theorem byteAt_overlay (r : List (BitVec 8)) (JL : List Word) (p : ℕ) (hp : p < r.length) (hJ : p / 8 < JL.length) :
    byteAt (overlay (hintWords r) JL) p = r[p]! := by
  have := inByte_overlay r JL p hp hJ
  unfold inByte at this
  rw [Nat.zero_add] at this
  exact this

/-- **Frame byte `p` is record byte `p + 8`**, through the three copies. -/
theorem inst_chain_byte (r : List (BitVec 8)) (JL O D27 D56 A27 A34 A56 : List Word)
    (hJL : JL.length = 175) (hr : 128 ≤ r.length)
    (h27 : mcpyW D27 ((List.range 15).map fun i =>
      (instW O ((List.range 16).map fun i => (overlay (hintWords r) JL)[i]!))[i + 2]!) 0 0 113 15 = A27)
    (h34 : mcpyW ((List.range 15).map fun i =>
        (instW O ((List.range 16).map fun i => (overlay (hintWords r) JL)[i]!))[i]!)
      ((List.range 15).map fun i => A27[i]!) 0 0 113 15 = A34)
    (h56 : mcpyW D56 ((List.range 15).map fun i => A34[i]!) 7 0 113 15 = A56)
    (p : ℕ) (hp : 24 ≤ p) (hp' : p < 88) :
    byteAt A56 p = r[p + 8]! := by
  rw [← h56, byteAt_mcpyW _ _ _ _ _ _ _ (by omega), if_pos (by omega), byteAt_range_map _ _ _ (by omega)]
  change byteAt A34 (p - 7 + 0) = _
  rw [← h34, byteAt_mcpyW _ _ _ _ _ _ _ (by omega), if_pos (by omega), byteAt_range_map _ _ _ (by omega)]
  change byteAt A27 (p - 7 + 0 - 0 + 0) = _
  rw [← h27, byteAt_mcpyW _ _ _ _ _ _ _ (by omega), if_pos (by omega), byteAt_range_map _ _ _ (by omega)]
  rw [show (p - 7 + 0 - 0 + 0 - 0 + 0) / 8 + 2 = (p + 9) / 8 by omega,
    show (p - 7 + 0 - 0 + 0 - 0 + 0) % 8 = (p + 9) % 8 by omega]
  change byteAt (instW O _) (p + 9) = _
  rw [byteAt_instW _ _ _ (by omega) (by omega)]
  unfold inByte
  rw [Nat.zero_add, show p + 9 - 1 = p + 8 by omega]
  change byteAt ((List.range 16).map fun i => (overlay (hintWords r) JL)[i]!) (p + 8) = _
  rw [byteAt_range_map _ _ _ (by omega)]
  change byteAt (overlay (hintWords r) JL) (p + 8) = _
  exact byteAt_overlay r JL _ (by omega) (by omega)

theorem word_of_bytes (A : List Word) (r : List (BitVec 8)) (w o : ℕ)
    (h : ∀ j, j < 8 → extractByte A[w]! j = r[o + j]!) :
    A[w]! = word8 r[o]! r[o + 1]! r[o + 2]! r[o + 3]! r[o + 4]! r[o + 5]! r[o + 6]! r[o + 7]! := by
  apply word_ext
  intro k hk
  rw [h k hk, extractByte_word8_fn (fun i => r[i]!) o k hk]

/-- **`rk` and `nf` in the frame are the record's words at 32 and 64.** -/
theorem inst_words (r : List (BitVec 8)) (JL O D27 D56 A27 A34 A56 : List Word)
    (hJL : JL.length = 175) (hr : 128 ≤ r.length)
    (h27 : mcpyW D27 ((List.range 15).map fun i =>
      (instW O ((List.range 16).map fun i => (overlay (hintWords r) JL)[i]!))[i + 2]!) 0 0 113 15 = A27)
    (h34 : mcpyW ((List.range 15).map fun i =>
        (instW O ((List.range 16).map fun i => (overlay (hintWords r) JL)[i]!))[i]!)
      ((List.range 15).map fun i => A27[i]!) 0 0 113 15 = A34)
    (h56 : mcpyW D56 ((List.range 15).map fun i => A34[i]!) 7 0 113 15 = A56) :
    [A56[3]!, A56[4]!, A56[5]!, A56[6]!] = wordsAt r 32 4 ∧
      [A56[7]!, A56[8]!, A56[9]!, A56[10]!] = wordsAt r 64 4 := by
  have hb : ∀ w j, 3 ≤ w → w < 11 → j < 8 → extractByte A56[w]! j = r[8 * w + 8 + j]! := by
    intro w j hw hw' hj
    have := inst_chain_byte r JL O D27 D56 A27 A34 A56 hJL hr h27 h34 h56 (8 * w + j) (by omega) (by omega)
    unfold byteAt at this
    rw [show (8 * w + j) / 8 = w by omega, show (8 * w + j) % 8 = j by omega, show 8 * w + j + 8 = 8 * w + 8 + j by omega] at this
    exact this
  simp only [wordsAt, List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil, Nat.mul_zero, Nat.add_zero]
  refine ⟨?_, ?_⟩ <;> simp only [List.cons.injEq, and_true] <;>
    refine ⟨word_of_bytes _ _ _ _ (fun j hj => hb _ j (by omega) (by omega) hj), ?_, ?_, ?_⟩ <;>
    exact word_of_bytes _ _ _ _ (fun j hj => hb _ j (by omega) (by omega) hj)

end Cases.Zip2005.Top
