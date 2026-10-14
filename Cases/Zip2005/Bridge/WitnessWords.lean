import Cases.Zip2005.Witness.WitnessModel
import Cases.Zip2005.Main.MainAccept
import Cases.Zip2005.Bridge.InputBytes

/-!
# The witness struct's words as the input record's

`witness_visitor_spec` leaves `Ok(witness)` as `witW W V`: every struct byte from the stream words
`W`. When `W` is `read_vec_raw`'s window over the witness record `r` and `sk` is present (tag 1),
the eight `Bytes32` fields, `value` and `sk` in the struct are the record's words at their bincode
offsets (`wordsAt`).
-/

namespace Cases.Zip2005.Top

open RiscvZkvm.Rv64 Cases.Zip2005

set_option autoImplicit false

theorem inByte_shift (W : List Word) (o k : ℕ) : inByte W o k = inByte W 0 (o + k) := by
  simp only [inByte, Nat.zero_add]

section
variable (r : List (BitVec 8)) (J V : List Word) (hJ : 174 ≤ J.length)
  (hr : 297 ≤ r.length) (htag : r[0]! = 1#8)
include hJ hr

omit hr in
theorem rd (o k : ℕ) (h : o + k < r.length) (h' : o + k < 1392) :
    inByte (overlay (hintWords r) J) o k = r[o + k]! := by
  rw [inByte_shift, inByte_overlay r J _ h (by omega)]

include htag

theorem witO1_one : witO1 (overlay (hintWords r) J) = 33 := by
  unfold witO1 optLen
  rw [inByte_overlay r J 0 (by omega) (by omega), htag, if_pos rfl]

/-- A word of the eight `Bytes32` fields (struct words 128..159). -/
theorem witW_mid (n : ℕ) (h1 : 128 ≤ n) (h2 : n < 160) :
    (witW (overlay (hintWords r) J) V)[n]! =
      word8 r[8 * n - 991]! r[8 * n - 991 + 1]! r[8 * n - 991 + 2]! r[8 * n - 991 + 3]!
        r[8 * n - 991 + 4]! r[8 * n - 991 + 5]! r[8 * n - 991 + 6]! r[8 * n - 991 + 7]! := by
  have e : ∀ k, k < 8 → witByte (overlay (hintWords r) J) V (8 * n + k) = r[8 * n - 991 + k]! := by
    intro k hk
    simp only [witByte, witO1_one r J hJ hr htag]
    rw [if_neg (by omega), if_pos (by omega), rd r J hJ _ _ (by omega) (by omega)]
    exact congrArg (fun i => r[i]!) (by omega)
  have e0 := e 0 (by decide)
  rw [Nat.add_zero, Nat.add_zero] at e0
  rw [witW_getElem! _ _ n (by omega), e0, e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 7 (by decide)]

/-- One of the eight `Bytes32` fields: struct words `n`..`n+3` are the record's words at `8n - 991`. -/
theorem witW_field (n : ℕ) (h1 : 128 ≤ n) (h2 : n + 4 ≤ 160) :
    [(witW (overlay (hintWords r) J) V)[n]!, (witW (overlay (hintWords r) J) V)[n + 1]!,
      (witW (overlay (hintWords r) J) V)[n + 2]!, (witW (overlay (hintWords r) J) V)[n + 3]!] =
      wordsAt r (8 * n - 991) 4 := by
  rw [witW_mid r J V hJ hr htag n (by omega) (by omega), witW_mid r J V hJ hr htag (n + 1) (by omega) (by omega),
    witW_mid r J V hJ hr htag (n + 2) (by omega) (by omega), witW_mid r J V hJ hr htag (n + 3) (by omega) (by omega)]
  simp only [wordsAt, List.range_succ, List.range_zero, List.nil_append, List.cons_append, List.map_cons,
    List.map_nil]
  rw [show 8 * (n + 1) - 991 = 8 * n - 991 + 8 * 1 by omega, show 8 * (n + 2) - 991 = 8 * n - 991 + 8 * 2 by omega,
    show 8 * (n + 3) - 991 = 8 * n - 991 + 8 * 3 by omega]
  simp only [Nat.mul_zero, Nat.add_zero]

/-- `value`, struct word 160. -/
theorem witW_value : (witW (overlay (hintWords r) J) V)[160]! = (wordsAt r 289 1)[0]! := by
  have e : ∀ k, k < 8 → witByte (overlay (hintWords r) J) V (8 * 160 + k) = r[289 + k]! := by
    intro k hk
    simp only [witByte, witO1_one r J hJ hr htag]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), rd r J hJ _ _ (by omega) (by omega)]
    exact congrArg (fun i => r[i]!) (by omega)
  have e0 := e 0 (by decide)
  rw [Nat.add_zero, Nat.add_zero] at e0
  rw [witW_getElem! _ _ 160 (by omega), e0, e 1 (by decide), e 2 (by decide), e 3 (by decide), e 4 (by decide),
    e 5 (by decide), e 6 (by decide), e 7 (by decide)]
  simp [wordsAt]

omit hJ hr htag in
theorem witW_byte (W V : List Word) (m k : ℕ) (hm : m < 174) (hk : k < 8) :
    extractByte (witW W V)[m]! k = witByte W V (8 * m + k) := by
  rw [witW_getElem! _ _ m hm]
  interval_cases k <;> simp (disch := decide) only [byte_simp, Nat.add_zero]

/-- `sk`'s words: its 32 bytes start at struct byte `0x50d`, mid-word, and `main` reassembles them
(`skWord`). -/
theorem witW_sk (i : ℕ) (hi : i < 4) :
    skWord (witW (overlay (hintWords r) J) V)[161 + i]! (witW (overlay (hintWords r) J) V)[162 + i]! =
      (wordsAt r 1 4)[i]! := by
  have e : ∀ p, 0x50c < p → p < 0x52d → witByte (overlay (hintWords r) J) V p = r[p - 0x50c]! := by
    intro p h1 h2
    simp only [witByte, witOptByte]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
      inByte_overlay r J 0 (by omega) (by omega), htag, if_pos rfl, rd r J hJ 0 _ (by omega) (by omega), Nat.zero_add]
  unfold skWord
  rw [witW_byte _ _ _ _ (by omega) (by decide), witW_byte _ _ _ _ (by omega) (by decide),
    witW_byte _ _ _ _ (by omega) (by decide), witW_byte _ _ _ _ (by omega) (by decide),
    witW_byte _ _ _ _ (by omega) (by decide), witW_byte _ _ _ _ (by omega) (by decide),
    witW_byte _ _ _ _ (by omega) (by decide), witW_byte _ _ _ _ (by omega) (by decide)]
  rw [e _ (by omega) (by omega), e _ (by omega) (by omega), e _ (by omega) (by omega), e _ (by omega) (by omega),
    e _ (by omega) (by omega), e _ (by omega) (by omega), e _ (by omega) (by omega), e _ (by omega) (by omega)]
  rw [getElem!_pos _ i (by simp [wordsAt]; omega)]
  simp only [wordsAt, List.getElem_map, List.getElem_range]
  have c : ∀ a b : ℕ, a = b → r[a]! = r[b]! := by intro a b h; rw [h]
  rw [c (8 * (161 + i) + 5 - 1292) (1 + 8 * i) (by omega),
    c (8 * (161 + i) + 6 - 1292) (1 + 8 * i + 1) (by omega),
    c (8 * (161 + i) + 7 - 1292) (1 + 8 * i + 2) (by omega),
    c (8 * (162 + i) + 0 - 1292) (1 + 8 * i + 3) (by omega),
    c (8 * (162 + i) + 1 - 1292) (1 + 8 * i + 4) (by omega),
    c (8 * (162 + i) + 2 - 1292) (1 + 8 * i + 5) (by omega),
    c (8 * (162 + i) + 3 - 1292) (1 + 8 * i + 6) (by omega),
    c (8 * (162 + i) + 4 - 1292) (1 + 8 * i + 7) (by omega)]

omit hJ hr htag in
theorem inBytes_get (k : ℕ) (hk : k < r.length) : (inBytes r)[k]! = UInt8.ofBitVec r[k]! := by
  unfold inBytes
  rw [getElem!_pos _ k (by simpa using hk), List.getElem_map, getElem!_pos r k hk]

omit hJ hr htag in
theorem optSize_ofBitVec (b : BitVec 8) : optSize (UInt8.ofBitVec b) = optLen b := by
  unfold optSize optLen
  by_cases h : b = 1#8
  · subst h; rfl
  · rw [if_neg h, if_neg]
    intro h'
    exact h (by simpa using congrArg UInt8.toBitVec h')

omit hJ hr htag in
theorem optLen_pos (b : BitVec 8) : 1 ≤ optLen b := by unfold optLen; split <;> omega

omit hJ hr htag in
theorem optLen_le (b : BitVec 8) : optLen b ≤ 33 := by unfold optLen; split <;> omega

omit hJ hr htag in
theorem witO4_le (W : List Word) : witO4 W ≤ 1391 := by
  unfold witO4 witO3 witO2 witO1 optLen
  split <;> split <;> split <;> omega

omit hr htag in
/-- `negate`'s stream offset is `Decodes`' `negOff`. -/
theorem witO4_negOff (hs : inByte (overlay (hintWords r) J) 0 0 = 1#8)
    (hw : witO4 (overlay (hintWords r) J) + 1 ≤ r.length) :
    witO4 (overlay (hintWords r) J) = negOff (inBytes r) := by
  have h1 : witO1 (overlay (hintWords r) J) = 33 := by unfold witO1 optLen; rw [hs, if_pos rfl]
  unfold witO4 witO3 witO2 at hw ⊢
  rw [h1] at hw ⊢
  have p1 := optLen_pos (inByte (overlay (hintWords r) J) (33 + 1292) 0)
  have e1 : inByte (overlay (hintWords r) J) (33 + 1292) 0 = r[1325]! := by
    rw [rd r J hJ _ _ (by omega) (by omega)]
  rw [e1] at hw ⊢
  rw [e1] at p1
  have p2 := optLen_pos (inByte (overlay (hintWords r) J) (33 + 1292 + optLen r[1325]!) 0)
  have e2 : inByte (overlay (hintWords r) J) (33 + 1292 + optLen r[1325]!) 0 = r[1325 + optLen r[1325]!]! := by
    have := optLen_le r[1325]!
    rw [rd r J hJ (33 + 1292 + optLen r[1325]!) 0 (by omega) (by omega)]
    exact congrArg (fun i => r[i]!) (by omega)
  rw [e2] at hw ⊢
  unfold negOff
  rw [inBytes_get r 1325 (by omega), optSize_ofBitVec, inBytes_get r _ (by omega), optSize_ofBitVec]

omit htag in
/-- `sk`'s tag, struct byte `0x50c`. -/
theorem witW_skTag : extractByte (witW (overlay (hintWords r) J) V)[161]! 4 = r[0]! := by
  rw [witW_byte _ _ 161 4 (by decide) (by decide)]
  simp only [witByte, witOptByte]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide), if_pos (by decide),
    inByte_overlay r J 0 (by omega) (by omega)]

omit hr htag in
/-- `negate`, struct byte `0x56f`. -/
theorem witW_negate (hw : witO4 (overlay (hintWords r) J) + 1 ≤ r.length) :
    extractByte (witW (overlay (hintWords r) J) V)[173]! 7 = r[witO4 (overlay (hintWords r) J)]! := by
  have := witO4_le (overlay (hintWords r) J)
  rw [witW_byte _ _ 173 7 (by decide) (by decide)]
  simp only [witByte]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), rd r J hJ (witO4 (overlay (hintWords r) J)) 0 (by omega) (by omega), Nat.add_zero]

end

end Cases.Zip2005.Top
