import Cases.Zip2005.Witness.OptArrModel
import Cases.Zip2005.Witness.WitnessTailModel

/-!
# `Ok(Zip2005Witness)` as the visitor writes it

The bincode stream at the aligned words `W`: `sk: Option<Bytes32>` at offset 0, the eight
`Bytes32` fields, `value: u64`, `merkle_position: u32`, `auth_path: [Bytes32; 32]`,
`qk` and `sigma_qsk: Option<Bytes32>`, and `negate: bool`. An `Option` takes 1 byte (`None`) or 33.

The struct (1392 bytes, 174 words) is those fields in another order: `auth_path` (`0x000`), the
eight `Bytes32` (`0x400`), `value` (`0x500`), `merkle_position` (`0x508`), the three options as tag
byte plus 32 bytes (`sk` `0x50c`, `qk` `0x52d`, `sigma_qsk` `0x54e`), and `negate` (`0x56f`).
A `None`'s 32 payload bytes are whatever the frame held: the model takes them from `V`, the
written words themselves, so `V = witW W V` says exactly that every other byte is the input's.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 MachineChecked.RiscV.Sym

set_option autoImplicit false

/-- The size an `Option<Bytes32>` with tag byte `t` takes in the stream. -/
def optLen (t : BitVec 8) : Nat := if t = 1#8 then 33 else 1

/-- Stream offset of `alpha` (after `sk`). -/
def witO1 (W : List Word) : Nat := optLen (inByte W 0 0)

/-- Stream offset of `qk`'s tag. -/
def witO2 (W : List Word) : Nat := witO1 W + 1292

/-- Stream offset of `sigma_qsk`'s tag. -/
def witO3 (W : List Word) : Nat := witO2 W + optLen (inByte W (witO2 W) 0)

/-- Stream offset of `negate`. -/
def witO4 (W : List Word) : Nat := witO3 W + optLen (inByte W (witO3 W) 0)

/-- Byte `j` of an `Option<Bytes32>` field whose tag sits at stream offset `o`, at struct
offset `j` from its tag (`j < 33`); a `None` payload's from `V` at struct byte `p`. -/
def witOptByte (W V : List Word) (o j p : Nat) : BitVec 8 :=
  if j = 0 then inByte W o 0
  else if inByte W o 0 = 1#8 then inByte W o j else extractByte V[p / 8]! (p % 8)

/-- Struct byte `p` of `Ok(witness)`. -/
def witByte (W V : List Word) (p : Nat) : BitVec 8 :=
  if p < 0x400 then inByte W (witO1 W + 268) p
  else if p < 0x500 then inByte W (witO1 W) (p - 0x400)
  else if p < 0x50c then inByte W (witO1 W + 256) (p - 0x500)
  else if p < 0x52d then witOptByte W V 0 (p - 0x50c) p
  else if p < 0x54e then witOptByte W V (witO2 W) (p - 0x52d) p
  else if p < 0x56f then witOptByte W V (witO3 W) (p - 0x54e) p
  else inByte W (witO4 W) 0

/-- `Ok(witness)`: the 174 words. -/
def witW (W V : List Word) : List Word :=
  (List.range 174).map fun i => word8 (witByte W V (8 * i)) (witByte W V (8 * i + 1))
    (witByte W V (8 * i + 2)) (witByte W V (8 * i + 3)) (witByte W V (8 * i + 4))
    (witByte W V (8 * i + 5)) (witByte W V (8 * i + 6)) (witByte W V (8 * i + 7))

@[simp] theorem witW_length (W V : List Word) : (witW W V).length = 174 := by
  simp [witW]

theorem witW_getElem! (W V : List Word) (i : Nat) (h : i < 174) :
    (witW W V)[i]! = word8 (witByte W V (8 * i)) (witByte W V (8 * i + 1))
      (witByte W V (8 * i + 2)) (witByte W V (8 * i + 3)) (witByte W V (8 * i + 4))
      (witByte W V (8 * i + 5)) (witByte W V (8 * i + 6)) (witByte W V (8 * i + 7)) := by
  simp [witW, h]

/-- The input conditions under which the visitor returns `Ok`: each tag a valid `Option` /
`bool` and the stream long enough (`l` bytes from offset 0). -/
def witOkCond (W : List Word) (l : Nat) : Prop :=
  (inByte W 0 0).toNat < 2 ∧ (inByte W (witO2 W) 0).toNat < 2
    ∧ (inByte W (witO3 W) 0).toNat < 2 ∧ (inByte W (witO4 W) 0).toNat < 2
    ∧ witO4 W + 1 ≤ l

/-! ## From `value` on

What the visitor writes when it has read `sk` and the eight `Bytes32` and the rest is read from
the words `W` at an aligned `qb`, the stream at `qb + 1` (`value` at offset 1, `merkle_position`
9, `auth_path` 13, `qk`'s tag 1037): the fields already read come from the frame `Fr` and the
registers as the tail moves them (`tailByte`), the others from `W`. -/

/-- Offset in `W` of `sigma_qsk`'s tag. -/
def midO3 (W : List Word) : Nat := 1037 + optLen (inByte W 1037 0)

/-- Offset in `W` of `negate`. -/
def midO4 (W : List Word) : Nat := midO3 W + optLen (inByte W (midO3 W) 0)

/-- Where the fields read before the cut sit at the cut, as struct bytes: where the tail finds
them (`tailByte`), except bytes `0x4a6`..`0x4ad` of `g_d`, which are in `s11` (`x27`) at the cut
and spilled by the second part to frame word 6. -/
def cutByte (Fr : List Word) (r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word) (p : Nat) : BitVec 8 :=
  if 0x4a6 ≤ p ∧ p < 0x4ae then extractByte r27 (p - 0x4a6)
  else tailByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 p

/-- Struct byte `p` of `Ok(witness)` from the cut on. -/
def midByte (Fr : List Word) (r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word) (W V : List Word)
    (p : Nat) : BitVec 8 :=
  if p < 0x400 then inByte W 13 p
  else if p < 0x500 then cutByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 p
  else if p < 0x508 then inByte W 1 (p - 0x500)
  else if p < 0x50c then inByte W 9 (p - 0x508)
  else if p < 0x52d then cutByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 p
  else if p < 0x54e then witOptByte W V 1037 (p - 0x52d) p
  else if p < 0x56f then witOptByte W V (midO3 W) (p - 0x54e) p
  else inByte W (midO4 W) 0

/-- The 174 words, from the cut on. -/
def midW (Fr : List Word) (r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word) (W V : List Word) :
    List Word :=
  (List.range 174).map fun i =>
    word8 (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i))
      (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i + 1))
      (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i + 2))
      (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i + 3))
      (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i + 4))
      (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i + 5))
      (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i + 6))
      (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i + 7))

@[simp] theorem midW_length (Fr : List Word) (r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word)
    (W V : List Word) : (midW Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V).length = 174 := by
  simp [midW]

theorem midW_getElem! (Fr : List Word) (r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 : Word) (W V : List Word) (i : Nat)
    (h : i < 174) :
    (midW Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V)[i]! =
      word8 (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i))
        (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i + 1))
        (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i + 2))
        (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i + 3))
        (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i + 4))
        (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i + 5))
        (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i + 6))
        (midByte Fr r9 r18 r19 r20 r22 r23 r24 r25 r26 r27 W V (8 * i + 7)) := by
  simp [midW, h]

/-- When the reads from the cut on return `Ok`: `qk`, `sigma_qsk` and `negate` valid and the
`l` bytes from `qb + 1` enough. -/
def midOkCond (W : List Word) (l : Nat) : Prop :=
  (inByte W 1037 0).toNat < 2 ∧ (inByte W (midO3 W) 0).toNat < 2
    ∧ (inByte W (midO4 W) 0).toNat < 2 ∧ midO4 W ≤ l

/-- A cell of the frame as the second part takes it: 17 words, the sequence access `[de, c]`,
315 words. -/
theorem frame3_getElem! (Fr1 Fr2 : List Word) (de c : Word) (h : Fr1.length = 17) (k : Nat) :
    (Fr1 ++ [de, c] ++ Fr2)[k]! =
      if k < 17 then Fr1[k]! else if k = 17 then de else if k = 18 then c else Fr2[k - 19]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.append_assoc]
  split_ifs with h1 h2 h3
  · rw [List.getElem?_append_left (by omega)]
  · subst h2
    rw [List.getElem?_append_right (by omega), h]
    rfl
  · subst h3
    rw [List.getElem?_append_right (by omega), h]
    rfl
  · rw [List.getElem?_append_right (by omega), h, List.getElem?_append_right (by simp; omega)]
    simp only [List.length_cons, List.length_nil]
    congr 2

attribute [byte_simp] cutByte midByte midW_getElem! witOptByte optLen midO3 midO4
attribute [byte_pre ↓] cutByte midByte midW_getElem! witOptByte

end Cases.Zip2005
