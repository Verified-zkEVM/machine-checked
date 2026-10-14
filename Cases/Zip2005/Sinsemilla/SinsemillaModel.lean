import Cases.Zip2005.Sinsemilla.IncompleteAdd
import Cases.Zip2005.Kit.RegionGlue
import Cases.Zip2005.Image.Ro

/-!
# The Sinsemilla hash as the guest computes it

The generator table `S` (1024 affine points) is read-only data at `0x78001968`, each entry
eight words: `x` then `y`, both in Montgomery form. `hash_to_point_inner` reads the entry of each
10-bit chunk, takes it out of Montgomery form (`pack`), and folds `acc ← (acc ⸭ S[m]) ⸭ acc` with
`incomplete_add` over canonical limbs, `⊥` (the tag word `0`) absorbing.
-/

namespace Cases.Zip2005

open RiscvZkvm.Rv64 RiscvZkvm.Rv64.Accel Cases.Zip2005.Image AsmVerif.RiscV.Sym

/-- Chunks `k, …, k + n - 1` of the read-only segment, concatenated. -/
def roChunksFrom (k : Nat) : Nat → List Word
  | 0 => []
  | n + 1 => roChunksFrom k n ++ Ro.layout.roChunk (k + n)

theorem roChunksFrom_length (k n : Nat) (hfull : ∀ i, i < n → (Ro.layout.roChunk (k + i)).length = 64) :
    (roChunksFrom k n).length = 64 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [roChunksFrom, List.length_append, ih (fun i hi => hfull i (by omega)),
      hfull n (by omega)]
    ring

theorem RoImage.chunksFrom {s : MachineState} (h : RoImage Ro.layout s) (k n : Nat) (hkn : k + n ≤ Ro.layout.roChunks)
    (hfull : ∀ i, i < n → (Ro.layout.roChunk (k + i)).length = 64) :
    Region (roChunkBase Ro.layout k) (roChunksFrom k n) s := by
  induction n with
  | zero => intro i hi; simp [roChunksFrom] at hi
  | succ n ih =>
    refine Region.append' (ih (by omega) (fun i hi => hfull i (by omega))) (h.get (k + n) (by omega)) ?_
    rw [roChunksFrom_length k n (fun i hi => hfull i (by omega))]
    unfold roChunkBase Ro.layout
    rw [← BitVec.ofNat_add]
    congr 1
    ring

/-- The Sinsemilla generator table: 1024 entries of eight words at `0x78001968`. -/
def sTable : List Word := ((roChunksFrom 12 129).drop 45).take 8192

theorem sTable_length : sTable.length = 8192 := by
  rw [sTable, List.length_take, List.length_drop, roChunksFrom_length 12 129 (by decide +kernel)]
  decide

theorem RoImage.sTable {s : MachineState} (h : RoImage Ro.layout s) : Region 0x78001968#64 sTable s :=
  (RoImage.chunksFrom h 12 129 (by decide) (by decide +kernel)).sub 45 8192 (by decide) rfl

theorem sTable_ok : RegionOk Ro.layout.textLo Ro.layout.textHi 0x78001968#64 8192 := ⟨by decide, by decide, Or.inl (by decide)⟩

/-- Entry `m` of the table as `pack` emits it: canonical limbs of `x`, then of `y`. -/
def sEntryW (T : List Word) (m : Nat) : List Word :=
  natToLeLimbs 4 (leLimbsToNat [T[8 * m]!, T[8 * m + 1]!, T[8 * m + 2]!, T[8 * m + 3]!] * Fp.rInv % Fp.p) ++
    natToLeLimbs 4 (leLimbsToNat [T[8 * m + 4]!, T[8 * m + 5]!, T[8 * m + 6]!, T[8 * m + 7]!] * Fp.rInv % Fp.p)

/-- `incomplete_add` on canonical limbs: `⊥` when the `x` coordinates agree. -/
def sinAdd (p q : List Word) : Option (List Word) :=
  if p.take 4 = q.take 4 then none else some (curveAddL Sp1.pallasP 4 p q)

/-- One chunk: `(acc ⸭ S[m]) ⸭ acc`, `⊥` absorbing. -/
def sinStep (T : List Word) (acc : Option (List Word)) (m : Nat) : Option (List Word) :=
  acc.bind fun a => (sinAdd a (sEntryW T m)).bind fun t => sinAdd t a

/-- The chunk fold from an accumulator. -/
def sinFold (T : List Word) (acc : Option (List Word)) (ms : List Nat) : Option (List Word) :=
  ms.foldl (sinStep T) acc

/-- Byte `o` of a byte string held as little-endian words. -/
def byteAt (ws : List Word) (o : Nat) : Word := BitVec.zeroExtend 64 (extractByte ws[o / 8]! (o % 8))

/-- Chunk `j` of a message of `0`/`1` bytes: bytes `10 j, …, 10 j + 9`, little-endian. -/
def chunkVal (ws : List Word) (j : Nat) : Nat :=
  (List.range 10).foldl (fun acc k => acc + (byteAt ws (10 * j + k)).toNat * 2 ^ k) 0

/-- The first `n` chunk values. -/
def chunks (ws : List Word) (n : Nat) : List Nat := (List.range n).map (chunkVal ws)

/-- The nine-word accumulator `(tag, limbs)` represents the model's `Option`: tag `0` is `⊥`
(limbs unconstrained), tag `1` carries the limbs. -/
def AccRep (m : Option (List Word)) (w : List Word) : Prop :=
  w.length = 9 ∧ (w[0]! = 0#64 ↔ m = none) ∧ ∀ L, m = some L → w = 1#64 :: L

theorem chunks_succ (ws : List Word) (n : Nat) : chunks ws (n + 1) = chunks ws n ++ [chunkVal ws n] := by
  simp [chunks, List.range_succ]

theorem sinFold_append (T : List Word) (acc : Option (List Word)) (ms : List Nat) (m : Nat) :
    sinFold T acc (ms ++ [m]) = sinStep T (sinFold T acc ms) m := by
  simp [sinFold, List.foldl_append]

end Cases.Zip2005
