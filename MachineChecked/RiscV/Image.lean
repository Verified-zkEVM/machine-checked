/-
  MachineChecked.RiscV.Image

  The RISC-V view of an image's code: runs of 32-bit encodings and their decoding by
  riscv-zkvm's own `decode`, the decoder `stepSp1` runs. Nothing here is a second
  disassembler.

  Two representations of a run of words, so their kernel cost can be compared:
  a `List (BitVec 32)` literal, and one `Nat` holding the words little-endian (word `i`
  at bits `[32 i, 32 i + 32)`), whose arithmetic the kernel does with GMP.
-/

import RiscvZkvm.Rv64
import RiscvZkvm.Interpreter.Decode

namespace MachineChecked.RiscV

open RiscvZkvm.Rv64

/-- The decoding of a run of encodings, word by word. -/
def decodeWords (ws : List (BitVec 32)) : List (Option Instr) :=
  ws.map RiscvZkvm.Interpreter.decode

/-- Word `i` of a run packed little-endian into one `Nat`. -/
def wordOfPacked (n i : Nat) : BitVec 32 :=
  BitVec.ofNat 32 (n >>> (32 * i))

/-- The first `len` words of a packed run. -/
def unpackWords (n len : Nat) : List (BitVec 32) :=
  (List.range len).map (wordOfPacked n)

/-- **Constant-time fetch.** Word `i` of the decoding of a packed run is the decoding of
    word `i`, which the kernel computes by one shift of the packed `Nat`. A generated module
    states `prog = decodeWords (unpackWords packed len)` once (`prog_packed`), and the
    symbolic executor fetches instruction `i` through this lemma instead of walking the
    literal `prog`. -/
theorem getElem!_decodeWords_unpack {n len i : Nat} (hi : i < len) {ins : Option Instr}
    (h : RiscvZkvm.Interpreter.decode (wordOfPacked n i) = ins) :
    (decodeWords (unpackWords n len))[i]! = ins := by
  subst h
  simp only [decodeWords, unpackWords, List.map_map]
  rw [getElem!_pos _ _ (by simpa using hi)]
  simp

end MachineChecked.RiscV
