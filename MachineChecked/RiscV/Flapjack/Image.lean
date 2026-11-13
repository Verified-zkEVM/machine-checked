/-
  MachineChecked.RiscV.Flapjack.Image

  A RISC-V binary from Flapjack, the Pancake compiler, and where it runs.

  Flapjack's output is code bytes, the stack-frame bitmaps beside them, and the names of the
  FFI functions the code calls. It is not an ELF: it is installed by CakeML's convention
  (`isRiscvMachineConfig` and `panInstalled` in Flapjack), which this file fixes as one
  layout, the one of flapjack-flip's machine:

  | what | where |
  | --- | --- |
  | code | `codeBase` |
  | entry `n` of the environment | `codeBase - 16 * (n + 1)`: halt, cache clear, then the FFI functions |
  | bitmaps | `bitmapBase` |
  | heap, then stack | `heapStart`, `stackStart` to `stackEnd` |
  | registers at entry | `a0 = codeBase`, `a1 = heapStart`, `a2 = stackStart`, `a3 = stackEnd` |

  The first five words of the heap hold the pointers `panInstalled` asks for (`heapHeader`).

  The code reaches its environment by jumping to an entry: at `halt` the run ends, a success
  if `a0 = 0`; at FFI function `i` the bytes `[a0, a0 + a1)` and `[a2, a2 + a3)` go to the
  function, which may rewrite the second, and the run goes on at `ra`.

  The image as Lprog is `Image.lift`, by the lift of code without functions
  (`RiscV/Lprog/Flat.lean`). Its meaning as an execution context (`Lprog.Context`) is not
  defined yet: `rvIsa` reads memory behind SP1's check, which this layout does not pass.

  ## Main definitions

  * `Image`, `Image.code`, `Image.lift`
-/

import RiscvZkvm.Interpreter.Decode
import MachineChecked.RiscV.Lprog.Flat

namespace MachineChecked.RiscV.Flapjack

open RiscvZkvm.Rv64 MachineChecked.Lprog MachineChecked.RiscV.Lprog

/-- A Flapjack binary: the FFI names in index order, the bitmaps and the code. -/
structure Image where
  ffiNames : List String
  bitmaps : List Word
  code : List (BitVec 8)
  deriving DecidableEq, Repr

def codeBase : Word := 0x80010000
def bitmapBase : Word := 0xa0000000
def heapStart : Word := 0xa0100000
def stackStart : Word := 0xa0500000
def stackEnd : Word := 0xa0900000

/-- The entries of the environment: `halt`, the cache clear, then FFI function `i` at
    `ffi i`. -/
def haltEntry : Nat := 0
def ffiEntry (i : Nat) : Nat := i + 2

/-- The entry at an address: entry `n` is `16 * (n + 1)` bytes below the code. -/
def entryAt (a : Word) : Option Nat :=
  let d := (codeBase - a).toNat
  if a < codeBase ∧ d % 16 = 0 then some (d / 16 - 1) else none

namespace Image

variable (img : Image)

/-- The words of the code, little-endian. -/
def words : List (BitVec 32) :=
  (List.range (img.code.length / 4)).map fun k =>
    match (img.code.drop (4 * k)).take 4 with
    | [b0, b1, b2, b3] => b3 ++ b2 ++ b1 ++ b0
    | _ => 0

/-- The image as code without functions. -/
def code' : Code where
  base := codeBase
  prog := img.words.map RiscvZkvm.Interpreter.decode
  entry := entryAt

/-- The words `panInstalled` asks for at the start of the heap. -/
def heapHeader : List Word :=
  let bitmapEnd := bitmapBase + BitVec.ofNat 64 (8 * img.bitmaps.length)
  let codeEnd := codeBase + BitVec.ofNat 64 img.code.length
  [bitmapBase, bitmapEnd, bitmapEnd, codeEnd, codeEnd]

/-- **The image as an Lprog program**: one function. -/
def lift : Lprog (Op Reg) Reg := img.code'.liftFlat "image"

end Image

end MachineChecked.RiscV.Flapjack
