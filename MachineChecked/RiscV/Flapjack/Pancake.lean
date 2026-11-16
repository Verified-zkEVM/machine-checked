/-
  MachineChecked.RiscV.Flapjack.Pancake

  A Flapjack image as a Pancake program: lift 2 (`Logical/Lift.lean`) in the image's
  execution environment.

  The Pancake program is compiled by Flapjack and installed as any image is
  (`Flapjack/Image.lean`), so it runs in the layout the image expects, with its own code,
  bitmaps and stack where the image's would be. `env` puts the image back in place inside it:

  * The image's heap and stack are the first and second halves of the new program's heap,
    which the new program uses only at its very top, for its globals (`reserved`); its own
    stack is elsewhere. So memory needs no translation, and a pointer the image shows the
    world is the pointer it showed before. The image gets `a1`, `a2` and `a3` for these, and
    half the heap and half the stack it had.
  * The image's bitmaps are written where bitmaps go, over the new program's own, and the
    five words at the start of the heap are the image's. The new program has read its own
    by the time `main` runs.
  * `halt` ends the program if `a0 = 0`; otherwise the image ran out of memory, which the
    new program cannot do on demand, so it loops (running out of memory promises nothing of
    what follows). FFI function `i` is the Pancake call `@name(a0, a1, a2, a3)`.

  Nothing is proved here. It is checked by running (`Tools/README.md`, `decompile`).

  ## Main definitions

  * `Image.env`, `Image.toPancake`
-/

import MachineChecked.Logical.Lift
import MachineChecked.RiscV.Flapjack.Image

namespace MachineChecked.RiscV.Flapjack

open RiscvZkvm.Rv64 MachineChecked.Lprog MachineChecked.RiscV.Lprog MachineChecked.Logical
open MachineChecked.Logical.Lift (gvar num gset add seq when wrong)

/-- The size of the heap the image gets, and of its stack: half the heap each. -/
def half : Nat := 0x200000

/-- Kept at the top of the heap for the new program's own globals, which Flapjack puts
    there: the registers and the lift's few variables. -/
def reserved : Nat := 4096

private def reg (r : Reg) : String := RegText.name r

namespace Image

variable (img : Image)

/-- **The environment of an image, for lift 2.** -/
def env : Env where
  regs := [reg .x1, reg .x10, reg .x11, reg .x12, reg .x13]
  init :=
    (img.bitmaps.zipIdx.map fun (w, k) =>
      .store (.const (bitmapBase + BitVec.ofNat 64 (8 * k))) (.const w)) ++
    (img.heapHeader.zipIdx.map fun (w, k) => .store (add .baseAddr (num (8 * k))) (.const w)) ++
    [gset (reg .x10) (.const codeBase),
     gset (reg .x11) .baseAddr,
     gset (reg .x12) (add .baseAddr (num half)),
     gset (reg .x13) (add .baseAddr (num (2 * half - reserved)))]
  ext n stop :=
    if n = haltEntry then
      some (seq [when (.cmp .equal (gvar (reg .x10)) (num 0)) [stop], wrong])
    else if 2 ≤ n then
      img.ffiNames[n - 2]?.map fun name =>
        .extCall name (gvar (reg .x10)) (gvar (reg .x11)) (gvar (reg .x12)) (gvar (reg .x13))
    else none

/-- **The image as a Pancake program.** -/
def toPancake : Except String (List (_root_.Flapjack.Decl Pancake.W)) :=
  Logical.lift img.env allRegs img.lift

end Image

end MachineChecked.RiscV.Flapjack
