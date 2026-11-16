/-
  MachineChecked.Logical.Guest

  What the environments of whole programs share, for lift 2 (`Lift.lean`): installing a
  program's memory, giving up, and a system call as an FFI call.

  * **Memory.** The Pancake program reads and writes the program's addresses as they are, so
    a pointer the program shows the world is the pointer it showed before, and nothing is
    translated. The machine that runs the Pancake program must therefore give it a heap that
    covers the program's address space, with Pancake's own stack and globals outside what the
    program uses. `inits` writes the words the program loads, a few hundred to a function
    (`l_init0`, …); all other memory starts as zero.
  * **`wrong`** is `l_trap(n)`: the FFI call `@trap(n, 0, 0, 0)`, then a loop. The
    environment sees that the program gave up, and at which place, and nothing follows.
  * **A system call** (`syscall`) is one FFI call on four registers: the number and three
    arguments. The environment does the call, on the same memory, and leaves what the
    program is to read back in words at `scratch`, one for each register of `results`. After
    the call with number 0 the program ends: 0 is `HALT` for every environment here.

  SP1's environment is `RiscV/Sp1/Pancake.lean`; that of a program without an operating
  system, `bare`, is here, for AArch64 (`ARM/Bare.lean`) and x86-64.

  ## Main definitions

  * `inits`, `trap`, `trapFn`, `syscall`, `bare`, `Program`, `Program.toPancake`
-/

import MachineChecked.Logical.Lift
import Lprog.Linked

namespace MachineChecked.Logical.Guest

open Flapjack (Prog Decl)
open Pancake (W)
open Lift (gvar num gset seq when fn)

/-- Where the environment leaves the results of a system call: below anything a program
    here uses. -/
def scratch : Nat := 0x100

/-- The words one installing function writes. -/
def perInit : Nat := 256

/-- The functions that write a program's memory: each word at its address. -/
def inits (memory : List (W × W)) : List (Decl W) :=
  (Lift.runs perInit memory).zipIdx.map fun (ws, k) =>
    fn s!"l_init{k}" [] (seq ((ws.map fun (a, w) => .store (.const a) (.const w)) ++ [.return (num 0)]))

/-- The calls of those functions. -/
def install (memory : List (W × W)) : List (Prog W) :=
  (List.range (inits memory).length).map fun k => .call (some (none, none)) s!"l_init{k}" []

/-- Where a program goes `wrong`: a call of `l_trap`, which does not come back. -/
def trap (place : Nat) : Prog W := .call (some (none, none)) "l_trap" [num place]

/-- `l_trap(n)`: tell the environment the program gave up at place `n`, and go no further. -/
def trapFn : Decl W :=
  fn "l_trap" ["n"] <| seq
    [.extCall "trap" (Lift.var "n") (num 0) (num 0) (num 0), .while (num 1) .skip, .return (num 0)]

/-- **A system call**: the FFI function `name` on the registers `number`, `a`, `b` and `c`;
    the program ends after number 0, and otherwise reads `results` back from `scratch`. -/
def syscall (name number a b c : String) (results : List String) (stop : Prog W) : Prog W :=
  seq ([.extCall name (gvar number) (gvar a) (gvar b) (gvar c),
        when (.cmp .equal (gvar number) (num 0)) [stop]] ++
    results.zipIdx.map fun (r, k) => gset r (.load .one (num (scratch + 8 * k))))

/-- **The environment of a program without an operating system**: its memory, and the four
    system calls of `scripts/decompile-check/rust/src/bare.rs` as the FFI function `syscall`,
    with the result in `result`. The registers start as zero. -/
def bare (memory : List (W × W)) (number a b c result : String) : Env where
  regs := [number, a, b, c, result]
  init := install memory
  decls := trapFn :: inits memory
  wrong := trap
  ext n stop := if n = 0 then some (syscall "syscall" number a b c [result] stop) else none

/-- **A linked program as it is loaded**: its functions, where it starts, and the words it
    loads, each at an address that is a multiple of eight. `I` is its instructions. -/
structure Program (I : Type) where
  fns : List (Lprog.Linked.Fun I)
  entry : W
  memory : List (W × W)

/-- **A loaded program as a Pancake program**, and the places where it may give up: lift 2
    of its lift `p`, from the function at its entry. -/
def Program.toPancake {I Reg : Type} [Lprog.RegText Reg] (g : Program I) (env : Env)
    (regs : List Reg) (link sp : Reg) (p : Lprog.Lprog (Lprog.Op Reg) Reg) :
    Except String (List (Decl W) × List String) := do
  let some entry := g.fns.findIdx? (·.addr == g.entry) | throw "the entry of the ELF is no function of it"
  lift env regs link sp entry p

end MachineChecked.Logical.Guest
