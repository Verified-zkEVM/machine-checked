/-
  Pancake.Env

  What a program the decompiler writes assumes of the environment it runs in: the names it
  calls the environment by, the exception that ends it, and where the environment leaves the
  results of a system call. Lift 2 (`MachineChecked/Logical`, in the root package) writes its
  programs with these, so a proof about one names the same things.

  * The program starts at `main`. Its registers are global variables; the program's memory is
    its heap, at the addresses the original program used.
  * `trap(n, 0, 0, 0)` says the program gave up at place `n` (where the program it was
    decompiled from would go `wrong`); nothing follows it.
  * A system call is one foreign call on four words: `syscall` for a program without an
    operating system, `ecall` for an SP1 guest. Its results are words at `scratch`.
  * The program ends by raising `halt`.

  ## Main definitions

  * `main`, `trap`, `syscall`, `ecall`, `mark`, `halt`, `scratch`
-/

import Pancake.Basic

namespace Pancake

/-- The function the program starts at. -/
def main : String := "main"

/-- The foreign call that says where the program gave up. -/
def trap : String := "trap"

/-- The system call of a program without an operating system. -/
def syscall : String := "syscall"

/-- The system call of an SP1 guest. -/
def ecall : String := "ecall"

/-- A foreign call that does nothing but mark that it was reached; testing puts it where it
    changes a program (`scripts/decompile-check`). -/
def mark : String := "mark"

/-- The exception that ends the program. -/
def halt : String := "l_halt"

/-- Where the environment leaves the results of a system call, one word for each: below
    anything a decompiled program uses. -/
def scratch : Nat := 0x100

end Pancake
