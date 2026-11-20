/-
  Examples.Sp1Runtime.RiscV.Proofs

  Functions of an SP1 guest's runtime: every proof.

  * `Memcmp`: `memcmp`, for every length, to the machine.
  * `WriteVectored`: `write_vectored` of the guest's standard error, through `sys_write` and
    `syscall_write` to the system call, to the machine.
  * `Udivti3`: `__udivti3`, from a contract of `u128_div_rem`, which is assumed.
-/

import Examples.Sp1Runtime.RiscV.Memcmp
import Examples.Sp1Runtime.RiscV.WriteVectored
import Examples.Sp1Runtime.RiscV.Udivti3
