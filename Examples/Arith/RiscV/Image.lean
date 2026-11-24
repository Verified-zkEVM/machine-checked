/-
  Examples.Arith.RiscV.Image

  Written by `decompile --to lean`: every module of it. The functions, by index (`f<i>`, `f<i>_eq`):

  * `F0`: "sdiv", at 0x1000
  * `F1`: "srem", at 0x1014
  * `F2`: "udiv", at 0x1020
  * `F3`: "mulhi", at 0x1034
  * `F4`: "smulhi", at 0x103c
  * `F5`: "rotl", at 0x105c
  * `F6`: "popcount", at 0x1070
  * `F7`: "abs_branchless", at 0x1090
  * `F8`: "_start", at 0x10b4

  Symbols of code that are not functions of `fns`:

  * "add32: `ADDW` at 0x1044, a 32-bit operation riscv-zkvm's machine does not run: the `--proved` lift does not take it (`--to lprog` without `--proved` does)"
  * "shl32: `SLLW` at 0x104c, a 32-bit operation riscv-zkvm's machine does not run: the `--proved` lift does not take it (`--to lprog` without `--proved` does)"
  * "sra32: `SRAW` at 0x1054, a 32-bit operation riscv-zkvm's machine does not run: the `--proved` lift does not take it (`--to lprog` without `--proved` does)"
  * "div32: `DIVW` at 0x10a4, a 32-bit operation riscv-zkvm's machine does not run: the `--proved` lift does not take it (`--to lprog` without `--proved` does)"
-/

import Examples.Arith.RiscV.Image.F0
import Examples.Arith.RiscV.Image.F1
import Examples.Arith.RiscV.Image.F2
import Examples.Arith.RiscV.Image.F3
import Examples.Arith.RiscV.Image.F4
import Examples.Arith.RiscV.Image.F5
import Examples.Arith.RiscV.Image.F6
import Examples.Arith.RiscV.Image.F7
import Examples.Arith.RiscV.Image.F8
