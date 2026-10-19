/-
  Precompile -- the SP1 precompiles the guest calls, proved against
  mathematics.

  The guest calls three accelerator syscalls, modelled (and trusted) in
  `riscv-zkvm`'s `Rv64/Sp1Accel.lean`:

    UINT256_MUL   0x1011d  x := (x * y) mod m          `Cases.Zip2005.Precompile.uint256Mul_machine`
    PALLAS_ADD    0x10136  P := P + Q  (chord)          `Cases.Zip2005.Precompile.pallasAdd_machine`
    PALLAS_DOUBLE 0x00137  P := 2 • P  (tangent)        `Cases.Zip2005.Precompile.pallasDouble_machine`

  * `Cases.Zip2005.Precompile.Limbs`  -- the four-limb LE wire format as numbers.
  * `Cases.Zip2005.Precompile.PowMod` -- `Accel.powMod` is `b^e % m` below `2^512`; `invMod`
    is the field inverse.
  * `Cases.Zip2005.Precompile.Prime`  -- `Sp1.pallasP` is prime (Pratt certificate, kernel
    `decide` on the model's own `powMod`).
  * `Cases.Zip2005.Precompile.Pallas` -- `curveAdd`/`curveDbl` (and their limb forms) are
    Mathlib's group law on `y² = x³ + 5` over `ZMod pallasP`.
  * `Cases.Zip2005.Precompile.Sp1`    -- the three `sp1AccelWrite`/`sp1AccelValid` arms, the
    exact trap condition of each (`↔`), and the composed machine-level results.

  ## What the curve theorems assume that the model does not check

  **On-curve inputs.** `sp1AccelValid` checks only that coordinates are reduced
  and the `x₁ ≠ x₂` / `y ≠ 0` side conditions. Off the curve the model -- and
  the real executor, which applies the same formulas -- returns *something*,
  but not a group operation. The guest has to supply `OnCurve`.

  ## Faithfulness against the real precompile (audited 2026-09-25)

  Compared with `dmpierre/sp1` @ `f2328b4` (the fork the guest is built
  against; paths relative to that checkout) and the guest callers in
  `pasta_curves` @ `9e00f38`.

  *Agrees.* Ids (`crates/core/executor/src/syscall_code.rs:108,165,168`);
  `a0`/`a1` = `X10`/`X11` (`minimal/ecall.rs:80-81`); RV64, u64 words, four
  words per coordinate, `x || y` little-endian (`crates/curves/src/params.rs`,
  `crates/curves/src/lib.rs:121-141`); `UINT256_MUL` reads `y || modulus` as
  one eight-word slice at `a1` and writes four words at `a0`
  (`minimal/precompiles/uint256.rs:22,32-35`); `PALLAS_DOUBLE` ignores `a1`
  (`minimal/precompiles/ec.rs:51`). The executor's formulas are the model's
  formulas (`crates/curves/src/weierstrass/mod.rs:267-321`: same `p + a - b`
  idiom, Fermat inverse by square-and-multiply).

  *Model traps, real executor continues* -- each is a case a proof over the
  model may silently exclude. A total-correctness (`∃k`) triple cannot exclude
  them (it must show the model does *not* trap, i.e. discharge the guard), so it
  stays sound; a statement that reads "the model trapped" as "the guest
  rejected" or as "no behaviour" does not. `MachineChecked.RiscV.Sym.Safe` is a statement of the second
  kind: `docs/AUDIT.md` ("Other issues found", item 1) records what that leaves open.

  1. `UINT256_MUL` with modulus `0`: the executor computes `(x*y) mod 2^256`
     (`minimal/precompiles/uint256.rs:43-48`) and the AIR proves it
     (`core/machine/src/syscall/precompiles/uint256/air.rs:397-419`). The model
     traps. The guest never passes `0` -- `sp1_mulmod` passes the Pallas
     modulus (`pasta_curves/src/fields/fp.rs:123-137`).
  2. `PALLAS_ADD` with `x₁ ≡ x₂` but `P ≠ Q` bitwise: the inverse of `0` is `0`
     (`dashu_modpow`, `mod.rs:167-189`), so the executor writes
     `(-x₁-x₂, -y₁)` and continues. The AIR cannot prove it (its inverse check,
     `weierstrass_add.rs:481-493`; trace generation asserts at
     `operations/field/field_op.rs:293-295`). `P = Q` bitwise panics
     (`mod.rs:267-270`), matching the model.
  3. `PALLAS_DOUBLE` with `y ≡ 0`: the executor writes `(-2x, 0)` and continues
     (`mod.rs:295-321`). Not provable for `x ≠ 0`; at `(0, 0)` the AIR's slope
     constraint `slope · 2y = 3x²` (`weierstrass_double.rs:560-569`) is `0 = 0`
     and the output is **unconstrained**. No Pallas point has `y = 0` (prime
     order), so only off-curve inputs reach this.
  4. Unreduced coordinates (`≥ p`): nothing range-checks the *inputs*, only the
     outputs (`weierstrass_add.rs:545-546`, `weierstrass_double.rs:607-608`).
     The executor reduces implicitly and either continues -- provably -- or
     panics on a `UBig` underflow (`mod.rs:282,287`) depending on the values.

  *The honest guest avoids all four.* `weierstrass_add_assign`
  (`sp1 crates/zkvm/lib/src/utils.rs:161-195`) handles infinity, doubles on
  bitwise-equal limbs and returns infinity on bitwise-equal `x` before calling
  `PALLAS_ADD`; `sp1_pallas.rs:42-47` passes canonical (`to_repr`) limbs. Those
  bitwise guards are correct only because every value is canonical, which is
  what the reduced-output half of `curveAddL_spec`/`curveDblL_spec` provides
  for chained calls. `double()` has no `y = 0` guard
  (`crates/zkvm/lib/src/pallas.rs:69-76`), safe on-curve by prime order.
-/

import Cases.Zip2005.Precompile.Limbs
import Cases.Zip2005.Precompile.PowMod
import Cases.Zip2005.Precompile.Prime
import Cases.Zip2005.Precompile.Pallas
import Cases.Zip2005.Precompile.Sp1
