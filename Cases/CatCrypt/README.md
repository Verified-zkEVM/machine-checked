# CatCrypt kernels

RV64 kernels emitted by catcrypt-compiler, verified at their encoded bytes against riscv-zkvm's
`stepSp1`, by correspondence (`MachineChecked/RiscV/Corres`).

| file | kernel | instructions | result |
| --- | --- | --- | --- |
| `Cswap.lean` | `cswap` | 52 | swaps two four-limb values when `t0 = 1` |
| `AddP256.lean` | `addp256` | 83 | `(x + y) mod p256`, for x, y below p256 |
| `FeAdd.lean` | `feAdd` | 186 | `(x + y) mod p25519`, for all inputs |
| `FeSub.lean` | `feSub` | 216 | `(x + 2p - y) mod p25519`, for y ≤ x + 2p |

- `Fe.lean`: the shared vocabulary. It has four-limb values (`limbs4`, `cat4`), the kernels'
  register conventions, the shape of a kernel specification (`KSpec`), and arithmetic lemmas.
- `Image/`: the kernels' instruction words and their decoding by riscv-zkvm's `decode`, checked
  by the kernel. `Image/FeMul121666.lean` holds a fifth kernel whose proof is not done yet.

Each proof runs the kernel with `regs_run`, which gives one named value per instruction, and
discharges the arithmetic with `bv_decide` or `omega`.

[`PROVENANCE.md`](PROVENANCE.md) records where the words came from.
