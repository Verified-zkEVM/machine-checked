# CatCrypt kernels

RV64 field and point kernels emitted by catcrypt-compiler, verified at their encoded bytes
against riscv-zkvm's `stepSp1`.

Each kernel is a pure block: its run on the machine is the fold of `execInstrBr` over its
instructions (`corres_block`, `MachineChecked/RiscV/Lift/Block.lean`). Each result is a
theorem `Cases.CatCrypt.<Kernel>.corres`, a correspondence (`MachineChecked.RiscV.CorresSp1`,
that is `Lprog.Ascent.Corres` over `stepSp1`) between the kernel's run and its specification.
Nothing depends on catcrypt-compiler's own RV64 model; the trusted base is riscv-zkvm's
decoder and step.

Build: `lake build Cases.CatCrypt`. The axiom check is in `scripts/AxiomCheckCases.lean`.

| file | kernel | instructions | result |
| --- | --- | --- | --- |
| `Cswap.lean` | `cswap` | 52 | swaps two four-limb values when `t0 = 1` |
| `AddP256.lean` | `addp256` | 83 | `(x + y) mod p256`, for x, y below p256 |
| `FeAdd.lean` | `feAdd` | 186 | `(x + y) mod p25519`, for all inputs |
| `FeSub.lean` | `feSub` | 216 | `(x + 2p - y) mod p25519`, for y ≤ x + 2p |

- `Fe.lean`: shared definitions: four-limb values (`limbs4`, `cat4`), the kernels' register
  conventions, the shape of a kernel specification (`KSpec`), and arithmetic lemmas.
- `Image/`: the kernels' instruction words and their decoding by riscv-zkvm's `decode`,
  checked by the kernel. `Image/FeMul121666.lean` holds a fifth kernel, not yet proved.

Each proof runs the kernel with `regs_run`, which names one value per instruction, and
discharges the arithmetic with `bv_decide` or `omega`.

[`PROVENANCE.md`](PROVENANCE.md) records where the words came from and their licence (MIT).
