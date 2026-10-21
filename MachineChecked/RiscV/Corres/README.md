# Corres

Correspondence tooling on riscv-zkvm's `stepSp1`. `../Corres.lean` defines `Corres`, which is
the ascent's `CorresM` at `stepsSp1`, together with its bridges into `SafeN`. This directory
holds what makes such proofs short.

| file | contents |
| --- | --- |
| `Block.lean` | Straight-line code: a block of straight instructions runs as the fold of `execInstrBr` (`Corres.straight`), and `reach_*` build a run one instruction at a time, memory side conditions included. |
| `Regs.lean` | The registers of a pure block as a fold over a valuation. `regs_run` names one value per instruction, so terms stay linear and `bv_decide` sees one small equation per instruction. |
| `Run.lean` | Runs whose length depends on the state: `Reach`, `CorresRun`, function specifications (`FnSpec`), calls (`Reach.call`), loops (`Reach.loop`), and the bridge `SafeN.of_reach`. |

Worked examples are in `Cases/CatCrypt/`: four field and point kernels, verified at their
encoded bytes.
