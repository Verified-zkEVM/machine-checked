# Provenance

The kernels here are catcrypt-compiler's RV64 kernels at their encoded bytes, taken with
the permission of its maintainer. catcrypt-compiler is MIT-licensed; its licence is in
`MachineChecked/Ascent/LICENSE-catcrypt`.

`Image/*.lean` hold the words `encodeMBlock64` produces for `addp256Phys`, `feAddPhys`,
`feSubPhys`, `feMul121666Phys` and `cswapPhys` of `Ascent/Demos/RiscvBytesProof.lean` on
catcrypt-compiler's branch `rv64-g5-x25519` (`523dffe6`). They were printed by evaluating
those definitions against catcrypt-compiler's built modules, and each `prog` is their
decoding by riscv-zkvm's `decode` (`decode_ok`, by `decide +kernel`). The words are the
artifact: every theorem here is about them under `stepSp1`, and nothing depends on
catcrypt-compiler's own RV64 model.

The proofs are new. They restate catcrypt-compiler's `*Bytes_correct` theorems as
correspondences (`MachineChecked.Ascent.Corres`) over riscv-zkvm's `stepSp1`, proved through the
lift to Lprog.
