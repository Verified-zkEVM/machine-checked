# Goals to Verify

- [zip-2005](https://github.com/dhsorens/zip-2005-asm/) - what we've already been looking at
- [the asm corresponding to this hash](https://github.com/leanEthereum/leanVM/pull/555)
    - the spec should be in [my hash-specs repo](https://github.com/dhsorens/hash-specs)
- Plonky3 SIMD Backends for finite fields
- precompiles? can we verify those in this framework?
    - hash function e.g. keccak precompiles; absolutely

## Hash precompiles: candidate targets (2026-10-14)

What "precompile" means here. In both zkVMs a precompile proper lives in the prover, not in
RISC-V code: SP1's `KECCAK_PERMUTE`, `SHA_COMPRESS` and the curve ops; leanVM's `blake2s`
compression instruction (custom-0, opcode `0x0b`) and its extension-field instruction
(custom-1, `0x2b`). The framework can verify the guest-side wrapper against the instruction's
contract (done for three SP1 wrappers in the zip-2005 table), and state the instruction's
contract as an axiom of the step relation (a hash-specs function). What it can verify fully is
the *software* implementation of the same primitive, and the ecosystem has several, each with
a spec in [hash-specs](https://github.com/dhsorens/hash-specs).

Note on leanVM PR 555: its assembly is x86-64 (`crates/primitives/src/hash/x86/gpr.rs`, the
verifier's scalar compression on the host), not RISC-V. `Cases/LeanVM/Blake2s` holds the
RISC-V guest `programs/blake2s/blake2s.elf` at the PR's merge commit, which the PR did not
change (same SHA-256 as at its base). Same algorithm, different code; the x86 kernel would be a
target for the x86 side of the framework, sharing only the spec.

In the order to take them:

1. **BLAKE2s, the leanVM `blake2s` guest** (`Cases/LeanVM/Blake2s`, scaffolded). 644-instruction
   `compress` in plain Rust, no heap; spec `Hash.BLAKE2`. Its cost is the one-time leanVM step
   relation (`exit` only, `unimp` ends the run, the fixed memory map, the advice region),
   which every leanVM target then shares.
2. **SHA-256 `compress256` in zip-2005** (`0x780361e0`). Image, step and a certified footprint
   contract already exist; only the functional link to `Hash.SHA2` is missing. Not on zip-2005's
   critical path as it stands: the public-values hasher is SHA-256, but the guest commits no
   public values, so its statement needs only the hasher's invariant (`Owned.env`), not the
   digest. It becomes necessary if the guest is changed to commit values.
3. **Keccak-f[1600] and keccak256 in the leanVM SDK** (`sdk/src/keccak.rs`, used by the
   `stateproof` guest). Ethereum's hash, in software (no Keccak instruction), written with
   shifts and ORs since rv64im has no rotate; spec `Hash.Keccak`.
4. **The BLAKE2s instruction as a precompile**: the `hash` guest and the SDK's `Blake2s` stream.
   The instruction's semantics axiomatised from hash-specs' compression function; the SDK's
   streaming code against `Hash.BLAKE2.Stream` and its lemmas.
5. **BLAKE3**: spec exists (`Hash.BLAKE3`), no RISC-V code in the ecosystem yet (a reference-crate
   guest would be easy). **Poseidon2** (`HashZK`): no implementation on the binary-field leanVM,
   only on the retired KoalaBear branch.

Other strong targets:

- **leanXMSS verification** (`leanxmss` guest, 19 KB): hash chains and Merkle paths over BLAKE2s,
  spec in leanVM's `formal/xmss` (`Scheme.lean`), the goal of `xmss-asm`. Decomposes into 1 and 4
  plus loop and advice reasoning.
- **The extension-field instruction** (`ext.rs`): leanVM's second precompile; its portable Rust
  fallback is the spec.
- **The `numbers` guest**: tiny; exercises the M extension and signed division end to end.

What the framework needs for functional proofs: the contract checker proves memory-safety
interfaces; functional results go through the symbolic executor at cut points (as the allocator
proofs did), heavy for a 4039-instruction unrolled compression. The ascent for these is
CatCrypt's `CorresIsa`, ported (`CATCRYPT-PORT.md`), with hash-specs' equivalence lemmas doing
the rest. `riscv-decomp` was considered and dropped (2026-10-20). Toolchain: hash-specs is on
v4.34.0, this repository on v4.33.0. Mathlib may now be imported anywhere here, so only the
Lean version separates them.
