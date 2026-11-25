# LeanVerifiers

rustc's code for the leanXMSS, leanSPHINCS and leanVM verifiers, on AArch64 and x86-64: the
target of [`docs/NativeVerifiers.md`](../../docs/NativeVerifiers.md). So far the images and the
specifications (milestone M0), and the pilot (M0.5, [below](#the-pilot)): `memcpy` and `keccak_f`
of the AArch64 signature image, proved at Lprog.

The code is the assembly [leanEthereum/leanVM#837](https://github.com/leanEthereum/leanVM/pull/837)
commits (rustc 1.99.1, `opt-level=3`, fat LTO, no SIMD, panics as trap instructions), fetched at
a pinned commit and checked against that pull request's checksums. [`build.sh`](build.sh)
assembles each file and links it, with a stub `_start`, into a statically linked executable in
[`../elf/`](../elf), pinned by [`SHA256SUMS`](SHA256SUMS); `build.sh --check` builds again and
compares.

| image | holds | functions | machine instructions | `decompile --to lprog` |
| --- | --- | --- | --- | --- |
| `lean_signatures_a64.elf` | `xmss_verify`, `sphincs_verify` | 15 | 4,303 | all lifted; 2 `abort`s, the panic traps (`udf`, `brk`) |
| `lean_signatures_x64.elf` | the same | 15 | 4,281 | all lifted; 2 `abort`s (`ud2`) |
| `lean_vm_a64.elf` | `leanvm_verify` | 138 | 15,082 | all lifted; no `abort` |
| `lean_vm_x64.elf` | the same | 138 | 17,113 | all lifted; no `abort` |

Each count includes the stub `_start`. The lifts of AArch64 and x86-64 are tested, not proved
([`ROADMAP.md`](../../ROADMAP.md)); proving them is milestones M1, M4 and M5.

On x86-64 rustc calls `memcpy` and `memset` through the GOT. The images are linked with
`--no-relax`, so the calls stay as rustc wrote them, and the GOT is part of the image: in
`lean_vm_x64.elf` its two slots, at `0x221ee0`, hold `0x220e20` and `0x220e80`, the addresses of
`memcpy` and `memset`. What #837 assumes of the loader (`GotAt`) is here a fact about the image,
to be checked against the ELF with the rest of its constant data
([#76](https://github.com/Verified-zkEVM/machine-checked/issues/76)).

## The package

This directory is a Lake package of its own, `lean-verifiers`, built from here:

```sh
cd Examples/LeanVerifiers
lake exe cache get      # Mathlib's oleans
lake build              # the library `LeanVerifiers`
```

It requires machine-checked by path, for the lifts, Lprog and `lsym`, and the package `native`
of #837, at that pull request's head, for the specifications: the models of the Rust code
(`NativeRustc.Xmss.verify_eq`, `NativeRustc.Sphincs.verify_eq`, imported by
[`LeanVerifiers/Specs.lean`](LeanVerifiers/Specs.lean)) and the statements they are proved
against. #837's own proofs over Kraken are not built.

It is apart from `lake build Examples` for two reasons. The specifications bring some twenty
packages with them (VCVio, ArkLib, CompPoly and what they require). And one of them, VCVio, has
a library `Examples`: in one package with machine-checked's, Lake takes the modules
`Examples.*` to be VCVio's. So nothing here imports `Examples.*`, and the modules are
`LeanVerifiers.*`.

## The pilot

Milestone M0.5: two functions of `lean_signatures_a64.elf`, each with its contract at Lprog,
proved with `lsym` on the lift, to compare the cost with #837's for the same two functions
before the rest is built.

| file | what |
| --- | --- |
| [`LeanVerifiers/ARM/Signatures/`](LeanVerifiers/ARM/Signatures) | the image and the two functions' lifts, written by `decompile --to lean --flags` and checked against the ELF's bytes by the kernel |
| [`LeanVerifiers/ARM/Isa.lean`](LeanVerifiers/ARM/Isa.lean) | AArch64 as an instance for `lsym`, over a memory of bytes |
| [`LeanVerifiers/ARM/Bytes.lean`](LeanVerifiers/ARM/Bytes.lean) | bytes and words read after bytes and words written |
| [`LeanVerifiers/ARM/Memcpy.lean`](LeanVerifiers/ARM/Memcpy.lean) | `memcpy_contract`, for every length |
| [`LeanVerifiers/ARM/KeccakF.lean`](LeanVerifiers/ARM/KeccakF.lean) | `keccak_f_contract`, against `keccakF1600` |

The generated modules are made, from this directory, by

```sh
../../.lake/build/bin/decompile --to lean --flags ../elf/lean_signatures_a64.elf <dir> LeanVerifiers.ARM.Signatures
```

of which `Code.lean`, `F2.lean` (`memcpy`) and `F10.lean` (`keccak_f`) are kept.

### The numbers

Lines are whole files, comments included, on both sides.

| | #837, AArch64 | here |
| --- | --- | --- |
| `memcpy` | 503 lines in 2 files | 143 lines |
| `keccak_f` | 861 lines in 8 files | 272 lines |
| shared by the two | 124 lines (`Mem/Common.lean`, shared with `memset`) | 245 lines (`Isa.lean`, `Bytes.lean`) |
| the executor | 5,766 lines (`Sym`), for AArch64 | `lsym`, as it was, for any instruction set |
| build of the proofs | not measured: they need #837's fork of Kraken | `memcpy` 2 s, `keccak_f` about 1 minute |
| build of the code | not measured | `memcpy` 1 s, `keccak_f` 24 s and 10 GB |

So about a third of the lines for each function. One round of `keccak_f` (some 170
instructions) is one call of `lsym`, and what it leaves in each of 30 registers and slots is
the model's lane or parity by `bv_decide`. #837's layout of the lanes at the loop head was
reused; finding it was not part of the cost here.

### Constant data

`keccak_f` reads its round constants from a table in the image. They are not a hypothesis
copied from a disassembly: the contract's precondition is that memory holds the image
(`Holds program.memory`), the image's words are in `Signatures/Code.lean`, checked against the
ELF when it is built (`memory_eq_elf`), and the 24 constants are among them by evaluation
(`rc_in_image`). This is what
[#76](https://github.com/Verified-zkEVM/machine-checked/issues/76) asks for, on the
whole-program route that AArch64 and x86-64 take; the route of RISC-V's proved lift
(`--proved`) does not have it yet.

### What the numbers do not say

The two theorems are weaker than #837's, in ways the roadmap closes once and not for each
function:

- **Nothing about the machine.** The lift of AArch64 is not proved (M4); the contracts are about
  the lifted program.
- **Partial correctness.** A run that never returns meets the contract (M2); #837 proves that
  the function returns. Each loop here would need its measure, which both proofs already have
  as the induction.
- **The memory is a model**: bytes by address, with no access that faults, so the contracts need
  no condition that the stack or the buffers are mapped, and say nothing of it (M4).
- **`keccak_f`'s state is 25 words** at the buffer (`StateAt`), where #837's is 200 bytes; the
  lemma between the two is not here.
- **Axioms.** `bv_decide` trusts its certificate checker as compiled code, through one axiom for
  each use; the repository allows that (`AxiomCheck.lean`), and #837's theorems depend on
  Lean's three only. The identities are of `xor`, `and`, `not` and rotations, and can be proved
  without it.

And two costs that will matter at 150 functions. The kernel's check of a function's lift
against the image is heavy on the whole-program route: 24 s and 10 GB for `keccak_f`'s 575
instructions, and it grows with the function, so the largest (6,000 instructions) need the
check in parts, as RISC-V's `--proved` route has it. And a loop head is given to `lsym` as a
position in the lifted body, counted by hand.

The program is the lift itself, with every write of the flags (`program.lifted`, `--flags`):
the pass that drops the writes nothing reads is not proved, and tripled the cost of the
check.
