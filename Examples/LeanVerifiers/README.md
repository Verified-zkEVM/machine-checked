# LeanVerifiers

rustc's code for the leanXMSS, leanSPHINCS and leanVM verifiers, on AArch64 and x86-64: the
target of [`docs/NativeVerifiers.md`](../../docs/NativeVerifiers.md). So far the images only
(milestone M0); nothing is proved yet.

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
