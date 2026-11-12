# ARM

**Layer 0 of the [roadmap](../../ROADMAP.md) for AArch64:** the machine model. The
counterpart of `RiscV/`, to be built out after it.

## Today

| file | contents |
| --- | --- |
| `Model.lean` | The AArch64 machine model: one state (the `X` registers, the carry and zero flags, byte-addressed memory, the pc) and one step over a scalar general-purpose subset: 64-bit arithmetic with the carry chain, the 32-bit `W` forms (acting on the low halves of the `X` registers), doubleword loads and stores, `CMP`, `CBNZ` and `B.cond`. **Trusted.** |
| `Mem64.lean` | Byte-addressed memory with little-endian doubleword access, used by the model. |

The model is not proved against a canonical AArch64 specification. It is named as trusted on
the trust ladder (`docs/ELF.md` §4) and stands in until DeepMind's arm64-semantics, the
semantics chosen in `docs/ISA.md`, is required; then it is removed. It has no decoder yet. Nothing outside
this directory imports it.

## Where it is going

AArch64 is meant to be a peer of RISC-V, with the same layers:
- a decoder and an image loader (layer -1);
- the judgement over this model's step (layer 0);
- a lift into the shared low logical program `../Lprog` (layer 0.5), with its simulation: the
  counterpart of `../RiscV/Lprog`. Its flags become explicit values in the shared operations;
- the proof tools where they pay off.

Everything from layer 0.5 up is shared with RISC-V. The order of work is in
[`ROADMAP.md`](../../ROADMAP.md).

Ported from catcrypt-compiler; see [`PROVENANCE.md`](PROVENANCE.md).
