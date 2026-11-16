# X86

**x86-64, at layers 0 and 0.5 of the [roadmap](../../ROADMAP.md):** the machine model, and a
lift into the low logical program for the decompiler. The counterpart of `RiscV/`, with less
built and nothing proved.

## Today

| file | contents |
| --- | --- |
| `Kraken.lean` | Imports the x86-64 semantics: [Kraken](https://github.com/AeneasVerif/kraken)'s x64 model (`Kraken.X64.Semantics`), a dependency used unmodified at the commit pinned in `lakefile.toml`. Its programs are assembly, not bytes. **Trusted** (`docs/ISA.md`). |
| `Lprog/Reg.lean` | The registers of x86-64 at Lprog: the sixteen general registers, the flags as registers that hold 0 or 1, a register for a return address in passing, and six of the lift's own. |
| `Lprog/Instr.lean` | The integer instructions of x86-64 in 64-bit mode, and their decoding from bytes (`decode`). This repository's own: Kraken has no decoder. Compared with LLVM's disassembler on the test programs. |
| `Lprog/Lift.lean` | The lift of x86-64 (`liftX86`): those instructions in the lift of linked programs (`../Lprog/Linked.lean`) over the shared operations. Nothing is proved of it, and it is not yet compared with Kraken's semantics. |
| `Lprog/Table.lean` | The instructions by kind, each with whether the lift takes it, said by the lift itself: the table of `LIMITS.md`. |
| `Bare.lean` | An x86-64 program without an operating system as a Pancake program (`Guest.toPancake`): the lift, then lift 2 (`../Logical`), with `syscall` as the system call. What `decompile --to pancake` runs on an x86-64 ELF. |
| [`LIMITS.md`](LIMITS.md) | **What the decompiler does not do on x86-64**: what it takes, every instruction lifted or not, where it gives up, what it assumes, where its output differs from the processor, how far it is tested. |

Nothing here states a judgement over Kraken's step yet. The lift does not go through
Kraken: it reads bytes, which Kraken does not, and takes instructions Kraken lacks. It is
tested against another machine (`scripts/decompile-check`).

## Where it is going

x86-64 is meant to be a peer of RISC-V, with the same layers:
- Kraken's programs are assembly, so layer -1 is reading `.S` files or disassembled `.o` files,
  not loading an ELF, and the assembler and linker are trusted (`docs/ELF.md` §4);
- the judgement over Kraken's x64 step (layer 0);
- the lift that is here, stated over Kraken's instructions where Kraken has them, with the
  simulation that carries a run of the lifted program down to Kraken's step: the counterpart
  of `../RiscV/Lprog`'s;
- the proof tools where they pay off.

Everything from layer 0.5 up is shared with RISC-V. The order of work is in
[`ROADMAP.md`](../../ROADMAP.md).
