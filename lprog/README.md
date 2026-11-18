# lprog

A Lake package of this repository containing **Lprog**, the low logical program the
decompiler lifts machine code to, and the semantics around it. It requires nothing beyond
Lean. [`docs/design/Packages.md`](../docs/design/Packages.md) explains how the packages fit
together.

| module | namespace | contents |
| --- | --- | --- |
| `Lprog.Syntax`, `Lprog.Expr`, `Lprog.Op` | `Lprog` | Programs: instructions, expressions, and the operations every instruction set shares. |
| `Lprog.Sem` | `Lprog` | The semantics (`Isa`, `step`, `Context`) and the judgement `Isa.SafeN`, with one rule per instruction at the same budget, plus `SafeN.label_spend`, which spends one unit at a label (for loops that need not terminate). |
| `Lprog.Text` | `Lprog` | A text format, with `parse_print`. |
| `Lprog.Linked`, `Lprog.Build`, `Lprog.Dead` | `Lprog`, `Lprog.Linked`, `Lprog.Build` | Building blocks for lifts: the lift of a linked program, the expressions lifts write, and removal of dead flag writes. Nothing is proved of `Linked` or `Dead`. |
| `Lprog.Ascent.*` | `Lprog.Ascent` | Runs, `SafeN`, refinement and equivalence, and correspondence, for any step relation. |
| `Lprog.Block`, `Lprog.Contract`, `Lprog.Tactic`, `Lprog.LsymAttr` | `Lprog` | Proof automation: a straight-line block in one step (`SafeN.block`); a function's contract over the register file (`Isa.Contract`); and `lsym`, which steps a body symbolically and calls through contracts, using each callee's postcondition on the path after the call. Its simp set `lsym_simp` (declared in `Lprog.LsymAttr`) is extended by each instruction set; `lsym_addr` is the normal form of addresses. |
| `Lprog.ARM.Reg`, `Lprog.X86.Reg` | `Lprog.ARM`, `Lprog.X86` | AArch64 and x86-64 registers at Lprog. |

`import Lprog` imports everything. [`Lprog/README.md`](Lprog/README.md) describes the
language, and [`Lprog/Ascent/README.md`](Lprog/Ascent/README.md) the generic semantics.

RISC-V at Lprog (its registers over riscv-zkvm's machine, and SP1's execution context) is the
separate package [`lprog-riscv`](../lprog-riscv/README.md), which requires this one and
riscv-zkvm.

## Requiring it

From another Lake project on the same Lean version as this repository (`lean-toolchain`):

```toml
[[require]]
name = "lprog"
git = "https://github.com/Verified-zkEVM/machine-checked"
rev = "<commit>"
subDir = "lprog"
```

## Provenance

`Lprog/Ascent/Run.lean`, `Lprog/Ascent/Corres.lean` and Lprog's syntax are ported from
[catcrypt-compiler](https://github.com/spitters/catcrypt-compiler). Details are in
[`Lprog/Ascent/PROVENANCE.md`](Lprog/Ascent/PROVENANCE.md), and the licence they came under is
[`Lprog/Ascent/LICENSE-catcrypt`](Lprog/Ascent/LICENSE-catcrypt). The rest is under this
repository's licence ([`LICENSE`](../LICENSE)).
