# lprog

A Lake package of this repository: **Lprog**, the low logical program the decompiler lifts
machine code to, and the semantics around it. It requires nothing beyond Lean itself. See
[`docs/design/Packages.md`](../docs/design/Packages.md) for how it fits with the rest.

| module | namespace | what |
| --- | --- | --- |
| `Lprog.Syntax`, `Lprog.Expr`, `Lprog.Op` | `Lprog` | programs: instructions, expressions, the operations every instruction set shares |
| `Lprog.Sem` | `Lprog` | the semantics (`Isa`, `step`, `Context`) and the judgement `Isa.SafeN` with a rule per instruction, at the same budget, and `SafeN.label_spend`, which spends one unit at a label: for a loop that need not end |
| `Lprog.Text` | `Lprog` | a text format, with `parse_print` |
| `Lprog.Linked`, `Lprog.Build`, `Lprog.Dead` | `Lprog`, `Lprog.Linked`, `Lprog.Build` | what lifts are built from: a linked program's lift, the expressions they write, dropping dead flag writes (not proved) |
| `Lprog.Ascent.*` | `Lprog.Ascent` | runs, `SafeN`, refinement and equivalence, correspondence, for any step relation |
| `Lprog.Block`, `Lprog.Contract`, `Lprog.Tactic` | `Lprog` | proof automation: a straight-line block in one step (`SafeN.block`); a function's contract over the register file (`Isa.Contract`); and `lsym`, which steps a body symbolically and calls through contracts (using what each callee's postcondition says on the path after it), with the simp set `lsym_simp` (`Lprog.LsymAttr`) an instruction set adds to and the normal form of addresses, `lsym_addr` |
| `Lprog.ARM.Reg`, `Lprog.X86.Reg` | `Lprog.ARM`, `Lprog.X86` | AArch64's and x86-64's registers at Lprog |

`import Lprog` imports all of it. [`Lprog/README.md`](Lprog/README.md) describes the language
and [`Lprog/Ascent/README.md`](Lprog/Ascent/README.md) the semantics.

## Requiring it

From another Lake project, on the same Lean version as this repository (`lean-toolchain`):

```toml
[[require]]
name = "lprog"
git = "https://github.com/Verified-zkEVM/machine-checked"
rev = "<commit>"
subDir = "lprog"
```

RISC-V at Lprog (its registers over riscv-zkvm's machine, and SP1's execution context) is the
package [`lprog-riscv`](../lprog-riscv/README.md), which requires this one and riscv-zkvm.

## Provenance

`Lprog/Ascent/Run.lean`, `Lprog/Ascent/Corres.lean` and Lprog's syntax are ported from
[catcrypt-compiler](https://github.com/spitters/catcrypt-compiler);
[`Lprog/Ascent/PROVENANCE.md`](Lprog/Ascent/PROVENANCE.md) has the details, and
[`Lprog/Ascent/LICENSE-catcrypt`](Lprog/Ascent/LICENSE-catcrypt) the licence they came under.
The rest is under this repository's licence ([`LICENSE`](../LICENSE)).
