# lprog-riscv

A Lake package of this repository: **RISC-V at Lprog**, on riscv-zkvm's machine. With
[`lprog`](../lprog/README.md), it is what a proof about a decompiled RISC-V program needs; the
lift itself and its proofs are in the root package. See
[`docs/design/Packages.md`](../docs/design/Packages.md).

| module | namespace | what |
| --- | --- | --- |
| `LprogRiscV.Machine` | `Lprog.RiscV.Machine` | facts about riscv-zkvm's machine: reading a state after an update, and SP1's accelerator calls (`isCSRS`) |
| `LprogRiscV.Instance` | `Lprog.RiscV` | RISC-V as an instruction set of Lprog (`rvIsa`): each instruction that does not transfer control as a shared operation (`opOf`, proved against riscv-zkvm by `opOf_spec`), and states that agree (`Agree`) |
| `LprogRiscV.Sp1Ctx` | `Lprog.RiscV` | SP1's execution context at Lprog (`sp1Ctx`) |
| `LprogRiscV.Ecall` | `Lprog.RiscV` | SP1's `ecall` cannot tell agreeing states apart (`sp1Ecall_agree`) |
| `LprogRiscV.Lsym` | `Lprog.RiscV` | RISC-V's definitions in `lsym`'s simp set, so that `lsym` computes RISC-V's operations and their checks |

`import LprogRiscV` imports all of it. The modules are `LprogRiscV.*` and not `Lprog.RiscV.*`
because Lean finds a module through the first directory on its search path that has the
module's root, so two packages cannot share the root `Lprog`. The declarations are in
`Lprog.RiscV` all the same.

## Requiring it

It requires `lprog` and riscv-zkvm, at the commit this repository pins. From another Lake
project, on the same Lean version as this repository:

```toml
[[require]]
name = "lprog-riscv"
git = "https://github.com/Verified-zkEVM/machine-checked"
rev = "<commit>"
subDir = "lprog-riscv"
```
