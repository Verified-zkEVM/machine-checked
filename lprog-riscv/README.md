# lprog-riscv

A Lake package of this repository containing **RISC-V at Lprog**, over riscv-zkvm's machine.
Together with [`lprog`](../lprog/README.md), it holds the RISC-V definitions a proof about a
decompiled program reasons with. The lift itself (`liftProg`), its proofs, and the modules
`decompile --to lean` writes need the root package
([`MachineChecked/RiscV/Lift`](../MachineChecked/RiscV/Lift/README.md)). See
[`docs/design/Packages.md`](../docs/design/Packages.md).

| module | namespace | contents |
| --- | --- | --- |
| `LprogRiscV.Machine` | `Lprog.RiscV.Machine` | Facts about riscv-zkvm's machine: reading a state after an update, and SP1's accelerator calls (`isCSRS`). |
| `LprogRiscV.Instance` | `Lprog.RiscV` | RISC-V as an Lprog instruction set (`rvIsa`): each instruction that does not transfer control as a shared operation (`opOf`, proved against riscv-zkvm by `opOf_spec`), and agreement of states (`Agree`). |
| `LprogRiscV.Sp1Ctx` | `Lprog.RiscV` | SP1's execution context at Lprog (`sp1Ctx`). |
| `LprogRiscV.Ecall` | `Lprog.RiscV` | SP1's `ecall` cannot distinguish agreeing states (`sp1Ecall_agree`). |
| `LprogRiscV.Lsym` | `Lprog.RiscV` | RISC-V's definitions added to `lsym`'s simp set, so `lsym` computes RISC-V operations and their checks; the frame of a postcondition (`frame_ofParts`); a contract proved over a machine state restated over the register file (`contract_of_agree`). |

`import LprogRiscV` imports everything. The modules are named `LprogRiscV.*` rather than
`Lprog.RiscV.*` because Lean resolves a module through the first directory on its search path
that contains the module's root, so two packages cannot share the root `Lprog`. The
declarations are still in `Lprog.RiscV`.

## Requiring it

It requires `lprog` and riscv-zkvm at the commit this repository pins. From another Lake
project on the same Lean version as this repository:

```toml
[[require]]
name = "lprog-riscv"
git = "https://github.com/Verified-zkEVM/machine-checked"
rev = "<commit>"
subDir = "lprog-riscv"
```
