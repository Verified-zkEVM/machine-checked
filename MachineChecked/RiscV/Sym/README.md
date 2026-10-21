# Sym

The symbolic executor, `sym_exec`. Given a goal `SafeN G n P s`, it steps the machine from
`s` one instruction at a time. It keeps the register file and memory regions as facts, splits
at branches, applies callee specifications at calls, and stops at a return or a requested pc.
`sym_close` then finishes the proof against the function's continuation.

## Files

| file | contents |
| --- | --- |
| `Tactic.lean` | `sym_exec`. |
| `Close.lean` | `sym_close`: finish a specification at a return. |
| `Resume.lean` | `sym_reframe`: resume from a stopped state. |
| `Core.lean` | The code facts specifications take (`CodeAt`, `CodeWithin`) and the stepping facts everything rests on. |
| `Exec.lean` | `execInstrBr` unfolded per instruction, and the memory side conditions (`memOk_*`). |
| `Regs.lean` | The register file as one fact. |
| `Region.lean` | Memory as named, 8-aligned regions (`Region`, `Disjoint`). |
| `Mem.lean` | Well-placed regions (`RegionOk`), sub-doubleword access, and `Unchanged`, the frame condition on memory. |
| `ByteFold.lean` | Reading sub-words back through chains of sub-word stores. |
| `Frame.lean` | What a specification says about what it does not compute: `CalleeSaved`, the stack (`StackOk`) and the code. |
| `Layout.lean`, `Ro.lean`, `LoadRo.lean`, `Load.lean` | Where the image sits, and its read-only segment as the executor sees it, from a loaded image. |
| `Carry.lean` | A memory invariant carried through stores and calls. |
| `Syscall.lean`, `Write.lean` | The system calls a guest makes (accelerators, hints, commit, halt, write), stated so the executor can apply them. |

## Use

```lean
theorem f_spec ... (hk : ∀ t, t.pc = ra → ... → SafeN G n P t) : SafeN G n P s := by
  sym_exec [callee_spec₁, callee_spec₂]
  sym_close hk
```

Case studies in `Cases/Zip2005/` use it for most functions of a compiled guest.
