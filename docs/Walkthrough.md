# Walkthrough: `memcmp`, from the binary to its specification

This guide follows one complete proof through every layer that exists today: load the binary,
lift it to the low logical program (Lprog), prove a contract there, and carry the result back
down to the machine. New proofs are meant to take this shape. Read it next to the code:

- `Cases/Hardening/Gen/Memcmp/`: the binary's words and their lift, written by
  `decompile --to lean --proved`.
- `Cases/Hardening/Memcmp.lean`: the contract at Lprog, proved with the `lsym` tactic, and the
  machine-level theorem `safe`. This is the recommended style for new proofs.

The function is `memcmp(a, b, n)`, from `Cases/Hardening/src/memcmp.c` compiled by clang:
twelve RISC-V instructions that compare `n` bytes at `a` and `b`, the ones rustc's
`compiler_builtins` has for `memcmp` in an SP1 guest, with two of the increments in another
order. The theorem holds for every `n`: the result is zero exactly when the bytes agree.

## 1. The binary as Lean data (layer -1)

`decompile --to lean --proved` (`Tools/ToLean.lean`) reads the ELF
(`Cases/Hardening/elf/memcmp.elf`) and writes a module with the image's words,
`Cases/Hardening/Gen/Memcmp/Words.lean`, and one module per function. The words module holds
each function's name, base address and 32-bit words, and the functions they decode to:

```lean
def w0 : List Nat :=
    [33947747, 345731, 378627, 15113827, 1377555, 4294313491, 1410451, 4261811427, 1299, 32871, 1088849203, 32871]
...
def words : List (String × Nat × List Nat) := [
  ("memcmp", 4096, w0),
  ("_start", 4144, w1)]

check_elf_words words "Cases/Hardening/elf/memcmp.elf"

def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := ((ws.map (BitVec.ofNat 32)).mapM decode).getD [] }
```

`memcmp` is function 0, at `0x1000`. The generator is not trusted: `check_elf_words` reads the
ELF when the module is built and fails if the words differ, and the instructions are not
written out but computed from the words by riscv-zkvm's decoder (`decode`). A proof then
assumes only that the machine holds each function's instructions at its base (`CodeAt`,
`MachineChecked/RiscV/Sym/Core.lean`). A case study discharges that once from its loaded
image.

## 2. The machine and the statement (layer 0)

Everything is stated over riscv-zkvm's `stepSp1`, the step function SP1 executes. The final
theorem, `Cases.Hardening.Memcmp.safe`, uses the judgement `SafeN` (`MachineChecked/RiscV/Safe.lean`; see
[`Architecture.md`](Architecture.md)) in continuation form:

```lean
theorem safe ... (hpc : s.pc = 0x1000#64) (hcode : ∀ f ∈ fns, CodeAt f.base (f.prog.map some) s)
    (hra : s.getReg .x1 = ra) (h10 : s.getReg .x10 = a) (h11 : s.getReg .x11 = b)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 n) ...
    (hk : ∀ t, t.pc = ra &&& ~~~1#64 → t.code = s.code → (∀ addr, t.getMem addr = s.getMem addr) →
      (∀ r, r ∉ clobbered → t.getReg r = s.getReg r) →
      (t.getReg .x10 = 0 ↔
        ∀ i < n, s.getByte (a + BitVec.ofNat 64 i) = s.getByte (b + BitVec.ofNat 64 i)) →
      BitVec.signExtend 64 ((t.getReg .x10).truncate 32) = t.getReg .x10 →
      SafeN G k P t) :
    SafeN G k P s
```

Read it as: if the caller is safe from every state in which `memcmp` can return, then the
caller is safe from the call. "Every state in which it can return" means: at `ra`, with code
and memory unchanged, registers outside `x10`..`x14` unchanged, and `x10` zero exactly when
the bytes agree (and sign-extended from 32 bits, as an `int`). Specifications in this form compose by application, through the contract
table ([`Architecture.md`](Architecture.md)).

## 3. The lift (layer 0 to layer 0.5)

The image's functions are lifted to an Lprog program, `liftProg fns`
(`MachineChecked/RiscV/Lift/Lift.lean`). `liftProg` puts a label before each instruction and
translates the instruction:

- an operation becomes `Lopn (opOf i)`, an operation shared by all ISAs
  (`lprog/Lprog/Op.lean`). For example, `LBU x13, 0(x10)` becomes
  `load .x13 .b1 false (x10 + 0)`;
- a conditional branch becomes `Lcond` on a comparison, jumping to the label of its target;
- `jalr x0, 0(ra)` becomes `Lret`, a call `Lcall`, a tail call `Ltail`, and `ecall` `Lext`;
- anything the lift does not cover becomes `Labort`.

After the lift, the body mentions nothing RISC-V-specific except register names. The
translation of an operation is proved once for every instruction, against riscv-zkvm's
`execInstrBr` (`opOf_spec`, `lprog-riscv/LprogRiscV/Instance.lean`).

The generator also writes the lifted body of each function as a term, so that a proof does not
have to compute it. For `memcmp` this is `f0` in `Cases/Hardening/Gen/Memcmp/F0.lean`, with
the theorem the proof steps through, checked by the kernel:

```lean
theorem f0_eq : (liftProg fns)[0]? = some f0
```

## 4. The proof at Lprog (layer 0.5)

An Lprog state is a stack of activations, a register file and a memory. `Lret` is defined only
when `ra` holds the value the call put there and `sp` is back where it was at the call.
Otherwise the step goes `wrong`, and the judgement at Lprog excludes `wrong`. That judgement
is `LSafeN` (`MachineChecked/RiscV/Lift/Lift.lean`): the generic `Isa.SafeN` of
`lprog/Lprog/Sem.lean`, at the lifted program under SP1. So a proof at Lprog also proves that
the function returns to its caller.

The contract is stated in continuation form, at Lprog:

```lean
theorem contract ... (hpost : ∀ r' m', Post u0 a b n (ofParts r' m') → LSafeN fns G N Q ⟨rest, r', m'⟩) :
    LSafeN fns G N Q ⟨⟨0, 0, ret, top⟩ :: rest, regs, m⟩
```

That is: from the call, every continuation that is safe from the states `Post` describes is
safe. The loop is an induction on the number of bytes left (`loop`); `contract` adds the entry
and the case `n = 0`.

### The rules

The generic rules are in `lprog/Lprog/Sem.lean` (`SafeN.label`, `SafeN.goto`, ...) and the
RISC-V rules in `MachineChecked/RiscV/Lift/Rules.lean` (`lsafe_opn`, `lsafe_cond`,
`lsafe_ret`, ...). Each RISC-V rule takes a machine state `u` that the Lprog state stands for
(`Agree (ofParts regs m) u`), so what an instruction reads is stated on `u`, in riscv-zkvm's
terms. A proof can apply them one instruction at a time; `memcmp` was first proved that way,
in 333 lines (the tree at tag `with-zip2005` has that proof).

### With `lsym`

`lsym` (`lprog/Lprog/Tactic.lean`, with RISC-V's simp set in
`lprog-riscv/LprogRiscV/Lsym.lean`) does the stepping. It steps through the body, computes
each operation, closes the memory checks of loads and the conditions of returns, and splits at
each `Lcond`. It stops at a loop head. What remains is what the function means: the loop
invariant at its head and the postcondition at each return.

```lean
lsym f0_eq stop [2] with [h10, h11, h12, hra, hsp, hva j hj, hvb j hj]
```

The loop is stated on Lprog's register file rather than on an agreeing machine state, because
`lsym` writes registers with `updReg`. `lframe` proves that registers outside `clobbered` are
unchanged.

## 5. Back down to the machine

The transfer theorem (`transfer`, `MachineChecked/RiscV/Lift/Transfer.lean`) carries a contract
at Lprog to the machine. Every `stepSp1` step from a state that an Lprog state stands for is
matched at Lprog, and Lprog's `wrong` matches nothing. `SafeN.of_contract` states this for a
function's entry:

```lean
refine SafeN.of_contract hok (g := 0) hg (hpc.trans hb.symm) hcode
  (Post := Post s a b n)
  (fun _ _ hk => contract s a b n hn hva hvb _ _ (agree_ofParts_regsOf s) h10 h11 h12 rfl rfl hk) ?_
```

What remains is to read the returned machine state off the Lprog state that stands for it
(`hag`). The proof of `safe` contains no symbolic execution and does not depend on how the run
was found.

## Where to go next

- A function with a loop, a call and a system call: `Cases/Hardening/WriteVectored.lean`,
  `write_vectored` of a Rust SP1 guest, with `lsym`. The call to `sys_write` uses
  `sys_write`'s contract at Lprog, which tail-calls `syscall_write`; its `WRITE` is SP1's
  execution context.
- Small C programs compiled by clang, decompiled with `decompile --to lean` and proved with
  `lsym`: [`Cases/Hardening/`](../Cases/Hardening/README.md).
- Straight-line blocks proved directly over the machine:
  `MachineChecked/RiscV/Lift/Block.lean`.
- A whole guest: zip-2005 has its verification in
  [zip-2005-asm](https://github.com/dhsorens/zip-2005-asm).
- What the lift does not cover yet, and what comes after layer 0.5:
  [`ROADMAP.md`](../ROADMAP.md) and [`MachineChecked/RiscV/LIMITS.md`](../MachineChecked/RiscV/LIMITS.md).
