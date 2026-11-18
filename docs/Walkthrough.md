# Walkthrough: `memcmp`, from the binary to its specification

This guide follows one complete proof through every layer that exists today: load the binary,
lift it to the low logical program (Lprog), prove a contract there, and carry the result back
down to the machine. New proofs are meant to take this shape. Read it next to the code:

- `Cases/Zip2005/Runtime/MemcmpLprog.lean`: the lift, the contract proved one rule per
  instruction, and the machine-level theorem `safe`.
- `Cases/Zip2005/Runtime/MemcmpLsym.lean`: the same contract proved with the `lsym` tactic.
  This is the recommended style for new proofs.

The function is `memcmp(a, b, n)` from the zip-2005 guest: twelve RISC-V instructions that
compare `n` bytes at `a` and `b`. The theorem holds for every `n`: the result is zero exactly
when the bytes agree.

## 1. The binary as Lean data (layer -1)

`lake exe gen-image` (`Tools/GenImage.lean`) reads the ELF and writes one Lean module per
function. For `memcmp` this is `Cases/Zip2005/Image/F_7803f54c.lean`. It contains the base
address, the 32-bit words, and their decoding into riscv-zkvm instructions (names shortened
here):

```lean
some (.BEQ .x12 .x0 0x0020#13),   -- n = 0: return 0
some (.LBU .x13 .x10 0x000#12),   -- loop: load a byte of a
some (.LBU .x14 .x11 0x000#12),   --       load a byte of b
some (.BNE .x13 .x14 0x001c#13),  --       they differ: return their difference
...
```

The generator is not trusted. The module proves `decode_ok`: riscv-zkvm's decoder turns these
words into this list (`by decide +kernel`). A proof then assumes only that the machine holds
these words at the base (`CodeAt`, `MachineChecked/RiscV/Sym/Core.lean`). A case study
discharges that once from its loaded image.

## 2. The machine and the statement (layer 0)

Everything is stated over riscv-zkvm's `stepSp1`, the step function SP1 executes. The final
theorem, `MemcmpLprog.safe`, uses the judgement `SafeN` (`MachineChecked/RiscV/Safe.lean`; see
[`Architecture.md`](Architecture.md)) in continuation form:

```lean
theorem safe ... (hpc : s.pc = F_7803f54c.base) (hcode : CodeAt F_7803f54c.base F_7803f54c.prog s)
    (hra : s.getReg .x1 = ra) (h10 : s.getReg .x10 = a) (h11 : s.getReg .x11 = b)
    (h12 : s.getReg .x12 = BitVec.ofNat 64 n) ...
    (hk : ∀ t, t.pc = ra &&& ~~~1#64 → t.code = s.code → (∀ addr, t.getMem addr = s.getMem addr) →
      (∀ r, r ∉ clobbered → t.getReg r = s.getReg r) →
      (t.getReg .x10 = 0 ↔
        ∀ i < n, s.getByte (a + BitVec.ofNat 64 i) = s.getByte (b + BitVec.ofNat 64 i)) → ... →
      SafeN G k P t) :
    SafeN G k P s
```

Read it as: if the caller is safe from every state in which `memcmp` can return, then the
caller is safe from the call. "Every state in which it can return" means: at `ra`, with code
and memory unchanged, registers outside `x10`..`x14` unchanged, and `x10` zero exactly when
the bytes agree. Specifications in this form compose by application, through the contract
table ([`Architecture.md`](Architecture.md)).

## 3. The lift (layer 0 to layer 0.5)

The function is lifted to an Lprog program with one function
(`MachineChecked/RiscV/Lift/Lift.lean`):

```lean
def prog : List Instr := F_7803f54c.prog.filterMap id
def F : Fn := ⟨"memcmp", F_7803f54c.base, prog, 0⟩
def fs : List Fn := [F]
```

`liftProg fs` puts a label before each instruction and translates the instruction:

- an operation becomes `Lopn (opOf i)`, an operation shared by all ISAs
  (`lprog/Lprog/Op.lean`). For example, `LBU x13, 0(x10)` becomes
  `load .x13 .b1 false (x10 + 0)`;
- a conditional branch becomes `Lcond` on a comparison, jumping to the label of its target;
- `jalr x0, 0(ra)` becomes `Lret`, a call `Lcall`, a tail call `Ltail`, and `ecall` `Lext`;
- anything the lift does not cover becomes `Labort`.

After the lift, the body mentions nothing RISC-V-specific except register names. The
translation of an operation is proved once for every instruction, against riscv-zkvm's
`execInstrBr` (`opOf_spec`, `lprog-riscv/LprogRiscV/Instance.lean`).

## 4. The proof at Lprog (layer 0.5)

An Lprog state is a stack of activations, a register file and a memory. `Lret` is defined only
when `ra` holds the value the call put there and `sp` is back where it was at the call.
Otherwise the step goes `wrong`, and the judgement at Lprog excludes `wrong`. That judgement
is `LSafeN` (`MachineChecked/RiscV/Lift/Lift.lean`): the generic `Isa.SafeN` of
`lprog/Lprog/Sem.lean`, at the lifted program under SP1. So a proof at Lprog also proves that
the function returns to its caller.

The contract is stated in continuation form, at Lprog:

```lean
theorem contract ... (hpost : ∀ r' m', Post u0 a b n (ofParts r' m') → LSafeN fs G N Q ⟨rest, r', m'⟩) :
    LSafeN fs G N Q ⟨⟨0, 0, ret, top⟩ :: rest, regs, m⟩
```

That is: from the call, every continuation that is safe from the states `Post` describes is
safe. The loop is an induction on the number of bytes left (`loop`); `contract` adds the entry
and the case `n = 0`.

### By hand: one rule per instruction (`MemcmpLprog.lean`)

The generic rules are in `lprog/Lprog/Sem.lean` (`SafeN.label`, `SafeN.goto`, ...) and the
RISC-V rules in `MachineChecked/RiscV/Lift/Rules.lean` (`lsafe_opn`, `lsafe_cond`,
`lsafe_ret`, ...). Each RISC-V rule takes a machine state `u` that the Lprog state stands for
(`Agree (ofParts regs m) u`), so what an instruction reads is stated on `u`, in riscv-zkvm's
terms:

```lean
apply lsafe_opn hf hag (i := .LBU .x13 .x10 0) (by decide) rfl
  (by simp [memOkSp1, memAccess, h10, signExtend12, hva j hj, alignedFor])
intro r1 m1 hag1
```

`(by decide)` finds the instruction in the body. The last argument is SP1's memory check for
the load, which holds because the address is valid. The proof continues from every next Lprog
state, with its agreement with `execInstrBr u i`. At the branch back to the loop head,
`lsafe_cond` splits on the comparison: one side returns, the other applies the induction
hypothesis.

### With `lsym` (`MemcmpLsym.lean`)

`lsym` (`lprog/Lprog/Tactic.lean`, with RISC-V's simp set in
`lprog-riscv/LprogRiscV/Lsym.lean`) does the stepping. It steps through the body, computes
each operation, closes the memory checks of loads and the conditions of returns, and splits at
each `Lcond`. It stops at a loop head. What remains is what the function means: the loop
invariant at its head and the postcondition at each return.

```lean
lsym hf stop [2] with [h10, h11, h12, hra, hsp, hva j hj, hvb j hj]
```

Here the loop is stated on Lprog's register file rather than on an agreeing machine state,
because `lsym` writes registers with `updReg`. `lframe` proves that registers outside
`clobbered` are unchanged. `MemcmpLsym.contract` has the same statement as
`MemcmpLprog.contract`, so the transfer below applies to either proof.

## 5. Back down to the machine

The transfer theorem (`transfer`, `MachineChecked/RiscV/Lift/Transfer.lean`) carries a contract
at Lprog to the machine. Every `stepSp1` step from a state that an Lprog state stands for is
matched at Lprog, and Lprog's `wrong` matches nothing. `SafeN.of_contract` states this for a
function's entry:

```lean
refine SafeN.of_contract hok (g := 0) (fn := F) rfl hpc ... (Post := Post s a b n)
  (fun _ _ hk => contract s a b n hn hva hvb _ _ (agree_ofParts_regsOf s) h10 h11 h12 rfl rfl hk) ?_
```

What remains is to read the returned machine state off the Lprog state that stands for it
(`hag`). The proof of `safe` contains no symbolic execution and does not depend on how the run
was found.

## Where to go next

- A function with a loop, a call and a system call: `Cases/Zip2005/Runtime/WriteVectored.lean`
  (by hand) and `WriteVectoredLsym.lean` (with `lsym`). The call to `sys_write` uses
  `sys_write`'s contract at Lprog, which tail-calls `syscall_write`; its `WRITE` is SP1's
  execution context.
- Small C programs compiled by clang, decompiled with `decompile --to lean` and proved with
  `lsym`: [`Cases/Hardening/`](../Cases/Hardening/README.md).
- Straight-line kernels proved directly over the machine: [`Cases/CatCrypt/`](../Cases/CatCrypt/README.md)
  and `MachineChecked/RiscV/Lift/Block.lean`.
- Using the result: `Cases/Zip2005/Runtime/Memcmp.lean` specialises `MemcmpLprog.safe` to
  doubleword-aligned blocks of `8k` bytes (`memcmp_blocks_spec`, and 64 and 32 bytes in
  `memcmp8_spec`, `memcmp4_spec`).
- What the lift does not cover yet, and what comes after layer 0.5:
  [`ROADMAP.md`](../ROADMAP.md) and [`MachineChecked/RiscV/LIMITS.md`](../MachineChecked/RiscV/LIMITS.md).
