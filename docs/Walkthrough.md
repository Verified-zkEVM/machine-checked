# Walkthrough: `memcmp`, from the ELF to its specification

This guide follows one complete proof, `Cases/Zip2005/Runtime/MemcmpLprog.lean`, through every
layer of the framework that exists today. It is the shape every new proof is meant to take:
load, lift, prove at the low logical program, carry the result down. Read it next to the file.

The function is `memcmp(a, b, n)` from the zip-2005 guest: twelve RISC-V instructions that
compare `n` bytes at `a` and `b` and return zero exactly when they agree. The theorem is
for every `n`.

## 1. The binary as Lean data (layer -1)

`lake exe gen-image` (`Tools/GenImage.lean`) reads the ELF and writes one Lean module per
function. For `memcmp` that is `Cases/Zip2005/Image/F_7803f54c.lean`: its base address, its
32-bit words, and their decoding into riscv-zkvm instructions:

```lean
some (.BEQ .x12 .x0 0x0020#13),   -- n = 0: return 0
some (.LBU .x13 .x10 0x000#12),   -- the loop: load a byte of a
some (.LBU .x14 .x11 0x000#12),   --           load a byte of b
some (.BNE .x13 .x14 0x001c#13),  --           they differ: return their difference
...
```

The tool is untrusted: the module proves `decode_ok`, that riscv-zkvm's own decoder gives
this list from these words, by kernel computation. A proof then assumes only that the machine
holds the words at the base (`CodeAt`), which a case discharges once from its loaded image.

## 2. The machine and the statement (layer 0)

Everything is stated over riscv-zkvm's `stepSp1`, the step SP1 executes. The final theorem,
`safe`, is in the framework's judgement `SafeN` (`MachineChecked/RiscV/Safe.lean`), in
continuation form:

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

Read it as: if the caller is safe from every state `memcmp` can return in (at `ra`, memory
and code untouched, the result in `x10` zero exactly when the bytes agree), then the caller
is safe from the call. Specifications in this form compose by application, through the
contract table (`docs/Architecture.md`).

## 3. The lift (layer 0 to layer 0.5)

The instructions are lifted to a low-logical-program body (`MachineChecked/RiscV/Lprog`):

```lean
def prog : List Instr := F_7803f54c.prog.filterMap id
theorem wf : WF prog := by unfold WF; decide      -- every branch lands inside the function
```

`lift prog` puts a label before each instruction and translates the instruction:
- an operation becomes `Lopn (opOf i)`, a shared operation (`MachineChecked/Lprog/Op.lean`):
  `LBU x13, 0(x10)` becomes `load "x13" .b1 false (x10 + 0)`;
- a conditional branch becomes `Lcond` on a comparison, to the label of its target;
- `jalr x0, 0(ra)` becomes `Lret`.

Nothing in the body mentions RISC-V any more except register names. The translation is
proved once, for every instruction (`opOf_spec`), against riscv-zkvm's own `execInstrBr`.

## 4. The proof at Lprog (layer 0.5)

The body is run with one rule per instruction kind (`MachineChecked/RiscV/Lprog/Lift.lean`):
`reaches_label`, `reaches_opn`, `reaches_cond`, `reaches_goto`, `halts_ret`. Each takes a
machine state `u` the Lprog state stands for (`Agree (ofParts regs m) u`), so what an
instruction reads is stated on `u`, in riscv-zkvm's terms:

```lean
apply reaches_opn hag (i := .LBU .x13 .x10 0) (by decide) rfl
  (by simp [memOkSp1, memAccess, h10, signExtend12, hva j hj, alignedFor])
intro r1 m1 hag1
```

`(by decide)` finds the instruction in the body; the last argument is SP1's memory check for
the load, which holds because the address is valid. The rule hands back the next Lprog state
and its agreement with `execInstrBr u i`.

The loop is an induction on the number of bytes left (`loop`). At the branch back to the
loop head, `reaches_cond` splits on the comparison; one side returns, the other applies the
induction hypothesis. `halts` adds the entry and the empty case. The result:

```lean
theorem halts ... : rvIsa.Halts (lift prog) (Post u0 a b n) ⟨0, regs, m⟩
```

the run of the body from its first label halts in a state satisfying `Post`.

## 5. Back down to the machine

The lift's simulation carries the Lprog run to a run of `stepSp1` from any machine state the
entry Lprog state stands for (`sim_entry`, `reach_of_halts`), and the bridge passes `SafeN`
back along it (`SafeN.of_reaches`):

```lean
refine SafeN.of_reaches (reach_of_halts wf (sim_entry (fun _ => 0) hc hpc)
  (halts s a b n hn hva hvb _ _ (agree_ofParts_regsOf _ s) h10 h11 h12)) ?_
```

What remains is to read the machine state at the end off the Lprog state that stands for it
(`hs'.agree`, `hs'.pc`). Nothing symbolic is left in the proof, and nothing in it depends on
how the run was found.

## Where to go from here

- A function with a call out of it: `Cases/Zip2005/Runtime/WriteVectored.lean`. The run at
  Lprog stops at the call, the call is taken over the machine with the callee's
  specification, and `sim_return` resumes at Lprog after it.
- Straight-line kernels: `Cases/CatCrypt/` and `MachineChecked/RiscV/Lprog/Block.lean`.
- What is not lifted yet (calls inside Lprog, indirect jumps, system calls) and what comes
  after layer 0.5: [`ROADMAP.md`](../ROADMAP.md).
