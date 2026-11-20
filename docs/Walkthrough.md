# Walkthrough: `gcd`, from its source to a theorem about the machine

This guide follows one small function through every layer that exists today: compile it, load
the binary into Lean, lift it to the low logical program (Lprog), prove a contract there, and
carry the contract down to riscv-zkvm's machine. New proofs are meant to take this shape. Read
it next to the code:

- `Examples/src/rust/basic.rs`, the source, and `Examples/elf/rustbasic.elf`, the binary
  `Examples/build.sh` made of it;
- `Examples/RustBasic/RiscV/Image/`: the binary's words and their lift, written by
  `decompile --to lean --proved`;
- `Examples/RustBasic/RiscV/Proofs.lean`: the contract (`gcd_contract`) and the theorem about the machine
  (`gcd_correct`).

## 1. The source

Euclid's algorithm, in Rust:

```rust
#[no_mangle]
pub extern "C" fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}
```

Nothing below is about this text; it says what the binary is meant to compute.

## 2. The binary

`Examples/build.sh RustBasic` compiles the file and links it at `0x10000`. rustc writes LLVM
IR and clang compiles that for RV64IM at `-O1`, so that the code has no compressed
instructions, which riscv-zkvm's machine does not have. `llvm-objdump -d
Examples/elf/rustbasic.elf` shows the six instructions of `gcd`:

```
0000000000010010 <gcd>:
   10010: 00058a63     	beqz	a1, 0x10024 <gcd+0x14>
   10014: 02b57633     	remu	a2, a0, a1
   10018: 00058513     	mv	a0, a1
   1001c: 00060593     	mv	a1, a2
   10020: fe061ae3     	bnez	a2, 0x10014 <gcd+0x4>
   10024: 00008067     	ret
```

`a0`, `a1`, `a2` and `ra` are the registers `x10`, `x11`, `x12` and `x1`. The loop is the four
instructions from `0x10014`, entered only with `a1` not zero. The compiler is not trusted:
everything that follows is about these words.

## 3. The binary in Lean

`build.sh` then runs

```sh
.lake/build/bin/decompile --to lean --proved Examples/elf/rustbasic.elf . Examples.RustBasic.RiscV.Image
```

which writes `Examples/RustBasic/RiscV/Image.lean` (the list of functions by index: `gcd` is
function 2) and one module per function. `Examples/RustBasic/RiscV/Image/Words.lean` has each
function's name,
address and words, and the functions they decode to:

```lean
-- the words are the ELF's: `words_eq_elf`, checked when this module is built
check_elf_words words "Examples/elf/rustbasic.elf"

/-- The functions the words decode to. -/
def fns : List Fn := words.map fun (name, base, ws) =>
  { name, base := BitVec.ofNat 64 base, prog := ((ws.map (BitVec.ofNat 32)).mapM decode).getD [] }
```

`gcd`'s words are `w2`, six numbers; the first, `363107`, is `0x00058a63`, the `beqz` above.
The instructions are not written out: riscv-zkvm's decoder (`decode`) computes them.

`Examples/RustBasic/RiscV/Image/F2.lean` has the lift of `gcd` as a term, `f2`, and the theorem a
proof steps through:

```lean
/-- **`f2` is the lift of the ELF's words.** -/
theorem f2_eq : (liftProg fns)[2]? = some f2 :=
  getElem?_eq_of_chunks f2_head f2_parts rfl
```

The kernel checks `f2_eq` by evaluation: `f2` is what `liftProg`
(`MachineChecked/RiscV/Lift/Lift.lean`) gives on `fns`. How `decompile` produced the term is
not trusted. What is trusted is that the words in `Words.lean` are the file's: the kernel
cannot read files, so `check_elf_words` reads the ELF when the module is built, with the
tool's own reader, and fails if they differ. A misread word cannot give a false theorem about
the machine, since the final theorem assumes the machine holds the words `fns` was built from
(`Loaded`, below). Beyond that: riscv-zkvm's model and the Lean kernel
([`ELF.md`](ELF.md#4-what-is-trusted-and-the-trust-ladder),
[`Tools/README.md`](../Tools/README.md)).

## 4. The lifted program

`decompile --to lprog --proved Examples/elf/rustbasic.elf` prints the same lift as text:

```
fn gcd 0x10010 0 12
  label 0
    if cmp eq %x11 0 5
  label 1
    set %x12 remu %x10 %x11
  label 2
    set %x10 add %x11 0
  label 3
    set %x11 add %x12 0
  label 4
    if cmp ne %x12 0 1
  label 5
    ret
```

The lift puts a label before each instruction and translates the instruction: an operation
becomes a `set`, a `load` or a `store` on shared operations (`lprog/Lprog/Op.lean`), a branch
a conditional jump to a label, `jalr x0, 0(ra)` a return, `jal ra` a call. The body mentions
nothing of RISC-V but register names. It has twelve entries, a label and an instruction six
times over, so **label `k` is at position `2k`**. The loop's head, label 1, is at position 2.

An Lprog state is a stack of activations, a register file and a memory. An activation
`⟨fn, pc, ret, top⟩` is a function's index, a position in its body, and the return address and
stack pointer of its call. A return is defined only when `ra` and `sp` hold those two values;
otherwise the step goes `wrong`, and the judgement at Lprog (`LSafeN`,
`MachineChecked/RiscV/Lift/Lift.lean`) excludes `wrong`.

## 5. The contract, proved with `lsym`

A contract (`Isa.Contract`, `lprog/Lprog/Contract.lean`) has a precondition on the return
address, the stack pointer, the registers and the memory at entry, and a postcondition that
also sees the registers and the memory at the return:

```lean
theorem gcd_contract : rvIsa.Contract (liftProg fns) sp1Ctx 2
    (fun ret top regs _ => regs .x1 = ret ∧ regs .x2 = top)
    (fun _ _ regs m r' m' =>
      r' .x10 = wgcd (regs .x10) (regs .x11) ∧
      (∀ r, r ∉ gcdClobbered → r' r = regs r) ∧ m' = m) := by
  intro G N Q ret top rest regs m ⟨hra, hsp⟩ hk
  lsym f2_eq stop [2] with [hra, hsp]
  · -- the second argument is zero: the first is the divisor
    exact hk _ _ ⟨by simp [wgcd, hc], fun _ _ => rfl, rfl⟩
  · exact gcd_loop m _ regs rfl hc hra hsp hk
```

The precondition says only that `ra` and `sp` are the frame's. The postcondition: `x10` is the
greatest common divisor (`wgcd a b`, in `Examples/Spec.lean`, is `Nat.gcd` of the two words'
numbers, as a word), registers outside `gcdClobbered` (`x10`, `x11`, `x12`) and the memory
are as they were.

`lsym` (`lprog/Lprog/Tactic.lean`) steps the body from the goal's activation. It computes each
operation, splits at a branch with the condition as `hc`, and at a return closes what it can
of "`ra` and `sp` are as the call left them", using the `with` lemmas. Here it leaves two
goals: the return when `x11` is zero, and the loop's head. `stop [2]` names the head, by
position. With the label's number, `stop [1]`, `lsym` would stop somewhere else and the goal
would be well typed but about another instruction.

**A loop is a lemma**, stated at its head from an arbitrary iteration:

```lean
theorem gcd_loop {G : State rvIsa → Prop} {N : Nat} {Q : State rvIsa → Prop} {ret top : Word}
    {rest : List Frame} (m : MachineState) :
    ∀ n (regs : Reg → Word), (regs .x11).toNat = n → regs .x11 ≠ 0#64 →
      regs .x1 = ret → regs .x2 = top →
      (∀ r' m', r' .x10 = wgcd (regs .x10) (regs .x11) ∧
        (∀ r, r ∉ gcdClobbered → r' r = regs r) ∧ m' = m → LSafeN fns G N Q ⟨rest, r', m'⟩) →
      LSafeN fns G N Q ⟨⟨2, 2, ret, top⟩ :: rest, regs, m⟩ := by
```

The activation `⟨2, 2, ret, top⟩` is function 2 at position 2. The statement is in
continuation form: the state is safe if every state the function may return in is. The proof
is by strong induction on the second argument (`induction n using Nat.strongRecOn`), because
one turn replaces `(a, b)` by `(b, a % b)` and `a % b < b` is all that is known of the new
one. `lsym f2_eq stop [2] with [hra, hsp, hb]` steps one turn of the loop and again leaves two
goals. Where the remainder is not zero the state is at the head again and the
induction hypothesis applies, with `Nat.gcd_rec` relating the two results. Where it is zero the
function returns `b`. The rest of the proof (`Examples/RustBasic/RiscV/Proofs.lean`) is that arithmetic and
the frame.

## 6. Down to the machine

`SafeN.of_isa_contract` (`MachineChecked/RiscV/Lift/Contract.lean`) turns a contract into a
statement about riscv-zkvm's machine. It rests on the transfer theorem
(`MachineChecked/RiscV/Lift/Transfer.lean`): every `stepSp1` step from a state that an Lprog
state stands for is matched at Lprog, and `wrong` matches nothing. The same file defines
`Loaded fs s`: each function of `fs` is in the code of `s`, at its address. The theorem and its
whole proof:

```lean
theorem gcd_correct {G : MachineState → Prop} {k : Nat} {P : Prop} (s : MachineState)
    (hpc : s.pc = 0x10010#64) (hcode : Loaded fns s)
    (hk : ∀ t, t.pc = s.getReg .x1 &&& ~~~1#64 →
      t.getReg .x10 = wgcd (s.getReg .x10) (s.getReg .x11) →
      (∀ a, t.getMem a = s.getMem a) → SafeN G k P t) :
    SafeN G k P s := by
  obtain ⟨fn, hg, hb⟩ : ∃ fn, fns[2]? = some fn ∧ fn.base = 0x10010#64 := ⟨_, rfl, rfl⟩
  refine SafeN.of_isa_contract hok hg (hpc.trans hb.symm) hcode gcd_contract ⟨rfl, rfl⟩ ?_
  rintro t r' m' hag hpc' ⟨h10, -, rfl⟩
  refine hk t hpc' ?_ fun a => (hag.mem a).symm
  rw [← hag.regs, getReg_ofParts, ite_eq_right (by decide)]; exact h10
```

How to read it:

- `s` is any machine state at `gcd`'s entry (`hpc`) whose code holds the binary's functions
  (`hcode`). Nothing else is assumed: not the arguments, not the stack, not the memory.
- `SafeN G k P s` (`MachineChecked/RiscV/Safe.lean`) is safety of `stepSp1`, the step function
  SP1 executes, for `k` steps from `s`.
- `hk` is the caller's side: it must be safe from every state `t` at the return address
  (`ra` with its low bit cleared, as `jalr` computes it) with the greatest common divisor in
  `x10` and the memory `s` had.
- So: the call is safe if what follows it is. This is partial correctness. It says what holds
  if `gcd` returns, not that it does.
- Nothing in the statement mentions Lprog or the lift. In the proof, `hok : ProgOk fns` says
  every function is at a multiple of four (by `decide`), the two `rfl`s are the precondition
  read off `s`, and the last three lines read the result off the machine state that agrees
  with the Lprog one (`hag`).

Statements in this form compose by application ([`Architecture.md`](Architecture.md)).

## 7. What it rests on

```lean
#print axioms Examples.RustBasic.RiscV.gcd_correct
```

reports `propext`, `Classical.choice` and `Quot.sound`, Lean's three. Proofs that use
`bv_decide` add its certificates. `scripts/AxiomCheckExamples.lean` lists every example's theorem,
and CI runs it.

## Where to go next

- The other examples, from straight-line code to a table in read-only data, and the habits
  their proofs share: [`Examples/README.md`](../Examples/README.md).
- Calls through registers, recursion, a function that never returns, signed arithmetic at its
  edges, and two functions of an SP1 guest's runtime with a system call:
  the stress tests and the guest code of [`Examples/README.md`](../Examples/README.md).
- `lsym` in full, and its limits: [`design/Automation.md`](design/Automation.md).
- A whole guest: zip-2005 has its verification in
  [zip-2005-asm](https://github.com/dhsorens/zip-2005-asm).
- What the lift does not cover, and what comes after layer 0.5:
  [`MachineChecked/RiscV/LIMITS.md`](../MachineChecked/RiscV/LIMITS.md) and
  [`ROADMAP.md`](../ROADMAP.md).
