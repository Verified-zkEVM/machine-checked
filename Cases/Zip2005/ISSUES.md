# Issues found during verification and documented here
## 1. The specification depends on a `native_decide` axiom (open, 2026-10-14)

**What.** `#print axioms Cases.Zip2005.guest_loaded_run` lists, besides `propext`,
`Classical.choice` and `Quot.sound`,
`CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt._native.native_decide.ax_1_1`. The lemma
`q_nsmul_Gpt : PALLAS_SCALAR_CARD • Gpt = 0` (the order of the Pallas generator) is proved
by `native_decide` in the vendored `CompElliptic`, and the specification's own definitions
use it: `Spec/Zip2005.lean` asserts it in the axioms of `commitIvk`, `noteCommit`,
`DerivesComponents`, `RecoveryStatement` and the key-binding statements. So it is in the
trust base of the statement itself, not only of a proof about it.

**Why it matters.** The repository's rules allow no `native_decide`: it trusts the
compiled evaluator and the code generator, not just the kernel. The end theorem
currently does not meet that rule, independently of anything about the guest.

**Options.** (a) Prove `q_nsmul_Gpt` by kernel computation (`decide +kernel` over a
scalar multiplication by a 255-bit number, by double-and-add with GMP-backed `Nat`
arithmetic; the Sinsemilla table check in `Bridge/SinsemillaTable.lean` already does
comparable kernel work). (b) Restructure the definitions so the group order enters only
as a hypothesis of the theorems that need it. (c) Accept it explicitly as a stated trust
assumption. (a) is the first thing to try; it needs editing the vendored `CompElliptic`
file, which is a third-party source kept under its own licence.

## 2. The `panic_with_hook` premise does not constrain the heap (open, 2026-10-14)

**What.** `Runtime.Panic.pwhIface.Holds Owned.env C` says `panic_with_hook` (`0x7803b8d0`)
never accepts from any state satisfying `Pre Owned.env C pwhIface`: the image's code, the
stack in range, the protected statics (both hooks) at their load values, and the owned
hasher invariant. Nothing in that precondition says the TLSF heap is well formed
(`Owned.env.inv` sees only the hasher's two doublewords). The same holds for the second
formatting premise added in M1 (`Runtime.PanicEntries.oomIface`).

**Why it is likely false.** `panic_with_hook` formats the message into a heap `String`: it
calls `__rust_alloc`/`__rust_realloc` and writes the returned buffer. From a state whose
allocator control block is arbitrary, `alloc` can return a pointer into the stack, the
formatting writes then overwrite a saved return address, and control can reach an accepting
`syscall_halt(0)`. So the premise, as stated, is not known to be satisfiable and is probably
false, which would make every theorem resting on it vacuous on inputs the statement
rejects (the T1 pattern again, one level down).

**Fix (part of M1).** State both formatting premises under the heap invariant the allocator
proofs already use (`Tlsf.Rep` for the control block at `0x78040620` and the arena at
`0x78048980`, with the guest's live blocks as used blocks), and thread that invariant to
every panic call site. No theorem has been weakened; the premises are restated before
anything is built on them.
