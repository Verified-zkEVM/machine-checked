/-
  Lprog.Contract

  A function's contract over the register file and the memory, for any instruction set: from
  its entry, with a precondition on the return address, the stack pointer, the registers and
  the memory, it is safe if every state that satisfies the postcondition when it returns is.
  This is the form `lsym … using [specs]` (`Lprog/Tactic.lean`) applies at a call or a tail
  call: the callee's index is the contract's, the precondition is a side goal, and the
  continuation is taken up after the return. Contracts compose: a caller's proof uses its
  callees' contracts, and gives its own.

  ## Main definitions

  * `Isa.Contract`

  ## Main results

  * `Isa.Contract.run`
-/

import Lprog.Sem

namespace Lprog

namespace Isa

variable {I : Isa} {p : Lprog I.Op I.Reg} {E : Type} {c : Context I E}

/-- **A contract of the function at index `f`** over the register file: from its entry, with
    the return address `ret` and the stack pointer `top` of its frame, where `Pre ret top regs m`
    holds, it is safe for any `G`, budget and `Q` if every state `⟨rest, r', m'⟩` it may return
    to with `Post ret top regs m r' m'` is. -/
def Contract (I : Isa) (p : Lprog I.Op I.Reg) {E : Type} (c : Context I E) (f : Nat)
    (Pre : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → Prop)
    (Post : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → (I.Reg → BitVec 64) → I.M → Prop) :
    Prop :=
  ∀ (G : State I → Prop) (n : Nat) (Q : State I → Prop) (ret top : BitVec 64) (rest : List Frame)
    (regs : I.Reg → BitVec 64) (m : I.M), Pre ret top regs m →
    (∀ r' m', Post ret top regs m r' m' → I.SafeN p c G n Q ⟨rest, r', m'⟩) →
    I.SafeN p c G n Q ⟨⟨f, 0, ret, top⟩ :: rest, regs, m⟩

/-- **A contract applied**: the precondition, then the continuation. -/
theorem Contract.run {f : Nat} {Pre : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → Prop}
    {Post : BitVec 64 → BitVec 64 → (I.Reg → BitVec 64) → I.M → (I.Reg → BitVec 64) → I.M → Prop}
    (h : I.Contract p c f Pre Post) {G : State I → Prop} {n : Nat} {Q : State I → Prop}
    {ret top : BitVec 64} {rest : List Frame} {regs : I.Reg → BitVec 64} {m : I.M}
    (hpre : Pre ret top regs m)
    (hk : ∀ r' m', Post ret top regs m r' m' → I.SafeN p c G n Q ⟨rest, r', m'⟩) :
    I.SafeN p c G n Q ⟨⟨f, 0, ret, top⟩ :: rest, regs, m⟩ :=
  h G n Q ret top rest regs m hpre hk

end Isa

end Lprog
