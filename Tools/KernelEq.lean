/-
  Tools.KernelEq

  What the modules `decompile --to lean` writes need of the tool to state their theorems: the
  command `kernel_eq`, and the lemmas a function's theorem is built from its parts with
  (`Tools/ToLean.lean`, "A function's theorem in parts"). It imports only `Lean.Elab.Command`
  and Lprog's syntax, not all of `Lean` as `Tools.ToLean` does, so that a written module that
  states a function's theorem does not load the tool: most of the cost of such a module was its
  imports. The namespace is `Tools.ToLean`'s, of which this was part.

  ## Main definitions

  * `chunks`, `flatten_chunks`, `chunk`, `getElem?_eq_of_chunks`
  * `kernel_eq`: an equation proved by `Eq.refl`, for the kernel to check
-/

import Lean.Elab.Command
import Lprog.Syntax

namespace Tools.ToLean

open Lean Elab Command Meta
open _root_.Lprog

/-! ## A function's theorem in parts -/

section
variable {α : Type}

/-- `l` in parts of `k`, at most `n` of them. -/
def chunksAux (k : Nat) : Nat → List α → List (List α)
  | 0, _ => []
  | n + 1, l => if l.isEmpty then [] else l.take k :: chunksAux k n (l.drop k)

/-- `l` in parts of `k`, the last perhaps shorter. -/
def chunks (k : Nat) (l : List α) : List (List α) := chunksAux k l.length l

theorem flatten_chunksAux {k : Nat} (hk : 0 < k) :
    ∀ (n : Nat) (l : List α), l.length ≤ n → (chunksAux k n l).flatten = l
  | 0, l, h => by
    rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp h)]; rfl
  | n + 1, l, h => by
    unfold chunksAux
    split
    · next he => simp [List.isEmpty_iff.mp he]
    · rw [List.flatten_cons, flatten_chunksAux hk n (l.drop k) (by simp; omega)]
      exact List.take_append_drop k l

theorem flatten_chunks {k : Nat} (hk : 0 < k) (l : List α) : (chunks k l).flatten = l :=
  flatten_chunksAux hk _ l (Nat.le_refl _)

end

/-- The parts of `chunk` instructions a function's theorem is checked in. -/
def chunk : Nat := 128

/-- **A function of a program, from its parts.** If the `i`th function of `p` has `f`'s name,
    address and stack bound, and its body in parts of `chunk` is `cs`, whose concatenation is
    `f`'s body, then it is `f`. The two facts are checked apart: the instances that decide
    them are found apart, and not together. -/
theorem getElem?_eq_of_chunks {Op Reg : Type} {p : Lprog Op Reg} {i : Nat} {f : Lfundef Op Reg}
    {cs : List (Lcmd Op Reg)}
    (hh : (p[i]?).map (fun g => (g.name, g.addr, g.depth)) = some (f.name, f.addr, f.depth))
    (hc : (p[i]?).map (fun g => chunks chunk g.body) = some cs)
    (hf : f.body = cs.flatten) : p[i]? = some f := by
  cases hp : p[i]? with
  | none => simp [hp] at hh
  | some g =>
    simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hh hc
    obtain ⟨hn, ha, hd⟩ := hh
    have hb : g.body = f.body := by
      rw [hf, ← hc, flatten_chunks (by decide)]
    cases g; cases f
    simp_all

/-! ## `kernel_eq` -/

/-- `kernel_eq name : a = b` adds the theorem `name : a = b`, proved by `Eq.refl a` for the
    kernel to check: definitional equality, decided by evaluation where it must be, with no
    instance of `Decidable` (Flapjack's syntax has none) and no check by the elaborator first,
    which would be slower than the kernel's. -/
syntax (name := kernelEq) "kernel_eq " ident " : " term : command

@[command_elab kernelEq]
def elabKernelEq : CommandElab := fun stx => do
  let name := (← getCurrNamespace) ++ stx[1].getId
  let (ty, lhs) ← liftTermElabM do
    -- an error in the statement fails the command, not a theorem stated with `sorry`
    let ty ← instantiateMVars (← Term.withoutErrToSorry (Term.elabType stx[3]))
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    let some (_, lhs, _) := ty.eq? | throwError "kernel_eq: {ty} is not an equation"
    if ty.hasMVar then throwError "kernel_eq: {ty} has holes"
    pure (ty, lhs)
  let some (α, _, _) := ty.eq? | throwError "kernel_eq: not an equation"
  let u ← liftTermElabM do
    let s ← inferType α
    match (← whnf s) with
    | .sort u => pure u
    | _ => throwError "kernel_eq: not a type"
  liftCoreM <| addDecl <| .thmDecl {
    name, levelParams := []
    type := ty
    value := mkApp2 (mkConst ``Eq.refl [u]) α lhs }

end Tools.ToLean
