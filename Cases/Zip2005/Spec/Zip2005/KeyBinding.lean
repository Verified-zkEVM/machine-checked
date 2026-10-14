import Cases.Zip2005.Spec.Zip2005.Recovery

set_option autoImplicit false

/-!
# Key binding

ZIP 2005 § Rationale → 'Security analysis' → 'Security argument for key binding'.

The ZIP restates the key-relevant part of the Recovery Statement as a
self-contained condition on a witness, and defines what it means to break it. The
shape is the point: `qk_or_sk` is a **tagged union**, not a pair of optional
fields conditioned on a flag, and the ZIP is explicit that the tagged form is
*strictly stronger* — it also forbids collisions *across* the two branches — and
that the extra strength "is required for Spend Authorization, not incidental".

## What is here and what is not

The definitions are transcribed. The ZIP's **theorem** — that a classical
adversary making at most `q_kb` queries breaks key binding with probability at
most `q_kb(q_kb − 1)/r_P`, and its QROM lift to `O(q_kb³/r_P)` — is not, and
could not be from this module alone: it is a random-oracle-model statement about
five oracles (`H^rivk_ext`, `H^rivk_legacy`, `H^rivk_int`, `H^ask`, `H^nk`),
needing a probability framework and Zhandry's compressed-oracle technique. That
machinery is where `zcash/ironwood`'s `Zcash/Security/KeyBinding/` and
`Zcash/Common/RelationProbability` live, and connecting to it is separate work.

What this module does give is the exact predicate such a theorem would be about,
plus the structural facts that do not need probability.
-/

namespace Zip2005

open Zcash.Circuits (Fp Fq Point)

/-! ## The tagged union -/

/-- `qk_or_sk ⦂ QK(𝔹^𝕐[ℓ_qk/8]) | SK(𝔹^[ℓ_sk])`.

A tagged union, deliberately: the branch is carried *by the witness*, so two
witnesses in different branches are comparable and a cross-branch collision
counts as a break. Modelling this as, say, a pair of `Option`s plus a `use_qsk`
flag would lose exactly that. -/
inductive QkOrSk where
  /-- The quantum branch, carrying `qk`. -/
  | QK : List UInt8 → QkOrSk
  /-- The classical branch, carrying `sk`. -/
  | SK : List UInt8 → QkOrSk
  deriving DecidableEq, Repr

/-- The witness `w = (ivk, ak^ℙ, nk, rivk_ext, rivk, qk_or_sk)` of the ZIP's
key-binding condition. -/
structure KeyBindingWitness where
  /-- `ivk`. -/
  ivk : Fp
  /-- `ak^ℙ ⦂ ℙ*`. -/
  akP : Point Fp
  /-- `nk ⦂ 𝔽_{q_P}`. -/
  nk : Fp
  /-- `rivk_ext ⦂ 𝔽_{r_P}`. -/
  rivkExt : Fq
  /-- `rivk ⦂ 𝔽_{r_P}`. -/
  rivk : Fq
  /-- The tagged authorisation branch. -/
  qkOrSk : QkOrSk

namespace KeyBindingWitness

/-- `ak = Extract_ℙ(ak^ℙ)`, as the condition's `where` clause defines it. -/
def ak (w : KeyBindingWitness) : Fp := extractP w.akP

/-- The projection a break must differ in: `(ak, nk, rivk, qk_or_sk)`.

Note what is *absent*: `ak^ℙ` itself, and hence the `ỹ` sign bit. Two witnesses
differing only in that sign are **not** a break. The ZIP is explicit that this is
a deliberate relaxation — it is what lets `ak` be a single `𝔽_{q_P}` element —
bought at a stated factor-2 loss in concrete security. -/
def projection (w : KeyBindingWitness) : Fp × Fp × Fq × QkOrSk :=
  (w.ak, w.nk, w.rivk, w.qkOrSk)

end KeyBindingWitness

/-! ## The condition -/

/-- The ZIP's key-binding condition on a witness:

```
   match qk_or_sk with
     QK(qk) ⇒ rivk_ext = H^rivk_ext_qk(ak, nk)
     SK(sk) ⇒ BindKeys^sk(sk, ak^ℙ, nk, rivk_ext)
∧  rivk ∈ { rivk_ext, H^rivk_int_rivk_ext(ak, nk) }
∧  ivk = Commit^ivk_rivk(ak, nk)
∧  ivk ∉ {0, ⊥}      where ak = Extract_ℙ(ak^ℙ)
```

The external/internal distinction is decided **by value** (`rivk = rivk_ext`),
not by a derivation or a flag — a detail the ZIP calls out, and one that matters
to the reduction, since the adversary chooses `rivk` freely.

Note that this condition needs **no** `H^qk`, even on the quantum branch: it
constrains `rivk_ext` in terms of the witnessed `qk`, and never asks where `qk`
came from. Establishing `qk = H^qk(qsk)` is `SoK^qsk.Statement`'s job. So the
`Blake3DeriveKey` parameter that `Zip2005.Recovery` needs does not appear here --
which is worth stating, because it means the key-binding argument is independent
of the one primitive this development does not implement. -/
def KeyBindingCondition (w : KeyBindingWitness) : Prop :=
  (match w.qkOrSk with
    | .QK qk => w.rivkExt = hRivkExtQk qk w.ak w.nk
    | .SK sk => BindKeysSk sk w.akP w.nk w.rivkExt)
  ∧ (w.rivk = w.rivkExt
      ∨ w.rivk = hRivkInt (i2leosp 256 w.rivkExt.val) w.ak w.nk)
  ∧ commitIvk w.rivk w.ak w.nk = some w.ivk
  ∧ w.ivk ≠ 0

/-- A **key-binding break**: two witnesses that satisfy the condition, agree on
`ivk`, and differ in the `(ak, nk, rivk, qk_or_sk)` projection.

Agreeing on `ivk` is what makes this an attack: `ivk` is what the diversified
address commits to, so a break lets one address be opened to two different key
tuples. -/
def KeyBindingBreak (w₁ w₂ : KeyBindingWitness) : Prop :=
  KeyBindingCondition w₁ ∧ KeyBindingCondition w₂
    ∧ w₁.ivk = w₂.ivk
    ∧ w₁.projection ≠ w₂.projection

/-! ## Structural facts

Everything below is independent of the probability argument.
-/

/-- A break is symmetric. -/
theorem KeyBindingBreak.symm {w₁ w₂ : KeyBindingWitness}
    (h : KeyBindingBreak w₁ w₂) : KeyBindingBreak w₂ w₁ :=
  ⟨h.2.1, h.1, h.2.2.1.symm, fun he => h.2.2.2 he.symm⟩

/-- Nothing is a break against itself. -/
theorem not_keyBindingBreak_self (w : KeyBindingWitness) :
    ¬ KeyBindingBreak w w := fun h => h.2.2.2 rfl

/-- **Cross-branch collisions are breaks.** Two witnesses with the same `ivk`,
one on the quantum branch and one on the classical branch, both satisfying the
condition, are a break — no matter what else they agree on.

This is the extra strength the tagged union buys, and the reason the ZIP does not
condition on a `use_qsk` flag: under a flag-conditioned predicate these two
witnesses would never be compared. -/
theorem crossBranch_isBreak {w₁ w₂ : KeyBindingWitness}
    (h₁ : KeyBindingCondition w₁) (h₂ : KeyBindingCondition w₂)
    (hivk : w₁.ivk = w₂.ivk)
    {qk sk : List UInt8} (hq : w₁.qkOrSk = .QK qk) (hs : w₂.qkOrSk = .SK sk) :
    KeyBindingBreak w₁ w₂ := by
  refine ⟨h₁, h₂, hivk, ?_⟩
  intro hproj
  have : w₁.qkOrSk = w₂.qkOrSk := congrArg (fun p => p.2.2.2) hproj
  rw [hq, hs] at this
  exact QkOrSk.noConfusion this

/-- Differing in the sign bit of `ak^ℙ` alone is *not* a break: the projection
does not see it. Stated so that the relaxation is visible as a fact rather than
buried in a definition. -/
theorem sign_flip_not_break {w₁ w₂ : KeyBindingWitness}
    (hak : w₁.ak = w₂.ak) (hnk : w₁.nk = w₂.nk) (hrivk : w₁.rivk = w₂.rivk)
    (hbranch : w₁.qkOrSk = w₂.qkOrSk) :
    ¬ KeyBindingBreak w₁ w₂ := by
  intro h
  exact h.2.2.2 (by
    simp only [KeyBindingWitness.projection, hak, hnk, hrivk, hbranch])

/-- On the classical branch the condition really does exhibit a spending key that
`ak^ℙ`, `nk` and `rivk_ext` all derive from — the content of `BindKeys^sk`. -/
theorem classical_binds {w : KeyBindingWitness} {sk : List UInt8}
    (h : KeyBindingCondition w) (hs : w.qkOrSk = .SK sk) :
    BindKeysSk sk w.akP w.nk w.rivkExt := by
  obtain ⟨hmatch, -⟩ := h
  rw [hs] at hmatch
  exact hmatch

/-- On the quantum branch it pins `rivk_ext` to `H^rivk_ext_qk(ak, nk)`. -/
theorem quantum_binds {w : KeyBindingWitness} {qk : List UInt8}
    (h : KeyBindingCondition w) (hq : w.qkOrSk = .QK qk) :
    w.rivkExt = hRivkExtQk qk w.ak w.nk := by
  obtain ⟨hmatch, -⟩ := h
  rw [hq] at hmatch
  exact hmatch

/-- The Recovery Statement's key-relevant conjuncts really are this condition, on
the classical branch: given a Recovery Statement and a `σ_sk`, the witness it
determines satisfies `KeyBindingCondition`.

This is the tie that makes the key-binding analysis about the deployed statement
rather than about a separate predicate that merely resembles it. -/
theorem recoveryStatement_keyBinding_classical
    {b3 : Blake3DeriveKey} {SigQsk SigSk : Type} {S : SoKSchemes b3 SigQsk SigSk}
    {T : RehashedTree merkleDepthOrchard} {pi : PrimaryInput}
    {aux : AuxiliaryInput SigQsk SigSk merkleDepthOrchard} {σ : SigSk}
    (h : RecoveryStatement b3 S T pi aux) (hs : aux.sigmaSk = some σ) :
    ∃ sk ivk, KeyBindingCondition
      { ivk := ivk, akP := aux.akP, nk := aux.nk, rivkExt := aux.rivkExt,
        rivk := aux.rivk, qkOrSk := .SK sk } := by
  obtain ⟨ivk, -, -, -, -, -, hsk, hrivk, hcommit, hne, -⟩ := h
  obtain ⟨sk, -, hbind⟩ := S.soundSk aux.akP aux.nk aux.rivkExt pi.sighash σ (hsk σ hs)
  exact ⟨sk, ivk, hbind, hrivk, hcommit, hne⟩

end Zip2005
