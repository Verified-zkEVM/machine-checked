/-
  Zip2005 — the ZIP 2005 specification, as Lean.

  ZIP 2005, "Ironwood Quantum Recoverability": <https://zips.z.cash/zip-2005>.

  This is a faithful transcription of the ZIP's own mathematics — its constants,
  the derivations it adds or changes, its Proposed Recovery Statement, and its
  key-binding condition. It says nothing about compiled code; relating the SP1
  guest to it is the next phase, and `Zip2005.Divergences` records the gap.

  Everything ZIP 2005 *imports* from the protocol specification comes from
  `zcash/ironwood`, the official Lean formalisation of the Zcash protocol for the
  Ironwood pool — which is the pool this ZIP is about. `Zip2005.Imported` is the
  single place where each borrowed name is pinned to a definition there.

  See `spec/README.md` for the layout, the trust boundary, and what is missing.
-/
import Cases.Zip2005.Spec.Zip2005.Constants
import Cases.Zip2005.Spec.Zip2005.Encoding
import Cases.Zip2005.Spec.Zip2005.Blake2b
import Cases.Zip2005.Spec.Zip2005.Prf
import Cases.Zip2005.Spec.Zip2005.Imported
import Cases.Zip2005.Spec.Zip2005.LeadBytes
import Cases.Zip2005.Spec.Zip2005.KeyComponents
import Cases.Zip2005.Spec.Zip2005.Sending
import Cases.Zip2005.Spec.Zip2005.Recovery
import Cases.Zip2005.Spec.Zip2005.KeyBinding
import Cases.Zip2005.Spec.Zip2005.Divergences
import Cases.Zip2005.Spec.Zip2005.Vectors

import Cases.Zip2005.Spec.Zcash.Meta.AxiomCheck

/-!
# Trust boundary

`assert_axioms` is `zcash/ironwood`'s own census gate (`Zcash.Meta.AxiomCheck`):
it fails the build unless the named declaration depends only on Lean's three
standard axioms. Reusing their gate rather than writing one keeps this package
held to the same standard as the dependency it rests on.

The entries below are the endpoints — the definitions a reader of ZIP 2005 would
look for. If a future import pulls `native_decide`'s `Lean.ofReduceBool` into the
closure of any of them, the build breaks rather than the axiom base drifting
silently. That matters here: `CompElliptic` deliberately admits `native_decide`
for some closed concrete facts, gated and censused, so the question of whether
any of it reaches *us* is one to answer mechanically rather than by reading.

The conformance checks in `Zip2005.Vectors` and `Zip2005.Blake2b` use `#guard`,
which evaluates at elaboration time and emits no proof term — so unlike
`native_decide` they add nothing to the axiom base. That is the same choice
`Zip2005Asm.lean` makes, for the same reason.
-/

/-! ## The measured result

Everything below rests on Lean's three standard axioms, the Pallas group included.
The prime-order witness `[q] G = 𝒪` (`CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt`)
was this census's one `native_decide` fact; it is now proved from a double-and-add
certificate checked by kernel `decide`
(`Spec/CompElliptic/Curves/PallasOrderCert.lean`), so no entry below carries a
`+native` flag, and a regression to `native_decide` would fail this file.
-/

/-! ### On Lean's three standard axioms -/

-- The ZIP's own new derivations.
assert_axioms Zip2005.hRcmOrchard
assert_axioms Zip2005.hPsiOrchard
assert_axioms Zip2005.hRivkExtQk
assert_axioms Zip2005.hRivkInt
assert_axioms Zip2005.hQsk
assert_axioms Zip2005.deriveRcmOrchard
assert_axioms Zip2005.allowedLeadBytes

/-! ### Through the Pallas group -/

-- The § 4.2.3 derivation procedure names `[ask] 𝒢^Orchard`, hence the group.
assert_axioms Zip2005.DerivesComponents

-- The statement, and the key-binding condition.
assert_axioms Zip2005.RecoveryStatement
assert_axioms Zip2005.KeyBindingCondition
assert_axioms Zip2005.KeyBindingBreak
assert_axioms Zip2005.BindKeysSk

-- The imported protocol functions, so a drift in the dependency is caught here.
assert_axioms Zip2005.commitIvk
assert_axioms Zip2005.noteCommit
assert_axioms Zip2005.merkleCRH
assert_axioms Zip2005.deriveNullifier
assert_axioms Zip2005.prfNfOrchard
assert_axioms Zip2005.spendAuthRandomizePublic

-- The primitives this package adds.
assert_axioms Zip2005.Blake2b.blake2b
assert_axioms Zip2005.prfExpand
assert_axioms Zip2005.reprP

-- The divergence record.
assert_axioms Zip2005.GuestChecks
assert_axioms Zip2005.recovery_implies_guest
assert_axioms Zip2005.guest_plus_gaps_gives_recovery
