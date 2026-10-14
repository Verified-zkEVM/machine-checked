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

/-! ## The measured split

The census below is in two halves, and the boundary was found by running it
rather than by reading code.

**Everything ZIP 2005 itself adds rests on Lean's three standard axioms.** The
new derivations, the lead-byte rule, BLAKE2b, `PRF^expand`, the encodings and the
`§ 4.2.3` procedure all pass the strict gate. That is the part of this
development a reader of the ZIP is being asked to trust, and it is clean.

**Anything that touches the Pallas group inherits exactly one `native_decide`
fact**, `CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt : PALLAS_SCALAR_CARD • Gpt = 0`
— the prime-order witness `[q] G = 𝒪`. `CompElliptic` names it as the sole trust
point of its order argument: every other obligation there is a closed numeric
fact discharged by kernel `decide`, and the library is additionally re-checked by
an independent kernel (`lean4export` + `nanoda`) in its own CI. It is `[q]G = 𝒪`
for one fixed point, which kernel `decide` could in principle establish but not
at a linear `nsmul`'s cost.

It is named explicitly at each entry that depends on it, so the dependency is a
declaration in this file rather than a footnote. The machine side of this repository
rests on Lean's three classical axioms (plus `bv_decide`'s where it is used); this is
the one documented exception, scoped to the imported curve.
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

/-! ### Additionally on the Pallas prime-order witness -/

-- The § 4.2.3 derivation procedure names `[ask] 𝒢^Orchard`, hence the group.
assert_axioms Zip2005.DerivesComponents +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- The statement, and the key-binding condition.
assert_axioms Zip2005.RecoveryStatement +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zip2005.KeyBindingCondition +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zip2005.KeyBindingBreak +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zip2005.BindKeysSk +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- The imported protocol functions, so a drift in the dependency is caught here.
assert_axioms Zip2005.commitIvk +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zip2005.noteCommit +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zip2005.merkleCRH +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zip2005.deriveNullifier +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zip2005.prfNfOrchard
assert_axioms Zip2005.spendAuthRandomizePublic +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)

-- The primitives this package adds.
assert_axioms Zip2005.Blake2b.blake2b
assert_axioms Zip2005.prfExpand
assert_axioms Zip2005.reprP

-- The divergence record.
assert_axioms Zip2005.GuestChecks +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zip2005.recovery_implies_guest +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
assert_axioms Zip2005.guest_plus_gaps_gives_recovery +native(CompElliptic.Curves.Pasta.Pallas.q_nsmul_Gpt)
