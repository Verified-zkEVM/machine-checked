# CompElliptic

Computable elliptic curves for Lean 4, built on and in the style of
[CompPoly](https://github.com/Verified-zkEVM/CompPoly). The aim is a computable development of
elliptic curves, and later pairings, with correct-by-construction types, for reasoning about
elliptic-curve arithmetic in verified settings such as zero-knowledge circuits. The first
curve form is short Weierstrass over the Pasta (Pallas/Vesta) cycle.

This is a vendored copy, kept for the zip-2005 specification. It holds only the modules that
specification needs. Upstream's design notes, `TODO.md`, `TrustBoundary.lean`, CI scripts
and the fast Vesta arithmetic (`Curves/Pasta/Fast/`) are not included.

## Contents

| module | contents |
| --- | --- |
| `Fields/Pasta.lean` | The Pasta base and scalar prime fields, with Pratt primality certificates. |
| `Fields/Sqrt.lean` | A computable Tonelli–Shanks square root for prime fields, sound and complete, with `pallasBase` and `vestaBase` instances. |
| `Fields/Residue.lean` | Higher-power residues: a power that misses 1 certifies a non-residue. |
| `CurveForms/ShortWeierstrass.lean` | The short-Weierstrass affine group law with `SWCurve`/`SWPoint` types and the full `AddCommGroup (SWPoint E)` instance. Associativity is transported from Mathlib's `WeierstrassCurve.Affine.Point`. |
| `CoordinateSystem.lean` | A curve-form-agnostic `CoordinateSystem`: a carrier with a validity predicate, an equivalence on representatives and computable operations, giving an `AddCommGroup` on the quotient. Affine coordinates are the `Rel = Eq` instance. |
| `Curves/Pasta.lean` | Pallas and Vesta as `SWCurve` instances. |
| `CurveOrder.lean`, `Curves/PastaOrder.lean` | A prime-order group's order pinned without point counting, and the orders of the Pasta and iso-Pasta groups. |
| `ScalarMul.lean` | Scalar multiplication by binary double-and-add. |
| `Curves/PallasOrderCert.lean` | Local addition: the order of the Pallas generator by a certificate the kernel checks (see below). |
| `Curves/IsoPasta.lean`, `Isogenies/` | The iso-Pasta curves (for hashing to Pallas and Vesta) and their degree-3 isogenies, proved to be group homomorphisms. |
| `Encodings/` | The protocol's integer, bit and byte conversions, and the compressed Pasta point encoding (`toBytes`). |

## Design principles

- **Separate types, explicit conversions.** Group elements, their internal representations,
  tagged coordinates and encoded values ("depictions") are distinct types. Every conversion
  is a named function; there are no coercions across levels. Each form puts its validity
  conditions in the type, so illegal states cannot be represented.
- **No hidden mistakes.** The API turns common cryptographic errors (a non-canonical encoding
  treated as canonical, wrong bit order, coordinates used as a point without an on-curve
  check, circuit cells not tied to their source) into type-level obligations.
- **Re-checkable trust.** Anything beyond the kernel and the standard axioms is confined to
  concrete, closed facts that another tool could reproduce or refute (below).
- **Consistent terminology**, following common cryptographic usage and the Zcash Protocol
  Specification.
- **Efficiency without leaks.** Efficiency choices, such as projective coordinates, must not
  show in the API.

## Trust

General, quantified theorems depend only on `propext`, `Classical.choice` and `Quot.sound`.
`native_decide`, which trusts the compiler, is allowed only for concrete, closed facts with no
free variables: a primality certificate, a field's cardinality, the order of a fixed root of
unity, a residuosity check. Any computer-algebra system could recompute these, so a wrong
result could be caught by disagreement. Kernel `decide` is preferred where it is feasible,
since it removes the compiler from the trusted base (though not GMP).

Some lemmas in this copy still use `native_decide` (for example in `Fields/Sqrt.lean` and
`Curves/PastaOrder.lean`). The one the zip-2005 statement depended on, `q_nsmul_Gpt` (the
order of the Pallas generator), is now proved by a double-and-add certificate checked with
`decide +kernel` (`Curves/PallasOrderCert.lean`; see [`ISSUES.md`](../../ISSUES.md) #1).
`Spec/Zip2005.lean` asserts that every entry of the zip-2005 specification's axiom census
depends only on the three standard axioms.

## Licence

Dual-licensed under the Apache License, Version 2.0, or the MIT license, at your option.
Claude Opus 4.8 was used in upstream's development.
