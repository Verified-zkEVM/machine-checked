import Mathlib.Data.Nat.Init
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Prime
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Data.List.Prime
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The Mathlib the ZIP 2005 proofs are written against

The machine-level proofs of ZIP 2005 use Mathlib's tactics (`push_neg`, `positivity`, …), its
lemmas and its `simp` set. They received them through the executor, which until `ad1c775`
imported the precompile proofs (`Cases/Zip2005/Precompile`) and with them these modules. The
framework no longer imports Mathlib, so the proofs that use it import this file.
-/
