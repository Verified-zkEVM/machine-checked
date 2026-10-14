import Lean.Elab.Tactic
import Cases.Zip2005.Spec.Clean.Halo2.QueryCorrect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.do.legacy true
set_option backward.isDefEq.respectTransparency false

/-!
# Query-declaration tactic

`query_correct` proves the routine local law that `queriedCells` contains valid query
atoms and covers every ordinary query used by the resulting gate or lookup expressions.
Extra declarations remain permitted because Halo 2 closures may issue a query whose
result is not used in the final expression.
-/

namespace Halo2

-- v4.33 port: see `Halo2.Expression.sub_unfold`.
attribute [query_correct] Expression.neg_unfold Expression.sub_unfold

/-- Prove concrete query-declaration goals from expression and list structure. -/
macro "query_correct" : tactic =>
  `(tactic| simp_all! +zetaDelta [query_correct])

end Halo2
