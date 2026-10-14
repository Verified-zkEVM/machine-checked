import Lean.Meta.Tactic.Simp.RegisterCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.do.legacy true
set_option backward.isDefEq.respectTransparency false

/-- Structural reductions used by the `query_correct` tactic. -/
register_simp_attr query_correct
