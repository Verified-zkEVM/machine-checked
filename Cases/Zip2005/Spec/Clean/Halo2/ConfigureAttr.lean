import Lean.Meta.Tactic.Simp.RegisterCommand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.do.legacy true
set_option backward.isDefEq.respectTransparency false

/-- Structural reductions for configure-time selector requirements. -/
register_simp_attr configure_selector_norm

/-- Structural reductions for configure-time query requirements. -/
register_simp_attr configure_query_norm
