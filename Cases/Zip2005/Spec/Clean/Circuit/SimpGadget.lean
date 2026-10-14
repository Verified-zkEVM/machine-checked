import Mathlib.Init
import Lean.Meta.Tactic.Simp.SimpTheorems
import Lean.Meta.Tactic.Simp.RegisterCommand
import Lean.LabelAttribute

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.do.legacy true
set_option backward.isDefEq.respectTransparency false

register_simp_attr circuit_norm
register_simp_attr explicit_circuit_norm
register_simp_attr explicit_provable_type
