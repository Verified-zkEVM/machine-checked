import Cases.Zip2005.Spec.Clean.Halo2
import Cases.Zip2005.Spec.Clean.Circuit
import Cases.Zip2005.Spec.Clean.Utils.Tactics
import Cases.Zip2005.Spec.Zcash.Circuits.Specs.Pallas
import Cases.Zip2005.Spec.Zcash.Circuits.Ecc.Defs

set_option autoImplicit false
set_option backward.do.legacy true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace Zcash.Circuits

open Halo2

theorem Point.eval_eq (env : Placed Environment Fp) (point : Point (AssignedCell Fp)) :
    eval env point = { x := eval env point.x, y := eval env point.y } := by
  simp only [circuit_norm, explicit_provable_type]

theorem Point.eval_eq_prover (env : Placed ProverEnvironment Fp)
    (point : Point (AssignedCell Fp)) :
    eval env point = { x := eval env point.x, y := eval env point.y } := by
  simp only [circuit_norm, explicit_provable_type]

/-- Witgen (prover-program) evaluation of a `Point` is componentwise. -/
theorem Point.witgen_eval_eq (ctx : Witgen.CtxOver Fp (Placed ProverEnvironment Fp))
    (point : Point (Witgen.FExprOver Fp (AssignedCell Fp))) :
    Witgen.eval ctx point = { x := Witgen.FExprOver.eval ctx point.x, y := Witgen.FExprOver.eval ctx point.y } := by
  simp only [circuit_norm, explicit_provable_type]
end Zcash.Circuits
