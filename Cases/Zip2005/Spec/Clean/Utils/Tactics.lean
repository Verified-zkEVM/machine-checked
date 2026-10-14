-- This file re-exports all tactics from the Tactics directory
import Cases.Zip2005.Spec.Clean.Utils.Tactics.SpecializeAuto
import Cases.Zip2005.Spec.Clean.Utils.Tactics.DecomposeProvableStruct
import Cases.Zip2005.Spec.Clean.Utils.Tactics.SplitProvableStructEq
import Cases.Zip2005.Spec.Clean.Utils.Tactics.SimplifyProvableStructEval
import Cases.Zip2005.Spec.Clean.Utils.Tactics.ProvableStructSimp
import Cases.Zip2005.Spec.Clean.Utils.Tactics.CircuitProofStart

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.do.legacy true
set_option backward.isDefEq.respectTransparency false
