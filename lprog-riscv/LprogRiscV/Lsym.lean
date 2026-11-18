/-
  LprogRiscV.Lsym

  RISC-V's definitions in the simp set of `lsym` (`Lprog/Tactic.lean`): the instance, how an
  operand and an immediate are read, the memory, and the translation of an instruction to an
  operation, so that `lsym` computes RISC-V's operations and their side conditions.
-/

import LprogRiscV.Instance
import Lprog.Tactic

namespace Lprog.RiscV

open RiscvZkvm.Rv64

attribute [lsym_simp] rvIsa rv opnd se12 sh addr opOf rvMem alignedFor signExtend12

end Lprog.RiscV
