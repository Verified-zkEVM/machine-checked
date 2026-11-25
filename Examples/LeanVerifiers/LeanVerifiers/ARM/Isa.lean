/-
  LeanVerifiers.ARM.Isa

  AArch64 at Lprog, for the pilot (`docs/NativeVerifiers.md`, M0.5): the shared operations over
  AArch64's registers, `x30` the link register, and a memory of bytes by address, read and
  written little-endian at each width.

  It is a model, not yet tied to arm64-semantics: no access faults, and nothing here says the
  lift agrees with the machine (M4). What is proved with it is about the lifted program.

  ## Main definitions

  * `Bytes`, `loadLE`, `storeLE`, `byteMem`, `armIsa`, `ctx`
-/

import Lprog.Tactic
import Lprog.ARM.Reg

namespace LeanVerifiers.ARM

open Lprog Lprog.ARM

/-- A memory: a byte at each address. -/
abbrev Bytes := BitVec 64 → BitVec 8

/-- The `n` bytes from `a`, little-endian. -/
def loadLE (m : Bytes) (a : BitVec 64) : Nat → BitVec 64
  | 0 => 0
  | n + 1 => (m a).zeroExtend 64 ||| (loadLE m (a + 1) n <<< 8)

/-- The low `n` bytes of `v` written from `a`, little-endian. -/
def storeLE (m : Bytes) (a v : BitVec 64) : Nat → Bytes
  | 0 => m
  | n + 1 => storeLE (fun b => if b = a then v.truncate 8 else m b) (a + 1) (v >>> 8) n

/-- The memory of bytes: no access faults. -/
def byteMem : Mem Bytes where
  load w a m := some (loadLE m a w.bytes)
  store w a v m := some (storeLE m a v w.bytes)

/-- AArch64 over the shared operations, with that memory. -/
abbrev armIsa : Isa := Isa.ofOps Reg .x30 .sp Bytes byteMem

/-- No external calls, and nothing accepts: the verifiers make no system call. -/
def ctx : Context armIsa Unit := ⟨fun _ _ _ _ => False, fun _ _ _ => False⟩

attribute [lsym_simp] armIsa byteMem

end LeanVerifiers.ARM
