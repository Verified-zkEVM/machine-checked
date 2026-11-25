/-
  LeanVerifiers.ARM.Machine

  The pilot's contracts over the machine: arm64-semantics' `Step`.

  The contracts are proved over a memory of bytes that refuses nothing (`Isa.lean`). The
  machine's memory refuses an access its permissions do not allow; seen as bytes (`bytes`),
  an access it allows is the access of the simple memory (`memAbs`). So a function safe over
  bytes is safe over the machine's memory (`Lprog.allSafe_abs`), and then over the machine
  (`MachineChecked.ARM.Lift.SafeN.of_lift`). What is lost is what partial correctness never
  had: that the function does not fault.

  ## Main definitions

  * `bytes`

  ## Main results

  * `memAbs`: the machine's memory as bytes
  * `SafeN.of_contract`: a contract over bytes, over the machine
  * `memcpy_machine`, `keccak_f_machine`: the pilot's two functions over arm64-semantics
-/

import LeanVerifiers.ARM.Memcpy
import LeanVerifiers.ARM.KeccakF
import MachineChecked.ARM.Lift.Transfer
import Lprog.MemAbs

namespace LeanVerifiers.ARM

open Lprog Lprog.ARM LeanVerifiers.ARM.Signatures
open NativeRustc.Keccak LeanVM.Semantics LeanVM.Parameters
open MachineChecked.ARM.Lift (armMem memWidth read8_write8 armCtx MSafeN Loaded Ret regsOf)

/-- The bytes of a machine memory. -/
def bytes (m : Arm64.Memory) : Bytes := fun a => m.read8 a

/-- A read of the machine's memory is the read of its bytes. -/
theorem readSized_bytes (m : Arm64.Memory) (w : Width) (a : BitVec 64) :
    m.readSized (memWidth w) false a = loadLE (bytes m) a w.bytes := by
  cases w <;>
    simp only [memWidth, Arm64.Memory.readSized, Arm64.Memory.read16, Arm64.Memory.read32,
      Arm64.Memory.read64, Width.bytes, loadLE, bytes, BitVec.add_assoc, BitVec.add_zero,
      Bool.false_eq_true, ↓reduceIte, BitVec.reduceAdd]
  all_goals bv_decide

/-- A write of the machine's memory is the write of its bytes. -/
theorem bytes_writeSized (m : Arm64.Memory) (w : Width) (a v : BitVec 64) :
    bytes (m.writeSized (memWidth w) a v) = storeLE (bytes m) a v w.bytes := by
  funext x
  cases w <;>
    simp only [memWidth, Arm64.Memory.writeSized, Arm64.Memory.write16, Arm64.Memory.write32,
      Arm64.Memory.write64, Width.bytes, storeLE, bytes, read8_write8, BitVec.add_assoc,
      BitVec.add_zero, BitVec.reduceAdd]
  all_goals bv_decide

/-- **The machine's memory as bytes**: an access it allows is the access of the bytes. -/
theorem memAbs : MemAbs armMem byteMem bytes where
  load w a m v h := by
    simp only [armMem] at h
    split at h
    · cases h
      simp only [byteMem, readSized_bytes]
    · cases h
  store w a v m m' h := by
    simp only [armMem] at h
    split at h
    · cases h
      simp only [byteMem, bytes_writeSized]
    · cases h

/-- **The image is a program the transfer theorem is for**: its instructions are four bytes
    each, one after another, since it is made from the ELF's words. -/
theorem program_ok : MachineChecked.ARM.Lift.ProgOk program.fns :=
  Tools.Program.progOk_armProgram _ _ _

/-- **A contract over bytes, over the machine.** If function `g` of the image has a contract
    at Lprog over the memory of bytes, then a running machine at its entry that holds the
    image, with its stack pointer aligned and the precondition true of its registers and the
    bytes of its memory, is safe whenever every state it may return in, with the
    postcondition, is. -/
theorem SafeN.of_contract {g : Nat} {fg : MachineChecked.ARM.Lift.Fun}
    (hg : program.fns[g]? = some fg)
    {Pre : BitVec 64 → BitVec 64 → (Reg → BitVec 64) → Bytes → Prop}
    {Post : BitVec 64 → BitVec 64 → (Reg → BitVec 64) → Bytes → (Reg → BitVec 64) → Bytes → Prop}
    (hcon : armIsa.Contract program.lifted ctx g Pre Post) {prog : Arm64.Program}
    {t : Arm64.State} (hpc : t.pc = fg.addr) (hrun : t.status = .Running)
    (hal : t.spAligned = true) (hld : Loaded prog program.fns t.mem)
    (hpre : Pre (t.regs.read 30) t.sp (regsOf t) (bytes t.mem)) {G : Arm64.State → Prop}
    {N : Nat} {P : Arm64.State → Prop}
    (hk : ∀ s' t', Ret prog program.fns (t.regs.read 30) s' t' →
      Post (t.regs.read 30) t.sp (regsOf t) (bytes t.mem) s'.regs (bytes s'.m) →
      MSafeN prog G N P t') :
    MSafeN prog G N P t := by
  refine MachineChecked.ARM.Lift.SafeN.of_lift program_ok hg hpc hrun hal hld
    (Q := fun s' => s'.stack = [] ∧
      Post (t.regs.read 30) t.sp (regsOf t) (bytes t.mem) s'.regs (bytes s'.m))
    ?_ (fun s' t' hR hq => hk s' t' hR hq.2)
  refine Lprog.allSafe_abs (mem₁ := byteMem) program.lifted ctx armCtx memAbs
    (fun n regs m o h => ⟨h, rfl⟩) (fun _ _ _ h => h)
    (Q := fun s => s.stack = [] ∧ Post (t.regs.read 30) t.sp (regsOf t) (bytes t.mem) s.regs s.m)
    _ ?_
  intro k
  exact hcon _ k _ _ _ [] _ _ hpre fun r' m' hp => Lprog.SafeN.returned ⟨rfl, hp⟩

/-- **`memcpy` over the machine.** A running machine at the entry of `memcpy` that holds the
    image, with its stack pointer aligned and the two regions apart, is safe whenever every
    state it may return in is: at the address in `x30`, with the `n` bytes at `dst` those that
    were at `src`, no other byte changed, and no register but the scratch ones. -/
theorem memcpy_machine {fg : MachineChecked.ARM.Lift.Fun} (hg : program.fns[2]? = some fg)
    {prog : Arm64.Program} {t : Arm64.State} (hpc : t.pc = fg.addr)
    (hrun : t.status = .Running) (hal : t.spAligned = true)
    (hld : Loaded prog program.fns t.mem)
    (hdis : ∀ i < (t.regs.read 2).toNat, ∀ j < (t.regs.read 2).toNat,
      t.regs.read 0 + BitVec.ofNat 64 i ≠ t.regs.read 1 + BitVec.ofNat 64 j)
    {G : Arm64.State → Prop} {N : Nat} {P : Arm64.State → Prop}
    (hk : ∀ s' t', Ret prog program.fns (t.regs.read 30) s' t' →
      Copied (bytes t.mem) (t.regs.read 0) (t.regs.read 1) (t.regs.read 2).toNat (bytes s'.m) →
      Kept (regsOf t) s'.regs → MSafeN prog G N P t') :
    MSafeN prog G N P t :=
  SafeN.of_contract hg memcpy_contract hpc hrun hal hld ⟨rfl, rfl, hdis⟩
    fun s' t' hR hp => hk s' t' hR hp.1 hp.2

/-- **`keccak_f` over the machine.** A running machine at the entry of `keccak_f` that holds
    the image, with its stack pointer aligned, the 25 lanes of `A` at the buffer in `x0`, the
    buffer and the table of round constants outside the 192 bytes below the stack pointer, and
    the image's data in memory, is safe whenever every state it may return in is: at the
    address in `x30`, with Keccak-f[1600] of `A` at the buffer, memory changed only there and
    in the frame, and the callee-saved registers as they were. -/
theorem keccak_f_machine (A : KeccakState) {fg : MachineChecked.ARM.Lift.Fun}
    (hg : program.fns[10]? = some fg) {prog : Arm64.Program} {t : Arm64.State}
    (hpc : t.pc = fg.addr) (hrun : t.status = .Running) (hal : t.spAligned = true)
    (hld : Loaded prog program.fns t.mem)
    (hA : StateAt (bytes t.mem) (t.regs.read 0) A)
    (hap : Apart (t.sp - 192#64) (t.regs.read 0))
    (hH : Holds program.memory (bytes t.mem))
    (hT : ∀ i < 24, Out (t.sp - 192#64) 192 (2097840#64 + BitVec.ofNat 64 (8 * i)))
    {G : Arm64.State → Prop} {N : Nat} {P : Arm64.State → Prop}
    (hk : ∀ s' t', Ret prog program.fns (t.regs.read 30) s' t' →
      StateAt (bytes s'.m) (t.regs.read 0) (keccakF1600 A) →
      (∀ x, 192 ≤ (x - (t.sp - 192#64)).toNat → 200 ≤ (x - t.regs.read 0).toNat →
        bytes s'.m x = bytes t.mem x) →
      (∀ r ∈ calleeSaved, s'.regs r = regsOf t r) → MSafeN prog G N P t') :
    MSafeN prog G N P t :=
  SafeN.of_contract hg (keccak_f_contract A) hpc hrun hal hld
    ⟨rfl, rfl, by simpa [Arm64.State.spAligned] using hal, hA, hap, hH, hT⟩
    fun s' t' hR hp => hk s' t' hR hp.1 hp.2.1 hp.2.2

end LeanVerifiers.ARM
