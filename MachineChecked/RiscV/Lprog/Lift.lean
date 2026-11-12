/-
  MachineChecked.RiscV.Lprog.Lift

  From decoded RISC-V to an Lprog program, and SP1's execution context.

  A program is a list of functions of an image, each with its address and its decoded
  instructions (`Fn`). `liftProg fs` lifts each to an Lprog function: instruction `k` becomes
  `Llabel k` followed by its lifted form (`liftI`):

  * an operation (pure, or a load or store) becomes `Lopn` of its shared operation (`opOf`),
    and `auipc` the constant it computes;
  * a conditional branch inside the function becomes `Lcond` on a comparison, to the label of
    its target, and `jal x0` inside the function `Lgoto`;
  * `jal ra` to a function of the program becomes `Lcall` of it, `jal x0` to one `Ltail`;
    `jalr ra` becomes an indirect `Lcall`, and `jalr x0` other than `ret` an indirect `Ltail`,
    with every function of the program as a candidate;
  * `jalr x0, 0(ra)` becomes `Lret`, and `ecall` becomes `Lext`;
  * anything else becomes `Labort`, which goes `wrong`, so a proof at Lprog shows the program
    never meets one.

  A call's return value is the address after it, the value `jal`/`jalr` write to `ra`, and a
  function's address is its entry, so the values code holds are the machine's.

  SP1's execution context (`sp1Ctx`) lets an `Lext` take any outcome riscv-zkvm's `ecall`
  (`sp1Ecall`) gives from a machine state the Lprog state stands for, and accepts at `HALT`
  with exit code `0`. The syscall facts the layer-0 tools use are lemmas about it
  (`RiscV/Lprog/Sp1.lean`).

  The correctness of the lift, by simulation, is `RiscV/Lprog/Transfer.lean`.
-/

import MachineChecked.RiscV.Lprog.Instance

namespace MachineChecked.RiscV.Lprog

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym MachineChecked.Lprog
open MachineChecked.Ascent (Outcome)

/-- A function of an image: its name, its address, its instructions and a stack bound for
    contracts. -/
structure Fn where
  name : String
  base : Word
  prog : List Instr
  depth : Nat := 0

/-- The index of the function whose entry is `a`. -/
def entryOf (fs : List Fn) (a : Word) : Option Nat := fs.findIdx? (·.base == a)

/-- The label an offset reaches from instruction `k`. -/
def tgt (k : Nat) (off : Word) : Nat := ((k : Int) + off.toInt / 4).toNat

/-- The jump from instruction `k` by `off` lands on an instruction of a function of `len`. -/
def jumpOk (k len : Nat) (off : Word) : Bool :=
  off.toInt % 4 == 0 && 0 ≤ (k : Int) + off.toInt / 4 && (k : Int) + off.toInt / 4 < len

/-- The value `auipc` adds to the pc. -/
def auipcOff (imm : BitVec 20) : Word := ((imm.zeroExtend 32 <<< 12 : BitVec 32).signExtend 64)

/-- The target `jalr` computes. -/
def jalrTgt (rs : Reg) (off : BitVec 12) : Expr Reg := .bin .and (addr rs off) (.imm (~~~1#64))

/-- A branch, lifted: `Lcond` when its target is in the function. -/
def liftBr (k len : Nat) (op : String) (a b : Reg) (off : BitVec 13) : LinstrR (Op Reg) Reg :=
  if jumpOk k len (signExtend13 off) then .Lcond (.cmp op (opnd a) (opnd b)) (tgt k (signExtend13 off))
  else .Labort

/-- `jal`, lifted: a jump inside the function, a tail call or a call of a function of the
    program. -/
def liftJal (fs : List Fn) (len k : Nat) (pc : Word) (rd : Reg) (off : BitVec 21) :
    LinstrR (Op Reg) Reg :=
  if rd = .x0 then
    if jumpOk k len (signExtend21 off) then .Lgoto (tgt k (signExtend21 off))
    else match entryOf fs (pc + signExtend21 off) with
      | some f => .Ltail (.direct f)
      | none => .Labort
  else if rd = .x1 then match entryOf fs (pc + signExtend21 off) with
    | some f => .Lcall (pc + 4) (.direct f)
    | none => .Labort
  else .Labort

/-- `jalr`, lifted: a return, an indirect tail call or an indirect call. -/
def liftJalr (fs : List Fn) (pc : Word) (rd rs : Reg) (off : BitVec 12) : LinstrR (Op Reg) Reg :=
  if rd = .x0 then
    if rs = .x1 ∧ off = 0 then .Lret
    else .Ltail (.indirect (jalrTgt rs off) (List.range fs.length))
  else if rd = .x1 then .Lcall (pc + 4) (.indirect (jalrTgt rs off) (List.range fs.length))
  else .Labort

/-- An instruction that is not an operation, lifted. -/
def liftCtl (fs : List Fn) (len k : Nat) (pc : Word) : Instr → LinstrR (Op Reg) Reg
  | .AUIPC rd imm => .Lopn (.set rd (.imm (pc + auipcOff imm)))
  | .BEQ a b off => liftBr k len "eq" a b off
  | .BNE a b off => liftBr k len "ne" a b off
  | .BLT a b off => liftBr k len "lt" a b off
  | .BGE a b off => liftBr k len "ge" a b off
  | .BLTU a b off => liftBr k len "ltu" a b off
  | .BGEU a b off => liftBr k len "geu" a b off
  | .JAL rd off => liftJal fs len k pc rd off
  | .JALR rd rs off => liftJalr fs pc rd rs off
  | .ECALL => .Lext
  | _ => .Labort

/-- One instruction, at index `k` of a function of `len` instructions at address `pc`. -/
def liftI (fs : List Fn) (len k : Nat) (pc : Word) (i : Instr) : LinstrR (Op Reg) Reg :=
  if opnOk i then .Lopn (opOf i) else liftCtl fs len k pc i

/-- Instructions from index `k` on, lifted. -/
def liftFrom (fs : List Fn) (base : Word) (len : Nat) : Nat → List Instr → Lcmd (Op Reg) Reg
  | _, [] => []
  | k, i :: is =>
    .Llabel .internal k :: liftI fs len k (base + BitVec.ofNat 64 (4 * k)) i :: liftFrom fs base len (k + 1) is

/-- A function, lifted. -/
def liftFn (fs : List Fn) (f : Fn) : Lfundef (Op Reg) Reg where
  name := f.name
  addr := f.base
  body := liftFrom fs f.base f.prog.length 0 f.prog
  depth := f.depth

/-- **A program, lifted.** -/
def liftProg (fs : List Fn) : Lprog (Op Reg) Reg := fs.map (liftFn fs)

/-! ## SP1's execution context -/

/-- **SP1's execution context.** An external call may end in any outcome riscv-zkvm's
    `ecall` gives from a machine state at an `ecall` that agrees with the Lprog state; it
    accepts at `HALT` (`t0 = 0`) with exit code `0`. -/
def sp1Ctx : Context rvIsa where
  ext regs m o := ∃ u, Agree (ofParts regs m) u ∧ u.code u.pc = some .ECALL ∧
    match sp1Ecall u with
    | some t => o = .ok (regsOf t, t)
    | none => o = .trap
  accept regs m := (ofParts regs m).getReg .x5 = 0 ∧ (ofParts regs m).getReg .x10 = 0

theorem sp1Ctx_ext_ne_wrong {regs : Reg → BitVec 64} {m : MachineState} :
    ¬ sp1Ctx.ext regs m .wrong := by
  rintro ⟨u, -, -, h⟩
  split at h <;> cases h

/-- The judgement at Lprog for a lifted program, under SP1. -/
abbrev LSafeN (fs : List Fn) (G : State rvIsa → Prop) (n : Nat) (Q : State rvIsa → Prop)
    (s : State rvIsa) : Prop :=
  rvIsa.SafeN (liftProg fs) sp1Ctx G n Q s

/-! ## The lifted code -/

theorem length_liftFrom (fs : List Fn) (base : Word) (len : Nat) :
    ∀ (k : Nat) (is : List Instr), (liftFrom fs base len k is).length = 2 * is.length
  | _, [] => rfl
  | k, _ :: is => by
    simp only [liftFrom, List.length_cons, length_liftFrom fs base len (k + 1) is]; omega

theorem getElem?_liftFrom_even (fs : List Fn) (base : Word) (len : Nat) :
    ∀ (k : Nat) (is : List Instr) (j : Nat), j < is.length →
      (liftFrom fs base len k is)[2 * j]? = some (.Llabel .internal (k + j))
  | _, [], _, h => absurd h (by simp)
  | k, i :: is, 0, _ => by simp [liftFrom]
  | k, i :: is, j + 1, h => by
    rw [show 2 * (j + 1) = (2 * j) + 1 + 1 by omega]
    simp only [liftFrom, List.getElem?_cons_succ]
    rw [getElem?_liftFrom_even fs base len (k + 1) is j (by simp only [List.length_cons] at h; omega),
      show k + 1 + j = k + (j + 1) by omega]

theorem getElem?_liftFrom_odd (fs : List Fn) (base : Word) (len : Nat) :
    ∀ (k : Nat) (is : List Instr) (j : Nat) (h : j < is.length),
      (liftFrom fs base len k is)[2 * j + 1]? =
        some (liftI fs len (k + j) (base + BitVec.ofNat 64 (4 * (k + j))) is[j])
  | _, [], _, h => absurd h (by simp)
  | k, i :: is, 0, _ => by simp [liftFrom]
  | k, i :: is, j + 1, h => by
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by omega]
    simp only [liftFrom, List.getElem?_cons_succ]
    rw [getElem?_liftFrom_odd fs base len (k + 1) is j (by simp only [List.length_cons] at h; omega)]
    simp only [List.getElem_cons_succ]
    rw [show k + 1 + j = k + (j + 1) by omega]

theorem isLabel_label {Op Reg : Type} (k l : LLabel) :
    isLabel (Op := Op) (Reg := Reg) l (.Llabel .internal k) = (k == l) := rfl

theorem liftI_not_label (fs : List Fn) (len k : Nat) (pc : Word) (i : Instr) (l : LLabel) :
    isLabel l (liftI fs len k pc i) = false := by
  unfold liftI
  split
  · rfl
  · unfold liftCtl
    split <;> (try simp only [liftBr, liftJal, liftJalr]) <;> (repeat' split) <;> rfl

/-- Label `l` sits at index `2 (l - k)` of the instructions lifted from index `k`. -/
theorem labelIdx_liftFrom (fs : List Fn) (base : Word) (len : Nat) :
    ∀ (k : Nat) (is : List Instr) (l : Nat), k ≤ l → l < k + is.length →
      labelIdx (liftFrom fs base len k is) l = some (2 * (l - k))
  | _, [], _, h1, h2 => absurd h2 (by simp; omega)
  | k, i :: is, l, h1, h2 => by
    unfold labelIdx
    simp only [liftFrom, List.findIdx?_cons, isLabel_label, liftI_not_label]
    by_cases hkl : k = l
    · subst hkl; simp
    · have := labelIdx_liftFrom fs base len (k + 1) is l (by omega)
        (by simp only [List.length_cons] at h2; omega)
      unfold labelIdx at this
      simp only [beq_iff_eq, hkl, ite_false, this, Option.map_some, Bool.false_eq_true]
      congr 1; omega

/-- The body of a lifted function. -/
abbrev bodyOf (fs : List Fn) (f : Fn) : Lcmd (Op Reg) Reg := liftFrom fs f.base f.prog.length 0 f.prog

theorem labelIdx_body (fs : List Fn) (f : Fn) {l : Nat} (h : l < f.prog.length) :
    labelIdx (bodyOf fs f) l = some (2 * l) := by
  simpa using labelIdx_liftFrom fs f.base f.prog.length 0 f.prog l (Nat.zero_le _) (by omega)

theorem length_body (fs : List Fn) (f : Fn) : (bodyOf fs f).length = 2 * f.prog.length :=
  length_liftFrom fs f.base f.prog.length 0 f.prog

theorem body_even (fs : List Fn) (f : Fn) {k : Nat} (hk : k < f.prog.length) :
    (bodyOf fs f)[2 * k]? = some (.Llabel .internal k) := by
  simpa using getElem?_liftFrom_even fs f.base f.prog.length 0 f.prog k hk

theorem body_odd (fs : List Fn) (f : Fn) {k : Nat} (hk : k < f.prog.length) :
    (bodyOf fs f)[2 * k + 1]? =
      some (liftI fs f.prog.length k (f.base + BitVec.ofNat 64 (4 * k)) f.prog[k]) := by
  simpa using getElem?_liftFrom_odd fs f.base f.prog.length 0 f.prog k hk

theorem body_end (fs : List Fn) (f : Fn) {p : Nat} (hp : 2 * f.prog.length ≤ p) :
    (bodyOf fs f)[p]? = none :=
  List.getElem?_eq_none (by rw [length_body]; exact hp)

theorem getElem?_liftProg {fs : List Fn} {i : Nat} {f : Fn} (h : fs[i]? = some f) :
    (liftProg fs)[i]? = some (liftFn fs f) := by
  simp [liftProg, h]

theorem length_liftProg (fs : List Fn) : (liftProg fs).length = fs.length := by
  simp [liftProg]

/-- The function `entryOf` finds has that entry. -/
theorem entryOf_spec {fs : List Fn} {a : Word} {f : Nat} (h : entryOf fs a = some f) :
    ∃ fn, fs[f]? = some fn ∧ fn.base = a := by
  unfold entryOf at h
  obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨fs[f], List.getElem?_eq_getElem hlt, by simpa using hp⟩

/-- An indirect target among all functions is a function with that address. -/
theorem callee_indirect {fs : List Fn} {regs : Reg → BitVec 64} {e : Expr Reg} {f : Nat}
    (h : rvIsa.callee (liftProg fs) regs (.indirect e (List.range fs.length)) = some f) :
    ∃ fn, fs[f]? = some fn ∧ fn.base = e.eval regs := by
  simp only [Isa.callee] at h
  have hp := List.find?_some h
  have hm := List.mem_of_find?_eq_some h
  rw [List.mem_range] at hm
  simp only [Isa.addrAt, getElem?_liftProg (List.getElem?_eq_getElem hm)] at hp
  exact ⟨fs[f], List.getElem?_eq_getElem hm, by simpa [liftFn] using hp⟩

/-- A function with that address is found among all functions. -/
theorem callee_indirect_of {fs : List Fn} {regs : Reg → BitVec 64} {e : Expr Reg}
    {f : Nat} {fn : Fn} (hf : fs[f]? = some fn) (ha : fn.base = e.eval regs) :
    ∃ g, rvIsa.callee (liftProg fs) regs (.indirect e (List.range fs.length)) = some g := by
  simp only [Isa.callee]
  have hlt : f < fs.length := (List.getElem?_eq_some_iff.mp hf).1
  cases hfind : (List.range fs.length).find? (fun g => rvIsa.addrAt (liftProg fs) g == some (e.eval regs)) with
  | some g => exact ⟨g, rfl⟩
  | none =>
    have := List.find?_eq_none.mp hfind f (List.mem_range.mpr hlt)
    simp [Isa.addrAt, getElem?_liftProg hf, liftFn, ha] at this

theorem callee_direct {fs : List Fn} {regs : Reg → BitVec 64} {f : Nat} (h : f < fs.length) :
    rvIsa.callee (liftProg fs) regs (.direct f) = some f := by
  simp [Isa.callee, length_liftProg, h]

end MachineChecked.RiscV.Lprog
