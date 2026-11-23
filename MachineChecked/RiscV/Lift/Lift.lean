/-
  MachineChecked.RiscV.Lift.Lift

  From decoded RISC-V to an Lprog program.

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

  The lift of a function reads the rest of the program in two places only: the function at
  each address it calls (`entry`), and the candidates of a computed jump it does not resolve
  (`all`). `liftFn entry all f` takes them as arguments, under the names `Lprog.Linked.Cx`
  gives them, and `liftProg fs` lifts every function with `entryOf fs` and every index of `fs`.
  `Fn.callTargets f` lists the addresses at which the lift of `f` applies `entry`, and
  `getElem?_liftProg_of_callTargets` gives function `i` of `liftProg fs` from `fs[i]` and any
  resolver that agrees with `entryOf fs` there: a function's lift can be checked from its own
  code and a table of the functions it calls.

  SP1's execution context (`sp1Ctx`) is in `lprog-riscv/LprogRiscV/Sp1Ctx.lean`, in the package
  `lprog-riscv`. The syscall facts the layer-0 tools use are lemmas about it
  (`RiscV/Lift/Rules.lean`).

  The correctness of the lift, by simulation, is `RiscV/Lift/Transfer.lean`.

  ## Main definitions and results

  * `liftFn`, `liftProg`, `Fn.callTargets`
  * `liftFn_congr`, `getElem?_liftProg_of_callTargets`
-/

import LprogRiscV.Sp1Ctx
import MachineChecked.RiscV.Sym.Core
namespace MachineChecked.RiscV.Lift

open Lprog.RiscV

open RiscvZkvm.Rv64 MachineChecked.RiscV MachineChecked.RiscV.Sym Lprog
open Lprog.Ascent (Outcome)

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

/-- `jal`, lifted: a jump inside the function, or a tail call or a call of the function
    `entry` finds at its target. -/
def liftJal (entry : Word → Option Nat) (len k : Nat) (pc : Word) (rd : Reg) (off : BitVec 21) :
    LinstrR (Op Reg) Reg :=
  if rd = .x0 then
    if jumpOk k len (signExtend21 off) then .Lgoto (tgt k (signExtend21 off))
    else match entry (pc + signExtend21 off) with
      | some f => .Ltail (.direct f)
      | none => .Labort
  else if rd = .x1 then match entry (pc + signExtend21 off) with
    | some f => .Lcall (pc + 4) (.direct f)
    | none => .Labort
  else .Labort

/-- The address a `jalr _, off(rs)` at `pc` jumps to, when the instruction before it, `prev`,
    is the `auipc` that sets `rs`, as in the `call` and `tail` pseudo-instructions
    (`Whole.paired` is the same for the lift of linked programs). -/
def jalrPaired (pc : Word) (prev : Option Instr) (rs : Reg) (off : BitVec 12) : Option Word :=
  match prev with
  | some (.AUIPC rd imm) =>
    if rd = rs ∧ rs ≠ .x0 then some ((pc - 4 + auipcOff imm + signExtend12 off) &&& ~~~1#64)
    else none
  | _ => none

/-- The function a `jalr` at `pc` reaches when `jalrPaired` gives its address. -/
def jalrStatic (entry : Word → Option Nat) (pc : Word) (prev : Option Instr) (rs : Reg)
    (off : BitVec 12) : Option Nat :=
  (jalrPaired pc prev rs off).bind entry

/-- **The candidates of a computed jump**: the function `jalrStatic` finds, or else `all`.
    Any list is sound (`callee_indirect`): a target outside it is a step to `wrong`, which a
    proof of safety rules out. A short list makes fewer cases to prove; it can only lose a
    jump into the `jalr` from elsewhere with another target, which compilers do not emit. -/
def jalrCands (entry : Word → Option Nat) (all : List Nat) (pc : Word) (prev : Option Instr)
    (rs : Reg) (off : BitVec 12) : List Nat :=
  match jalrStatic entry pc prev rs off with
  | some g => [g]
  | none => all

/-- `jalr` after `prev`, lifted: a return, an indirect tail call or an indirect call. -/
def liftJalr (entry : Word → Option Nat) (all : List Nat) (pc : Word) (prev : Option Instr)
    (rd rs : Reg) (off : BitVec 12) : LinstrR (Op Reg) Reg :=
  if rd = .x0 then
    if rs = .x1 ∧ off = 0 then .Lret
    else .Ltail (.indirect (jalrTgt rs off) (jalrCands entry all pc prev rs off))
  else if rd = .x1 then
    .Lcall (pc + 4) (.indirect (jalrTgt rs off) (jalrCands entry all pc prev rs off))
  else .Labort

/-- An instruction that is not an operation, after `prev`, lifted. -/
def liftCtl (entry : Word → Option Nat) (all : List Nat) (len k : Nat) (pc : Word)
    (prev : Option Instr) : Instr → LinstrR (Op Reg) Reg
  | .AUIPC rd imm => .Lopn (.set rd (.imm (pc + auipcOff imm)))
  | .BEQ a b off => liftBr k len "eq" a b off
  | .BNE a b off => liftBr k len "ne" a b off
  | .BLT a b off => liftBr k len "lt" a b off
  | .BGE a b off => liftBr k len "ge" a b off
  | .BLTU a b off => liftBr k len "ltu" a b off
  | .BGEU a b off => liftBr k len "geu" a b off
  | .JAL rd off => liftJal entry len k pc rd off
  | .JALR rd rs off => liftJalr entry all pc prev rd rs off
  | .ECALL => .Lext 0
  | _ => .Labort

/-- One instruction, at index `k` of a function of `len` instructions at address `pc`, after
    the instruction `prev`, with `entry` the function at an address and `all` the candidates
    of a computed jump `jalrStatic` does not resolve. -/
def liftI (entry : Word → Option Nat) (all : List Nat) (len k : Nat) (pc : Word)
    (prev : Option Instr) (i : Instr) : LinstrR (Op Reg) Reg :=
  if opnOk i then .Lopn (opOf i) else liftCtl entry all len k pc prev i

/-- Only `ecall` lifts to an external call. -/
theorem liftI_eq_ext {entry : Word → Option Nat} {all : List Nat} {len k n : Nat} {pc : Word}
    {prev : Option Instr} {i : Instr} (h : liftI entry all len k pc prev i = .Lext n) :
    i = .ECALL := by
  unfold liftI at h
  split at h
  · cases h
  · cases i <;> first
      | rfl
      | (simp only [liftCtl, liftBr, liftJal, liftJalr] at h
         repeat' split at h
         all_goals cases h)

/-- Instructions from index `k` on, after the instruction `prev`, lifted. -/
def liftFrom (entry : Word → Option Nat) (all : List Nat) (base : Word) (len : Nat) :
    Nat → Option Instr → List Instr → Lcmd (Op Reg) Reg
  | _, _, [] => []
  | k, prev, i :: is =>
    .Llabel .internal k :: liftI entry all len k (base + BitVec.ofNat 64 (4 * k)) prev i ::
      liftFrom entry all base len (k + 1) (some i) is

/-- The instruction before index `j` of `is`, the first having `prev` before it. -/
def prevAt (prev : Option Instr) (is : List Instr) : Nat → Option Instr
  | 0 => prev
  | j + 1 => is[j]?

/-- A function, lifted: from its own code, the function at each address it calls (`entry`),
    and the candidates of a computed jump it does not resolve (`all`). -/
def liftFn (entry : Word → Option Nat) (all : List Nat) (f : Fn) : Lfundef (Op Reg) Reg where
  name := f.name
  addr := f.base
  body := liftFrom entry all f.base f.prog.length 0 none f.prog
  depth := f.depth

/-- **A program, lifted**: each function with the program's entries, and every function a
    candidate. -/
def liftProg (fs : List Fn) : Lprog (Op Reg) Reg :=
  fs.map (liftFn (entryOf fs) (List.range fs.length))

/-! ## SP1's execution context -/

/-- The judgement at Lprog for a lifted program, under SP1. -/
abbrev LSafeN (fs : List Fn) (G : State rvIsa → Prop) (n : Nat) (Q : State rvIsa → Prop)
    (s : State rvIsa) : Prop :=
  rvIsa.SafeN (liftProg fs) sp1Ctx G n Q s

/-! ## The lifted code -/

theorem length_liftFrom (entry : Word → Option Nat) (all : List Nat) (base : Word) (len : Nat) :
    ∀ (k : Nat) (prev : Option Instr) (is : List Instr),
      (liftFrom entry all base len k prev is).length = 2 * is.length
  | _, _, [] => rfl
  | k, _, i :: is => by
    simp only [liftFrom, List.length_cons, length_liftFrom entry all base len (k + 1) (some i) is]
    omega

theorem getElem?_liftFrom_even (entry : Word → Option Nat) (all : List Nat) (base : Word)
    (len : Nat) :
    ∀ (k : Nat) (prev : Option Instr) (is : List Instr) (j : Nat), j < is.length →
      (liftFrom entry all base len k prev is)[2 * j]? = some (.Llabel .internal (k + j))
  | _, _, [], _, h => absurd h (by simp)
  | k, _, i :: is, 0, _ => by simp [liftFrom]
  | k, _, i :: is, j + 1, h => by
    rw [show 2 * (j + 1) = (2 * j) + 1 + 1 by omega]
    simp only [liftFrom, List.getElem?_cons_succ]
    rw [getElem?_liftFrom_even entry all base len (k + 1) (some i) is j
        (by simp only [List.length_cons] at h; omega),
      show k + 1 + j = k + (j + 1) by omega]

theorem getElem?_liftFrom_odd (entry : Word → Option Nat) (all : List Nat) (base : Word)
    (len : Nat) :
    ∀ (k : Nat) (prev : Option Instr) (is : List Instr) (j : Nat) (h : j < is.length),
      (liftFrom entry all base len k prev is)[2 * j + 1]? =
        some (liftI entry all len (k + j) (base + BitVec.ofNat 64 (4 * (k + j)))
          (prevAt prev is j) is[j])
  | _, _, [], _, h => absurd h (by simp)
  | k, _, i :: is, 0, _ => by simp [liftFrom, prevAt]
  | k, _, i :: is, j + 1, h => by
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 by omega]
    simp only [liftFrom, List.getElem?_cons_succ]
    rw [getElem?_liftFrom_odd entry all base len (k + 1) (some i) is j
      (by simp only [List.length_cons] at h; omega)]
    simp only [List.getElem_cons_succ]
    rw [show k + 1 + j = k + (j + 1) by omega]
    congr 2
    cases j <;> simp [prevAt]

theorem isLabel_label {Op Reg : Type} (k l : LLabel) :
    isLabel (Op := Op) (Reg := Reg) l (.Llabel .internal k) = (k == l) := rfl

theorem liftI_not_label (entry : Word → Option Nat) (all : List Nat) (len k : Nat) (pc : Word)
    (prev : Option Instr) (i : Instr) (l : LLabel) :
    isLabel l (liftI entry all len k pc prev i) = false := by
  unfold liftI
  split
  · rfl
  · unfold liftCtl
    split <;> (try simp only [liftBr, liftJal, liftJalr]) <;> (repeat' split) <;> rfl

/-- Label `l` sits at index `2 (l - k)` of the instructions lifted from index `k`. -/
theorem labelIdx_liftFrom (entry : Word → Option Nat) (all : List Nat) (base : Word)
    (len : Nat) :
    ∀ (k : Nat) (prev : Option Instr) (is : List Instr) (l : Nat), k ≤ l → l < k + is.length →
      labelIdx (liftFrom entry all base len k prev is) l = some (2 * (l - k))
  | _, _, [], _, h1, h2 => absurd h2 (by simp; omega)
  | k, _, i :: is, l, h1, h2 => by
    unfold labelIdx
    simp only [liftFrom, List.findIdx?_cons, isLabel_label, liftI_not_label]
    by_cases hkl : k = l
    · subst hkl; simp
    · have := labelIdx_liftFrom entry all base len (k + 1) (some i) is l (by omega)
        (by simp only [List.length_cons] at h2; omega)
      unfold labelIdx at this
      simp only [beq_iff_eq, hkl, ite_false, this, Option.map_some, Bool.false_eq_true]
      congr 1; omega

/-- The body of a lifted function. -/
abbrev bodyOf (entry : Word → Option Nat) (all : List Nat) (f : Fn) : Lcmd (Op Reg) Reg :=
  liftFrom entry all f.base f.prog.length 0 none f.prog

theorem labelIdx_body (entry : Word → Option Nat) (all : List Nat) (f : Fn) {l : Nat}
    (h : l < f.prog.length) : labelIdx (bodyOf entry all f) l = some (2 * l) := by
  simpa using
    labelIdx_liftFrom entry all f.base f.prog.length 0 none f.prog l (Nat.zero_le _) (by omega)

theorem length_body (entry : Word → Option Nat) (all : List Nat) (f : Fn) :
    (bodyOf entry all f).length = 2 * f.prog.length :=
  length_liftFrom entry all f.base f.prog.length 0 none f.prog

theorem body_even (entry : Word → Option Nat) (all : List Nat) (f : Fn) {k : Nat}
    (hk : k < f.prog.length) : (bodyOf entry all f)[2 * k]? = some (.Llabel .internal k) := by
  simpa using getElem?_liftFrom_even entry all f.base f.prog.length 0 none f.prog k hk

theorem body_odd (entry : Word → Option Nat) (all : List Nat) (f : Fn) {k : Nat}
    (hk : k < f.prog.length) :
    (bodyOf entry all f)[2 * k + 1]? =
      some (liftI entry all f.prog.length k (f.base + BitVec.ofNat 64 (4 * k))
        (prevAt none f.prog k) f.prog[k]) := by
  simpa using getElem?_liftFrom_odd entry all f.base f.prog.length 0 none f.prog k hk

theorem body_end (entry : Word → Option Nat) (all : List Nat) (f : Fn) {p : Nat}
    (hp : 2 * f.prog.length ≤ p) : (bodyOf entry all f)[p]? = none :=
  List.getElem?_eq_none (by rw [length_body]; exact hp)

theorem getElem?_liftProg {fs : List Fn} {i : Nat} {f : Fn} (h : fs[i]? = some f) :
    (liftProg fs)[i]? = some (liftFn (entryOf fs) (List.range fs.length) f) := by
  simp [liftProg, h]

theorem length_liftProg (fs : List Fn) : (liftProg fs).length = fs.length := by
  simp [liftProg]

/-- The function `entryOf` finds has that entry. -/
theorem entryOf_spec {fs : List Fn} {a : Word} {f : Nat} (h : entryOf fs a = some f) :
    ∃ fn, fs[f]? = some fn ∧ fn.base = a := by
  unfold entryOf at h
  obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.mp h
  exact ⟨fs[f], List.getElem?_eq_getElem hlt, by simpa using hp⟩

/-- An indirect target among any candidates is a function with that address. -/
theorem callee_indirect {fs : List Fn} {regs : Reg → BitVec 64} {e : Expr Reg} {cs : List Nat} {f : Nat}
    (h : rvIsa.callee (liftProg fs) regs (.indirect e cs) = some f) :
    ∃ fn, fs[f]? = some fn ∧ fn.base = e.eval regs := by
  simp only [Isa.callee] at h
  have hp := List.find?_some h
  simp only [Isa.addrAt, beq_iff_eq, Option.map_eq_some_iff] at hp
  obtain ⟨fd, hfd, ha⟩ := hp
  simp only [liftProg, List.getElem?_map, Option.map_eq_some_iff] at hfd
  obtain ⟨fn, hfn, rfl⟩ := hfd
  exact ⟨fn, hfn, by simpa [liftFn] using ha⟩

/-- A function with that address, among the candidates, is found. -/
theorem callee_indirect_of {fs : List Fn} {regs : Reg → BitVec 64} {e : Expr Reg} {cs : List Nat}
    {f : Nat} {fn : Fn} (hf : fs[f]? = some fn) (ha : fn.base = e.eval regs) (hm : f ∈ cs) :
    ∃ g, rvIsa.callee (liftProg fs) regs (.indirect e cs) = some g := by
  simp only [Isa.callee]
  cases hfind : cs.find? (fun g => rvIsa.addrAt (liftProg fs) g == some (e.eval regs)) with
  | some g => exact ⟨g, rfl⟩
  | none =>
    have := List.find?_eq_none.mp hfind f hm
    simp [Isa.addrAt, getElem?_liftProg hf, liftFn, ha] at this

/-- Every candidate in `all` is a candidate of a computed jump that `jalrStatic` does not
    resolve. -/
theorem mem_jalrCands {entry : Word → Option Nat} {all : List Nat} {pc : Word}
    {prev : Option Instr} {rs : Reg} {off : BitVec 12} {f : Nat}
    (h : jalrStatic entry pc prev rs off = none) (hf : f ∈ all) :
    f ∈ jalrCands entry all pc prev rs off := by
  simp [jalrCands, h, hf]

theorem callee_direct {fs : List Fn} {regs : Reg → BitVec 64} {f : Nat} (h : f < fs.length) :
    rvIsa.callee (liftProg fs) regs (.direct f) = some f := by
  simp [Isa.callee, length_liftProg, h]

/-! ## The lift of a function from its own code -/

/-- The address whose function the lift of instruction `i` asks `entry` for, if it asks: the
    target of a `jal ra`, of a `jal x0` that leaves the function, and of a `jalr` that calls
    or tail-calls after the `auipc` of its register. -/
def callTargetOf (len k : Nat) (pc : Word) (prev : Option Instr) : Instr → Option Word
  | .JAL rd off =>
    if rd = .x0 then
      if jumpOk k len (signExtend21 off) then none else some (pc + signExtend21 off)
    else if rd = .x1 then some (pc + signExtend21 off)
    else none
  | .JALR rd rs off =>
    if rd = .x0 then (if rs = .x1 ∧ off = 0 then none else jalrPaired pc prev rs off)
    else if rd = .x1 then jalrPaired pc prev rs off
    else none
  | _ => none

/-- The addresses the lift of the instructions from index `k` on asks `entry` for, in order. -/
def callTargetsFrom (base : Word) (len : Nat) : Nat → Option Instr → List Instr → List Word
  | _, _, [] => []
  | k, prev, i :: is =>
    (callTargetOf len k (base + BitVec.ofNat 64 (4 * k)) prev i).toList ++
      callTargetsFrom base len (k + 1) (some i) is

/-- **The addresses a function's lift asks for**: where its calls and tail calls go, one per
    call site. -/
def Fn.callTargets (f : Fn) : List Word := callTargetsFrom f.base f.prog.length 0 none f.prog

theorem jalrCands_congr {entry entry' : Word → Option Nat} {all : List Nat} {pc : Word}
    {prev : Option Instr} {rs : Reg} {off : BitVec 12}
    (h : ∀ a ∈ jalrPaired pc prev rs off, entry a = entry' a) :
    jalrCands entry all pc prev rs off = jalrCands entry' all pc prev rs off := by
  unfold jalrCands jalrStatic
  cases ha : jalrPaired pc prev rs off with
  | none => rfl
  | some a => simp [h a ha]

theorem liftI_congr {entry entry' : Word → Option Nat} {all : List Nat} {len k : Nat}
    {pc : Word} {prev : Option Instr} {i : Instr}
    (h : ∀ a ∈ callTargetOf len k pc prev i, entry a = entry' a) :
    liftI entry all len k pc prev i = liftI entry' all len k pc prev i := by
  unfold liftI
  split
  · rfl
  · cases i with
    | JAL rd off =>
      simp only [liftCtl, liftJal]
      simp only [callTargetOf] at h
      by_cases h0 : rd = .x0 <;> by_cases h1 : rd = .x1 <;>
        by_cases hj : jumpOk k len (signExtend21 off) = true <;> simp_all
    | JALR rd rs off =>
      simp only [liftCtl, liftJalr]
      simp only [callTargetOf] at h
      split <;> split <;> first
        | rfl
        | rw [jalrCands_congr (by simpa only [*, ↓reduceIte] using h)]
        | rw [jalrCands_congr (by simpa [*] using h)]
    | _ => rfl

theorem liftFrom_congr {entry entry' : Word → Option Nat} {all : List Nat} {base : Word}
    {len : Nat} :
    ∀ (k : Nat) (prev : Option Instr) (is : List Instr),
      (∀ a ∈ callTargetsFrom base len k prev is, entry a = entry' a) →
      liftFrom entry all base len k prev is = liftFrom entry' all base len k prev is
  | _, _, [], _ => rfl
  | k, prev, i :: is, h => by
    simp only [callTargetsFrom, List.mem_append, Option.mem_toList] at h
    simp only [liftFrom]
    rw [liftI_congr fun a ha => h a (.inl ha),
      liftFrom_congr (k + 1) (some i) is fun a ha => h a (.inr ha)]

/-- **The lift of a function depends on the program only through the functions at its call
    targets**: two resolvers that agree there give the same lift. -/
theorem liftFn_congr {entry entry' : Word → Option Nat} {all : List Nat} {f : Fn}
    (h : ∀ a ∈ f.callTargets, entry a = entry' a) :
    liftFn entry all f = liftFn entry' all f := by
  simp only [liftFn, liftFrom_congr 0 none f.prog h]

/-- **A function of a lifted program, from its own code.** Function `i` of `liftProg fs` is
    the lift of `fs[i]` alone with any resolver that agrees with the program's entries at the
    addresses it calls. A client states the agreement as
    `f.callTargets.map (entryOf fs) = f.callTargets.map entry`, which the kernel evaluates, and
    passes `List.map_inj_left.mp` of it. -/
theorem getElem?_liftProg_of_callTargets {fs : List Fn} {i : Nat} {f : Fn}
    {entry : Word → Option Nat} (hf : fs[i]? = some f)
    (h : ∀ a ∈ f.callTargets, entryOf fs a = entry a) :
    (liftProg fs)[i]? = some (liftFn entry (List.range fs.length) f) := by
  rw [getElem?_liftProg hf, liftFn_congr h]

end MachineChecked.RiscV.Lift
