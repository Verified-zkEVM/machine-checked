/-
  Lprog.LinkedSpec

  Where things are in a lifted linked program (`Lprog/Linked.lean`): what a proof of the
  lift of an instruction set needs of `liftProgram`, whichever the instructions are.

  For a function of one part (its own code, the default):

  * its body is the instructions in order, each a label and what `liftI` gives for it, then
    `Labort`, then the label to give up at if an instruction asks for it (`body_eq`);
  * instruction `k` is at position `pos k`, its label there and its commands after
    (`getElem?_label`, `getElem?_cmd`), and the next instruction right after its last
    command (`pos_succ`);
  * label `k` is found at `pos k`, if no instruction's commands hold a label
    (`labelIdx_label`), and the label to give up at leads to `Labort` (`labelIdx_abort`);
  * an address the context maps to a label or to a function is the address of that
    instruction or function (`label_sound`, `entry_sound`).

  ## Main definitions

  * `cxOf`, `chunks`, `pos`

  ## Main results

  * `getElem?_liftProgram`, `body_eq`
  * `getElem?_label`, `getElem?_cmd`, `pos_succ`
  * `labelIdx_label`, `labelIdx_abort`
  * `label_sound`, `entry_sound`
-/

import Lprog.Linked

namespace Lprog.Linked

variable {Reg I : Type}

/-! ## Lists of lists -/

/-- The length of the first `k` lists together. -/
def offset {α : Type} (cs : List (List α)) (k : Nat) : Nat := ((cs.take k).map List.length).sum

@[simp] theorem offset_zero {α : Type} (cs : List (List α)) : offset cs 0 = 0 := by simp [offset]

theorem offset_cons_succ {α : Type} (c : List α) (cs : List (List α)) (k : Nat) :
    offset (c :: cs) (k + 1) = c.length + offset cs k := by simp [offset]

theorem offset_succ {α : Type} (cs : List (List α)) (k : Nat) (hk : k < cs.length) :
    offset cs (k + 1) = offset cs k + cs[k].length := by
  induction cs generalizing k with
  | nil => simp at hk
  | cons c cs ih =>
    cases k with
    | zero => simp [offset]
    | succ k =>
      rw [offset_cons_succ, offset_cons_succ, ih k (by simpa using hk)]
      simp only [List.getElem_cons_succ]; omega

theorem offset_length {α : Type} (cs : List (List α)) : offset cs cs.length = cs.flatten.length := by
  simp [offset, List.length_flatten]

theorem offset_le {α : Type} (cs : List (List α)) (k : Nat) : offset cs k ≤ cs.flatten.length := by
  induction cs generalizing k with
  | nil => simp [offset]
  | cons c cs ih =>
    cases k with
    | zero => simp
    | succ k =>
      rw [offset_cons_succ, List.flatten_cons, List.length_append]
      exact Nat.add_le_add_left (ih k) _

/-- An element of one of the lists, in them all together. -/
theorem getElem?_flatten_offset {α : Type} (cs : List (List α)) (k : Nat) (hk : k < cs.length)
    (j : Nat) (hj : j < cs[k].length) : cs.flatten[offset cs k + j]? = cs[k][j]? := by
  induction cs generalizing k with
  | nil => simp at hk
  | cons c cs ih =>
    cases k with
    | zero =>
      simp only [List.flatten_cons, offset_zero, Nat.zero_add, List.getElem_cons_zero] at hj ⊢
      exact List.getElem?_append_left hj
    | succ k =>
      simp only [List.flatten_cons, offset_cons_succ, List.getElem_cons_succ] at hj ⊢
      rw [List.getElem?_append_right (by omega), show c.length + offset cs k + j - c.length =
        offset cs k + j by omega]
      exact ih k (by simpa using hk) hj

/-! ## Labelled runs of commands -/

section labelled

variable {Op Z : Type}

/-- Each of `zs`, at its index from `b`: a label, then its commands. -/
def labelled (g : Z → Lcmd Op Reg) (zs : List Z) (b : Nat) : List (Lcmd Op Reg) :=
  (zs.zipIdx b).map fun (z, k) => .Llabel .internal k :: g z

@[simp] theorem length_labelled (g : Z → Lcmd Op Reg) (zs : List Z) (b : Nat) :
    (labelled g zs b).length = zs.length := by simp [labelled]

theorem labelled_cons (g : Z → Lcmd Op Reg) (z : Z) (zs : List Z) (b : Nat) :
    labelled g (z :: zs) b = (.Llabel .internal b :: g z) :: labelled g zs (b + 1) := by
  simp [labelled, List.zipIdx_cons]

theorem getElem_labelled (g : Z → Lcmd Op Reg) (zs : List Z) (b k : Nat) (hk : k < zs.length) :
    (labelled g zs b)[k]'(by simpa using hk) = .Llabel .internal (b + k) :: g zs[k] := by
  simp [labelled]

/-- No command of `g` is a label. -/
def NoLabel (g : Z → Lcmd Op Reg) (zs : List Z) : Prop :=
  ∀ z ∈ zs, ∀ c ∈ g z, ∀ l, isLabel l c = false

/-- A label outside the run is not in it. -/
theorem findIdx?_labelled_none {g : Z → Lcmd Op Reg} {zs : List Z} (hg : NoLabel g zs) (b l : Nat)
    (hl : l < b ∨ b + zs.length ≤ l) :
    (labelled g zs b).flatten.findIdx? (isLabel l) = none := by
  rw [List.findIdx?_eq_none_iff]
  intro c hc
  obtain ⟨cs, hcs, hc⟩ := List.mem_flatten.1 hc
  obtain ⟨⟨z, k⟩, hzk, rfl⟩ := List.mem_map.1 hcs
  obtain ⟨hk1, hk2, hz⟩ := List.mem_zipIdx hzk
  rcases List.mem_cons.1 hc with rfl | hc
  · simp only [isLabel, beq_eq_false_iff_ne, ne_eq]
    intro h
    have h' : (k : Nat) = l := h
    omega
  · exact hg z (hz ▸ List.getElem_mem _) c hc l

/-- **A label of the run is found** at the start of its commands. -/
theorem findIdx?_labelled {g : Z → Lcmd Op Reg} {zs : List Z} (hg : NoLabel g zs) (b l : Nat)
    (hb : b ≤ l) (hl : l < b + zs.length) (rest : Lcmd Op Reg) :
    ((labelled g zs b).flatten ++ rest).findIdx? (isLabel l) =
      some (offset (labelled g zs b) (l - b)) := by
  induction zs generalizing b with
  | nil => simp at hl; omega
  | cons z zs ih =>
    rw [labelled_cons, List.flatten_cons, List.cons_append, List.cons_append, List.findIdx?_cons]
    by_cases hbl : b = l
    · subst hbl; simp [isLabel]
    · have hno : (g z).findIdx? (isLabel l) = none := by
        rw [List.findIdx?_eq_none_iff]
        exact fun c hc => hg z (List.mem_cons_self) c hc l
      have := ih (fun z' hz' => hg z' (List.mem_cons_of_mem _ hz')) (b + 1) (by omega)
        (by simp at hl ⊢; omega)
      simp only [isLabel, beq_iff_eq, hbl, ↓reduceIte, List.append_assoc, List.findIdx?_append,
        hno, Option.none_or, this, Option.map_some]
      rw [show l - b = (l - (b + 1)) + 1 by omega, offset_cons_succ]
      simp only [List.length_cons]
      congr 1; omega

end labelled

/-! ## A function of one part -/

/-- The labels of a function: the index of the instruction at an address. -/
def labelsOf (code : List (At I)) : Std.TreeMap (BitVec 64) Nat :=
  Std.TreeMap.ofList (code.zipIdx.reverse.map fun (a, k) => (a.addr, k))

/-- The entries of a program: the index of the function at an address. -/
def entriesOf (fns : List (Fun I)) : Std.TreeMap (BitVec 64) Nat :=
  Std.TreeMap.ofList (fns.zipIdx.reverse.map fun (f, k) => (f.addr, k))

/-- **The context** `liftProgram` gives the instructions of a function of one part. -/
def cxOf (fns : List (Fun I)) (f : Fun I) : Cx where
  label := ((labelsOf f.code)[·]?)
  entry := ((entriesOf fns)[·]?)
  all := List.range fns.length
  abort := f.code.length
  cands := f.targets.eraseDups.filterMap fun a => (labelsOf f.code)[a]?.map (a, ·)

/-- The instructions of a function with the one before each, as `liftI` takes them. -/
def withPrev (code : List (At I)) : List (At I × Option (At I)) := code.zip (none :: code.map some)

/-- **The commands of a function**, instruction by instruction: a label, then what `liftI`
    gives. -/
def chunks (liftI : Cx → Option (At I) → At I → Lcmd (Op Reg) Reg) (fns : List (Fun I))
    (f : Fun I) : List (Lcmd (Op Reg) Reg) :=
  labelled (fun z => liftI (cxOf fns f) z.2 z.1) (withPrev f.code) 0

/-- **The body of a lifted function**: its instructions, `Labort`, and perhaps the label to
    give up at. -/
theorem getElem?_liftProgram (liftI : Cx → Option (At I) → At I → Lcmd (Op Reg) Reg)
    (fns : List (Fun I)) {i : Nat} {f : Fun I} (hf : fns[i]? = some f) :
    ∃ tail, (liftProgram liftI fns)[i]? = some
        { name := f.name, addr := f.addr
          body := (chunks liftI fns f).flatten ++ [.Labort] ++ tail } ∧
      (tail = [] ∨ tail = [.Llabel .internal f.code.length, .Labort]) := by
  have hgo : ∀ cx, liftProgram.go liftI cx 0 [f.code] =
      (labelled (fun z => liftI cx z.2 z.1) (withPrev f.code) 0).flatten ++ [.Labort] := by
    intro cx
    simp [liftProgram.go, labelled, withPrev]
  simp only [liftProgram, List.getElem?_map, hf, Option.map_some, hgo, List.flatten_cons,
    List.flatten_nil, List.append_nil, List.flatMap_cons, List.flatMap_nil]
  split
  · exact ⟨_, rfl, Or.inr rfl⟩
  · exact ⟨[], by simp only [List.append_nil]; rfl, Or.inl rfl⟩

section positions

variable (liftI : Cx → Option (At I) → At I → Lcmd (Op Reg) Reg) (fns : List (Fun I)) (f : Fun I)

@[simp] theorem length_withPrev (code : List (At I)) : (withPrev code).length = code.length := by
  simp [withPrev]

theorem getElem_withPrev_fst (code : List (At I)) (k : Nat) (hk : k < code.length) :
    ((withPrev code)[k]'(by simpa using hk)).1 = code[k] := by
  simp [withPrev]

@[simp] theorem length_chunks : (chunks liftI fns f).length = f.code.length := by simp [chunks]

/-- The position of instruction `k` in the body: of its label. -/
def pos (k : Nat) : Nat := offset (chunks liftI fns f) k

/-- What `liftI` gives for instruction `k`. -/
def cmds (k : Nat) (hk : k < f.code.length) : Lcmd (Op Reg) Reg :=
  liftI (cxOf fns f) ((withPrev f.code)[k]'(by simpa using hk)).2 f.code[k]

theorem getElem_chunks (k : Nat) (hk : k < f.code.length) :
    (chunks liftI fns f)[k]'(by simpa using hk) = .Llabel .internal k :: cmds liftI fns f k hk := by
  simp only [chunks, cmds]
  rw [getElem_labelled _ _ _ _ (by simpa using hk), Nat.zero_add, getElem_withPrev_fst _ _ hk]

@[simp] theorem pos_zero : pos liftI fns f 0 = 0 := offset_zero _

/-- The next instruction is right after the last command. -/
theorem pos_succ (k : Nat) (hk : k < f.code.length) :
    pos liftI fns f (k + 1) = pos liftI fns f k + 1 + (cmds liftI fns f k hk).length := by
  rw [pos, pos, offset_succ _ _ (by simpa using hk), getElem_chunks liftI fns f k hk]
  simp only [List.length_cons]; omega

variable (tail : Lcmd (Op Reg) Reg)

/-- **The label of instruction `k`** is at its position. -/
theorem getElem?_label (k : Nat) (hk : k < f.code.length) :
    ((chunks liftI fns f).flatten ++ [.Labort] ++ tail)[pos liftI fns f k]? =
      some (.Llabel .internal k) := by
  have h := getElem?_flatten_offset (chunks liftI fns f) k (by simpa using hk) 0
    (by rw [getElem_chunks liftI fns f k hk]; simp)
  have hlt : pos liftI fns f k < (chunks liftI fns f).flatten.length := by
    have h1 := pos_succ liftI fns f k hk
    have h2 := offset_le (chunks liftI fns f) (k + 1)
    simp only [pos] at h1 ⊢
    omega
  rw [List.append_assoc, List.getElem?_append_left hlt]
  rw [Nat.add_zero] at h
  rw [pos, h, getElem_chunks liftI fns f k hk]
  rfl

/-- **Command `j` of instruction `k`** is after its label. -/
theorem getElem?_cmd (k : Nat) (hk : k < f.code.length) (j : Nat)
    (hj : j < (cmds liftI fns f k hk).length) :
    ((chunks liftI fns f).flatten ++ [.Labort] ++ tail)[pos liftI fns f k + 1 + j]? =
      (cmds liftI fns f k hk)[j]? := by
  have h := getElem?_flatten_offset (chunks liftI fns f) k (by simpa using hk) (1 + j)
    (by rw [getElem_chunks liftI fns f k hk]; simp; omega)
  have hlt : pos liftI fns f k + 1 + j < (chunks liftI fns f).flatten.length := by
    have h1 := pos_succ liftI fns f k hk
    have h2 := offset_le (chunks liftI fns f) (k + 1)
    simp only [pos] at h1 ⊢
    omega
  rw [List.append_assoc, List.getElem?_append_left hlt, Nat.add_assoc, pos, h]
  simp only [getElem_chunks liftI fns f k hk]
  rw [Nat.add_comm 1 j]
  rfl

/-- **After the last instruction** is `Labort`. -/
theorem getElem?_end :
    ((chunks liftI fns f).flatten ++ [.Labort] ++ tail)[pos liftI fns f f.code.length]? =
      some .Labort := by
  have : pos liftI fns f f.code.length = (chunks liftI fns f).flatten.length := by
    rw [pos, ← offset_length, length_chunks]
  rw [this, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- **Label `k`** is found at the position of instruction `k`, when no command of an
    instruction is a label. -/
theorem labelIdx_label
    (hno : NoLabel (fun z => liftI (cxOf fns f) z.2 z.1) (withPrev f.code)) (k : Nat)
    (hk : k < f.code.length) :
    labelIdx ((chunks liftI fns f).flatten ++ [.Labort] ++ tail) k = some (pos liftI fns f k) := by
  have := findIdx?_labelled hno 0 k (Nat.zero_le _) (by simpa using hk) ([.Labort] ++ tail)
  rw [labelIdx, List.append_assoc]
  exact this

/-- **The label to give up at**, where there is one, leads to `Labort`. -/
theorem labelIdx_abort
    (hno : NoLabel (fun z => liftI (cxOf fns f) z.2 z.1) (withPrev f.code))
    (ht : tail = [] ∨ tail = [.Llabel .internal f.code.length, .Labort]) :
    labelIdx ((chunks liftI fns f).flatten ++ [.Labort] ++ tail) f.code.length = none ∨
    ∃ j, labelIdx ((chunks liftI fns f).flatten ++ [.Labort] ++ tail) f.code.length = some j ∧
      ((chunks liftI fns f).flatten ++ [.Labort] ++ tail)[j]? =
        some (.Llabel .internal f.code.length) ∧
      ((chunks liftI fns f).flatten ++ [.Labort] ++ tail)[j + 1]? = some .Labort := by
  have hn : (chunks liftI fns f).flatten.findIdx? (isLabel f.code.length) = none :=
    findIdx?_labelled_none hno 0 f.code.length (Or.inr (by simp))
  rcases ht with rfl | rfl
  · left
    rw [labelIdx, List.append_nil, List.findIdx?_append, hn]
    rfl
  · right
    refine ⟨(chunks liftI fns f).flatten.length + 1, ?_, ?_, ?_⟩
    · rw [labelIdx, List.findIdx?_append, List.findIdx?_append, hn]
      simp [List.findIdx?_cons, isLabel]
    · rw [List.getElem?_append_right (by simp)]
      simp
    · rw [List.getElem?_append_right (by simp)]
      simp

end positions

/-! ## What the context finds -/

/-- A value a map made from a list holds is in the list. -/
theorem mem_of_getElem?_insertMany {t : Std.TreeMap (BitVec 64) Nat} {l : List (BitVec 64 × Nat)}
    {a : BitVec 64} {k : Nat} (h : (t.insertMany l)[a]? = some k) : (a, k) ∈ l ∨ t[a]? = some k := by
  induction l generalizing t with
  | nil => exact Or.inr (by simpa using h)
  | cons x l ih =>
    obtain ⟨x1, x2⟩ := x
    rw [Std.TreeMap.insertMany_cons] at h
    rcases ih h with h1 | h1
    · exact Or.inl (List.mem_cons_of_mem _ h1)
    · rw [Std.TreeMap.getElem?_insert] at h1
      by_cases hc : compare x1 a = .eq
      · simp only [hc, ↓reduceIte] at h1
        rw [Std.LawfulEqCmp.compare_eq_iff_eq] at hc
        subst hc
        cases h1
        exact Or.inl List.mem_cons_self
      · simp only [hc, ↓reduceIte] at h1
        exact Or.inr h1

theorem mem_of_getElem?_ofList {l : List (BitVec 64 × Nat)} {a : BitVec 64} {k : Nat}
    (h : (Std.TreeMap.ofList l)[a]? = some k) : (a, k) ∈ l := by
  rw [Std.TreeMap.ofList_eq_insertMany_empty] at h
  rcases mem_of_getElem?_insertMany h with h | h
  · exact h
  · simp at h

/-- **A label the context finds** is the instruction at that address. -/
theorem label_sound (fns : List (Fun I)) (f : Fun I) {a : BitVec 64} {k : Nat}
    (h : (cxOf fns f).label a = some k) : ∃ hk : k < f.code.length, f.code[k].addr = a := by
  have := mem_of_getElem?_ofList h
  simp only [List.mem_map, List.mem_reverse, Prod.mk.injEq] at this
  obtain ⟨⟨x, j⟩, hx, rfl, rfl⟩ := this
  obtain ⟨hj, hxe⟩ := List.mem_zipIdx' hx
  exact ⟨hj, by rw [hxe]⟩

/-- **A function the context finds** is the one at that address. -/
theorem entry_sound (fns : List (Fun I)) (f : Fun I) {a : BitVec 64} {g : Nat}
    (h : (cxOf fns f).entry a = some g) : ∃ hg : g < fns.length, fns[g].addr = a := by
  have := mem_of_getElem?_ofList h
  simp only [List.mem_map, List.mem_reverse, Prod.mk.injEq] at this
  obtain ⟨⟨x, j⟩, hx, rfl, rfl⟩ := this
  obtain ⟨hj, hxe⟩ := List.mem_zipIdx' hx
  exact ⟨hj, by rw [hxe]⟩

end Lprog.Linked
