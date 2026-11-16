import Tools.Decompile

/-! Experiment: emit the proved route's lift of an ELF as Lean, with a kernel-checked theorem
    per function that the emitted term is `liftFn` of the decoded words. Run with
    `lake env lean Gen.lean` and the environment variables ELF, OUT and NS. -/

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter MachineChecked.Lprog MachineChecked.RiscV.Lprog
open Tools.Elf Tools.Decompile

def strip (s : String) : String :=
  -- shorter names; `open` in the emitted file brings them back
  ((s.replace "MachineChecked.Lprog.LinstrR." "LinstrR.").replace "MachineChecked.Lprog.Op." "Op.")
    |>.replace "MachineChecked.Lprog.Expr." "Expr." |>.replace "MachineChecked.Lprog.BinOp." "BinOp."
    |>.replace "MachineChecked.Lprog.UnOp." "UnOp." |>.replace "MachineChecked.Lprog.LOperand." "LOperand."
    |>.replace "MachineChecked.Lprog.Target." "Target." |>.replace "MachineChecked.Lprog.Width." "Width."
    |>.replace "MachineChecked.Lprog.LabelKind." "LabelKind." |>.replace "RiscvZkvm.Rv64.Reg." "Reg."

/-- `xs` in groups of 128. -/
def groups (xs : List String) : List (List String) :=
  (List.range ((xs.length + 127) / 128)).map fun k => (xs.drop (128 * k)).take 128

def lit (xs : List String) : String := "[" ++ ", ".intercalate xs ++ "]"

/-- A long list as a tree of `List.flatten` over lists of at most 128: a literal of thousands
    of elements, or a long chain of `++`, is too deep for the elaborator. -/
def chunked (xs : List String) : String :=
  if xs.length ≤ 128 then lit xs
  else
    let parts := (groups xs).map lit
    if parts.length ≤ 128 then "List.flatten " ++ lit parts
    else "List.flatten (List.flatten " ++ lit ((groups parts).map lit) ++ ")"

/-- `List.range n` in place of the literal `[0, 1, …, n-1]` (the candidates of an indirect
    call, which are every function): one literal of hundreds of numbers inside an
    instruction is too much for the elaborator. `reprStr` wraps long lists across lines, so
    literals are compared with their whitespace taken out. -/
partial def ranges (n : Nat) (s : String) : String :=
  let flat := "[" ++ ",".intercalate ((List.range n).map toString) ++ "]"
  match s.splitOn "[0," with
  | [] | [_] => s
  | before :: after =>
    let tail := "[0," ++ "[0,".intercalate after
    let lit := String.ofList (tail.toList.takeWhile (· != ']')) ++ "]"
    if String.ofList (lit.toList.filter fun c => !c.isWhitespace) == flat then
      before ++ s!"(List.range {n})" ++ ranges n (String.ofList (tail.toList.drop lit.length))
    else
      before ++ "[0," ++ ranges n (String.ofList (tail.toList.drop 3))

def gen : IO Unit := do
  let elf := (← IO.getEnv "ELF").get!
  let out := (← IO.getEnv "OUT").get!
  let ns := (← IO.getEnv "NS").get!
  let bytes ← IO.FS.readBinFile elf
  let .ok img := parseElf64 bytes | throw (IO.userError "elf")
  let .ok syms := symbols bytes | throw (IO.userError "symbols")
  let (fs, _) := functions img syms
  IO.FS.createDirAll (out ++ "/" ++ ns)
  -- the words of each function
  let mut w := s!"import RiscvZkvm.Interpreter\nimport MachineChecked.RiscV.Lprog.Lift\n\nnamespace {ns}\nopen RiscvZkvm.Rv64 RiscvZkvm.Interpreter MachineChecked.RiscV.Lprog\n\n-- data for the kernel, not code to run: the code generator does not take terms this large\nnoncomputable section\n\n"
  let mut entries : Array String := #[]
  for h : k in [0 : fs.size] do
    let f := fs[k]
    let .ok ws := wordsAt img f.base.toNat f.prog.length | throw (IO.userError "words")
    w := w ++ s!"def w{k} : List Nat :=\n    {chunked (ws.map fun x => toString x.toNat)}\n"
    entries := entries.push s!"({repr f.name}, {f.base.toNat}, w{k})"
  w := w ++ "\ndef words : List (String × Nat × List Nat) := [\n  " ++ ",\n  ".intercalate entries.toList ++ "]\n\n"
  w := w ++ "def fns : List Fn := words.map fun (name, base, ws) =>\n  { name, base := BitVec.ofNat 64 base, prog := ((ws.map (BitVec.ofNat 32)).mapM decode).getD [] }\n\n"
  w := w ++ s!"end\n\nend {ns}\n"
  IO.FS.writeFile s!"{out}/{ns}/Words.lean" w
  -- each function, with its theorem
  let p := liftProg fs.toList
  for h : i in [0 : p.length] do
    let fd := p[i]
    let mut t := s!"import {ns}.Words\n\nnamespace {ns}\nopen RiscvZkvm.Rv64 MachineChecked.Lprog MachineChecked.RiscV.Lprog\n\nnoncomputable section\n\n"
    t := t ++ s!"def f{i} : Lfundef (Op Reg) Reg :=\n  \{ name := {repr fd.name}, addr := {fd.addr.toNat}, depth := {fd.depth},\n    body := {chunked (fd.body.map fun i => ranges fs.size (strip (reprStr i)))} }\n\n"
    t := t ++ s!"theorem f{i}_eq : (liftProg fns)[{i}]? = some f{i} := by decide +kernel\n\nend\n\nend {ns}\n"
    IO.FS.writeFile s!"{out}/{ns}/F{i}.lean" t
  IO.println s!"{fs.size} functions, {(fs.toList.map (·.prog.length)).sum} instructions"

#eval gen
