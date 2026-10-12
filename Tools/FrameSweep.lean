/-
  Tools.FrameSweep

  Run the frame analysis (`AsmVerif.RiscV.Frame.Domain`) over every function of an ELF and
  report, per function, whether its annotation checks and, if not, why.

      lake exe frame-sweep ELF NM OUT.tsv

  Untrusted and diagnostic: it runs the same `Fn.step`/`Fn.valid` the kernel re-checks, but
  in compiled code, to see how far the checker reaches before any proof is attempted.
  Every function is given every outlined fragment in the image (`OUTLINED_FUNCTION_*`).
-/

import RiscvZkvm.Interpreter
import AsmVerif.RiscV.Frame.Domain
import Tools.Elf

namespace Tools.FrameSweep

open RiscvZkvm.Rv64 RiscvZkvm.Interpreter AsmVerif.RiscV.Frame Tools.Elf

/-- Why the analysis stopped. -/
inductive Outcome where
  | ok (reqs residual noreturn : Nat)
  /-- `Fn.step` is undefined at instruction `i`. -/
  | stuck (i : Nat) (ins : Option Instr)
  /-- The worklist ran out of fuel. -/
  | noFixpoint
  /-- The annotation does not check at instruction `i` (typically an exit with `ra` or
      `sp` not provably restored). -/
  | badEdge (i : Nat) (ins : Option Instr)

/-- Why `Fn.step` is undefined on an instruction, in words. -/
def stuckReason : Option Instr → String
  | none => "undecodable word"
  | some .ECALL => "ecall"
  | some .EBREAK => "ebreak"
  | some (.CSRS ..) => "csrs"
  | some (.JAL rd _) => s!"jal with link x{regIdx rd}"
  | some (.JALR rd _ _) => if rd = .x5 then "outlined call (fragment unsupported)" else s!"jalr with link x{regIdx rd}"
  | some i => s!"unmodeled: {(repr i).pretty 200}"

/-- `Fn.analyze`, reporting where it gets stuck. -/
def analyzeE (f : Fn) : Except Outcome (Array (Option AState)) :=
  go (64 * f.prog.length + 64) (((List.replicate f.prog.length none).toArray).set! 0 (some AState.entry)) [0]
where
  go : Nat → Array (Option AState) → List Nat → Except Outcome (Array (Option AState))
    | 0, _, _ => throw .noFixpoint
    | _, anno, [] => pure anno
    | fuel + 1, anno, i :: work =>
      match anno[i]? with
      | some (some A) =>
        match f.step i A with
        | none => throw (.stuck i (f.instrAt? i))
        | some st =>
          let (anno, work) := st.edges.foldl (fun (acc : Array (Option AState) × List Nat) e =>
            match e with
            | .goto j B =>
                let (a, ch) := joinAt acc.1 j B
                (a, if ch then j :: acc.2 else acc.2)
            | .exit _ => acc
            | .anywhere B =>
                (List.range f.prog.length).foldl (fun acc j =>
                  let (a, ch) := joinAt acc.1 j B
                  (a, if ch then j :: acc.2 else acc.2)) acc) (anno, work)
          go fuel anno work
      | _ => go fuel anno work

def sweep (f : Fn) : Outcome :=
  match analyzeE f with
  | .error o => o
  | .ok anno =>
    let r := f.report anno
    if r.ok then .ok r.reqs.length r.residual.length r.noreturn.length
    else
      match (List.range f.prog.length).find? (fun i => !f.instrOk anno i) with
      | some i => .badEdge i (f.instrAt? i)
      | none => .badEdge 0 (f.instrAt? 0)

def main (args : List String) : IO UInt32 := do
  let [elfPath, nmPath, outPath] := args
    | IO.eprintln "usage: frame-sweep ELF NM OUT.tsv"; return 2
  let img ← match parseElf64 (← IO.FS.readBinFile elfPath) with
    | .ok img => pure img
    | .error e => IO.eprintln s!"frame-sweep: {e}"; return 1
  let syms := parseNm (← IO.FS.readFile nmPath)
  let progOf (s : Sym) : Except String (List (Option Instr)) :=
    (wordsAt img s.addr (s.size / 4)).map (·.map decode)
  -- Every outlined fragment, offered to every function.
  let mut frags : List (Word × List (Option Instr)) := []
  for s in syms do
    if s.name.startsWith "OUTLINED_FUNCTION" then
      if let .ok p := progOf s then frags := (BitVec.ofNat 64 s.addr, p) :: frags
  let mut rows : Array String := #["addr\twords\tstatus\tdetail\treqs\tresidual\tnoreturn\tname"]
  let mut tally : Std.HashMap String Nat := {}
  let mut reasons : Std.HashMap String Nat := {}
  let mut words := 0
  for s in syms do
    if s.size % 4 != 0 || s.name.startsWith "OUTLINED_FUNCTION" then continue
    let prog ← match progOf s with
      | .ok p => pure p
      | .error e => IO.eprintln s!"frame-sweep: {s.name}: {e}"; continue
    let f : Fn := { base := BitVec.ofNat 64 s.addr, prog, frags }
    let pcHex (i : Nat) := hex (s.addr + 4 * i) 8
    let (status, detail, q, r, n) := match sweep f with
      | .ok q r n => ("ok", "", q, r, n)
      | .stuck i ins => ("stuck", s!"{pcHex i}: {stuckReason ins}", 0, 0, 0)
      | .noFixpoint => ("nofix", "", 0, 0, 0)
      | .badEdge i ins => ("exit", s!"{pcHex i}: {(repr ins).pretty 200}", 0, 0, 0)
    tally := tally.insert status (tally.getD status 0 + 1)
    if status == "stuck" then
      let why := (detail.splitOn ": ").drop 1 |> ": ".intercalate
      let key := if why.startsWith "unmodeled" then (why.splitOn " ").take 2 |> " ".intercalate else why
      reasons := reasons.insert key (reasons.getD key 0 + 1)
    if status == "ok" then words := words + prog.length
    rows := rows.push s!"{hex s.addr 8}\t{prog.length}\t{status}\t{detail}\t{q}\t{r}\t{n}\t{s.name}"
  IO.FS.writeFile outPath ("\n".intercalate rows.toList ++ "\n")
  IO.println s!"frame-sweep: {rows.size - 1} functions; {tally.toList}"
  IO.println s!"frame-sweep: {words} words in functions that check"
  IO.println s!"frame-sweep: stuck because: {reasons.toList}"
  return 0

end Tools.FrameSweep

def main (args : List String) : IO UInt32 := Tools.FrameSweep.main args
