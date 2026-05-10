/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Data.Json
import NoExpose.Cli
import NoExpose.Paths

/-!
# `NoExpose.Report` — read and render the joined report

A `report.jsonl` record (built by `collect`) carries everything `report`
and `edit` need:

```
{"name": "Foo.bar", "kind": "def", "effect": "exposed",
 "module": "Mathlib.Foo", "file": "Mathlib/Foo.lean",
 "line": 42, "col": 0,
 "downstream_usage": 17, "num_using_files": 5,
 "top_using_files": [{"file": "...", "count": 4}, ...]}
```

This module parses those records and renders per-file output in three
formats. Building `report.jsonl` from raw signals is the responsibility
of `NoExpose.Diagnostics` and the `collect` orchestrator.
-/

open Lean (Json)

namespace NoExpose

/-- A single decl's report row. -/
structure ReportRecord where
  name : String
  kind : String
  effect : String
  module : String
  file : String
  line : Nat
  col : Nat
  downstreamUsage : Nat
  numUsingFiles : Nat
  topUsingFiles : Array (String × Nat)
  deriving Inhabited

/-- The ordered groups we render. -/
inductive Verdict where
  | safeToUnexpose
  | loadBearing
  | noopAlwaysExported
  deriving BEq

def Verdict.classify (r : ReportRecord) : Verdict :=
  if r.effect == "noop-always-exported" then .noopAlwaysExported
  else if r.downstreamUsage == 0 then .safeToUnexpose
  else .loadBearing

private def jsonGetStr (j : Json) (field : String) : Except String String :=
  (j.getObjVal? field).bind (·.getStr?)

private def jsonGetNat (j : Json) (field : String) : Except String Nat := do
  let v ← j.getObjVal? field
  match v with
  | .num n =>
    -- JSON numbers can be integer-valued; reject negatives.
    if n.mantissa ≥ 0 then
      pure (n.mantissa.toNat * 10 ^ n.exponent)
    else
      .error s!"non-integer or negative count in field {field}: {n}"
  | _ => .error s!"expected number for field {field}, got {v.compress}"

private def parseTopUsing (j : Json) : Except String (Array (String × Nat)) := do
  let arr ← j.getArr?
  arr.mapM fun entry => do
    let file ← jsonGetStr entry "file"
    let count ← jsonGetNat entry "count"
    pure (file, count)

/-- Parse a single line of `report.jsonl`. -/
def parseRecord (line : String) : Except String ReportRecord := do
  let j ← Json.parse line
  let topJ := j.getObjVal? "top_using_files" |>.toOption |>.getD (.arr #[])
  return {
    name := ← jsonGetStr j "name"
    kind := ← jsonGetStr j "kind"
    effect := ← jsonGetStr j "effect"
    module := ← jsonGetStr j "module"
    file := ← jsonGetStr j "file"
    line := ← jsonGetNat j "line"
    col := ← jsonGetNat j "col"
    downstreamUsage := ← jsonGetNat j "downstream_usage"
    numUsingFiles := ← jsonGetNat j "num_using_files"
    topUsingFiles := ← parseTopUsing topJ
  }

/-- Read all records from `report.jsonl`, accumulating any parse errors
into a separate channel rather than aborting on the first one. -/
def readReport (path : System.FilePath) :
    IO (Array ReportRecord × Array String) := do
  let mut ok : Array ReportRecord := #[]
  let mut errs : Array String := #[]
  let lines := (← IO.FS.readFile path).splitOn "\n"
  for (line, i) in lines.zip (List.range lines.length) do
    if line.trimAscii.isEmpty then continue
    match parseRecord line with
    | .ok r => ok := ok.push r
    | .error msg => errs := errs.push s!"line {i+1}: {msg}"
  return (ok, errs)

/-- Group records by their `file`. -/
def byFile (rs : Array ReportRecord) : Std.HashMap String (Array ReportRecord) :=
  rs.foldl (init := {}) fun acc r =>
    let existing := acc.getD r.file #[]
    acc.insert r.file (existing.push r)

/-- Pad a string to at least `n` characters with trailing spaces. -/
private def padTo (n : Nat) (s : String) : String :=
  if s.length ≥ n then s
  else s ++ "".pushn ' ' (n - s.length)

/-- Sort records within a file: by line first, then by name. -/
private def sortByPosition (rs : Array ReportRecord) : Array ReportRecord :=
  rs.qsort fun a b => if a.line ≠ b.line then a.line < b.line else a.name < b.name

/-- Render one file's records in text format. -/
def renderTextFile (file : String) (rs : Array ReportRecord) : String := Id.run do
  let total := rs.size
  let safe := rs.filter (Verdict.classify · == .safeToUnexpose)
  let load := rs.filter (Verdict.classify · == .loadBearing)
  let noop := rs.filter (Verdict.classify · == .noopAlwaysExported)
  let mut out := s!"{file}: {safe.size} safe-to-unexpose, " ++
    s!"{load.size} load-bearing, {noop.size} noop ({total} total)\n"
  if !safe.isEmpty then
    out := out ++ "\n  safe-to-unexpose:\n"
    for r in sortByPosition safe do
      out := out ++ s!"    {padTo 60 r.name}  (line {r.line})\n"
  if !load.isEmpty then
    out := out ++ "\n  load-bearing (must keep @[expose]):\n"
    for r in sortByPosition load do
      out := out ++ s!"    {padTo 60 r.name}  " ++
        s!"(line {r.line}; {r.downstreamUsage} uses across " ++
        s!"{r.numUsingFiles} files)\n"
  return out

/-- Render one file's records in TSV (no header per file; caller adds). -/
def renderTsvFile (rs : Array ReportRecord) : String := Id.run do
  let mut out := ""
  for r in sortByPosition rs do
    let top := String.intercalate ";" <|
      r.topUsingFiles.toList.map fun (f, c) => s!"{f}:{c}"
    out := out ++ s!"{r.name}\t{r.kind}\t{r.effect}\t{r.module}\t" ++
      s!"{r.file}:{r.line}\t{r.downstreamUsage}\t{r.numUsingFiles}\t{top}\n"
  return out

/-- Render one file's records in JSON (one object per file, decls grouped). -/
def renderJsonFile (file : String) (rs : Array ReportRecord) : Json := Id.run do
  let mkDecl (r : ReportRecord) : Json := Json.mkObj [
    ("name", r.name),
    ("line", r.line),
    ("downstream_usage", r.downstreamUsage),
    ("num_using_files", r.numUsingFiles)]
  let bucket (vs : Array ReportRecord) : Json :=
    .arr (sortByPosition vs |>.map mkDecl)
  let safe := rs.filter (Verdict.classify · == .safeToUnexpose)
  let load := rs.filter (Verdict.classify · == .loadBearing)
  let noop := rs.filter (Verdict.classify · == .noopAlwaysExported)
  return Json.mkObj [
    ("file", file),
    ("safe_to_unexpose", bucket safe),
    ("load_bearing", bucket load),
    ("noop", bucket noop)]

/-- Top-level `report` subcommand. -/
def runReport (args : ReportArgs) : IO UInt32 := do
  unless ← System.FilePath.pathExists reportPath do
    IO.eprintln s!"no_expose: {reportPath} not found."
    if args.collectOnDemand then
      IO.eprintln "  (would run `collect` here, but `collect` is not yet \
        implemented in the new tool — TODO)"
    else
      IO.eprintln "  Run `lake exe no_expose collect` first, or pass \
        `--collect-on-demand`."
    return 2
  let (records, errs) ← readReport reportPath
  for e in errs do IO.eprintln s!"warning: {e}"
  let groups := byFile records
  -- Determine which files to render.
  let selectedFiles : Array String :=
    if args.all then groups.toArray.map (·.1)
    else args.paths
  if selectedFiles.isEmpty then
    IO.eprintln "no_expose: pass at least one PATH or --all"
    return 2
  match args.format with
  | .text => do
    for f in selectedFiles do
      let rs := groups.getD f #[]
      if rs.isEmpty then
        IO.println s!"{f}: no exposed decls in report"
      else
        IO.print (renderTextFile f rs)
  | .json => do
    let objs := selectedFiles.map fun f =>
      renderJsonFile f (groups.getD f #[])
    IO.println (Json.arr objs).pretty
  | .tsv => do
    IO.println "name\tkind\teffect\tmodule\tsource\tdownstream_usage\tnum_using_files\ttop_using_files"
    for f in selectedFiles do
      IO.print (renderTsvFile (groups.getD f #[]))
  return 0

end NoExpose
