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
 "downstream_usage": 17, "num_usingMap_files": 5,
 "top_usingMap_files": [{"file": "...", "count": 4}, ...]}
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
  | neededDownstream
  | noopAlwaysExported
  deriving BEq

def Verdict.classify (r : ReportRecord) : Verdict :=
  if r.effect == "noop-always-exported" then .noopAlwaysExported
  else if r.downstreamUsage == 0 then .safeToUnexpose
  else .neededDownstream

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
  let needed := rs.filter (Verdict.classify · == .neededDownstream)
  let noop := rs.filter (Verdict.classify · == .noopAlwaysExported)
  let mut out := s!"{file}: {safe.size} safe-to-unexpose, " ++
    s!"{needed.size} needed-downstream, {noop.size} noop ({total} total)\n"
  if !safe.isEmpty then
    out := out ++ "\n  safe-to-unexpose:\n"
    for r in sortByPosition safe do
      out := out ++ s!"    {padTo 60 r.name}  (line {r.line})\n"
  if !needed.isEmpty then
    out := out ++ "\n  needed downstream (must keep @[expose]):\n"
    for r in sortByPosition needed do
      out := out ++ s!"    {padTo 60 r.name}  " ++
        s!"(line {r.line}; {r.downstreamUsage} uses across " ++
        s!"{r.numUsingFiles} files)\n"
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
  let needed := rs.filter (Verdict.classify · == .neededDownstream)
  let noop := rs.filter (Verdict.classify · == .noopAlwaysExported)
  return Json.mkObj [
    ("file", file),
    ("safe_to_unexpose", bucket safe),
    ("needed_downstream", bucket needed),
    ("noop", bucket noop)]

/-- Top-level `report` subcommand. -/
def runReport (args : ReportArgs) : IO UInt32 := do
  unless ← System.FilePath.pathExists reportPath do
    IO.eprintln s!"no_expose: {reportPath} not found. \
      Run `lake exe no_expose collect` first."
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
  return 0

/-! ## Build side: join raw signals into `report.jsonl` -/

/-- Decl key + originating file. `Std.HashMap` lacks structural keys
of arbitrary nested type, so we use a `String × String` here. -/
private abbrev UseKey := String × String

/-- Parse one line of `diagnostics.jsonl` or `static_refs.jsonl`. Returns
`(decl, file, count, theoremCount)`. `theoremCount = 0` when the field
is absent (diagnostics records). -/
private def parseSignalLine (line : String) :
    Except String (String × String × Nat × Nat) := do
  let j ← Json.parse line
  let decl ← jsonGetStr j "decl"
  let file ← jsonGetStr j "file"
  let count ← jsonGetNat j "count"
  let thm := j.getObjVal? "theorem_count" |>.toOption
    |>.bind (·.getNat?.toOption) |>.getD 0
  return (decl, file, count, thm)

/-- Parse one line of `decl_refs.jsonl`: `{decl: ..., refs: [...]}`. -/
private def parseDeclRefsLine (line : String) :
    Except String (String × Array String) := do
  let j ← Json.parse line
  let decl ← jsonGetStr j "decl"
  let refsJ ← j.getObjVal? "refs"
  let refsArr ← refsJ.getArr?
  let refs ← refsArr.mapM (·.getStr?)
  return (decl, refs)

/-- Read `exposed.jsonl` into a map keyed by decl name. -/
private def readExposed (path : System.FilePath) : IO (Std.HashMap String Json) := do
  let mut acc : Std.HashMap String Json := {}
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match Json.parse line with
    | .ok j =>
      match jsonGetStr j "name" with
      | .ok name => acc := acc.insert name j
      | .error _ => pure ()
    | .error _ => pure ()
  return acc

/-- Same-module-but-from-theorem references count; other same-module
refs are skipped. Mirrors `expose_report.py:117`. -/
private def shouldCount (sameModule : Bool) (count theoremCount : Nat) : Option Nat :=
  if sameModule then
    if theoremCount > 0 then some theoremCount else none
  else
    some count

/-- Absorb one signal file into the running usage map. Returns the
number of records actually counted (skipping any that don't match an
exposed decl or are filtered out). -/
private def absorbSignal (exposed : Std.HashMap String Json)
    (path : System.FilePath)
    (usage : Std.HashMap String Nat)
    (usingMap : Std.HashMap UseKey Nat) :
    IO (Std.HashMap String Nat × Std.HashMap UseKey Nat × Nat) := do
  let mut usage := usage
  let mut usingMap := usingMap
  let mut absorbed := 0
  for line in (← IO.FS.readFile path).splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    match parseSignalLine line with
    | .error _ => continue
    | .ok (decl, file, count, thm) =>
      let some rec := exposed[decl]? | continue
      let recFile := (rec.getObjVal? "file" |>.bind (·.getStr?)).toOption.getD ""
      let some delta := shouldCount (file == recFile) count thm | continue
      usage := usage.insert decl ((usage.getD decl 0) + delta)
      let key : UseKey := (decl, file)
      usingMap := usingMap.insert key ((usingMap.getD key 0) + delta)
      absorbed := absorbed + 1
  return (usage, usingMap, absorbed)

/-- One-hop transitive closure: a downstream use of decl `K` propagates
to every decl in `K`'s body. Mirrors `expose_report.py:154`. -/
private def applyTransitiveClosure (exposed : Std.HashMap String Json)
    (declRefsPath : System.FilePath)
    (usage : Std.HashMap String Nat)
    (usingMap : Std.HashMap UseKey Nat) :
    IO (Std.HashMap String Nat × Std.HashMap UseKey Nat × Nat) := do
  -- Load decl_refs into a map.
  let mut refsMap : Std.HashMap String (Array String) := {}
  for line in (← IO.FS.readFile declRefsPath).splitOn "\n" do
    if line.trimAscii.isEmpty then continue
    if let .ok (decl, refs) := parseDeclRefsLine line then
      refsMap := refsMap.insert decl refs
  -- Snapshot usingMap to avoid iterating while mutating.
  let snapshot := usingMap.toArray
  let mut usage := usage
  let mut usingMap := usingMap
  let mut propagated := 0
  for ((decl, file), count) in snapshot do
    let some refs := refsMap[decl]? | continue
    for ref in refs do
      let some refRec := exposed[ref]? | continue
      let recFile := (refRec.getObjVal? "file" |>.bind (·.getStr?)).toOption.getD ""
      if file == recFile then continue  -- same-module
      usage := usage.insert ref ((usage.getD ref 0) + count)
      let key : UseKey := (ref, file)
      usingMap := usingMap.insert key ((usingMap.getD key 0) + count)
      propagated := propagated + 1
  return (usage, usingMap, propagated)

/-- Build `report.jsonl` by joining the four input files. -/
def build (exposedPath diagnosticsPath staticRefsPath declRefsPath : System.FilePath)
    (outPath : System.FilePath) : IO Unit := do
  let exposed ← readExposed exposedPath
  IO.eprintln s!"[no_expose report] loaded {exposed.size} exposed decls"

  let mut usage : Std.HashMap String Nat := {}
  let mut usingMap : Std.HashMap UseKey Nat := {}
  if ← System.FilePath.pathExists diagnosticsPath then
    let (u, uf, n) ← absorbSignal exposed diagnosticsPath usage usingMap
    usage := u; usingMap := uf
    IO.eprintln s!"[no_expose report] absorbed {n} diagnostics records"
  if ← System.FilePath.pathExists staticRefsPath then
    let (u, uf, n) ← absorbSignal exposed staticRefsPath usage usingMap
    usage := u; usingMap := uf
    IO.eprintln s!"[no_expose report] absorbed {n} static-reference records"
  if ← System.FilePath.pathExists declRefsPath then
    let (u, uf, n) ← applyTransitiveClosure exposed declRefsPath usage usingMap
    usage := u; usingMap := uf
    IO.eprintln s!"[no_expose report] one-hop transitive: propagated {n} extra (ref,file) edges"

  -- Build per-decl `top_usingMap_files` from `usingMap`.
  let mut perDecl : Std.HashMap String (Array (String × Nat)) := {}
  for ((decl, file), count) in usingMap.toArray do
    let cur := perDecl.getD decl #[]
    perDecl := perDecl.insert decl (cur.push (file, count))

  IO.FS.writeFile outPath ""
  IO.FS.withFile outPath .append fun h => do
    for (name, exposedRec) in exposed.toArray do
      let u := usage.getD name 0
      let top := perDecl.getD name #[]
      let topSorted := top.qsort fun a b => a.2 > b.2
      let topNFiles := top.size
      let top5 := topSorted.take 5
      let topJson := "[" ++ String.intercalate "," (top5.toList.map fun (f, c) =>
        "{\"file\":\"" ++ jsonEscape f ++ "\",\"count\":" ++ toString c ++ "}") ++ "]"
      -- Re-emit the original exposed record's fields plus our additions.
      let baseStr := exposedRec.compress
      -- Drop the trailing `}` and append our fields.
      let baseStripped := baseStr.dropEnd 1
      h.putStrLn (baseStripped.toString ++
        ",\"downstream_usage\":" ++ toString u ++
        ",\"num_using_files\":" ++ toString topNFiles ++
        ",\"top_using_files\":" ++ topJson ++ "}")
  IO.eprintln s!"[no_expose report] wrote {exposed.size} report rows to {outPath}"

end NoExpose
