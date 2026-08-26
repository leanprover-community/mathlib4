/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import NoExpose.Paths
import NoExpose.Restore

/-!
# `NoExpose.Diagnostics` — lakefile patch + lake build + log parser

Three pieces:

* **patchLakefile**: insert two `mathlibLeanOptions` entries
  (`diagnostics=true`, `diagnostics.threshold=0`). Recognises Mathlib's
  `mathlibLeanOptions` `abbrev`; errors out on any other lakefile shape.
* **patchDiagnosticsOffFiles**: 5-file hardcoded list of source files
  that fail to elaborate under global `diagnostics=true`; we splice in
  `set_option diagnostics false` after the last import.
* **parseLog**: scan `build.log` line-by-line, emit one JSONL record
  per (file, decl, count, category) tuple.

The build itself is `lake build Mathlib`, run as a child process.
Hours of CPU; pass `--skip-build` to `collect` to reuse an existing
`build.log` and skip this step.
-/

open System

namespace NoExpose

/-! ## Lakefile patching -/

private def patchMarkerBegin : String :=
  "    -- BEGIN no_expose diagnostics patch"
private def patchMarkerEnd : String :=
  "    -- END no_expose diagnostics patch"

private def patchAnchor : String := "    ⟨`autoImplicit, false⟩,\n"

private def patchBlock : String :=
  patchMarkerBegin ++ "\n" ++
  "    ⟨`diagnostics, true⟩,\n" ++
  "    ⟨`diagnostics.threshold, (0 : Nat)⟩,\n" ++
  patchMarkerEnd ++ "\n"

/-- Insert the diagnostics options into Mathlib's `mathlibLeanOptions`.
Aborts (with a clear error) for any non-Mathlib lakefile shape. -/
def patchLakefile (lakefilePath : FilePath) : IO Unit := do
  let original ← IO.FS.readFile lakefilePath
  let markerHits := (original.splitOn patchMarkerBegin).length
  if markerHits > 1 then
    throw <| IO.userError s!"{lakefilePath} already contains no_expose patch markers; \
      restore it manually before re-running."
  let anchorHits := (original.splitOn patchAnchor).length
  unless anchorHits > 1 do
    throw <| IO.userError s!"could not find insertion anchor in {lakefilePath}; \
      only Mathlib-shaped lakefiles are supported. \
      Pass --skip-build and enable diagnostics yourself, or run on Mathlib."
  -- Replace first occurrence only.
  let parts := original.splitOn patchAnchor
  let patched := parts[0]! ++ patchAnchor ++ patchBlock ++
                 String.intercalate patchAnchor (parts.drop 1)
  -- Back up before writing.
  backup lakefilePath
  IO.FS.writeFile lakefilePath patched

/-! ## Per-file diagnostics-off patches

Five Mathlib files fail under global `diagnostics=true`. Splice
`set_option diagnostics false` after the last `import` line. -/

/-- Mathlib's hardcoded fragile-files list. Override via
`patchDiagnosticsOffFiles extra` to add downstream files. -/
def diagnosticsOffFiles : Array FilePath := #[
  "Mathlib/Tactic/Linter/ValidatePRTitle.lean",
  "Mathlib/Order/Interval/Lex.lean",
  "Mathlib/Tactic/NormNum/Ordinal.lean",
  "Mathlib/Probability/ConditionalProbability.lean",
  "Mathlib/CategoryTheory/Discrete/Basic.lean"]

private def filePatchLine : String :=
  "-- no_expose: locally disable diagnostics so this file builds " ++
  "under global `diagnostics=true`\nset_option diagnostics false\n"

/-- Insert `set_option diagnostics false` after the last
`import` / `public import` line. Idempotent: re-applying is a no-op. -/
def patchOneFile (path : FilePath) : IO Unit := do
  unless ← System.FilePath.pathExists path do
    IO.eprintln s!"[no_expose diagnostics] skipping non-existent {path}"
    return
  let text ← IO.FS.readFile path
  let alreadyPatched := (text.splitOn filePatchLine).length > 1
  if alreadyPatched then return
  let lines : List String := text.splitOn "\n"
  let mut lastImport : Int := -1
  for h : i in [:lines.length] do
    let line : String := lines[i]
    let stripped : String := line.trimAscii.toString
    if stripped.startsWith "import " || stripped.startsWith "public import " then
      lastImport := i
  if lastImport < 0 then
    throw <| IO.userError s!"no import line in {path}; can't insert set_option"
  let i := lastImport.toNat + 1
  let prefixLines := lines.take i
  let suffixLines := lines.drop i
  let patched := String.intercalate "\n"
    (prefixLines ++ ["", filePatchLine.trimAsciiEnd.toString] ++ suffixLines)
  backup path
  IO.FS.writeFile path patched

/-- Patch all `diagnosticsOffFiles ++ extra`. -/
def patchDiagnosticsOffFiles (extra : Array FilePath := #[]) : IO Unit := do
  for p in diagnosticsOffFiles ++ extra do patchOneFile p

/-! ## Build-log parser -/

structure DiagRecord where
  file     : String
  decl     : String
  count    : Nat
  category : String
  deriving Inhabited

private def diagToJsonLine (r : DiagRecord) : String :=
  "{\"file\":\"" ++ r.file ++ "\",\"decl\":\"" ++ r.decl ++
  "\",\"count\":" ++ toString r.count ++
  ",\"category\":\"" ++ r.category ++ "\"}"

private def categoryShort (tag label : String) : Option String :=
  match tag, label with
  | "reduction", "unfolded declarations"           => some "reduction/unfolded"
  | "reduction", "unfolded instances"              => some "reduction/instances"
  | "reduction", "unfolded reducible declarations" => some "reduction/reducible"
  | "kernel",    "unfolded declarations"           => some "kernel/unfolded"
  | "type_class","used instances"                  => some "type_class/used"
  | _, _ => none

private def targetToFile (target : String) : Option String :=
  if target.contains ':' then none
  else some (target.replace "." "/" ++ ".lean")

/-- Match `✔ [N/M] Built Mathlib.Foo.Bar` and friends; return the target. -/
private def parseBuiltLine (line : String) : Option String := Id.run do
  -- Accept any of ✔ ℹ ⚠ ✖ as the leading bullet. Cheap precheck.
  unless line.startsWith "✔" || line.startsWith "ℹ" ||
         line.startsWith "⚠" || line.startsWith "✖" do return none
  let parts : List String := line.splitOn "Built "
  unless parts.length ≥ 2 do return none
  let after : String := parts[1]!
  -- `Mathlib.Foo` then optional whitespace; take up to first space.
  let target : String :=
    (after.takeWhile (fun c => c != ' ' && c != '\t' && c != '\n')).toString
  return some target

/-- Strip a literal `[tag] ` prefix; on success return `(tag, rest)`. -/
private def stripTagPrefix (s : String) : Option (String × String) := Id.run do
  unless s.startsWith "[" do return none
  for tag in ["reduction", "kernel", "type_class"] do
    let p := "[" ++ tag ++ "] "
    if s.startsWith p then
      let rest : String := s.drop p.length |>.toString
      return some (tag, rest)
  return none

/-- `[reduction] unfolded declarations (max: N, num: M):` -/
private def parseCategoryHeader (line : String) : Option (String × String) := Id.run do
  let trimmed : String := line.trimAscii.toString
  let some (tag, rest) := stripTagPrefix trimmed | none
  unless line.endsWith ":" do return none
  -- `rest` is `<label> (max: ..., num: ...):`
  let parenParts : List String := rest.splitOn " ("
  unless parenParts.length ≥ 2 do return none
  let label : String := parenParts[0]!
  return some (tag, label)

/-- `    [reduction] Foo.bar ↦ 3` -/
private def parseEntry (line : String) : Option (String × String × Nat) := Id.run do
  let trimmed : String := line.trimAscii.toString
  let some (tag, rest) := stripTagPrefix trimmed | none
  let arrowParts : List String := rest.splitOn " ↦ "
  unless arrowParts.length == 2 do return none
  let decl : String := arrowParts[0]!
  let countRaw : String := arrowParts[1]!
  let countStr : String := countRaw.trimAscii.toString
  let some count := String.toNat? countStr | none
  return some (tag, decl, count)

/-- Scan log into `(file, decl, count, category)` records in memory. -/
def parseLogToRecords (logPath : FilePath) : IO (Array DiagRecord) := do
  let raw ← IO.FS.readFile logPath
  let lines := raw.splitOn "\n"
  let mut currentFile : Option String := none
  let mut currentCategory : Option String := none
  let mut out : Array DiagRecord := #[]
  for line in lines do
    if let some target := parseBuiltLine line then
      currentFile := targetToFile target
      currentCategory := none
      continue
    if let some (tag, label) := parseCategoryHeader line then
      currentCategory := categoryShort tag label
      continue
    if let some (tag, decl, count) := parseEntry line then
      if let some cat := currentCategory then
        if cat.startsWith tag then
          if let some f := currentFile then
            out := out.push { file := f, decl := decl, count := count, category := cat }
          continue
        else
          currentCategory := none
          continue
    if !line.isEmpty && !line.startsWith " " then
      currentCategory := none
  return out

/-- Parse `logPath` and write `outPath` with one JSONL record per
(file, decl, count, category). -/
def parseLog (logPath outPath : FilePath) : IO Nat := do
  let records ← parseLogToRecords logPath
  IO.FS.withFile outPath .write fun h => do
    for r in records do h.putStrLn (diagToJsonLine r)
  return records.size

/-! ## Build runner -/

/-- Run `lake build Mathlib`, streaming output to `logPath` (and stdout).
Returns the lake exit code. -/
def runBuild (logPath : FilePath) : IO UInt32 := do
  IO.FS.createDirAll logPath.parent.get!
  let proc ← IO.Process.spawn {
    cmd := "lake"
    args := #["build", "Mathlib"]
    stdout := .piped
    stderr := .piped
  }
  -- Tee stdout+stderr to logPath.
  IO.FS.withFile logPath .write fun h => do
    let outTask ← IO.asTask <| do
      let mut acc : String := ""
      while true do
        let line ← proc.stdout.getLine
        if line.isEmpty then break
        IO.print line
        h.putStr line
        acc := acc ++ line
      return acc
    let errTask ← IO.asTask <| do
      while true do
        let line ← proc.stderr.getLine
        if line.isEmpty then break
        IO.eprint line
        h.putStr line
      return ()
    let _ ← IO.wait outTask
    let _ ← IO.wait errTask
    pure ()
  let rc ← proc.wait
  return rc

/-- Top-level diagnostics collection: patch, build, parse. Restores via
`Restore.withBackups`-like discipline (callers should use
`withBackups`). -/
def runDiagnostics (lakefilePath : FilePath) (extraOffFiles : Array FilePath := #[]) :
    IO UInt32 := do
  IO.FS.createDirAll dataDir
  patchLakefile lakefilePath
  patchDiagnosticsOffFiles extraOffFiles
  let rc ← runBuild buildLogPath
  -- Parse regardless (partial logs are still useful).
  let n ← parseLog buildLogPath diagnosticsPath
  IO.eprintln s!"[no_expose diagnostics] wrote {n} records to {diagnosticsPath}"
  restoreAll
  return rc

end NoExpose
