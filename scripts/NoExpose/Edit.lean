/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import NoExpose.Cli
import NoExpose.Paths
import NoExpose.Report

/-!
# `NoExpose.Edit` — apply `@[expose]` removals to source files

The user-facing core. For each target file:

1. **Read** the report to find this file's safe-to-unexpose and
   load-bearing decls.
2. **Detect strategy**: `auto` picks `section` if the file has
   `@[expose] public section`; otherwise `individual`.
3. **Compute edits** (text-level, deliberately not full Lean parse):
   * `section`: drop `@[expose] ` from the section line, then prepend
     `@[expose]` to each load-bearing decl line.
   * `individual`: for each safe-to-unexpose decl, drop `@[expose]`
     from its attribute list (only handles single-attribute lines in
     v1; multi-attribute lines are skipped with a logged diagnostic).
4. **Safety checks**:
   * stale-data check: report.jsonl mtime ≥ source mtime
   * clean-tree check: `git status --porcelain PATH` is empty
5. **Apply** unless `--dry-run`.
6. **Audit trail**: append a unified diff to `edits.patch`.

v1 punts on `--verify` (rebuild the smallest containing target after
edit). The conservative defaults + audit trail give the user a quick
`git diff` / `git checkout` recovery path.
-/

open System

namespace NoExpose

/-! ## Source-file location helpers -/

/-- True if any line in `text` matches `@[expose] public section`
(stripped of leading whitespace). -/
private def hasExposeSection (text : String) : Bool :=
  let lines := text.splitOn "\n"
  lines.any fun line =>
    let trimmed := line.trimAscii.toString
    trimmed.startsWith "@[expose] public section"

/-- Strategy used for a particular file. -/
inductive ResolvedStrategy where
  | section_   : ResolvedStrategy
  | individual : ResolvedStrategy
  deriving Repr, DecidableEq

private def chooseStrategy (sel : EditStrategy) (text : String) : ResolvedStrategy :=
  match sel with
  | .section_   => .section_
  | .individual => .individual
  | .auto       => if hasExposeSection text then .section_ else .individual

/-! ## Section-strategy edit

Algorithm:
1. Find the line `@[expose] public section`. Replace with `public section`.
2. For each load-bearing decl in the file (sorted by line desc, so
   line numbers stay valid), insert a new line `@[expose]` *above* it.
   "Above" means: insert before the first preceding line that is the
   start of the decl's declaration block (skipping `@[...]` attribute
   lines and `/-- ... -/` doccomments).
-/

/-- Starting at `idx` (a 0-based index pointing somewhere inside the
"decl block" — i.e. doc-comment lines, attribute lines, or the decl
keyword itself), advance forward past doc comments and attribute lines
until we reach the line containing the decl keyword (`def`,
`theorem`, `instance`, `abbrev`, …). Returns that line's index.

Doc comments are handled in two shapes: single-line `/-- ... -/` and
multi-line `/-- ...` … `... -/`. Attributes are single-line
`@[...]`. Other modifier-only lines (`noncomputable`) are also
skipped. -/
private partial def declKeywordLineFrom
    (lines : Array String) (idx : Nat) : Nat := Id.run do
  let mut i := idx
  while i < lines.size do
    let line : String := lines[i]!
    let trimmed : String := line.trimAscii.toString
    if trimmed.startsWith "/--" then
      -- Single-line doc on this same line?
      if trimmed.endsWith "-/" && trimmed.length > "/----/".length then
        i := i + 1
      else
        -- Multi-line doc; skip until the closing `-/`.
        i := i + 1
        while i < lines.size do
          let l2 := (lines[i]!).trimAscii.toString
          i := i + 1
          if l2.endsWith "-/" then break
    else if trimmed.startsWith "@[" then
      i := i + 1
    else
      break
  return i

/-- Apply the section strategy. Returns the new file contents (or
`none` to indicate "no changes needed"). -/
def applySectionStrategy (text : String) (loadBearing : Array Nat) :
    Option String := Id.run do
  let lines := (text.splitOn "\n").toArray
  -- Step 1: rewrite the section line.
  let mut sectionRewritten := false
  let mut newLines : Array String := #[]
  for line in lines do
    let trimmed := line.trimAscii.toString
    if !sectionRewritten && trimmed.startsWith "@[expose] public section" then
      sectionRewritten := true
      let leading : String := (line.takeWhile Char.isWhitespace).toString
      let rest : String :=
        (line.drop (leading.length + "@[expose] public section".length)).toString
      newLines := newLines.push (leading ++ "public section" ++ rest)
    else
      newLines := newLines.push line
  unless sectionRewritten do return none
  -- Step 2: insert `@[expose]` above each load-bearing decl, processing
  -- highest line first so earlier indices remain valid. Lean does not
  -- allow stacked `@[...]` blocks before a decl, so if the first line
  -- of the decl block is already `@[...]` we merge into it.
  let sortedDesc := loadBearing.qsort (· > ·)
  for declLine in sortedDesc do
    if declLine == 0 then continue
    let blockStart := declLine - 1
    if blockStart ≥ newLines.size then continue
    -- Walk forward to the actual decl-keyword line.
    let declIdx := declKeywordLineFrom newLines blockStart
    if declIdx == 0 || declIdx ≥ newLines.size then continue
    -- Look at the line immediately above the decl. If it's an attribute
    -- list, merge `@[expose, ...]`; otherwise insert a new line above
    -- the decl (so the order is `/-- doc -/`, then `@[expose]`, then
    -- the decl keyword).
    let above : String := newLines[declIdx - 1]!
    let aboveTrim : String := above.trimAscii.toString
    if aboveTrim.startsWith "@[" then
      -- Already-exposed shapes: skip.
      if aboveTrim == "@[expose]" || aboveTrim.startsWith "@[expose " ||
         aboveTrim.startsWith "@[expose," then
        continue
      let leading : String := (above.takeWhile Char.isWhitespace).toString
      let body : String :=
        (above.drop (leading.length + "@[".length)).toString
      let merged : String := leading ++ "@[expose, " ++ body
      newLines := newLines.set! (declIdx - 1) merged
    else
      let declLineStr : String := newLines[declIdx]!
      let leading : String := (declLineStr.takeWhile Char.isWhitespace).toString
      let attrLine : String := leading ++ "@[expose]"
      newLines := newLines.insertIdx! declIdx attrLine
  return some (String.intercalate "\n" newLines.toList)

/-! ## Individual-strategy edit

For each safe-to-unexpose decl on a recorded line, look for an
`@[expose]` attribute on or above the decl line and remove it. This v1
only handles two shapes:

* `@[expose]` on its own line → delete the entire line.
* Decl line is `@[expose] def foo …` → strip the `@[expose] ` prefix
  (only if it's the *only* attribute on the line).

Anything else (multi-attribute `@[expose, simp]`, splits across lines
in unusual ways) is skipped with a diagnostic — these are the ~34
hand-written edge cases. -/

/-- Strip `@[expose]` from a single-attribute occurrence around `line`
(0-based index into `lines`). Returns `(modifiedLines?, reason)`
where `reason` is a short tag for logging skipped cases. -/
private def stripIndividualOne (lines : Array String) (lineIdx : Nat) :
    Option (Array String) := Id.run do
  if lineIdx ≥ lines.size then return none
  let line := lines[lineIdx]!
  let trimmed := line.trimAscii.toString
  -- Case A: `@[expose] decl ...` on the same line, single attribute.
  if trimmed.startsWith "@[expose] " then
    let leading := line.takeWhile Char.isWhitespace |>.toString
    let rest := (line.drop (leading.length + "@[expose] ".length)).toString
    return some (lines.set! lineIdx (leading ++ rest))
  -- Case B: previous line is exactly `@[expose]` (with optional whitespace).
  if lineIdx > 0 then
    let prev := lines[lineIdx - 1]!
    if prev.trimAscii.toString == "@[expose]" then
      return some (lines.eraseIdx! (lineIdx - 1))
  return none

/-- Apply the individual strategy. Returns the new contents and a list
of decl lines that we couldn't safely edit (caller logs them). -/
def applyIndividualStrategy (text : String) (safe : Array Nat) :
    String × Array Nat := Id.run do
  let mut lines := (text.splitOn "\n").toArray
  let mut skipped : Array Nat := #[]
  -- Process highest line first so index shifts don't matter.
  let sortedDesc := safe.qsort (· > ·)
  for declLine in sortedDesc do
    if declLine == 0 then continue
    let idx := declLine - 1
    match stripIndividualOne lines idx with
    | some lines' => lines := lines'
    | none        => skipped := skipped.push declLine
  return (String.intercalate "\n" lines.toList, skipped)

/-! ## Safety checks -/

/-- Compare modification times: ok if `report` is at least as new as `source`. -/
private def checkStaleness (sourcePath reportPath : FilePath) : IO Bool := do
  let srcTime := (← sourcePath.metadata).modified
  let rptTime := (← reportPath.metadata).modified
  return rptTime ≥ srcTime

/-- True if the working tree for `path` has no uncommitted changes. -/
private def isCleanInGit (path : FilePath) : IO Bool := do
  let out ← IO.Process.output {
    cmd := "git", args := #["status", "--porcelain", path.toString] }
  return out.stdout.trimAscii.toString == ""

/-! ## Top-level driver -/

/-- Compute a tiny unified-diff-ish summary of two strings. v1 is
"line N: -<old>\n+<new>"-style, not a real `diff -u` (no hunk
headers). Good enough for the audit trail. -/
private def quickDiff (oldText newText : String) : String := Id.run do
  let oldLines := oldText.splitOn "\n"
  let newLines := newText.splitOn "\n"
  let mut acc : String := ""
  for i in [:oldLines.length.max newLines.length] do
    let o := oldLines[i]?.getD ""
    let n := newLines[i]?.getD ""
    if o != n then
      acc := acc ++ s!"@@ line {i+1}\n-{o}\n+{n}\n"
  return acc

/-- Apply edits to a single file. Returns `true` if the file was
modified (or would be, in dry-run mode). -/
def editOneFile (file : FilePath) (records : Array ReportRecord)
    (args : EditArgs) (auditAccum : IO.Ref String) : IO Bool := do
  unless ← System.FilePath.pathExists file do
    IO.eprintln s!"no_expose edit: {file} does not exist; skipping"
    return false
  -- Safety: clean tree.
  unless args.forceDirty do
    if !(← isCleanInGit file) then
      IO.eprintln s!"no_expose edit: {file} has uncommitted changes; \
        pass --force-dirty to override."
      return false
  -- Safety: stale data.
  unless args.forceStale do
    if !(← checkStaleness file reportPath) then
      IO.eprintln s!"no_expose edit: {file} is newer than {reportPath}; \
        re-run `collect` or pass --force-stale."
      return false
  let originalText ← IO.FS.readFile file
  -- Dedupe by line: `to_additive` (and similar) macros produce multiple
  -- report rows that all point at the same source line. Each line should
  -- get at most one edit.
  let dedupe (xs : Array Nat) : Array Nat :=
    let init : Array Nat × Std.HashSet Nat := (#[], {})
    (xs.foldl (init := init) fun (acc, seen) x =>
      if seen.contains x then (acc, seen) else (acc.push x, seen.insert x)).1
  let safeLines : Array Nat := dedupe (records
    |>.filter (Verdict.classify · == .safeToUnexpose) |>.map (·.line))
  let loadBearingLines : Array Nat := dedupe (records
    |>.filter (Verdict.classify · == .loadBearing) |>.map (·.line))
  let strategy := chooseStrategy args.strategy originalText
  let (newText, skipped) : String × Array Nat ← do
    match strategy with
    | .section_ => do
      match applySectionStrategy originalText loadBearingLines with
      | some t => pure (t, #[])
      | none => do
        IO.eprintln s!"no_expose edit: {file}: section strategy chosen but \
          no `@[expose] public section` line found; skipping."
        pure (originalText, #[])
    | .individual => pure (applyIndividualStrategy originalText safeLines)
  if newText == originalText then
    IO.println s!"{file}: no changes."
    return false
  for s in skipped do
    IO.eprintln s!"  skipped {file}:{s} (multi-attribute or unknown shape)"
  -- Audit trail.
  auditAccum.modify (· ++ s!"--- {file}\n" ++ quickDiff originalText newText)
  if args.dryRun then
    IO.println s!"{file}: would modify (dry-run; pass without --dry-run to apply)."
    IO.println (quickDiff originalText newText)
    return true
  IO.FS.writeFile file newText
  IO.println s!"{file}: applied edits."
  return true

/-- Top-level `edit` subcommand. -/
def runEdit (args : EditArgs) : IO UInt32 := do
  unless ← System.FilePath.pathExists reportPath do
    IO.eprintln s!"no_expose edit: {reportPath} not found; \
      run `lake exe no_expose collect` first."
    return 2
  let (records, errs) ← readReport reportPath
  for e in errs do IO.eprintln s!"warning: {e}"
  let groups := byFile records
  if args.paths.isEmpty then
    IO.eprintln "no_expose edit: pass at least one PATH"
    return 2
  let auditAccum ← IO.mkRef ""
  let mut anyModified := false
  for p in args.paths do
    let recs := groups.getD p #[]
    if recs.isEmpty then
      IO.eprintln s!"{p}: no exposed decls in report"
      continue
    let modified ← editOneFile (FilePath.mk p) recs args auditAccum
    if modified then anyModified := true
  -- Append audit trail.
  let auditBody ← auditAccum.get
  if anyModified && !auditBody.isEmpty then
    IO.FS.createDirAll dataDir
    IO.FS.withFile editsPatchPath .append fun h => h.putStr auditBody
    IO.eprintln s!"[no_expose edit] audit trail appended to {editsPatchPath}"
  return 0

end NoExpose
