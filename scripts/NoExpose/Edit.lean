/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean.Parser.Module
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
6. **Audit trail** (apply-only): append a `git apply`-compatible unified
   diff to `scripts/.no_expose/edits.patch`. `--dry-run` prints the same
   diff to stdout but does not touch the audit file.
7. **Verify** (apply-only, `--verify`): re-run `lake build` on the
   touched module and roll back the edit on non-zero exit.
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
in unusual ways) is skipped with a diagnostic. -/

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

/-! ## Parse validation + lake-build verify -/

/-- Count parse errors in `text` at the syntax level only (no
elaboration). Cheap — only `Init` is in scope, so Mathlib-defined
notations produce false positives. Callers should use this
*differentially* (compare before/after) rather than absolutely. -/
unsafe def countParseErrors (file : System.FilePath) (text : String) :
    IO Nat := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Init }] {}
  let inputCtx := Lean.Parser.mkInputContext text file.toString
  let (_, mps, msgs) ← Lean.Parser.parseHeader inputCtx
  let pmctx : Lean.Parser.ParserModuleContext := { env, options := {} }
  let mut state := mps
  let mut messages := msgs
  repeat
    let (stx, state', msgs') := Lean.Parser.parseCommand inputCtx pmctx state messages
    state := state'
    messages := msgs'
    if Lean.Parser.isTerminalCommand stx then break
  return messages.toList.foldl (init := 0) fun n m =>
    if m.severity == .error then n + 1 else n

/-- Convert `Mathlib/Foo/Bar.lean` to the module name `Mathlib.Foo.Bar`. -/
private def fileToModule (path : System.FilePath) : String :=
  let s := path.toString
  let stripped : String :=
    if s.endsWith ".lean" then (s.dropEnd 5).toString else s
  stripped.replace "/" "."

/-- Run `lake build <module>` for the touched file. Returns the exit code. -/
def verifyByLakeBuild (file : System.FilePath) : IO UInt32 := do
  let mod := fileToModule file
  IO.eprintln s!"[no_expose edit] verifying: lake build {mod}"
  let proc ← IO.Process.spawn {
    cmd := "lake", args := #["build", mod]
    stdout := .inherit, stderr := .inherit }
  proc.wait

/-! ## Unified-diff rendering

A standard LCS-based line diff with `git apply`-compatible hunk headers
(`@@ -A,B +C,D @@`). Used for both the on-screen `--dry-run` preview and
the persisted audit trail at `scripts/.no_expose/edits.patch`. -/

private inductive DiffOp where
  | keep (line : String)
  | del  (line : String)
  | ins  (line : String)
  deriving Inhabited

/-- Split on `"\n"` and drop the trailing empty element produced by a
final newline, so that "a\nb\n" yields `#["a", "b"]` (two lines, not
three). -/
private def splitIntoLines (s : String) : Array String :=
  let xs := (s.splitOn "\n").toArray
  if xs.size > 0 && xs[xs.size - 1]! == "" then xs.pop else xs

/-- Line-level LCS diff. O(m·n) time and memory; fine for the file
sizes `no_expose` edits (mathlib files are at most a few thousand
lines). -/
private def diffOps (old new : Array String) : Array DiffOp := Id.run do
  let m := old.size
  let n := new.size
  let w := n + 1
  -- Flat (m+1) × (n+1) LCS-length table.
  let mut t : Array Nat := Array.replicate ((m+1) * w) 0
  for i in [:m] do
    for j in [:n] do
      let v :=
        if old[i]! == new[j]! then
          t[i*w + j]! + 1
        else
          Nat.max t[i*w + (j+1)]! t[(i+1)*w + j]!
      t := t.set! ((i+1)*w + (j+1)) v
  -- Backtrack from (m, n).
  let mut ops : Array DiffOp := #[]
  let mut i := m
  let mut j := n
  while i > 0 || j > 0 do
    if i > 0 && j > 0 && old[i-1]! == new[j-1]! then
      ops := ops.push (.keep old[i-1]!)
      i := i - 1; j := j - 1
    else if j > 0 && (i == 0 || t[i*w + (j-1)]! ≥ t[(i-1)*w + j]!) then
      ops := ops.push (.ins new[j-1]!)
      j := j - 1
    else
      ops := ops.push (.del old[i-1]!)
      i := i - 1
  return ops.reverse

private structure Hunk where
  oldStart : Nat
  newStart : Nat
  oldLen : Nat
  newLen : Nat
  lines : Array String  -- each prefixed by ' ', '-', or '+'

/-- Group diff ops into hunks with `context` lines of unchanged context
around each run of changes. Adjacent runs whose contexts touch are
merged into a single hunk. -/
private def buildHunks (ops : Array DiffOp) (context : Nat := 3) : Array Hunk := Id.run do
  let n := ops.size
  if n == 0 then return #[]
  -- Mark each op that is within `context` positions of a non-keep op.
  let mut inHunk : Array Bool := Array.replicate n false
  for k in [:n] do
    match ops[k]! with
    | .keep _ => pure ()
    | _ =>
      let lo := if k ≥ context then k - context else 0
      let hi := Nat.min n (k + context + 1)
      for p in [lo:hi] do
        inHunk := inHunk.set! p true
  -- Walk, emitting one hunk per maximal run of inHunkd ops.
  let mut hunks : Array Hunk := #[]
  let mut oldLine : Nat := 1
  let mut newLine : Nat := 1
  let mut k : Nat := 0
  while k < n do
    if !inHunk[k]! then
      match ops[k]! with
      | .keep _ => oldLine := oldLine + 1; newLine := newLine + 1
      | .del _ => oldLine := oldLine + 1
      | .ins _ => newLine := newLine + 1
      k := k + 1
    else
      let hOldStart := oldLine
      let hNewStart := newLine
      let mut hLines : Array String := #[]
      let mut hOldLen := 0
      let mut hNewLen := 0
      while k < n && inHunk[k]! do
        match ops[k]! with
        | .keep s =>
          hLines := hLines.push (" " ++ s)
          oldLine := oldLine + 1; newLine := newLine + 1
          hOldLen := hOldLen + 1; hNewLen := hNewLen + 1
        | .del s =>
          hLines := hLines.push ("-" ++ s)
          oldLine := oldLine + 1
          hOldLen := hOldLen + 1
        | .ins s =>
          hLines := hLines.push ("+" ++ s)
          newLine := newLine + 1
          hNewLen := hNewLen + 1
        k := k + 1
      hunks := hunks.push ⟨hOldStart, hNewStart, hOldLen, hNewLen, hLines⟩
  return hunks

private def formatHunkHeader (h : Hunk) : String :=
  -- For pure insertions/deletions, the conventional start in unified
  -- diff is the line *before* the change (or 0 at file start).
  let oldStart := if h.oldLen == 0 && h.oldStart > 0 then h.oldStart - 1 else h.oldStart
  let newStart := if h.newLen == 0 && h.newStart > 0 then h.newStart - 1 else h.newStart
  s!"@@ -{oldStart},{h.oldLen} +{newStart},{h.newLen} @@"

/-- Render a `git apply`-compatible unified diff for a single file. -/
private def renderUnifiedDiff (filePath : String) (oldText newText : String) : String := Id.run do
  let oldLines := splitIntoLines oldText
  let newLines := splitIntoLines newText
  let ops := diffOps oldLines newLines
  let hunks := buildHunks ops
  if hunks.isEmpty then return ""
  let mut acc : String := s!"--- a/{filePath}\n+++ b/{filePath}\n"
  for h in hunks do
    acc := acc ++ formatHunkHeader h ++ "\n"
    for line in h.lines do
      acc := acc ++ line ++ "\n"
  return acc

/-! ## Top-level driver -/

/-- Apply edits to a single file. Returns `true` if the file was
modified (or would be, in dry-run mode). -/
unsafe def editOneFile (file : FilePath) (records : Array ReportRecord)
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
  let diff := renderUnifiedDiff file.toString originalText newText
  -- Parse-validate (differential): the edited text must not introduce
  -- new syntax errors over the original. False positives from
  -- Mathlib-only notation cancel out.
  let oldErrCount ← countParseErrors file originalText
  let newErrCount ← countParseErrors file newText
  if newErrCount > oldErrCount then
    IO.eprintln s!"no_expose edit: {file}: edit introduced {newErrCount - oldErrCount} \
      new parse error(s); refusing to write."
    return false
  if args.dryRun then
    IO.println s!"{file}: would modify (dry-run; pass without --dry-run to apply)."
    IO.print diff
    return true
  -- Persisted audit trail (apply-only).
  auditAccum.modify (· ++ diff)
  IO.FS.writeFile file newText
  IO.println s!"{file}: applied edits."
  if args.verify then
    let rc ← verifyByLakeBuild file
    if rc != 0 then
      IO.eprintln s!"no_expose edit: {file}: lake build failed (exit {rc}); \
        rolling back."
      IO.FS.writeFile file originalText
      return false
    IO.println s!"{file}: verify ok."
  return true

/-- Top-level `edit` subcommand. -/
unsafe def runEdit (args : EditArgs) : IO UInt32 := do
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
