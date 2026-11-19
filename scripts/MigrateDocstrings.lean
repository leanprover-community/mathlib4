/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Thrane Christiansen
-/
import VersoMigrateDocstrings

/-!
# Mathlib docstring migrator

A custom front-end for the `verso-migrate-docstrings` tool that wires in the
extensions for Mathlib's migration roles:

* `{url}` for bare URLs (`VersoMigrateDocstrings.UrlRole`).
* `{cite "key"}[text]` for reference-style citations whose key is in
  `docs/references.bib` (`VersoMigrateDocstrings.Cite`).
* `` {library_note}`label` `` for `[label]` references to known library notes
  (`libraryNoteExtension`, defined here).
* The `code` code block for non-Lean fenced blocks (the `--code-block code`
  setting, supplied by default).

The bibliography keys and library-note labels are gathered by IO at startup and
baked into the extensions as pure data, following the tool's design.

Run it like the underlying tool, e.g. `lake exe migrate-docstrings --write Mathlib/Foo.lean`.
-/

/-! ## The `library_note` extension -/

/-- The length of the longest run of backticks in `s`. -/
private def longestBacktickRun (s : String) : Nat := Id.run do
  let mut longest := 0
  let mut current := 0
  for c in s.toList do
    if c == '`' then
      current := current + 1
      if current > longest then longest := current
    else current := 0
  return longest

/-- Emits `` {library_note}`label` ``, choosing a backtick run that doesn't
collide with backticks inside `label`. -/
private def emitLibraryNote (label : String) : VersoMigrateDocstrings.EmitM Unit := do
  let fence := String.ofList (List.replicate (longestBacktickRun label + 1) '`')
  let padLeft := label.startsWith "`" || label.startsWith " "
  let padRight := label.endsWith "`" || label.endsWith " "
  VersoMigrateDocstrings.pushRaw "{library_note}"
  VersoMigrateDocstrings.pushRaw fence
  if padLeft then VersoMigrateDocstrings.pushRaw " "
  VersoMigrateDocstrings.pushRaw label
  if padRight then VersoMigrateDocstrings.pushRaw " "
  VersoMigrateDocstrings.pushRaw fence

/-- Reads characters up to the first `delim`. Returns the text before it and, if
found, the characters after it. -/
private def splitAtDelim (cs : List Char) (delim : Char) : String × Option (List Char) :=
  Id.run do
    let mut buf := ""
    let mut i := 0
    for c in cs do
      if c == delim then return (buf, some (cs.drop (i + 1)))
      buf := buf.push c
      i := i + 1
    return (buf, none)

/-- Splits text into segments. The flag is `true` for a `[label]` reference to a
known library note and `false` for plain text. A `[label]` immediately followed
by `[` is left as plain text, since it belongs to a reference-style link or
citation. -/
private def splitNotes (labels : Std.HashSet String) (cs : List Char) : Array (Bool × String) :=
  Id.run do
    let mut segs : Array (Bool × String) := #[]
    let mut plain := ""
    let mut rest := cs
    while !rest.isEmpty do
      match rest with
      | '[' :: tl =>
        match splitAtDelim tl ']' with
        | (label, some after) =>
          if labels.contains label && after.head? != some '[' then
            if !plain.isEmpty then
              segs := segs.push (false, plain)
              plain := ""
            segs := segs.push (true, label)
            rest := after
          else
            plain := plain.push '['
            rest := tl
        | (_, none) =>
          plain := plain.push '['
          rest := tl
      | c :: tl =>
        plain := plain.push c
        rest := tl
      | [] => rest := []
    if !plain.isEmpty then segs := segs.push (false, plain)
    return segs

/--
Migration extension rewriting `[label]` to `` {library_note}`label` `` for every
`label` in `labels`. Pass it to `VersoMigrateDocstrings.run`.

The caller supplies the labels of the library notes defined in the project; they
are captured here so the conversion stays pure.
-/
def libraryNoteExtension (labels : List String) : VersoMigrateDocstrings.MigrationExtension :=
  let known := Std.HashSet.ofList labels
  { name := `Mathlib.VersoMigrate.LibraryNote
    inlineRewrite := fun emit t =>
      match t with
      | MD4Lean.Text.normal s => do
        let segs := splitNotes known s.toList
        if segs.all (!·.1) then
          return false
        for (isNote, text) in segs do
          if isNote then emitLibraryNote text
          else emit #[MD4Lean.Text.normal text]
        return true
      | _ => pure false }

/-! ## Gathering the bibliography keys and note labels -/

/-- The keys of every entry in a `references.bib` file. -/
private def parseBibKeys (bib : String) : List String := Id.run do
  let mut keys : List String := []
  for line in bib.splitOn "\n" do
    let line := line.trimAscii.copy
    if line.startsWith "@" then
      match line.splitOn "{" with
      | _ :: rest :: _ =>
        let key := (rest.takeWhile (· != ',')).trimAscii.copy
        if !key.isEmpty then keys := key :: keys
      | _ => pure ()
  return keys.reverse

/-- Loads the bibliography keys from `path`, or `[]` if it is absent. -/
private def loadBibKeys (path : System.FilePath) : IO (List String) := do
  if ← path.pathExists then return parseBibKeys (← IO.FS.readFile path)
  else return []

/-- The text between the first `op` and the following `cl`, if both are present. -/
private def between (s op cl : String) : Option String :=
  match s.splitOn op with
  | _ :: rest :: _ => some ((rest.splitOn cl).headD rest)
  | _ => none

/-- The label of a `library_note` declaration on `line`, if any. The label is
written either in «french quotes» or in "double quotes". -/
private def noteLabelOf (line : String) : Option String :=
  let trimmed := line.trimAscii.copy
  if !trimmed.startsWith "library_note" then none
  else
    let after := (trimmed.drop "library_note".length).copy
    match between after "«" "»" |>.orElse fun _ => between after "\"" "\"" with
    | some label => if label.isEmpty then none else some label
    | none => none

/-- Scans the Lean sources under `root` for the labels of all `library_note`
declarations. -/
private def scanNoteLabels (root : System.FilePath) : IO (Array String) := do
  let mut labels : Std.HashSet String := {}
  for file in ← root.walkDir do
    if file.extension == some "lean" then
      for line in (← IO.FS.readFile file).splitOn "\n" do
        if let some label := noteLabelOf line then labels := labels.insert label
  return labels.toArray

/-- Where the parent process caches the note labels for its workers. -/
private def noteLabelCache : System.FilePath := ".lake" / "build" / "verso-migrate-note-labels.txt"

/-- `true` when this process was spawned by the tool as a worker or verifier; such
processes read the cached labels instead of rescanning the source tree. -/
private def isChildProcess (args : List String) : Bool :=
  args.contains "--worker" || args.contains "--verify-output"

/-- The library-note labels for this run. The parent scans the source tree and
caches the result; workers and verifiers read the cache. -/
private def loadNoteLabels (args : List String) : IO (Array String) := do
  if isChildProcess args then
    if ← noteLabelCache.pathExists then
      return ((← IO.FS.readFile noteLabelCache).splitOn "\n").filter (· != "") |>.toArray
    else
      return ← scanNoteLabels "Mathlib"
  else
    let labels ← scanNoteLabels "Mathlib"
    if let some dir := noteLabelCache.parent then IO.FS.createDirAll dir
    IO.FS.writeFile noteLabelCache (String.intercalate "\n" labels.toList)
    return labels

/-! ## Entry point -/

unsafe def main (args : List String) : IO UInt32 := do
  let keys ← loadBibKeys ("docs" / "references.bib")
  let labels ← loadNoteLabels args
  let extensions := #[
    VersoMigrateDocstrings.UrlRole.extension,
    VersoMigrateDocstrings.Cite.extension keys,
    libraryNoteExtension labels.toList]
  -- Render non-Lean fenced blocks with the `code` block. In parent mode this is
  -- forwarded to workers; in child mode the parent already supplied it.
  let args := if isChildProcess args then args else "--code-block" :: "code" :: args
  VersoMigrateDocstrings.run extensions args
