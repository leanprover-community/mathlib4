/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Batteries.Data.String.Matcher
import Mathlib.Data.Nat.Notation
import Std.Data.HashMap.Basic

/-!
## Text-based linters

This file defines various mathlib linters which are based on reading the source code only.
In practice, all such linters check for code style issues.

For now, this only contains linters checking
- that the copyright header and authors line are correctly formatted
- existence of module docstrings (in the right place)
- for certain disallowed imports
- if the string "adaptation note" is used instead of the command #adaptation_note
- files are at most 1500 lines long (unless specifically allowed).

For historic reasons, some of these checks are still written in a Python script `lint-style.py`:
these are gradually being rewritten in Lean.

This linter maintains a list of exceptions, for legacy reasons.
Ideally, the length of the list of exceptions tends to 0.

The `longFile` and the `longLine` *syntax* linter take care of flagging lines that exceed the
100 character limit and files that exceed the 1500 line limit.
The text-based versions of this file are still used for the files where the linter is not imported.
This means that the exceptions for the text-based linters are shorter, as they do not need to
include those handled with `set_option linter.style.longFile x`/`set_option linter.longLine false`.

An executable running all these linters is defined in `scripts/lint-style.lean`.
-/

open System

namespace Mathlib.Linter.TextBased

/-- Different kinds of "broad imports" that are linted against. -/
inductive BroadImports
  /-- Importing the entire "Mathlib.Tactic" folder -/
  | TacticFolder
  /-- Importing any module in `Lake`, unless carefully measured
  This has caused unexpected regressions in the past. -/
  | Lake
deriving BEq

/-- Possible errors that text-based linters can report. -/
-- We collect these in one inductive type to centralise error reporting.
inductive StyleError where
  /-- Missing or malformed copyright header.
  Unlike in the python script, we may provide some context on the actual error. -/
  | copyright (context : Option String)
  /-- Malformed authors line in the copyright header -/
  | authors
  /-- The bare string "Adaptation note" (or variants thereof): instead, the
  #adaptation_note command should be used. -/
  | adaptationNote
  /-- Lint against "too broad" imports, such as `Mathlib.Tactic` or any module in `Lake`
  (unless carefully measured) -/
  | broadImport (module : BroadImports)
  /-- A line ends with windows line endings (\r\n) instead of unix ones (\n). -/
  | windowsLineEnding
  | duplicateImport (importStatement: String) (alreadyImportedLine: ℕ)
deriving BEq

/-- How to format style errors -/
inductive ErrorFormat
  /-- Produce style error output aimed at humans: no error code, clickable file name -/
  | humanReadable : ErrorFormat
  /-- Produce an entry in the style-exceptions file: mention the error code, slightly uglier
  than humand-readable output -/
  | exceptionsFile : ErrorFormat
  /-- Produce output suitable for Github error annotations: in particular,
  duplicate the file path, line number and error code -/
  | github : ErrorFormat
  deriving BEq

/-- Create the underlying error message for a given `StyleError`. -/
def StyleError.errorMessage (err : StyleError) : String := match err with
  | StyleError.copyright (some context) => s!"Malformed or missing copyright header: {context}"
  | StyleError.copyright none => "Malformed or missing copyright header"
  | StyleError.authors =>
    "Authors line should look like: 'Authors: Jean Dupont, Иван Иванович Иванов'"
  | StyleError.adaptationNote =>
    "Found the string \"Adaptation note:\", please use the #adaptation_note command instead"
  | StyleError.broadImport BroadImports.TacticFolder =>
    "Files in mathlib cannot import the whole tactic folder"
  | StyleError.broadImport BroadImports.Lake =>
      "In the past, importing 'Lake' in mathlib has led to dramatic slow-downs of the linter (see \
      e.g. mathlib4#13779). Please consider carefully if this import is useful and make sure to \
      benchmark it. If this is fine, feel free to allow this linter."
  | windowsLineEnding => "This line ends with a windows line ending (\r\n): please use Unix line\
    endings (\n) instead"
  | StyleError.duplicateImport (importStatement) (alreadyImportedLine) =>
    s!"Duplicate imports: {importStatement} (already imported on line {alreadyImportedLine})"

/-- The error code for a given style error. Keep this in sync with `parse?_errorContext` below! -/
-- FUTURE: we're matching the old codes in `lint-style.py` for compatibility;
-- in principle, we could also print something more readable.
def StyleError.errorCode (err : StyleError) : String := match err with
  | StyleError.copyright _ => "ERR_COP"
  | StyleError.authors => "ERR_AUT"
  | StyleError.adaptationNote => "ERR_ADN"
  | StyleError.broadImport _ => "ERR_IMP"
  | StyleError.windowsLineEnding => "ERR_WIN"
  | StyleError.duplicateImport _ _ => "ERR_DIMP"

/-- Context for a style error: the actual error, the line number in the file we're reading
and the path to the file. -/
structure ErrorContext where
  /-- The underlying `StyleError`-/
  error : StyleError
  /-- The line number of the error (1-based) -/
  lineNumber : ℕ
  /-- The path to the file which was linted -/
  path : FilePath

/-- Possible results of comparing an `ErrorContext` to an `existing` entry:
most often, they are different --- if the existing entry covers the new exception,
depending on the error, we prefer the new or the existing entry. -/
inductive ComparisonResult
  /-- The contexts describe different errors: two separate style exceptions are required
  to cover both. -/
  | Different
  /-- The existing exception also covers the new error.
  Indicate whether we prefer keeping the existing exception (the more common case)
  or would rather replace it by the new exception
  (this is more rare, and currently only happens for particular file length errors). -/
  | Comparable (preferExisting : Bool)
  deriving BEq

/-- Determine whether a `new` `ErrorContext` is covered by an `existing` exception,
and, if it is, if we prefer replacing the new exception or keeping the previous one. -/
def compare (existing new : ErrorContext) : ComparisonResult :=
  -- Two comparable error contexts must have the same path.
  -- To avoid issues with different path separators across different operating systems,
  -- we compare the set of path components instead.
  if existing.path.components != new.path.components then ComparisonResult.Different
  -- We entirely ignore their line numbers: not sure if this is best.

  -- NB: keep the following in sync with `parse?_errorContext` below.
  -- Generally, comparable errors must have equal `StyleError`s, but there are some exceptions.
  else match (existing.error, new.error) with
  -- We do *not* care about the *kind* of wrong copyright,
  -- nor about the particular length of a too long line.
  | (StyleError.copyright _, StyleError.copyright _) => ComparisonResult.Comparable true
  -- In all other cases, `StyleErrors` must compare equal.
  | (a, b) => if a == b then ComparisonResult.Comparable true else ComparisonResult.Different

/-- Find the first style exception in `exceptions` (if any) which covers a style exception `e`. -/
def ErrorContext.find?_comparable (e : ErrorContext) (exceptions : Array ErrorContext) :
    Option ErrorContext :=
  (exceptions).find? (fun new ↦ compare e new matches ComparisonResult.Comparable _)

/-- Output the formatted error message, containing its context.
`style` specifies if the error should be formatted for humans to read, github problem matchers
to consume, or for the style exceptions file. -/
def outputMessage (errctx : ErrorContext) (style : ErrorFormat) : String :=
  let errorMessage := errctx.error.errorMessage
  match style with
  | ErrorFormat.github =>
   -- We are outputting for github: duplicate file path, line number and error code,
    -- so that they are also visible in the plain text output.
    let path := errctx.path
    let nr := errctx.lineNumber
    let code := errctx.error.errorCode
    s!"::ERR file={path},line={nr},code={code}::{path}:{nr} {code}: {errorMessage}"
  | ErrorFormat.exceptionsFile =>
    -- Produce an entry in the exceptions file: with error code and "line" in front of the number.
    s!"{errctx.path} : line {errctx.lineNumber} : {errctx.error.errorCode} : {errorMessage}"
  | ErrorFormat.humanReadable =>
    -- Print for humans: clickable file name and omit the error code
    s!"error: {errctx.path}:{errctx.lineNumber}: {errorMessage}"

/-- Try parsing an `ErrorContext` from a string: return `some` if successful, `none` otherwise. -/
def parse?_errorContext (line : String) : Option ErrorContext := Id.run do
  let parts := line.split (· == ' ')
  match parts with
    | filename :: ":" :: "line" :: lineNumber :: ":" :: errorCode :: ":" :: errorMessage =>
      -- Turn the filename into a path. In general, this is ambiguous if we don't know if we're
      -- dealing with e.g. Windows or POSIX paths. In our setting, this is fine, since no path
      -- component contains any path separator.
      let path := mkFilePath (filename.split (FilePath.pathSeparators.contains ·))
      -- Parse the error kind from the error code, ugh.
      -- NB: keep this in sync with `StyleError.errorCode` above!
      let err : Option StyleError := match errorCode with
        -- Use default values for parameters which are ignored for comparing style exceptions.
        -- NB: keep this in sync with `compare` above!
        | "ERR_COP" => some (StyleError.copyright none)
        | "ERR_AUT" => some (StyleError.authors)
        | "ERR_ADN" => some (StyleError.adaptationNote)
        | "ERR_WIN" => some (StyleError.windowsLineEnding)
        | "ERR_DIMP" => some (StyleError.duplicateImport "" 0)
        | "ERR_IMP" =>
          -- XXX tweak exceptions messages to ease parsing?
          if (errorMessage.get! 0).containsSubstr "tactic" then
            some (StyleError.broadImport BroadImports.TacticFolder)
          else
            some (StyleError.broadImport BroadImports.Lake)
        | _ => none
      match String.toNat? lineNumber with
      | some n => err.map fun e ↦ (ErrorContext.mk e n path)
      | _ => none
    -- It would be nice to print an error on any line which doesn't match the above format,
    -- but is awkward to do so (this `def` is not in any IO monad). Hopefully, this is not necessary
    -- anyway as the style exceptions file is mostly automatically generated.
    | _ => none

/-- Parse all style exceptions for a line of input.
Return an array of all exceptions which could be parsed: invalid input is ignored. -/
def parseStyleExceptions (lines : Array String) : Array ErrorContext := Id.run do
  -- We treat all lines starting with "--" as a comment and ignore them.
  Array.filterMap (parse?_errorContext ·) (lines.filter (fun line ↦ !line.startsWith "--"))

/-- Print information about all errors encountered to standard output.
`style` specifies if the error should be formatted for humans to read, github problem matchers
to consume, or for the style exceptions file. -/
def formatErrors (errors : Array ErrorContext) (style : ErrorFormat) : IO Unit := do
  for e in errors do
    IO.println (outputMessage e style)

/-- Core logic of a text based linter: given a collection of lines,
return an array of all style errors with line numbers. If possible,
also return the collection of all lines, changed as needed to fix the linter errors.
(Such automatic fixes are only possible for some kinds of `StyleError`s.)
-/
abbrev TextbasedLinter := Array String → Array (StyleError × ℕ) × (Option (Array String))

/-! Definitions of the actual text-based linters. -/
section

/-- Return if `line` looks like a correct authors line in a copyright header. -/
def isCorrectAuthorsLine (line : String) : Bool :=
  -- We cannot reasonably validate the author names, so we look only for a few common mistakes:
  -- the file starting wrong, double spaces, using ' and ' between names,
  -- and ending the line with a period.
  line.startsWith "Authors: " && (!line.containsSubstr "  ")
    && (!line.containsSubstr " and ") && (!line.endsWith ".")

/-- Lint a collection of input lines if they are missing an appropriate copyright header.

A copyright header should start at the very beginning of the file and contain precisely five lines,
including the copy year and holder, the license and main author(s) of the file (in this order).
-/
def copyrightHeaderLinter : TextbasedLinter := fun lines ↦ Id.run do
  -- Unlike the Python script, we just emit one warning.
  let start := lines.extract 0 4
  -- The header should start and end with blank comments.
  let _ := match (start.get? 0, start.get? 4) with
  | (some "/-", some "-/") => none
  | (some "/-", _) => return #[(StyleError.copyright none, 4)]
  | _ => return #[(StyleError.copyright none, 0)]

  -- If this is given, we go over the individual lines one by one,
  -- and provide some context on what is mis-formatted (if anything).
  let mut output := Array.mkEmpty 0
  -- By hypotheses above, start has at least five lines, so the `none` cases below are never hit.
  -- The first real line should state the copyright.
  if let some copy := start.get? 1 then
    if !(copy.startsWith "Copyright (c) 20" && copy.endsWith ". All rights reserved.") then
      output := output.push (StyleError.copyright "Copyright line is malformed", 2)
  -- The second line should be standard.
  let expectedSecondLine := "Released under Apache 2.0 license as described in the file LICENSE."
  if start.get? 2 != some expectedSecondLine then
    output := output.push (StyleError.copyright
      s!"Second line should be \"{expectedSecondLine}\"", 3)
  -- The third line should contain authors.
  if let some line := start.get? 3 then
    if !line.containsSubstr "Author" then
      output := output.push (StyleError.copyright
        "The third line should describe the file's main authors", 4)
    else
      -- If it does, we check the authors line is formatted correctly.
      if !isCorrectAuthorsLine line then
        output := output.push (StyleError.authors, 4)
  return (output, none)

/-- Lint on any occurrences of the string "Adaptation note:" or variants thereof. -/
def adaptationNoteLinter : TextbasedLinter := fun lines ↦ Id.run do
  let mut errors := Array.mkEmpty 0
  let mut lineNumber := 1
  for line in lines do
    -- We make this shorter to catch "Adaptation note", "adaptation note" and a missing colon.
    if line.containsSubstr "daptation note" then
      errors := errors.push (StyleError.adaptationNote, lineNumber)
    lineNumber := lineNumber + 1
  return (errors, none)

/-- Lint on a collection of input strings if one of the is a duplicate import statement. -/
def duplicateImportsLinter : TextbasedLinter := fun lines ↦ Id.run do
  let mut lineNumber := 1
  let mut errors := Array.mkEmpty 0
  let mut importStatements : Std.HashMap String ℕ := {}
  for line in lines do
    if line.startsWith "import " then
      let lineWithoutComment := (line.splitOn "--")[0]!
      let importStatement := lineWithoutComment.trim
      if importStatements.contains importStatement then
        let alreadyImportedLine := importStatements[importStatement]!
        errors := errors.push (
          (StyleError.duplicateImport importStatement alreadyImportedLine),
          lineNumber
        )
      else
        importStatements := importStatements.insert importStatement lineNumber
    lineNumber := lineNumber + 1
  return (errors, none)

/-- Lint a collection of input strings if one of them contains an unnecessarily broad import. -/
def broadImportsLinter : TextbasedLinter := fun lines ↦ Id.run do
  let mut errors := Array.mkEmpty 0
  -- All import statements must be placed "at the beginning" of the file:
  -- we can have any number of blank lines, imports and single or multi-line comments.
  -- Doc comments, however, are not allowed: there is no item they could document.
  let mut inDocComment : Bool := False
  let mut lineNumber := 1
  for line in lines do
    if inDocComment then
      if line.endsWith "-/" then
        inDocComment := False
    else
      -- If `line` is just a single-line comment (starts with "--"), we just continue.
      if line.startsWith "/-" then
        inDocComment := True
      else if let some (rest) := line.dropPrefix? "import " then
          -- If there is any in-line or beginning doc comment on that line, trim that.
          -- Small hack: just split the string on space, "/" and "-":
          -- none of these occur in module names, so this is safe.
          if let some name := ((toString rest).split (" /-".contains ·)).head? then
            if name == "Mathlib.Tactic" then
              errors := errors.push (StyleError.broadImport BroadImports.TacticFolder, lineNumber)
            else if name == "Lake" || name.startsWith "Lake." then
              errors := errors.push (StyleError.broadImport BroadImports.Lake, lineNumber)
      lineNumber := lineNumber + 1
  return (errors, none)


/-- Whether a collection of lines consists *only* of imports, blank lines and single-line comments.
In practice, this means it's an imports-only file and exempt from almost all linting. -/
def isImportsOnlyFile (lines : Array String) : Bool :=
  -- The Python version also excluded multi-line comments: for all files generated by `mk_all`,
  -- this is in fact not necessary. (It is needed for `Tactic/Linter.lean`, though.)
  lines.all (fun line ↦ line.startsWith "import " || line == "" || line.startsWith "-- ")

end

/-- All text-based linters registered in this file. -/
def allLinters : Array TextbasedLinter := #[
    copyrightHeaderLinter, adaptationNoteLinter, broadImportsLinter, duplicateImportsLinter
  ]


/-- Read a file and apply all text-based linters.
Return a list of all unexpected errors, and, if some errors could be fixed automatically,
the collection of all lines with every automatic fix applied.
`exceptions` are any pre-existing style exceptions for this file. -/
def lintFile (path : FilePath) (exceptions : Array ErrorContext) :
    IO (Array ErrorContext × Option (Array String)) := do
  let mut errors := #[]
  -- Whether any changes were made by auto-fixes.
  let mut changes_made := false
  -- Check for windows line endings first: as `FS.lines` treats Unix and Windows lines the same,
  -- we need to analyse the actual file contents.
  let contents ← IO.FS.readFile path
  let replaced := contents.crlfToLf
  if replaced != contents then
    changes_made := true
    errors := errors.push (ErrorContext.mk StyleError.windowsLineEnding 1 path)
  let lines := (replaced.splitOn "\n").toArray

  -- We don't need to run any further checks on imports-only files.
  if isImportsOnlyFile lines then
    return (errors, if changes_made then some lines else none)

  -- All further style errors raised in this file.
  let mut allOutput := #[]
  -- A working copy of the lines in this file, modified by applying the auto-fixes.
  let mut changed := lines

  for lint in allLinters do
    let (err, changes) := lint changed
    allOutput := allOutput.append (Array.map (fun (e, n) ↦ #[(ErrorContext.mk e n path)]) err)
    if let some c := changes then
      changed := c
      changes_made := true
  -- This list is not sorted: for github, this is fine.
  errors := errors.append
    (allOutput.flatten.filter (fun e ↦ (e.find?_comparable exceptions).isNone))
  return (errors, if changes_made then some changed else none)


/-- Lint a collection of modules for style violations.
Print formatted errors for all unexpected style violations to standard output;
correct automatically fixable style errors if configured so.
Return the number of files which had new style errors.
`moduleNames` are all the modules to lint,
`mode` specifies what kind of output this script should produce,
`fix` configures whether fixable errors should be corrected in-place. -/
def lintModules (moduleNames : Array String) (style : ErrorFormat) (fix : Bool) : IO UInt32 := do
  -- Read the `nolints` file, with manual exceptions for the linter.
  let nolints ← IO.FS.lines ("scripts" / "nolints-style.txt")
  let styleExceptions := parseStyleExceptions nolints

  let mut numberErrorFiles : UInt32 := 0
  let mut allUnexpectedErrors := #[]
  for module in moduleNames do
    -- Convert the module name to a file name, then lint that file.
    let path := (mkFilePath (module.split (· == '.'))).addExtension "lean"

    let (errors, changed) := ← lintFile path styleExceptions
    if let some c := changed then
      if fix then
        let _ := ← IO.FS.writeFile path ("\n".intercalate c.toList)
    if errors.size > 0 then
      allUnexpectedErrors := allUnexpectedErrors.append errors
      numberErrorFiles := numberErrorFiles + 1

  -- Run the remaining python linters. It is easier to just run on all files.
  -- If this poses an issue, I can either filter the output
  -- or wait until lint-style.py is fully rewritten in Lean.
  let args := if fix then #["--fix"] else #[]
  let output ← IO.Process.output { cmd := "./scripts/print-style-errors.sh", args := args }
  if output.exitCode != 0 then
    numberErrorFiles := numberErrorFiles + 1
    IO.eprintln s!"error: `print-style-error.sh` exited with code {output.exitCode}"
    IO.eprint output.stderr
  else if output.stdout != "" then
    numberErrorFiles := numberErrorFiles + 1
    IO.eprint output.stdout
  formatErrors allUnexpectedErrors style
  if allUnexpectedErrors.size > 0 then
    IO.eprintln s!"error: found {allUnexpectedErrors.size} new style error(s)"
  return numberErrorFiles

end Mathlib.Linter.TextBased
