/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Batteries.Data.String.Matcher
import Mathlib.Data.Nat.Notation
import Lake.Util.Casing

-- Don't warn about the lake import: the above file has almost no imports, and this PR has been
-- benchmarked.
set_option linter.style.header false

/-!
## Text-based linters

This file defines various mathlib linters which are based on reading the source code only.
In practice, all such linters check for code style issues.

Currently, this file contains linters checking
- if the string "adaptation note" is used instead of the command #adaptation_note,
- for lines with windows line endings,
- for lines containing trailing whitespace.

For historic reasons, some further such check checks are written in a Python script `lint-style.py`:
these are gradually being rewritten in Lean.

This linter has a file for style exceptions (to avoid false positives in the implementation),
or for downstream projects to allow a gradual adoption of this linter.

An executable running all these linters is defined in `scripts/lint-style.lean`.
-/

open Lean.Linter System

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
  /-- The bare string "Adaptation note" (or variants thereof):
  instead, the #adaptation_note command should be used. -/
  | adaptationNote
  /-- A line ends with windows line endings (\r\n) instead of unix ones (\n). -/
  | windowsLineEnding
  /-- A line contains trailing whitespace. -/
  | trailingWhitespace
  /-- A line contains a space before a semicolon -/
  | semicolon
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
  | StyleError.adaptationNote =>
    "Found the string \"Adaptation note:\", please use the #adaptation_note command instead"
  | windowsLineEnding => "This line ends with a windows line ending (\r\n): please use Unix line\
    endings (\n) instead"
  | trailingWhitespace => "This line ends with some whitespace: please remove this"
  | semicolon => "This line contains a space before a semicolon"

/-- The error code for a given style error. Keep this in sync with `parse?_errorContext` below! -/
-- FUTURE: we're matching the old codes in `lint-style.py` for compatibility;
-- in principle, we could also print something more readable.
def StyleError.errorCode (err : StyleError) : String := match err with
  | StyleError.adaptationNote => "ERR_ADN"
  | StyleError.windowsLineEnding => "ERR_WIN"
  | StyleError.trailingWhitespace => "ERR_TWS"
  | StyleError.semicolon => "ERR_SEM"

/-- Context for a style error: the actual error, the line number in the file we're reading
and the path to the file. -/
structure ErrorContext where
  /-- The underlying `StyleError` -/
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
  /-- The existing exception also covers the new error:
  we keep the existing exception. -/
  | Comparable
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
  -- Generally, comparable errors must have equal `StyleError`s.
  else
    if existing.error == new.error then ComparisonResult.Comparable else ComparisonResult.Different

/-- Find the first style exception in `exceptions` (if any) which covers a style exception `e`. -/
def ErrorContext.find?_comparable (e : ErrorContext) (exceptions : Array ErrorContext) :
    Option ErrorContext :=
  (exceptions).find? (fun new ↦ compare e new == ComparisonResult.Comparable)

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
    | filename :: ":" :: "line" :: lineNumber :: ":" :: errorCode :: ":" :: _errorMessage =>
      -- Turn the filename into a path. In general, this is ambiguous if we don't know if we're
      -- dealing with e.g. Windows or POSIX paths. In our setting, this is fine, since no path
      -- component contains any path separator.
      let path := mkFilePath (filename.split (FilePath.pathSeparators.contains ·))
      -- Parse the error kind from the error code, ugh.
      -- NB: keep this in sync with `StyleError.errorCode` above!
      let err : Option StyleError := match errorCode with
        -- Use default values for parameters which are ignored for comparing style exceptions.
        -- NB: keep this in sync with `compare` above!
        | "ERR_ADN" => some (StyleError.adaptationNote)
        | "ERR_SEM" => some (StyleError.semicolon)
        | "ERR_TWS" => some (StyleError.trailingWhitespace)
        | "ERR_WIN" => some (StyleError.windowsLineEnding)
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
abbrev TextbasedLinter := LinterOptions → Array String →
  Array (StyleError × ℕ) × (Option (Array String))

/-! Definitions of the actual text-based linters. -/
section

/-- Lint on any occurrences of the string "Adaptation note:" or variants thereof. -/
register_option linter.adaptationNote : Bool := { defValue := true }

@[inherit_doc linter.adaptationNote]
def adaptationNoteLinter : TextbasedLinter := fun opts lines ↦ Id.run do
  unless getLinterValue linter.adaptationNote opts do return (#[], none)

  let mut errors := Array.mkEmpty 0
  for h : idx in [:lines.size] do
    -- We make this shorter to catch "Adaptation note", "adaptation note" and a missing colon.
    if lines[idx].containsSubstr "daptation note" then
      errors := errors.push (StyleError.adaptationNote, idx + 1)
  return (errors, none)

/-- Lint a collection of input strings if one of them contains trailing whitespace. -/
register_option linter.trailingWhitespace : Bool := { defValue := true }

@[inherit_doc linter.trailingWhitespace]
def trailingWhitespaceLinter : TextbasedLinter := fun opts lines ↦ Id.run do
  unless getLinterValue linter.trailingWhitespace opts do return (#[], none)

  let mut errors := Array.mkEmpty 0
  let mut fixedLines : Vector String lines.size := lines.toVector
  for h : idx in [:lines.size] do
    let line := lines[idx]
    if line.back == ' ' then
      errors := errors.push (StyleError.trailingWhitespace, idx + 1)
      fixedLines := fixedLines.set idx line.trimRight
  return (errors, if errors.size > 0 then some fixedLines.toArray else none)

/-- Lint a collection of input strings for a semicolon preceded by a space. -/
register_option linter.whitespaceBeforeSemicolon : Bool := { defValue := true }

@[inherit_doc linter.whitespaceBeforeSemicolon]
def semicolonLinter : TextbasedLinter := fun opts lines ↦ Id.run do
  unless getLinterValue linter.whitespaceBeforeSemicolon opts do return (#[], none)

  let mut errors := Array.mkEmpty 0
  let mut fixedLines := lines
  for h : idx in [:lines.size] do
    let line := lines[idx]
    let pos := line.find (· == ';')
    -- Future: also lint for a semicolon *not* followed by a space or ⟩.
    if pos != line.endPos && line.get (line.prev pos) == ' ' then
      errors := errors.push (StyleError.semicolon, idx + 1)
      -- We spell the bad string pattern this way to avoid the linter firing on itself.
      fixedLines := fixedLines.set! idx (line.replace (⟨[' ', ';']⟩ : String) ";")
   return (errors, if errors.size > 0 then some fixedLines else none)


/-- Whether a collection of lines consists *only* of imports, blank lines and single-line comments.
In practice, this means it's an imports-only file and exempt from almost all linting. -/
def isImportsOnlyFile (lines : Array String) : Bool :=
  -- The Python version also excluded multi-line comments: for all files generated by `mk_all`,
  -- this is in fact not necessary. (It is needed for `Tactic/Linter.lean`, though.)
  lines.all (fun line ↦ line.startsWith "import " || line == "" || line.startsWith "-- ")

end

/-- All text-based linters registered in this file. -/
def allLinters : Array TextbasedLinter := #[
    adaptationNoteLinter, semicolonLinter, trailingWhitespaceLinter
  ]


/-- Read a file and apply all text-based linters.
Return a list of all unexpected errors, and, if some errors could be fixed automatically,
the collection of all lines with every automatic fix applied.
`exceptions` are any pre-existing style exceptions for this file. -/
def lintFile (opts : LinterOptions) (path : FilePath) (exceptions : Array ErrorContext) :
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
    let (err, changes) := lint opts changed
    allOutput := allOutput.append (Array.map (fun (e, n) ↦ #[(ErrorContext.mk e n path)]) err)
    -- TODO: auto-fixes do not take style exceptions into account
    if let some c := changes then
      changed := c
      changes_made := true
  -- This list is not sorted: for github, this is fine.
  errors := errors.append
    (allOutput.flatten.filter (fun e ↦ (e.find?_comparable exceptions).isNone))
  return (errors, if changes_made then some changed else none)

/-- Enables the old Python-based style linters. -/
register_option linter.pythonStyle : Bool := { defValue := true }

/-- Lint a collection of modules for style violations.
Print formatted errors for all unexpected style violations to standard output;
correct automatically fixable style errors if configured so.
Return the number of files which had new style errors.
`opts` contains the options defined in the Lakefile, determining which linters to enable.
`nolints` is a list of style exceptions to take into account.
`moduleNames` are the names of all the modules to lint,
`mode` specifies what kind of output this script should produce,
`fix` configures whether fixable errors should be corrected in-place. -/
def lintModules (opts : LinterOptions) (nolints : Array String) (moduleNames : Array Lean.Name)
    (style : ErrorFormat) (fix : Bool) : IO UInt32 := do
  let styleExceptions := parseStyleExceptions nolints
  let mut numberErrorFiles : UInt32 := 0
  let mut allUnexpectedErrors := #[]
  for module in moduleNames do
    -- Convert the module name to a file name, then lint that file.
    let path := mkFilePath (module.components.map toString)|>.addExtension "lean"

    let (errors, changed) := ← lintFile opts path styleExceptions
    if let some c := changed then
      if fix then
        let _ := ← IO.FS.writeFile path ("\n".intercalate c.toList)
    if errors.size > 0 then
      allUnexpectedErrors := allUnexpectedErrors.append errors
      numberErrorFiles := numberErrorFiles + 1

  -- Passing Lean options to Python files seems like a lot of work for something we want to
  -- run entirely inside of Lean in the end anyway.
  -- So for now, we enable/disable all of them with a single switch.
  if getLinterValue linter.pythonStyle opts then
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

/-- Verify that all modules are named in `UpperCamelCase` -/
register_option linter.modulesUpperCamelCase : Bool := { defValue := true }

/-- Verifies that all modules in `modules` are named in `UpperCamelCase`
(except for explicitly discussed exceptions, which are hard-coded here).
Return the number of modules violating this. -/
def modulesNotUpperCamelCase (opts : LinterOptions) (modules : Array Lean.Name) : IO Nat := do
  unless getLinterValue linter.modulesUpperCamelCase opts do return 0

  -- Exceptions to this list should be discussed on zulip!
  let exceptions := [
    `Mathlib.Analysis.CStarAlgebra.lpSpace,
    `Mathlib.Analysis.InnerProductSpace.l2Space,
    `Mathlib.Analysis.Normed.Lp.lpSpace
  ]
  -- We allow only names in UpperCamelCase, possibly with a trailing underscore.
  let badNames := modules.filter fun name ↦
    let upperCamelName := Lake.toUpperCamelCase name
    !exceptions.contains name &&
      upperCamelName != name && s!"{upperCamelName}_" != name.toString
  for bad in badNames do
    let upperCamelName := Lake.toUpperCamelCase bad
    let good := if bad.toString.endsWith "_" then s!"{upperCamelName}_" else upperCamelName.toString
    IO.eprintln
      s!"error: module name '{bad}' is not in 'UpperCamelCase': it should be '{good}' instead"
  return badNames.size

end Mathlib.Linter.TextBased
