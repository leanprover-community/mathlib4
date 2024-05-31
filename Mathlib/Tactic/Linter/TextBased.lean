/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Batteries.Data.String.Basic
import Mathlib.Init.Data.Nat.Notation

/-!
## Text-based linters

This file defines various mathlib linters which are based on reading the source code only.
In practice, only style linters will have this form.
All of these have been rewritten from the `lint-style.py` script.

For now, this only contains the linter for the copyright and author headers:
further linters will be ported in subsequent PRs.

-/

open Lean Elab

/-- Possible errors that text-based linters can report. -/
-- We collect these in one inductive type to centralise error reporting.
inductive StyleError where
  /-- Missing or malformed copyright header.
  Unlike in the python script, we may provide some context on the actual error. -/
  | copyright (context : Option String)
  /-- Malformed authors line in the copyright header -/
  | authors
  deriving BEq

/-- Create the underlying error message for a given `StyleError`. -/
def StyleError.errorMessage (err : StyleError) : String := match err with
  | StyleError.copyright (some context) => s!"Malformed or missing copyright header: {context}"
  | StyleError.copyright none => s!"Malformed or missing copyright header"
  | StyleError.authors =>
    "Authors line should look like: 'Authors: Jean Dupont, Иван Иванович Иванов'"

/-- The error code for a given style error. Keep this in sync with `parse?_style_error` below! -/
-- FUTURE: we're matching the old codes in `lint-style.py` for compatibility;
-- in principle, we could also print something more readable.
def StyleError.errorCode (err : StyleError) : String := match err with
  | StyleError.copyright _ => "ERR_COP"
  | StyleError.authors => "ERR_AUT"

/-- Context for a style error: the actual error, the line number in the file we're reading
and the path to the file. -/
structure ErrorContext where
  /-- The underlying `StyleError`-/
  error : StyleError
  /-- The line number of the error -/
  lineNumber : ℕ
  /-- The path to the file which was linted -/
  path : System.FilePath

/-- The parts of a `StyleError` which are considered when matching against the existing
  style exceptions: for example, we ignore the particular line length of a "line too long" error. -/
def StyleError.normalise (err : StyleError) : StyleError := match err with
  -- We do *not* care about the *kind* of wrong copyright.
  -- NB: keep this in sync with `parse?_style_error` below.
  | StyleError.copyright _ => StyleError.copyright ""
  | _ => err

/-- Careful: we do not want to compare `ErrorContexts` exactly; we ignore some details. -/
instance : BEq ErrorContext where
  beq ctx ctx' :=
      -- XXX: `lint-style.py` was calling `resolve()` on the path before before comparing them
      -- should we also do so?
      ctx.path == ctx'.path
      -- We completely ignore line numbers of errors. Not sure if this is best.
      -- We normalise errors before comparing them.
      && (ctx.error).normalise == (ctx'.error).normalise

/-- Output the formatted error message, containing its context. -/
def outputMessage (errctx : ErrorContext) : String :=
  -- We are outputting for github: duplicate file path, line number and error code,
  -- so that they are also visible in the plain text output.
  let path := errctx.path
  let nr := errctx.lineNumber
  let code := errctx.error.errorCode
  s!"::ERR file={path},line={nr},code={code}::{path}:{nr} {code}: {errctx.error.errorMessage}"

/-- Try parsing an `ErrorContext` from a string: return `some` if successful, `none` otherwise. -/
def parse?_errorContext (line : String) : Option ErrorContext := Id.run do
  let parts := line.split (fun c ↦ c == ' ')
  match parts with
    | filename :: ":" :: "line" :: _line_number :: ":" :: error_code :: ":" :: _error_message =>
      -- Turn the filename into a path. XXX: is there a nicer way to do this?
      -- Invariant: `style-exceptions.txt` always contains Unix paths
      -- (because, for example, in practice it is updated by CI, which runs on unix).
      -- Hence, splitting and joining on "/" is actually somewhat safe.
      let path : System.FilePath := System.mkFilePath (filename.split (fun c ↦ c == '/'))
      -- Parse the error kind from the error code, ugh.
      -- NB: keep this in sync with `StyleError.error_code` above!
      let err : Option StyleError := match error_code with
        -- Use default values for parameters which are normalised.
        -- NB: keep this in sync with `normalise` above!
        | "ERR_COP" => some (StyleError.copyright "")
        | "ERR_AUT" => some (StyleError.authors)
        | _ => none
      -- Omit the line number, as we don't use it anyway.
      err.map fun e ↦ (ErrorContext.mk e 0 path)
    -- We ignore any lines which don't match the particular format.
    | _ => none

/-- Parse all style exceptions for a line of input.
Return an array of all exceptions which could be parsed: invalid input is ignored. -/
def parseStyleExceptions (lines : Array String) : Array ErrorContext := Id.run do
  Array.filterMap (fun line ↦ parse?_errorContext line) lines

/-- Print information about all errors encountered to standard output. -/
def formatErrors (errors : Array ErrorContext) : IO Unit := do
  for e in errors do
    IO.println (outputMessage e)

/-- Core logic of a text based linter: given a collection of lines,
return an array of all style errors with line numbers. -/
abbrev TextbasedLinter := Array String → Array (StyleError × ℕ)

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
  | (some "/-", _) => return Array.mkArray1 (StyleError.copyright none, 4)
  | _ => return Array.mkArray1 (StyleError.copyright none, 0)

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
  return output


/-- Whether a collection of lines consists *only* of imports:
in practice, this means it's an imports-only file and exempt from almost all linting. -/
def isImportsOnlyFile (lines : Array String) : Bool :=
  -- The Python version also excluded comments: since the import-only files are
  -- automatically generated and don't contains comments, this is in fact not necessary.
  -- XXX: also implement parsing of multi-line comments.
  lines.all (fun line ↦ line.startsWith "import " || line == "" || line.startsWith "-- ")

end

/-- All text-based linters registered in this file. -/
def allLinters : Array TextbasedLinter := Array.mk
  [copyrightHeaderLinter]

/-- Read a file, apply all text-based linters and print the formatted errors.

`exceptions` are any previous style exceptions.

Return `true` if there were new errors (and `false` otherwise). -/
def lintFile (path : System.FilePath) (exceptions : Array ErrorContext) : IO Bool := do
  let lines ← IO.FS.lines path
  -- We don't need to run any checks on imports-only files.
  -- NB. The Python script used to still run a few linters; this is in fact not necessary.
  if isImportsOnlyFile lines then
    return false
  let all_output := (Array.map (fun lint ↦
    (Array.map (fun (e, n) ↦ ErrorContext.mk e n path)) (lint lines))) allLinters
  -- This this list is not sorted: for github, this is fine.
  let errors := (Array.flatten all_output).filter (fun e ↦ !exceptions.contains e)
  formatErrors errors
  return errors.size > 0

/-- Lint all files referenced in a given import-only file.
Return the number of files which had new style errors. -/
def lintAllFiles (path : System.FilePath) : IO UInt32 := do
  -- Read all module names in Mathlib from the file at `path`.
  let allModules ← IO.FS.lines path
  -- Read the style exceptions file.
  -- We also have a `nolints` file with manual exceptions for the linter.
  let exceptions_file ← IO.FS.lines (System.mkFilePath ["scripts/style-exceptions.txt"])
  let mut style_exceptions := parseStyleExceptions exceptions_file
  let nolints ← IO.FS.lines (System.mkFilePath ["scripts/nolints-style.txt"])
  style_exceptions := style_exceptions.append (parseStyleExceptions nolints)
  let mut number_error_files := 0
  for module in allModules do
    let module := module.stripPrefix "import "
    -- Convert the module name to a file name, then lint that file.
    let path := (System.mkFilePath (module.split fun c ↦ (c == '.'))).addExtension "lean"
    let e ← lintFile path style_exceptions
    if e then
      number_error_files := number_error_files + 1
  return number_error_files


/-- The entry point to the `lake exe lint_style` command. -/
def main : IO UInt32 := do
  let mut number_error_files := 0
  for s in ["Archive.lean", "Counterexamples.lean", "Mathlib.lean"] do
    let n ← lintAllFiles (System.mkFilePath [s])
    number_error_files := number_error_files + n
  return number_error_files
