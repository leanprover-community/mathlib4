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

For now, this only contains the linter for too large files:
further linters will be ported in subsequent PRs.

-/

open Lean Elab

/-- Possible errors that text-based linters can report. -/
-- We collect these in one inductive type to centralise error reporting.
inductive StyleError where
  /-- The current file was too large: this error contains the current number of lines
  as well as a size limit (slightly larger). On future runs, this linter will allow this file
  to grow up to this limit. -/
  | fileTooLong (number_lines : ℕ) (new_size_limit : ℕ) : StyleError
  deriving BEq

/-- Create the underlying error message for a given `StyleError`. -/
def StyleError.errorMessage (err : StyleError) : String := match err with
  | StyleError.fileTooLong current_size size_limit =>
      s!"{size_limit} file contains {current_size} lines, try to split it up"

/-- The error code for a given style error. Keep this in sync with `parse?_errorContext` below! -/
-- FUTURE: we're matching the old codes in `lint-style.py` for compatibility;
-- in principle, we could also print something more readable.
def StyleError.errorCode (err : StyleError) : String := match err with
  | StyleError.fileTooLong _ _ => "ERR_NUM_LIN"

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
  -- NB: keep this in sync with `parse?_errorContext` below.
  | StyleError.fileTooLong _ _ => StyleError.fileTooLong 0 0

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
  -- Lines starting with "-- " are treated as a comment and ignored.
  if line.startsWith "-- " then
    return none
  let parts := line.split (fun c ↦ c == ' ')
  match parts with
    | filename :: ":" :: "line" :: _line_number :: ":" :: error_code :: ":" :: error_message =>
      -- Turn the filename into a path. XXX: is there a nicer way to do this?
      -- Invariant: `style-exceptions.txt` always contains Unix paths
      -- (because, for example, in practice it is updated by CI, which runs on unix).
      -- Hence, splitting and joining on "/" is actually somewhat safe.
      let path : System.FilePath := System.mkFilePath (filename.split (fun c ↦ c == '/'))
      -- Parse the error kind from the error code, ugh.
      -- NB: keep this in sync with `StyleError.errorCode` above!
      let err : Option StyleError := match error_code with
        -- Use default values for parameters which are normalised.
        -- NB: keep this in sync with `normalise` above!
        | "ERR_NUM_LIN" =>
          -- Parse the error message in the script. `none` indicates invalid input.
          match (error_message.get? 0, error_message.get? 3) with
          | (some limit, some current) =>
            match (String.toNat? limit, String.toNat? current) with
            | (some size_limit, some current_size) =>
              some (StyleError.fileTooLong current_size size_limit)
            | _ => none
          | _ => none
        | _ => none
      -- Omit the line number, as we don't use it anyway.
      return (err.map fun e ↦ (ErrorContext.mk e 0 path))
    -- XXX: print an error on any lines which don't match the particular format.
    | _ => -- IO.println s!"Invalid input file: line {line} doesn't match any particular format"
      none

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

/-- Whether a collection of lines consists *only* of imports, blank lines and single-line comments.
In practice, this means it's an imports-only file and exempt from almost all linting. -/
def isImportsOnlyFile (lines : Array String) : Bool :=
  -- The Python version also excluded multi-line comments: for all files generated by `mk_all`,
  -- this is in fact not necessary.
  lines.all (fun line ↦ line.startsWith "import " || line == "" || line.startsWith "-- ")

/-- Error if a collection of lines is too large. "Too large" means more than 1500 lines
**and** longer than an optional previous limit.
If the file is too large, return a matching `StyleError`, which includes a new size limit
(which is somewhat larger than the current size). -/
def checkFileLength (lines : Array String) (existing_limit : Option ℕ) : Option StyleError :=
  Id.run do
  if lines.size > 1500 then
    let is_larger : Bool := match existing_limit with
    | some mark => lines.size > mark
    | none => true
    if is_larger then
      -- We add about 200 lines of slack to the current file size:
      -- small PRs will be unperturbed, but sufficiently large PRs will get nudged towards
      -- splitting up this file.
      return some (StyleError.fileTooLong lines.size ((Nat.div lines.size 100) * 100 + 200))
  none

end

/-- All text-based linters registered in this file. -/
def allLinters : Array TextbasedLinter := Array.mk
  []

/-- Read a file, apply all text-based linters and print formatted errors.
Return `true` if there were new errors (and `false` otherwise).
`sizeLimit` is any pre-existing limit on this file's size. -/
def lintFile (path : System.FilePath) (sizeLimit : Option ℕ) : IO Bool := do
  let lines ← IO.FS.lines path
  -- We don't need to run any checks on imports-only files.
  -- NB. The Python script used to still run a few linters; this is in fact not necessary.
  if isImportsOnlyFile lines then
    return false
  if let some (StyleError.fileTooLong n limit) := checkFileLength lines sizeLimit then
    let arr := Array.mkArray1 (ErrorContext.mk (StyleError.fileTooLong n limit) 1 path)
    formatErrors arr
    return true
  return false

/-- Lint all files referenced in a given import-only file.
Return the number of files which had new style errors. -/
def lintAllFiles (path : System.FilePath) : IO UInt32 := do
  -- Read all module names from the file at `path`.
  let allModules ← IO.FS.lines path
  -- Read the style exceptions file.
  let exceptions_file ← IO.FS.lines (System.mkFilePath ["scripts/style-exceptions.txt"])
  let mut style_exceptions := parseStyleExceptions exceptions_file
  let mut number_error_files := 0
  for module in allModules do
    let module := module.stripPrefix "import "
    -- Convert the module name to a file name, then lint that file.
    let path := (System.mkFilePath (module.split fun c ↦ (c == '.'))).addExtension "lean"
    -- Find the size limit for this given file.
    -- If several size limits are given (unlikely in practice), we use the first one.
    let size_limits := (style_exceptions.filter (fun e ↦ e.path == path)).filterMap (fun errctx ↦
      match errctx.error with
      | StyleError.fileTooLong _ limit => some limit)
    if ← lintFile path (size_limits.get? 0) then
      number_error_files := number_error_files + 1
  return number_error_files

/-- The entry point to the `lake exe lint_style` command. -/
def main : IO UInt32 := do
  let mut number_error_files := 0
  for s in ["Archive.lean", "Counterexamples.lean", "Mathlib.lean"] do
    let n ← lintAllFiles (System.mkFilePath [s])
    number_error_files := number_error_files + n
  return number_error_files
