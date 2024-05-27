/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Batteries.Data.String.Basic
import Cli.Basic
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
  line_number : ℕ
  /-- The path to the file which was linted -/
  path : System.FilePath

/-- Output the formatted error message, containing its context. -/
def outputMessage (errctx : ErrorContext) : String :=
  -- We are outputting for github: duplicate file path, line number and error code,
  -- so that they are also visible in the plain text output.
  let path := errctx.path
  let nr := errctx.line_number
  let code := errctx.error.errorCode
  s!"::ERR file={path},line={nr},code={code}::{path}:{nr} {code}: {errctx.error.errorMessage}"

/-- Print information about all errors encountered to standard output. -/
def formatErrors (errors : Array ErrorContext) : IO Unit := do
  for e in errors do
    IO.println (outputMessage e)

/-- Core logic of a text based linter: given a collection of lines,
return an array of all style errors with line numbers. -/
abbrev LinterCore := Array String → Array (StyleError × ℕ)

/-! Definitions of the actual text-based linters. -/
section

/-- Return if `line` looks like a correct authors line in a copyright header. -/
def is_correct_authors_line (line : String) : Bool :=
  -- We cannot reasonably validate the author names, so we look only for a few common mistakes:
  -- the file starting wrong, double spaces, using ' and ' between names,
  -- and ending the line with a period.
  line.startsWith "Authors: " && (!line.containsSubstr "  ")
    && (!line.containsSubstr " and ") && (!line.endsWith ".")

/-- Lint a collection of input lines if they are missing an appropriate copyright header.

A copyright header should start at the very beginning of the file and contain precisely five lines,
including the copy year and holder, the license and main author(s) of the file (in this order).
-/
def copyright_header : LinterCore := fun lines ↦ Id.run do
  -- Unlike the Python script, we just emit one warning.
  let start := lines.extract 0 4
  -- The header should start and end with blank comments.
  let _ := match (start.get? 0, start.get? 4) with
  | (some "/-", some "-/") => none
  | (some "/-", _) => return Array.mk [(StyleError.copyright none, 4)]
  | _ => return Array.mk [(StyleError.copyright none, 0)]

  -- If this is given, we go over the individual lines one by one,
  -- and provide some context on what is mis-formatted (if anything).
  let mut output := Array.mkEmpty 0
  -- By hypotheses above, start has at least five lines, so the `none` cases below are never hit.
  -- The first real line should state the copyright.
  if let some copy := start.get? 1 then
    if !(copy.startsWith "Copyright (c) 20" && copy.endsWith ". All rights reserved.") then
      output := output.push (StyleError.copyright "Copyright line is malformed", 2)
  -- The second line should be standard.
  let expected_second_line := "Released under Apache 2.0 license as described in the file LICENSE."
  if start.get? 2 != some expected_second_line then
    output := output.push (StyleError.copyright
      s!"Second line should be \"{expected_second_line}\"", 3)
  -- The third line should contain authors.
  if let some line := start.get? 3 then
    if !line.containsSubstr "Author" then
      output := output.push (StyleError.copyright
        "The third line should describe the file's main authors", 4)
    else
      -- If it does, we check the authors line is formatted correctly.
      if !is_correct_authors_line line then
        output := output.push (StyleError.authors, 4)
  return output


/-- Whether a collection of lines consists *only* of imports:
in practice, this means it's an imports-only file and exempt from almost all linting. -/
def is_imports_only_file (lines : Array String) : Bool :=
  -- The Python version also excluded comments: since the import-only files are
  -- automatically generated and don't contains comments, this is in fact not necessary.
  -- XXX: also implement parsing of multi-line comments.
  lines.all (fun line ↦ line.startsWith "import " || line == "" || line.startsWith "-- ")

end

/-- All text-based linters registered in this file. -/
def all_linters : Array LinterCore := Array.mk
  [copyright_header]

/-- Read a file, apply all text-based linters and return the formatted errors.

Return `true` if there were new errors (and `false` otherwise). -/
def lint_file (path : System.FilePath) : IO Bool := do
  let lines ← IO.FS.lines path
  -- We don't need to run any checks on imports-only files.
  -- NB. The Python script used to still run a few linters; this is in fact not necessary.
  if is_imports_only_file lines then
    return false
  let all_output := (Array.map (fun lint ↦
    (Array.map (fun (e, n) ↦ ErrorContext.mk e n path)) (lint lines))) all_linters
  -- XXX: this list is currently not sorted: for github, that's probably fine
  let errors := Array.flatten all_output
  formatErrors errors
  return errors.size > 0

/-- Lint all files referenced in a given import-only file.
Return the number of files which had new style errors. -/
def lint_all_files (path : System.FilePath) : IO UInt32 := do
  -- Read all module names in Mathlib from the file at `path`.
  let allModules ← IO.FS.lines path
  let mut number_error_files := 0
  for module in allModules do
    let module := module.stripPrefix "import "
    -- Exclude `Archive.Sensitivity` and `Mathlib.Tactic.Linter` for now.
    -- FUTURE: replace this by proper parsing of style exceptions.
    if #["Archive.Sensitivity", "Mathlib.Tactic.Linter"].contains module then
      continue
    -- Convert the module name to a file name, then lint that file.
    let path := (System.mkFilePath (module.split fun c ↦ (c == '.'))).addExtension "lean"
    let e ← lint_file path
    if e then
      number_error_files := number_error_files + 1
  return number_error_files


/-- The entry point to the `lake exe lint_style` command. -/
def main (_args : List String) : IO UInt32 := do
  let mut number_error_files := 0
  for s in ["Archive.lean", "Counterexamples.lean", "Mathlib.lean"] do
    let n ← lint_all_files (System.mkFilePath [s])
    number_error_files := number_error_files + n
  return number_error_files
