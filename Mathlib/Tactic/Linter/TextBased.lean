/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Lean.Elab.Command
import Batteries.Data.String.Basic
import Mathlib.Init.Data.Nat.Notation
import Lake.Build.Trace

/-!
## Text-based linters

This file defines various mathlib linters which are based on reading the source code only.
In practice, only style linters will have this form.
All of these have been rewritten from the `lint-style.py` script.

FUTURE: rewrite the remaining lints

-/

open Lean Elab Command

/-- Possible errors that text-based linters can report. -/
-- We collect these in one inductive type to centralise error reporting.
inductive StyleError where
  /-- Line longer than 100 characters -/
  | lineLength (actual : Int) : StyleError
  /-- Broad import, which is disallowed in Mathlib -/
  -- Future: if this includes more than one import, report the module name
  | broadImport : StyleError
  /-- Missing or malformed copyright header.
  Unlike in the python script, we may provide some context on the actual error. -/
  | copyright (context : Option String)
  /-- Malformed authors line in the copyright header -/
  | authors
  /-- A "leading by": a line starting with "by" (this should go on the previous line) -/
  | leading_by : StyleError
    /-- An "isolated where": a line containing just the string "where" -/
  | isolated_where : StyleError
  /-- Line is an isolated focusing dot or uses `.` instead of `·` -/
  | dot : StyleError
  /-- A semicolon preceded by a space -/
  | semicolon : StyleError
  /-- A line starting with a colon: `:` and `:=` should be put before line breaks, not after. -/
  | colon : StyleError
  /-- Trailing whitespace on this line -/
  | trailingWhitespace : StyleError
  /-- A line ends with Windows line endings (\\r\\n) -/
  | windowsLineEndings : StyleError
  /-- The current file was too large: this error contains the current number of lines
  as well as a size limit (slightly larger). On future runs, this linter will allow this file
  to grow up to this limit. -/
  | fileTooLong (number_lines : ℕ) (new_size_limit : ℕ) : StyleError
  deriving BEq

/-- Create the underlying error message for a given `StyleError`. -/
def errorMessage (err : StyleError) : String := match err with
  | StyleError.lineLength n => s!"Line has {n} characters, which is more than 100"
  | StyleError.broadImport => "Files in mathlib must not import the whole tactic folder"
  | StyleError.copyright (some context) => s!"Malformed or missing copyright header: {context}"
  | StyleError.copyright none => s!"Malformed or missing copyright header"
  | StyleError.authors =>
    "Authors line should look like: 'Authors: Jean Dupont, Иван Иванович Иванов'"
  | StyleError.leading_by => "Line starts with 'by'"
  | StyleError.isolated_where => "Line containing just the string 'where'"
  | StyleError.dot => "Line is an isolated focusing dot or uses . instead of ·"
  | StyleError.semicolon => "Line contains a space before a semicolon"
  | StyleError.colon => "Put : and := before line breaks, not after"
  | StyleError.trailingWhitespace => "Trailing whitespace detected"
  | StyleError.windowsLineEndings => "Windows line endings (\\r\\n) detected"
  | StyleError.fileTooLong current_size size_limit =>
      s!"{size_limit} file contains {current_size} lines, try to split it up"

/-- The error code for a given style error. Kept in sync with `lint-style.py` for now. -/
def errorCode (err : StyleError) : String := match err with
  | StyleError.lineLength _ => "ERR_LIN"
  | StyleError.broadImport => "ERR_TAC"
  | StyleError.copyright _ => "ERR_COP"
  | StyleError.authors => "ERR_AUT"
  | StyleError.leading_by => "ERR_IBY"
  | StyleError.isolated_where => "ERR_IWH"
  | StyleError.semicolon => "ERR_SEM"
  | StyleError.colon => "ERR_CLN"
  | StyleError.dot => "ERR_DOT"
  | StyleError.trailingWhitespace => "ERR_TWS"
  | StyleError.windowsLineEndings => "ERR_WIN"
  | StyleError.fileTooLong _ _ => "ERR_NUM_LIN"

/-- Context for a style error: the actual error, the line number in the file we're reading
and the path to the file. -/
structure ErrorContext where
  /-- The underlying `StyleError`-/
  error : StyleError
  /-- The line number of the error -/
  line_number : ℕ
  /-- The path to the file which was linted -/
  path : System.FilePath
  deriving BEq

/-- Output the formatted error message, containing its context. -/
def output_message (errctx : ErrorContext) : String :=
  -- XXX: we're just porting the second branch, running on CI
  -- generating an exceptions file (the first branch) is not implemented yet

  -- We are outputting for github: duplicate path, line_nr and code,
  -- so that they are also visible in the plaintext output.
  let path := errctx.path
  let nr := errctx.line_number
  let code := errorCode errctx.error
  s!"::ERR file={path},line={nr},code={code}::{path}:{nr} {code}: {errorMessage errctx.error}"

/-- Print information about all errors encountered to standard output. -/
def format_errors (errors : Array ErrorContext) (exceptions : Array ErrorContext): IO Unit := do
  -- XXX: `lint-style.py` was `resolve()`ing paths in the `exceptions` list;
  -- do we also need to?
  -- TODO: do I need to compare exceptions in a fancy way? for instance, are line number ignored?
  for e in errors do
    if !exceptions.contains e then IO.println (output_message e)

/-- Core logic of a text based linter: given a collection of lines,
return an array of all style errors with line numbers. -/
abbrev LinterCore := Array String → Array (StyleError × ℕ)

/-! Definitions of the actual text-based linters. -/
section

/-- Iterates over a collection of strings, finding all lines which are longer than 101 chars.
We allow #aligns or URLs to be longer, though.
-/
def check_line_length : LinterCore := fun lines ↦
  let is_too_long := fun s : String ↦
    if !(s.containsSubstr "http" || s.containsSubstr "#align") && s.length > 101 then
      some (StyleError.lineLength s.length)
    else none
  let errors := Array.filterMap is_too_long lines
  -- TODO: enumerate over all lines, and report actual line numbers!
  Array.map (fun e ↦ (e, 42)) errors

/-- Lint a collection of input strings if one of them contains an unnecessary broad import.
Return `none` if no import was found, and `some n` if such an import was on line `n` (1-based). -/
def contains_broad_imports : LinterCore := fun lines ↦ Id.run do
  let mut output := Array.mkEmpty 0
  -- All import statements must be placed "at the beginning" of the file:
  -- we can have any number of blank lines, imports and single or multi-line comments.
  -- Doc comments, however, are not allowed: there is no item they could document.
  let mut in_doc_comment : Bool := False
  let mut line_number := 0
  for line in lines do
    line_number := line_number + 1
    if in_doc_comment then
      if line.endsWith "-/" then
        in_doc_comment := False
    else
      if let some (rest) := line.dropPrefix? "import " then
          -- If there is any in-line or beginning doc comment on that line, trim that.
          -- HACK: just split the string on space, "/" and "-":
          -- none of these occur in module names, so this is safe.
          if let some name := ((toString rest).split fun c ↦ (" /-".contains c)).head? then
            if name == "Mathlib.Tactic" then
              output := output.push (StyleError.broadImport, line_number)
      -- If this is just a single-line comment (starts with "--"), just continue.
      if line.startsWith "/-" then
        in_doc_comment := True
  output

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
    if !(copy.startsWith "Copyright (c) " && copy.endsWith ". All rights reserved.") then
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

/-- Check for miscellaneous formatting things: starting with a dot or using the wrong dot,
  isolated by, a semicolon preceded by a space or a line starting with a colon. -/
-- FUTURE: remove most of these, once there is a formatter!
def isolated_by_dot_semicolon : LinterCore := fun lines ↦ Id.run do
    let mut output := Array.mkEmpty 0
    let mut line_number := 0
    for line in lines do
      line_number := line_number + 1
      if line.trimLeft.startsWith "by" && line_number >= 2 then
        -- This is safe since `line_number` is the line we iterated over, just a moment ago.
        let previous_line := lines[line_number - 2]!
        -- We excuse those "by"s following a comma or ", fun ... =>", since generally hanging "by"s
        -- should not be used in the second or later arguments of a tuple/anonymous constructor
        -- See https://github.com/leanprover-community/mathlib4/pull/3825#discussion_r1186702599
        if !previous_line.endsWith "," then
          if !(previous_line.containsSubstr ", fun" &&
              (previous_line.endsWith "=>" || previous_line.endsWith "↦")) then
            output := output.push (StyleError.leading_by, line_number)
      else if line.trimLeft.startsWith "by " then
        -- Let's see what this finds!
        output := output.push (StyleError.leading_by, line_number)
      -- We also check for a "leading where", which has far fewer exceptions.
      if line.trim == "where " then
        output := output.push (StyleError.isolated_where, line_number)
      if line.trimRight.startsWith ". " then
        output := output.push (StyleError.dot, line_number) -- has an auto-fix
      if [".", "·"].contains line.trim then
        output := output.push (StyleError.dot, line_number)
      if line.containsSubstr " ;" then
        output := output.push (StyleError.semicolon, line_number) -- has an auto-fix
      if line.trimRight.startsWith ":" then
        output := output.push (StyleError.colon, line_number)
    return output

/-- Check if a line ends with trailing whitespace or with a windows line ending.

Assumes the lines are not newline-terminated. -/
def line_endings : LinterCore := fun lines ↦ Id.run do
  let mut output := Array.mkEmpty 0
  -- XXX: more elegant fix? is there an enumerate for Lean?
  let mut line_number := 0
  for line in lines do
    line_number := line_number + 1
    let line' := Lake.crlf2lf line
    if line' != line then
      output := output.push (StyleError.windowsLineEndings, line_number)
    if line'.trimRight != line' then
      output := output.push (StyleError.trailingWhitespace, line_number)
  return output

/-- Whether a collection of lines consists *only* of imports:
in practice, this means it's an imports-only file and exempt from file length linting. -/
def is_imports_only_file (lines : Array String) : Bool :=
  -- The Python version also excluded comments: since the import-only files are
  -- automatically generated and don't contains comments, this is in fact not necessary.
  lines.all (fun line ↦ line.startsWith "import ")

/-- Error if a collection of lines is too large. "Too large" means more than 1500 lines
**and** longer than an optional previous limit.
If the file is too large, return a matching `StyleError`, which includes a new size limit
(which is somewhat larger than the current size). -/
def check_file_length (lines : Array String) (existing_limit : Option ℕ) : Option StyleError :=
  Id.run do
  if lines.size > 1500 then
    let is_larger : Bool := match existing_limit with
    | some mark => lines.size > mark
    | none => true
    if is_larger then
      -- We add about 200 lines of slack to the current file size:
      -- small PRs will be unperturbed, but sufficiently large PRs will get nudged towards
      -- split up this file.
      return some (StyleError.fileTooLong lines.size ((Nat.div lines.size 100) * 100 + 200))
  none
end

/-- All text-based linters registered in this file. -/
def all_linters : Array LinterCore := Array.mk
  [check_line_length, contains_broad_imports, copyright_header, isolated_by_dot_semicolon,
    line_endings]

/-- Read a file, apply all text-based linters and return the formatted errors.

`size_limit` is any pre-existing limit on this file's size;
`exceptions` are any previous style exceptions. -/
def lint_file (path : System.FilePath)
    (size_limit : Option ℕ) (exceptions : Array ErrorContext) : IO Unit := do
  let lines ← IO.FS.lines path
  -- We don't need to run any checks on imports-only files.
  -- NB. The Python script used to still run a few linters; this is in fact not necessary.
  if is_imports_only_file lines then
    return
  -- Check first if the file is too long: since this requires mucking with previous exceptions,
  -- I'll just handle this directly.
  if let some (StyleError.fileTooLong n limit) := check_file_length lines size_limit then
    let arr := Array.mkArray1 (ErrorContext.mk (StyleError.fileTooLong n limit) 1 path)
    format_errors arr (Array.mkEmpty 0)
  let all_output := (Array.map (fun lint ↦
    (Array.map (fun (e, n) ↦ ErrorContext.mk e n path)) (lint lines))) all_linters
  -- XXX: this list is currently not sorted: for github, that's probably fine
  format_errors (Array.flatten all_output) exceptions

#eval lint_file (System.mkFilePath ["Mathlib", "Tactic", "Linter", "TextBased.lean"])
  none (Array.mkEmpty 0)

/-- Lint all files in `Mathlib.lean`. -/
def check_all_files : IO Unit := do
  -- Read all module names in Mathlib from `Mathlib.lean`.
  let allModules ← IO.FS.lines (System.mkFilePath [(toString "Mathlib.lean")])
  for module in allModules do
    -- Convert the module name to a file name, then lint that file.
    -- TODO: parse `style-exceptions.txt`, then pass these exceptions in, including a size limit!
    let path := (System.mkFilePath ((module.split fun c ↦ (c == '.')).append [".lean"]))
    lint_file path (some 1500) (Array.mkEmpty 0)
