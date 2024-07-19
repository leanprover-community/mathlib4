/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Batteries.Data.String.Matcher
import Mathlib.Data.Nat.Notation

/-!
## Text-based linters

This file defines various mathlib linters which are based on reading the source code only.
In practice, only style linters will have this form.
All of these have been rewritten from the `lint-style.py` script.

For now, this only contains the linters for the copyright and author headers and large files:
further linters will be ported in subsequent PRs.

An executable running all these linters is defined in `scripts/lint_style.lean`.
-/

open System

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
  /-- Line longer than 100 characters -/
  | lineLength (actual : Int) : StyleError
  /-- The current file was too large: this error contains the current number of lines
  as well as a size limit (slightly larger). On future runs, this linter will allow this file
  to grow up to this limit. -/
  | fileTooLong (number_lines : ℕ) (new_size_limit : ℕ) : StyleError
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
def StyleError.errorMessage (err : StyleError) (style : ErrorFormat) : String := match err with
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
  | StyleError.lineLength n => s!"Line has {n} characters, which is more than 100"
  | StyleError.fileTooLong current_size size_limit =>
    match style with
    | ErrorFormat.github =>
        s!"file contains {current_size} lines (at most {size_limit} allowed), try to split it up"
    | ErrorFormat.exceptionsFile =>
        s!"{size_limit} file contains {current_size} lines, try to split it up"
    | ErrorFormat.humanReadable => s!"file contains {current_size} lines, try to split it up"

/-- The error code for a given style error. Keep this in sync with `parse?_errorContext` below! -/
-- FUTURE: we're matching the old codes in `lint-style.py` for compatibility;
-- in principle, we could also print something more readable.
def StyleError.errorCode (err : StyleError) : String := match err with
  | StyleError.copyright _ => "ERR_COP"
  | StyleError.authors => "ERR_AUT"
  | StyleError.adaptationNote => "ERR_ADN"
  | StyleError.broadImport _ => "ERR_IMP"
  | StyleError.lineLength _ => "ERR_LIN"
  | StyleError.fileTooLong _ _ => "ERR_NUM_LIN"

/-- Context for a style error: the actual error, the line number in the file we're reading
and the path to the file. -/
structure ErrorContext where
  /-- The underlying `StyleError`-/
  error : StyleError
  /-- The line number of the error (1-based) -/
  lineNumber : ℕ
  /-- The path to the file which was linted -/
  path : FilePath

/-- The parts of a `StyleError` which are considered when matching against the existing
  style exceptions: for example, we ignore the particular line length of a "line too long" error. -/
def StyleError.normalise (err : StyleError) : StyleError := match err with
  -- NB: keep this in sync with `parse?_errorContext` below.
  | StyleError.fileTooLong _ _ => StyleError.fileTooLong 0 0
  -- We do *not* care about the *kind* of wrong copyright.
  | StyleError.copyright _ => StyleError.copyright none
  | _ => err

/-- Careful: we do not want to compare `ErrorContexts` exactly; we ignore some details. -/
instance : BEq ErrorContext where
  beq ctx ctx' :=
      ctx.path == ctx'.path
      -- We completely ignore line numbers of errors. Not sure if this is best.
      -- We normalise errors before comparing them.
      && (ctx.error).normalise == (ctx'.error).normalise

/-- Output the formatted error message, containing its context.
`style` specifies if the error should be formatted for humans to read, github problem matchers
to consume, or for the style exceptions file. -/
def outputMessage (errctx : ErrorContext) (style : ErrorFormat) : String :=
  let error_message := errctx.error.errorMessage style
  match style with
  | ErrorFormat.github =>
   -- We are outputting for github: duplicate file path, line number and error code,
    -- so that they are also visible in the plain text output.
    let path := errctx.path
    let nr := errctx.lineNumber
    let code := errctx.error.errorCode
    s!"::ERR file={path},line={nr},code={code}::{path}:{nr} {code}: {error_message}"
  | ErrorFormat.exceptionsFile =>
    -- Produce an entry in the exceptions file: with error code and "line" in front of the number.
    s!"{errctx.path} : line {errctx.lineNumber} : {errctx.error.errorCode} : {error_message}"
  | ErrorFormat.humanReadable =>
    -- Print for humans: clickable file name and omit the error code
    s!"error: {errctx.path}:{errctx.lineNumber}: {error_message}"

/-- Try parsing an `ErrorContext` from a string: return `some` if successful, `none` otherwise. -/
def parse?_errorContext (line : String) : Option ErrorContext := Id.run do
  let parts := line.split (· == ' ')
  match parts with
    | filename :: ":" :: "line" :: line_number :: ":" :: error_code :: ":" :: error_message =>
      -- Turn the filename into a path. In general, this is ambiguous if we don't know if we're
      -- dealing with e.g. Windows or POSIX paths. In our setting, this is fine, since no path
      -- component contains any path separator.
      let path := mkFilePath (filename.split (FilePath.pathSeparators.contains ·))
      -- Parse the error kind from the error code, ugh.
      -- NB: keep this in sync with `StyleError.errorCode` above!
      let err : Option StyleError := match error_code with
        -- Use default values for parameters which are normalised.
        -- NB: keep this in sync with `normalise` above!
        | "ERR_COP" => some (StyleError.copyright none)
        | "ERR_LIN" =>
          if let some n := error_message.get? 2 then
            match String.toNat? n with
              | some n => return StyleError.lineLength n
              | none => none
          else none
        | "ERR_AUT" => some (StyleError.authors)
        | "ERR_ADN" => some (StyleError.adaptationNote)
        | "ERR_IMP" =>
          -- XXX tweak exceptions messages to ease parsing?
          if (error_message.get! 0).containsSubstr "tactic" then
            some (StyleError.broadImport BroadImports.TacticFolder)
          else
            some (StyleError.broadImport BroadImports.Lake)
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
      match String.toNat? line_number with
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
  return output

/-- Lint on any occurrences of the string "Adaptation note:" or variants thereof. -/
def adaptationNoteLinter : TextbasedLinter := fun lines ↦ Id.run do
  let mut errors := Array.mkEmpty 0
  let mut lineNumber := 1
  for line in lines do
    -- We make this shorter to catch "Adaptation note", "adaptation note" and a missing colon.
    if line.containsSubstr "daptation note" then
      errors := errors.push (StyleError.adaptationNote, lineNumber)
    lineNumber := lineNumber + 1
  return errors

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
  return errors

/-- Iterates over a collection of strings, finding all lines which are longer than 101 chars.
We allow #aligns or URLs to be longer, though.
-/
def lineLengthLinter : TextbasedLinter := fun lines ↦ Id.run do
  let errors := (lines.toList.enumFrom 1).filterMap (fun (line_number, line) ↦
    if line.length > 101 &&
      !(line.startsWith "#align" || line.containsSubstr "http" || line.startsWith "-- #align")  then
      some (StyleError.lineLength line.length, line_number)
    else none)
  errors.toArray

/-- Whether a collection of lines consists *only* of imports, blank lines and single-line comments.
In practice, this means it's an imports-only file and exempt from almost all linting. -/
def isImportsOnlyFile (lines : Array String) : Bool :=
  -- The Python version also excluded multi-line comments: for all files generated by `mk_all`,
  -- this is in fact not necessary. (It is needed for `Tactic/Linter.lean`, though.)
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
      -- We add about 200 lines of slack to the current file size: small PRs will be unaffected,
      -- but sufficiently large PRs will get nudged towards splitting up this file.
      return some (StyleError.fileTooLong lines.size ((Nat.div lines.size 100) * 100 + 200))
  none

end

/-- All text-based linters registered in this file. -/
def allLinters : Array TextbasedLinter := #[
    copyrightHeaderLinter, adaptationNoteLinter, broadImportsLinter, lineLengthLinter
  ]

/-- Read a file and apply all text-based linters. Return a list of all unexpected errors.
`sizeLimit` is any pre-existing limit on this file's size.
`exceptions` are any other style exceptions. -/
def lintFile (path : FilePath) (sizeLimit : Option ℕ) (exceptions : Array ErrorContext) :
    IO (Array ErrorContext) := do
  let lines ← IO.FS.lines path
  -- We don't need to run any checks on imports-only files.
  -- NB. The Python script used to still run a few linters; this is in fact not necessary.
  if isImportsOnlyFile lines then
    return #[]
  let mut errors := #[]
  if let some (StyleError.fileTooLong n limit) := checkFileLength lines sizeLimit then
    errors := #[ErrorContext.mk (StyleError.fileTooLong n limit) 1 path]
  let allOutput := (Array.map (fun lint ↦
    (Array.map (fun (e, n) ↦ ErrorContext.mk e n path)) (lint lines))) allLinters
  -- This this list is not sorted: for github, this is fine.
  errors := errors.append (allOutput.flatten.filter (fun e ↦ !exceptions.contains e))
  return errors

/-- Lint a collection of modules for style violations.
Print formatted errors for all unexpected style violations to standard output.
Return the number of files which had new style errors.
`style` specifies if the error should be formatted for humans to read, github problem matchers
to consume or for the style exceptions file. -/
def lintModules (moduleNames : Array String) (style : ErrorFormat) : IO UInt32 := do
  -- Read the style exceptions file.
  -- We also have a `nolints` file with manual exceptions for the linter.
  let exceptions ← IO.FS.lines (mkFilePath ["scripts", "style-exceptions.txt"])
  let mut styleExceptions := parseStyleExceptions exceptions
  let nolints ← IO.FS.lines (mkFilePath ["scripts", "nolints-style.txt"])
  styleExceptions := styleExceptions.append (parseStyleExceptions nolints)

  let mut numberErrorFiles := 0
  let mut allUnexpectedErrors := #[]
  for module in moduleNames do
    -- Convert the module name to a file name, then lint that file.
    let path := (mkFilePath (module.split (· == '.'))).addExtension "lean"
    -- Find all size limits for this given file.
    -- If several size limits are given (unlikely in practice), we use the first one.
    let sizeLimits := (styleExceptions.filter (·.path == path)).filterMap (fun errctx ↦
      match errctx.error with
      | StyleError.fileTooLong _ limit => some limit
      | _ => none)
    let errors := ← lintFile path (sizeLimits.get? 0) styleExceptions
    if errors.size > 0 then
      allUnexpectedErrors := allUnexpectedErrors.append errors
      numberErrorFiles := numberErrorFiles + 1
  formatErrors allUnexpectedErrors style
  return numberErrorFiles
