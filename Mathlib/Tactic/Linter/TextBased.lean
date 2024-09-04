/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Batteries.Data.String.Matcher
import Batteries.Lean.HashSet
import Mathlib.Data.Nat.Notation
import Mathlib.Init.Data.String

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
- unicode characters that aren't used in math or in Mathlib

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

-- TODO remove Repr instances (used for debugging) if it's bad to have them!

/-- Different kinds of "broad imports" that are linted against. -/
inductive BroadImports
  /-- Importing the entire "Mathlib.Tactic" folder -/
  | TacticFolder
  /-- Importing any module in `Lake`, unless carefully measured
  This has caused unexpected regressions in the past. -/
  | Lake
deriving BEq, Repr

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
  /-- The current file was too large: this error contains the current number of lines
  as well as a size limit (slightly larger). On future runs, this linter will allow this file
  to grow up to this limit.
  For diagnostic purposes, this may also contain a previous size limit, which is now exceeded.
  The `longFile` linter implements the line-length check as a syntax linter.
  This text-based check is present to ensure the limit on files that do not import the linter. -/
  | fileTooLong (numberLines : ℕ) (newSizeLimit : ℕ) (previousLimit : Option ℕ) : StyleError
  /-- A unicode character was used that isn't recommended -/
  | unwantedUnicode (c : Char)
  /-- Unicode variant selectors are used in a bad way.

  * `s` is the string containing the unicode character and any unicode-variant-selector following it
  * `selector` is the desired selector or `none`
  * `pos`: the character position in the line.
  -/
  | unicodeVariant (s : String) (selector: Option Char) (pos : String.Pos)
deriving BEq, Repr

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

/-- Following any unicode character, this indicates that the emoji-variant should be displayed -/
def UnicodeVariant.emoji := '\uFE0F'

/-- Following any unicode character, this indicates that the text-variant should be displayed -/
def UnicodeVariant.text := '\uFE0E'

/-- Prints a unicode character's codepoint in hexadecimal with prefix 'U+'.
E.g., 'a' is "U+0061".-/
def printCodepointHex (c : Char) : String :=
  let digits := Nat.toDigits 16 c.val.toNat
  match digits.length with  -- print at least 4 (could be more) hex characters using leading zeros
  | 1 => "U+000".append <| String.mk digits
  | 2 => "U+00".append <| String.mk digits
  | 3 => "U+0".append <| String.mk digits
  | _ => "U+".append <| String.mk digits

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
  | StyleError.fileTooLong currentSize sizeLimit previousLimit =>
    match style with
    | ErrorFormat.github =>
      if let some n := previousLimit then
        s!"file contains {currentSize} lines (at most {n} allowed), try to split it up"
      else
        s!"file contains {currentSize} lines, try to split it up"
    | ErrorFormat.exceptionsFile =>
        s!"{sizeLimit} file contains {currentSize} lines, try to split it up"
    | ErrorFormat.humanReadable => s!"file contains {currentSize} lines, try to split it up"
  | StyleError.unwantedUnicode c =>
      s!"unicode character '{c}' ({printCodepointHex c}) is not recommended. \
        Consider adding it to the whitelist."
  | StyleError.unicodeVariant s selector pos =>
    let variant := if selector == UnicodeVariant.emoji then "emoji"
      else if selector == UnicodeVariant.text then "text"
      else "default"
    let oldHex := " ".intercalate <| s.data.map printCodepointHex
    let instruction : String := match s, selector with
    | ⟨c₀ :: _⟩, some sel =>
      let newC : String := ⟨[c₀, sel]⟩
      let newHex := " ".intercalate <| newC.data.map printCodepointHex
      s!"Please use the {variant}-variant: \"{newC}\" ({newHex})!"
    | _, _ => "It does not select anything, consider deleting it."
    s!"bad or missing unicode variant-selector at char {pos}: \"{s}\" ({oldHex}). {instruction}"

/-- The error code for a given style error. Keep this in sync with `parse?_errorContext` below! -/
-- FUTURE: we're matching the old codes in `lint-style.py` for compatibility;
-- in principle, we could also print something more readable.
def StyleError.errorCode (err : StyleError) : String := match err with
  | StyleError.copyright _ => "ERR_COP"
  | StyleError.authors => "ERR_AUT"
  | StyleError.adaptationNote => "ERR_ADN"
  | StyleError.broadImport _ => "ERR_IMP"
  | StyleError.fileTooLong _ _ _ => "ERR_NUM_LIN"
  | StyleError.unwantedUnicode _ => "ERR_UNICODE"
  | StyleError.unicodeVariant _ _ _ => "ERR_UNICODE_VARIANT"

/-- Context for a style error: the actual error, the line number in the file we're reading
and the path to the file. -/
structure ErrorContext where
  /-- The underlying `StyleError`-/
  error : StyleError
  /-- The line number of the error (1-based) -/
  lineNumber : ℕ
  /-- The path to the file which was linted -/
  path : FilePath
deriving BEq, Repr

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
  if existing.path != new.path then
    ComparisonResult.Different
  -- We entirely ignore their line numbers: not sure if this is best.

  -- NB: keep the following in sync with `parse?_errorContext` below.
  -- Generally, comparable errors must have equal `StyleError`s, but there are some exceptions.
  else match (existing.error, new.error) with
    -- File length errors are the biggest exceptions: generally, we prefer to keep the
    -- existing entry, *except* when a newer entry is much shorter.
  | (StyleError.fileTooLong n nLimit _, StyleError.fileTooLong m _mLimit _) =>
    -- The only exception are "file too long" errors.
    -- If a file got much longer, the existing exception does not apply;
    if m > nLimit then ComparisonResult.Different
    -- if it does apply, we prefer to keep the existing entry,
    -- *unless* the newer entry is much shorter.
    else if m + 200 <= n then ComparisonResult.Comparable false
    else ComparisonResult.Comparable true
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
  let errorMessage := errctx.error.errorMessage style
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

-- TODO check if this doc change is correct as per intentions of original authors!!!

/-- Try parsing an `ErrorContext` from a string: return `some` if successful, `none` otherwise.
This should be the inverse of `fun ctx ↦ outputMessage ctx .exceptionsFile` -/
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
        | "ERR_IMP" =>
          -- XXX tweak exceptions messages to ease parsing?
          if (errorMessage.get! 0).containsSubstr "tactic" then
            some (StyleError.broadImport BroadImports.TacticFolder)
          else
            some (StyleError.broadImport BroadImports.Lake)
        | "ERR_NUM_LIN" =>
          -- Parse the error message in the script. `none` indicates invalid input.
          match (errorMessage.get? 0, errorMessage.get? 3) with
          | (some limit, some current) =>
            match (String.toNat? limit, String.toNat? current) with
            | (some sizeLimit, some currentSize) =>
              some (StyleError.fileTooLong currentSize sizeLimit (some sizeLimit))
            | _ => none
          | _ => none
        | "ERR_UNICODE" =>
            if let some str := errorMessage.get? 2 then
              if let some c := str.get? ⟨1⟩ then
                some (StyleError.unwantedUnicode c)
              else none
            else none
        | "ERR_UNICODE_VARIANT" =>
          -- some (StyleError.unicodeVariant _ _ _)
          none --TODO
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
def checkFileLength (lines : Array String) (existingLimit : Option ℕ) : Option StyleError :=
  Id.run do
  if lines.size > 1500 then
    let isLarger : Bool := match existingLimit with
    | some mark => lines.size > mark
    | none => true
    if isLarger then
      -- If the `longFile` linter is not active on the file, this text-based linter kicks in.
      if (lines.filter ("set_option linter.style.longFile ".isPrefixOf)).isEmpty then
        -- We add about 200 lines of slack to the current file size: small PRs will be unaffected,
        -- but sufficiently large PRs will get nudged towards splitting up this file.
        return some (StyleError.fileTooLong lines.size
          ((Nat.div lines.size 100) * 100 + 200) existingLimit)
      -- Otherwise, the `longFile` linter already manages the exception for this file.
      else return none
  none

end


namespace unicodeLinter

/-- Hashable instance for use with the unicodeLinter -/
local instance instHashableChar : Hashable Char where
  hash c := c.val.toUInt64

def allowedWhitespace := #[' ', '\n']

/-- Printable ASCII characters.
**excluding** 0x7F ('DEL') -/
def printableASCII := #[
'!', '"', '#', '$', '%', '&', '\'', '(', ')', '*', '+', ',', '-',
'.', '/', '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', ':', ';', '<',
'=', '>', '?', '@', 'A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K',
'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T', 'U', 'V', 'W', 'X', 'Y', 'Z',
'[', '\\', ']', '^', '_', '`', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i',
'j', 'k', 'l', 'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x',
'y', 'z', '{', '|', '}', '~'
]

/--
Symbols with VSCode extension abbreviation as of Aug. 28, 2024

Taken from abbreviations.json in
github.com/leanprover/vscode-lean4/blob/97d7d8c382d1549c18b66cd99ab4df0b6634c8f1

Obtained using Julia code:
```julia
filter(!isascii, unique( <all text in JSON file> )) |> repr
```
And manually **excluding** \quad (U+2001) and Rial (U+FDFC).
-/
def withVSCodeAbbrev := #[
'⦃', '⦄', '⟦', '⟧', '⟨', '⟩', '⟮', '⟯', '‹', '›', '«',
'»', '⁅', '⁆', '‖', '₊', '⌊', '⌋', '⌈', '⌉', 'α', 'β',
'χ', '↓', 'ε', 'γ', '∩', 'μ', '¬', '∘', 'Π', '▸', '→',
'↑', '∨', '×', '⁻', '¹', '∼', '·', '⋆', '¿', '₁', '₂',
'₃', '₄', '₅', '₆', '₇', '₈', '₉', '₀', '←', 'Ø', '⅋',
'𝔸', 'ℂ', 'Δ', '𝔽', 'Γ', 'ℍ', '⋂', '𝕂', 'Λ', 'ℕ', 'ℚ',
'ℝ', 'Σ', '⋃', 'ℤ', '♯', '∶', '∣', '¡', 'δ', 'ζ', 'η',
'θ', 'ι', 'κ', 'λ', 'ν', 'ξ', 'π', 'ρ', 'ς', 'σ', 'τ',
'φ', 'ψ', 'ω', 'À', 'Á', 'Â', 'Ã', 'Ä', 'Ç', 'È', 'É',
'Ê', 'Ë', 'Ì', 'Í', 'Î', 'Ï', 'Ñ', 'Ò', 'Ó', 'Ô', 'Õ',
'Ö', 'Ù', 'Ú', 'Û', 'Ü', 'Ý', 'à', 'á', 'â', 'ã', 'ä',
'ç', 'è', 'é', 'ê', 'ë', 'ì', 'í', 'î', 'ï', 'ñ', 'ò',
'ó', 'ô', 'õ', 'ö', 'ø', 'ù', 'ú', 'û', 'ü', 'ý', 'ÿ',
'Ł', '∉', '♩', '𐆎', '∌', '∋', '⟹', '♮', '₦', '∇', '≉',
'№', '⇍', '⇎', '⇏', '⊯', '⊮', '≇', '↗', '≢', '≠', '∄',
'≱', '≯', '↚', '↮', '≰', '≮', '∤', '∦', '⋠', '⊀', '↛',
'≄', '≁', '⊈', '⊄', '⋡', '⊁', '⊉', '⊅', '⋬', '⋪', '⋭',
'⋫', '⊭', '⊬', '↖', '≃', '≖', '≕', '⋝', '⋜', '⊢', '–',
'∃', '∅', '—', '€', 'ℓ', '≅', '∈', '⊺', '∫', '⨍', '∆',
'⊓', '⨅', '∞', '↔', 'ı', '≣', '≡', '≗', '⇒', '≋', '≊',
'≈', '⟶', 'ϩ', '↩', '↪', '₴', 'ͱ', '♥', 'ℏ', '∻', '≔',
'∺', '∷', '≂', '⊣', '²', '³', '∹', '─', '═', '━', '╌',
'⊸', '≑', '≐', '∔', '∸', '⋯', '≘', '⟅', '≙', '∧', '∠',
'∟', 'Å', '∀', 'ᶠ', 'ᵐ', 'ℵ', '⁎', '∗', '≍', '⌶', 'å',
'æ', '₳', '؋', '∐', '≚', 'ª', 'º', '⊕', 'ᵒ', 'ᵈ', 'ᵃ',
'ᵖ', '⊖', '⊝', '⊗', '⊘', '⊙', '⊚', '⊜', 'œ', '🛑', 'Ω',
'℥', 'ο', '∮', '∯', '⨂', '∂', '≛', '≜', '▹', '▿', '⊴',
'◃', '⊵', '▵', '⬝', '◂', '↞', '↠', '⁀', '∴', '℡', '₸',
'♪', 'µ', '⁄', '฿', '✝', '⁒', '₡', '℗', '₩', '₱', '‱',
'₤', '℞', '※', '‽', '℮', '◦', '₮', '⊤', 'ₛ', 'ₐ', 'ᵇ',
'ₗ', 'ₘ', 'ₚ', '⇨', '￢', '⋖', '⩿', '≝', '°', 'ϯ', '⊡',
'₫', '⇊', '⇃', '⇂', '↘', '⇘', '₯', '↙', '⇙', '⇵', '↧',
'⟱', '⇓', '↡', '‡', '⋱', '↯', '◆', '◇', '◈', '⚀', '÷',
'⋇', '⌀', '♢', '⋄', 'ϝ', '†', 'ℸ', 'ð', '≞', '∡', '↦',
'♂', '✠', '₼', 'ℐ', '−', '₥', '℧', '⊧', '∓', '≟', '⁇',
'🛇', '∏', '∝', '≾', '≼', '⋨', '≺', '′', '↣', '𝒫', '£',
'▰', '▱', '㉐', '¶', '∥', '±', '⟂', 'ᗮ', '‰', '⅌', '₧',
'⋔', '✂', '≦', '≤', '↝', '↢', '↽', '↼', '⇇', '⇆', '⇋',
'↭', '⋋', '≲', '⋚', '≶', '⊔', '⟷', '⇔', '⌟', '⟵', '↤',
'⇚', '⇐', '↜', '⌞', '〚', '≪', '₾', '…', '“', '《', '⧏',
'◁', '⋦', '≨', '↫', '↬', '✧', '‘', '⋉', '≧', '≥', '„',
'‚', '₲', 'ϫ', '⋙', '≫', 'ℷ', '⋧', '≩', '≳', '⋗', '⋛',
'≷', '≴', '⟪', '≵', '⟫', '√', '⊂', '⊃', '⊏', '⊐', '⊆',
'⊊', '⊇', '⊋', '⨆', '∛', '∜', '≿', '≽', '⋩', '≻', '∑',
'⤳', '⋢', '⊑', '⋣', '⊒', '□', '⇝', '■', '▣', '▢', '◾',
'✦', '✶', '✴', '✹', 'ϛ', '₷', '∙', '♠', '∢', '§', 'ϻ',
'ϡ', 'ϸ', 'ϭ', 'ϣ', '﹨', '∖', '⌣', '•', '◀', 'Τ', 'Θ',
'Þ', '∪', '‿', '⯑', '⊎', '⊍', '↨', '↕', '⇕', '⇖', '⌜',
'⇗', '⌝', '⇈', '⇅', '↥', '⟰', '⇑', '↟', 'υ', '↿', '↾',
'⋀', 'Å', 'Æ', 'Α', '⋁', '⨁', '⨀', '⍟', 'Œ', 'Ω', 'Ο',
'Ι', 'ℑ', '⨄', '⨃', 'Υ', 'ƛ', 'Ϫ', 'Β', 'Ε', 'Ζ', 'Κ',
'Μ', 'Ν', 'Ξ', 'Ρ', 'Φ', 'Χ', 'Ψ', '✉', '⋘', '↰', '⊨',
'⇰', '⊩', '⊫', '⊪', '⋒', '⋓', '¤', '⋞', '⋟', '⋎', '⋏',
'↶', '↷', '♣', '🚧', 'ᶜ', '∁', '©', '●', '◌', '○', '◯',
'◎', '↺', '®', '↻', '⊛', 'Ⓢ', '¢', '℃', '₵', '✓', 'ȩ',
'₢', '☡', '∎', '⧸', '⊹', '⊟', '⊞', '⊠', '¦', '𝔹', 'ℙ',
'𝟘', '⅀', '𝟚', '𝟙', '𝟜', '𝟛', '𝟞', '𝟝', '𝟠', '𝟟', '𝟬',
'𝟡', '𝟮', '𝟭', '𝟰', '𝟯', '𝟲', '𝟱', '𝟴', '𝟳', '𝟵', '‣',
'≏', '☣', '★', '▽', '△', '≬', 'ℶ', '≌', '∵', '‵', '∍',
'∽', '⋍', '⊼', '☻', '▪', '▾', '▴', '⊥', '⋈', '◫', '⇉',
'⇄', '⇶', '⇛', '▬', '▭', '⟆', '〛', '☢', '’', '⇁',
'⇀', '⇌', '≓', '⋌', '₨', '₽', '▷', '”', '⋊', '⥤', '》',
'½', '¼', '⅓', '⅙', '⅕', '⅟', '⅛', '⅖', '⅔', '⅗', '¾',
'⅘', '⅜', '⅝', '⅚', '⅞', '⌢', '♀', '℻', 'ϥ', '♭', '≒',
'ℜ', 'Ϥ', '↱', 'Ϩ', '☹', 'Ϧ', 'Ͱ', 'Ϟ', 'ᵉ', 'ʰ', 'ᵍ',
'ʲ', 'ⁱ', 'ˡ', 'ᵏ', 'ⁿ', 'ˢ', 'ʳ', 'ᵘ', 'ᵗ', 'ʷ', 'ᵛ',
'ʸ', 'ˣ', 'ᴬ', 'ᶻ', 'ᴰ', 'ᴮ', 'ᴳ', 'ᴱ', 'ᴵ', 'ᴴ', 'ᴷ',
'ᴶ', 'ᴹ', 'ᴸ', 'ᴼ', 'ᴺ', 'ᴿ', 'ᴾ', 'ᵁ', 'ᵀ', 'ᵂ', 'ⱽ',
'⁰', '⁵', '⁴', '⁷', '⁶', '⁹', '⁸', '⁽', '⁾', '⁺', '⁼',
'ꭟ', 'ᶷ', 'ᶶ', 'ꭝ', 'ꭞ', 'ᶩ', 'ᶪ', 'ꭜ', 'ꟹ', 'ʱ', 'ᶿ',
'ꟸ', 'ᶭ', 'ᶺ', 'ᶣ', 'ᵚ', 'ᵆ', 'ᶛ', 'ᵎ', 'ᵄ', 'ʵ', 'ᵌ',
'ʴ', 'ᵔ', 'ᶵ', 'ᶴ', 'ᶾ', 'ᵑ', 'ᶞ', 'ᶼ', 'ᶽ', 'ᶦ', 'ᶹ',
'ᶰ', 'ᶫ', 'ᶧ', 'ᶸ', 'ᶝ', 'ʶ', 'ᶳ', 'ᵡ', 'ᵊ', 'ᶢ', 'ᶲ',
'ᵙ', 'ᵝ', 'ᶱ', 'ᶯ', 'ᵕ', 'ᶬ', 'ᶮ', 'ᶥ', 'ᶨ', 'ᶟ', 'ᶤ',
'ᵠ', 'ˤ', 'ˠ', 'ᵞ', 'ᵅ', 'ᵜ', 'ᵋ', 'ᵓ', 'ᴻ', 'ᴽ', 'ᴯ',
'ᴲ', '℠', 'ᴭ', '™', 'ₑ', 'ᵢ', 'ₕ', 'ₖ', 'ⱼ', 'ₒ', 'ₙ',
'ᵣ', 'ₜ', 'ᵥ', 'ᵤ', 'ₓ', '₎', '₌', '₍', '̲', '‼', '₋',
'Ϻ', '⁉', 'Ϸ', 'Ϡ', 'Ϣ', 'Ϭ', 'Ϛ', '⋑', '⋐', '☺', '𝐁',
'𝐀', '𝐃', '𝐂', '𝐅', '𝐄', '𝐇', '𝐆', '𝐉', '𝐈', '𝐋', '𝐊',
'𝐍', '𝐌', '𝐏', '𝐎', '𝐑', '𝐐', '𝐓', '𝐒', '𝐕', '𝐔', '𝐗',
'𝐖', '𝐘', '𝐙', '𝐛', '𝐚', '𝐝', '𝐜', '𝐟', '𝐞', '𝐡', '𝐠',
'𝐣', '𝐢', '𝐥', '𝐤', '𝐧', '𝐦', '𝐩', '𝐨', '𝐫', '𝐪', '𝐭',
'𝐬', '𝐯', '𝐮', '𝐱', '𝐰', '𝐲', '𝐳', '𝐴', '𝐶', '𝐵', '𝐸',
'𝐷', '𝐺', '𝐹', '𝐼', '𝐻', '𝐾', '𝐽', '𝑀', '𝐿', '𝑂', '𝑁',
'𝑄', '𝑃', '𝑆', '𝑅', '𝑈', '𝑇', '𝑊', '𝑉', '𝑌', '�', '𝑎',
'𝑍', '𝑐', '𝑏', '𝑒', '𝑑', '𝑔', '𝑓', '𝑗', '𝑖', '𝑙', '𝑘',
'𝑛', '𝑚', '𝑝', '𝑜', '𝑟', '𝑞', '𝑡', '𝑠', '𝑣', '𝑢', '𝑥',
'𝑤', '𝑧', '𝑦', '𝑩', '𝑨', '𝑫', '𝑪', '𝑭', '𝑬', '𝑯', '𝑮',
'𝑱', '𝑰', '𝑳', '𝑲', '𝑵', '𝑴', '𝑷', '𝑶', '𝑹', '𝑸', '𝑻',
'𝑺', '𝑽', '𝑼', '𝑿', '𝒁', '𝒀', '𝒃', '𝒂', '𝒅', '𝒄', '𝒇',
'𝒆', '𝒉', '𝒈', '𝒋', '𝒊', '𝒍', '𝒌', '𝒏', '𝒎', '𝒑', '𝒐',
'𝒓', '𝒒', '𝒕', '𝒔', '𝒗', '𝒖', '𝒙', '𝒘', '𝒛', '𝒚', 'ℬ',
'𝒜', '𝒟', '𝒞', 'ℱ', 'ℰ', 'ℋ', '𝒢', '𝒥', 'ℒ', '𝒦', '𝒩',
'ℳ', '𝒪', 'ℛ', '𝒬', '𝒯', '𝒮', '𝒱', '𝒰', '𝒳', '𝒲', '𝒵',
'𝒴', '𝒷', '𝒶', '𝒹', '𝒸', '𝒻', 'ℯ', '𝒽', 'ℊ', '𝒿', '𝒾',
'𝓁', '𝓀', '𝓃', '𝓂', '𝓅', 'ℴ', '𝓇', '𝓆', '𝓉', '𝓈', '𝓋',
'𝓊', '𝓍', '𝓌', '𝓏', '𝓎', '𝓑', '𝓐', '𝓓', '𝓒', '𝓕', '𝓔',
'𝓗', '𝓖', '𝓙', '𝓘', '𝓛', '𝓚', '𝓝', '𝓜', '𝓟', '𝓞', '𝓠',
'𝓣', '𝓢', '𝓥', '𝓤', '𝓧', '𝓦', '𝓩', '𝓨', '𝓫', '𝓪', '𝓭',
'𝓬', '𝓯', '𝓮', '𝓱', '𝓰', '𝓳', '𝓲', '𝓵', '𝓴', '𝓷', '𝓶',
'𝓹', '𝓸', '𝓻', '𝓺', '𝓽', '𝓼', '𝓿', '𝓾', '𝔁', '𝔀', '𝔃',
'𝔂', '𝔅', '𝔄', '𝔇', 'ℭ', '𝔉', '𝔈', 'ℌ', '𝔊', '𝔍', '𝔏',
'𝔎', '𝔑', '𝔐', '𝔓', '𝔒', '𝔔', '𝔗', '𝔖', '𝔙', '𝔘', '𝔚',
'ℨ', '𝔜', '𝔟', '𝔞', '𝔡', '𝔠', '𝔣', '𝔢', '𝔥', '𝔤', '𝔧',
'𝔦', '𝔩', '𝔨', '𝔫', '𝔪', '𝔭', '𝔬', '𝔯', '𝔮', '𝔱', '𝔰',
'𝔳', '𝔲', '𝔵', '𝔶', '𝔷', '¥', 'ϰ', 'ϱ', 'ϗ', 'ϕ', 'ϖ',
'⊲', 'ϑ', 'ϐ', '⊳', '⊻', 'ě', 'Ě', 'ď', '⋮', 'Ď', 'Č',
'č', '₭', 'ϟ', 'Į', 'į', 'K', '⚠', 'ϧ', '≀', '℘', 'Ϯ',
'Ϝ', 'Ð', 'Η', '≎', '𝔻', '𝔼', '𝔾', '𝕁', '𝕀', '𝕃', '𝕄',
'𝕆', '𝕋', '𝕊', '𝕍', '𝕌', '𝕏', '𝕎', '𝕐', '𝕓', '𝕒', '𝕕',
'𝕔', '𝕗', '𝕖', '𝕙', '𝕘', '𝕛', '𝕚', '𝕜', '𝕟', '𝕞', '𝕡',
'𝕠', '𝕣', '𝕢', '𝕥', '𝕤', '𝕧', '𝕦', '𝕩', '𝕨', '𝕪', '𝕫',
'⨯', '⨿', 'Ϳ'
]

/-- Other characters already in Mathlib as of Aug. 28, 2024 -/
def othersInMathlib := #[
 '▼', 'c', 'ō', '⏩', '❓',
'🆕', 'š', 'ř', '⚬', '│', '├', '┌', 'ő',
'⟍', '̂', 'ᘁ', 'ń', 'ć', '⟋', 'ỳ', 'ầ', '⥥',
'ł', '◿', '◹', '－', '＼', '◥', '／', '◢', 'Ž', 'ă',
'И', 'в', 'а', 'н', 'о', 'и', 'ч', 'Š', 'ᴜ', 'ᵧ', '´',
'ᴄ', 'ꜰ', 'ß', 'ᴢ', 'ᴏ', 'ᴀ', 'ꜱ', 'ɴ', 'ꞯ', 'ʟ',
'ʜ', 'ᵟ', 'ʙ', 'ᵪ', 'ᵩ', 'ᵦ', 'ᴊ', 'ᴛ', 'ᴡ', 'ᴠ',
'ɪ', '̀', 'ᴇ', 'ᴍ', 'ʀ', 'ᴅ', 'ɢ', 'ʏ', 'ᴘ', 'ĝ', 'ᵨ',
'ᴋ', 'ś', '꙳', '𝓡', '𝕝', '𝖣', '⨳']

/- TODO there are more symbols we could use that aren't in this list yet. E.g, see
 https://en.wikipedia.org/wiki/Mathematical_operators_and_symbols_in_Unicode
-/

/--
Hash-set of all unicode characters allowed by the unicodeLinter.
-/
def unicodeWhitelist : Lean.HashSet Char := Lean.HashSet.ofArray (
    allowedWhitespace ++ printableASCII ++ withVSCodeAbbrev ++ othersInMathlib
    -- #[UnicodeVariant.emoji, UnicodeVariant.text]
)

/-- Checks if a character is whitelisted.
Such characters are always allowed by the linter.
Other characters are examined further and may be allowed under suitable conditions. -/
def isWhitelisted (c : Char) : Bool := unicodeWhitelist.contains c

/-- Unicode symbols in Mathilb that should always be followed by the emoji-variant selector.

This files leads by example (and is linted), so we cannot add literals for these directly.
The characters would have to be followed by selectors,
but character literals cannot contain two characters. -/
def mathlibEmojiSymbols := #[
'\u2705', -- ✅️
'\u274C', -- ❌️
 -- TODO "missing end of character literal" if written as '\u1F4A5'
 -- see https://github.com/leanprover/lean4/blob/4eea57841d1012d6c2edab0f270e433d43f92520/src/Lean/Parser/Basic.lean#L709
.ofNat 0x1F4A5, -- 💥️
.ofNat 0x1F7E1, -- 🟡️
.ofNat 0x1F4A1, -- 💡️
.ofNat 0x1F419, -- 🐙️
.ofNat 0x1F50D, -- 🔍️
.ofNat 0x1F389, -- 🎉️
'\u23F3', -- ⏳️
.ofNat 0x1F3C1  -- 🏁️
]

-- this changes how it's displayed
#eval s!"✅{UnicodeVariant.emoji}"
#eval s!"✅{UnicodeVariant.text}"

-- However, these are rendered the same:
#eval s!"🐙{UnicodeVariant.emoji}"
#eval s!"🐙{UnicodeVariant.text}" -- TODO why does this not change anything?
-- TODO can we recheck if all variants really all make sense?

-- Mathlib uses this arrow with text-selector sometimes
#eval s!"↗{UnicodeVariant.emoji}"
#eval s!"↗{UnicodeVariant.text}" -- TODO why does this not change anything?
-- TODO can we check if these variants really all make sense?

/-- Unicode symbols in mathilb that should always be followed by the text-variant selector -/
def mathlibTextSymbols : Array Char := #['↗', '↘'] -- TODO fix / make complete

end unicodeLinter
-- é or é  \u0301
open unicodeLinter in
/-- Lint a collection of input strings if one of them contains unwanted unicode. -/
def unicodeLinter : TextbasedLinter := fun lines ↦ Id.run do
  let mut errors : Array (StyleError × ℕ) := Array.mkEmpty 0
  let mut lineNumber := 1
  for line in lines do
    -- Ensure no bad unicode characters are used
    let suspiciousCharsIdx := line.findAll (!isWhitelisted ·)
    -- check if the suspicious character is allowed by special circumstances
    for pos in suspiciousCharsIdx do
      -- Note that `pos`, being returned by `findAll`, is a valid position.
      let previousC := line.get₂ (line.prev pos) -- may be `thisC` if `pos == 0`
      let thisC := line.get₂ pos
      -- using '\n' would be proper but we don't want linebreaks in the linter warning output.
      let nextC := if pos == line.endPos then '\uFFFD' else line.get₂ (line.next pos)
      -- Ensure specified emojis/text-symbols have the correct variant-selector
      -- Ensure variant-selectors only appear when there is someting to select
      if thisC ∈ mathlibEmojiSymbols then
        if nextC == UnicodeVariant.emoji then
          continue  -- correct selector, linter does not complain.
        else
          errors := errors.push
            (.unicodeVariant ⟨[thisC, nextC]⟩ UnicodeVariant.emoji pos, lineNumber)
      else if thisC ∈ mathlibTextSymbols then
        if nextC == UnicodeVariant.text then
          continue  -- correct selector, linter does not complain.
        else
          errors := errors.push
            (.unicodeVariant ⟨[thisC, nextC]⟩ UnicodeVariant.text pos, lineNumber)
      else if thisC == UnicodeVariant.emoji then
        if previousC ∈ mathlibEmojiSymbols then
          continue  -- selector correctly applied, linter does not complain.
        else
          errors := errors.push (StyleError.unicodeVariant ⟨[thisC]⟩ none pos, lineNumber)
      else if thisC == UnicodeVariant.text then
        if previousC ∈ mathlibTextSymbols then
          continue  -- selector correctly applied, linter does not complain.
        else
          errors := errors.push (StyleError.unicodeVariant ⟨[thisC]⟩ none pos, lineNumber)
      else  -- End of "special circumstances".
        -- Linter rejects generic non-whitelisted unicode.
        errors := errors.push (StyleError.unwantedUnicode thisC, lineNumber)
    lineNumber := lineNumber + 1
  return errors

/-- All text-based linters registered in this file. -/
def allLinters : Array TextbasedLinter := #[
    copyrightHeaderLinter, adaptationNoteLinter, broadImportsLinter, unicodeLinter
  ]

/-- Controls what kind of output this programme produces. -/
inductive OutputSetting : Type
  /-- Print any style error to standard output (the default) -/
  | print (style : ErrorFormat)
  /-- Update the style exceptions file (and still print style errors to standard output).
  This adds entries for any new exceptions, removes any entries which are no longer necessary,
  and tries to not modify exception entries unless necessary.
  To fully regenerate the exceptions file, delete `style-exceptions.txt` and run again in this mode.
  -/
  | update
  deriving BEq

/-- Read a file and apply all text-based linters. Return a list of all unexpected errors.
`sizeLimit` is any pre-existing limit on this file's size.
`exceptions` are any other style exceptions. -/
def lintFile (path : FilePath) (sizeLimit : Option ℕ) (exceptions : Array ErrorContext) :
    IO (Array ErrorContext) := do
  let lines ← IO.FS.lines path
  -- We don't need to run any checks on imports-only files.
  if isImportsOnlyFile lines then
    return #[]
  let mut errors := #[]
  if let some (StyleError.fileTooLong n limit ex) := checkFileLength lines sizeLimit then
    errors := #[ErrorContext.mk (StyleError.fileTooLong n limit ex) 1 path]
  let allOutput := (Array.map (fun lint ↦
    (Array.map (fun (e, n) ↦ ErrorContext.mk e n path)) (lint lines))) allLinters
  -- This list is not sorted: for github, this is fine.
  errors := errors.append
    (allOutput.flatten.filter (fun e ↦ (e.find?_comparable exceptions).isNone))
  return errors

/-- Lint a collection of modules for style violations.
Print formatted errors for all unexpected style violations to standard output;
update the list of style exceptions if configured so.
Return the number of files which had new style errors.
`moduleNames` are all the modules to lint,
`mode` specifies what kind of output this script should produce,
`fix` configures whether fixable errors should be corrected in-place. -/
def lintModules (moduleNames : Array String) (mode : OutputSetting) (fix : Bool) : IO UInt32 := do
  -- Read the style exceptions file.
  -- We also have a `nolints` file with manual exceptions for the linter.
  let exceptionsFilePath : FilePath := "scripts" / "style-exceptions.txt"
  let exceptions ← IO.FS.lines exceptionsFilePath
  let mut styleExceptions := parseStyleExceptions exceptions
  let nolints ← IO.FS.lines ("scripts" / "nolints-style.txt")
  styleExceptions := styleExceptions.append (parseStyleExceptions nolints)

  let mut numberErrorFiles : UInt32 := 0
  let mut allUnexpectedErrors := #[]
  for module in moduleNames do
    -- Convert the module name to a file name, then lint that file.
    let path := (mkFilePath (module.split (· == '.'))).addExtension "lean"
    -- Find all size limits for this given file.
    -- If several size limits are given (unlikely in practice), we use the first one.
    let sizeLimits := (styleExceptions.filter (fun ex ↦ ex.path == path)).filterMap (fun errctx ↦
      match errctx.error with
      | StyleError.fileTooLong _ limit _ => some limit
      | _ => none)
    let errors :=
    if let OutputSetting.print _ := mode then
      ← lintFile path (sizeLimits.get? 0) styleExceptions
    else
      -- In "update" mode, we ignore the exceptions file (and only take `nolints` into account).
      ← lintFile path none (parseStyleExceptions nolints)
    if errors.size > 0 then
      allUnexpectedErrors := allUnexpectedErrors.append errors
      numberErrorFiles := numberErrorFiles + 1
  match mode with
  | OutputSetting.print style =>
    -- Run the remaining python linters. It is easier to just run on all files.
    -- If this poses an issue, I can either filter the output
    -- or wait until lint-style.py is fully rewritten in Lean.
    let args := if fix then #["--fix"] else #[]
    let pythonOutput ← IO.Process.run { cmd := "./scripts/print-style-errors.sh", args := args }
    if pythonOutput != "" then
      numberErrorFiles := numberErrorFiles + 1
      IO.print pythonOutput
    formatErrors allUnexpectedErrors style
    if allUnexpectedErrors.size > 0 && mode matches OutputSetting.print _ then
      IO.println s!"error: found {allUnexpectedErrors.size} new style error(s)\n\
        run `lake exe lint-style --update` to ignore all of them"
  | OutputSetting.update =>
    formatErrors allUnexpectedErrors ErrorFormat.humanReadable
    -- Regenerate the style exceptions file, including the Python output.
    IO.FS.writeFile exceptionsFilePath ""
    let pythonOutput ← IO.Process.run { cmd := "./scripts/print-style-errors.sh" }
    -- Combine style exception entries: for each new error, replace by a corresponding
    -- previous exception if that is preferred.
    let mut tweaked := allUnexpectedErrors.map fun err ↦
      if let some existing := err.find?_comparable styleExceptions then
        if let ComparisonResult.Comparable (true) := compare err existing then existing
        else err
      else err
    let thisOutput := "\n".intercalate (tweaked.map
        (fun err ↦ outputMessage err ErrorFormat.exceptionsFile)).toList
    IO.FS.writeFile exceptionsFilePath s!"{pythonOutput}{thisOutput}\n"
  return numberErrorFiles

end Mathlib.Linter.TextBased
