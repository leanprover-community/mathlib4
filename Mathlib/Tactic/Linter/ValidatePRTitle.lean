/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

module

import Mathlib.Init
import Mathlib.Tactic.Linter.TextBased.UnicodeLinter
import Batteries.Data.String.Matcher

/-!
# Checker for well-formed title and labels
This script checks if a PR title matches
[mathlib's commit conventions](https://leanprover-community.github.io/contribute/commit.html).
Not all checks from the commit conventions are implemented: for instance, no effort is made to
verify whether the title or body are written in present imperative tense.
-/

open Std.Internal.Parsec String

/-- Basic parser for PR titles: given a title `kind(scope): main title` or `kind: title`,
extracts the `kind`, `scope` and `main title` components. -/
def prTitle : Parser (String × Option String × String) := do
  let kind ←
    ["feat", "chore", "perf", "refactor", "style", "fix", "doc", "test", "ci"].firstM pstring
  let scope ← (
      (skipString "(" *> some <$> manyChars (notFollowedBy (skipString "):") *> any)
        <* skipString "):" <* ws)
      <|> (skipString ":" *> ws *> pure none)
    )
  let mainTitle ← manyChars any
  return (kind, scope, mainTitle)

-- Some self-tests for the parser.

/-- info: Except.ok ("feat", some "x", "") -/
#guard_msgs in
#eval Parser.run prTitle "feat(x):"
/-- info: Except.ok ("feat", some "x", "") -/
#guard_msgs in
#eval Parser.run prTitle "feat(x): "

/-- info: Except.ok ("feat", some "x", "foo") -/
#guard_msgs in
#eval Parser.run prTitle "feat(x): foo"
/-- info: Except.ok ("feat", none, "foo") -/
#guard_msgs in
#eval Parser.run prTitle "feat: foo"
/-- info: Except.error "offset 10: expected: ):" -/
#guard_msgs in
#eval Parser.run prTitle "feat(: foo"
/-- info: Except.error "offset 4: expected: :" -/
#guard_msgs in
#eval Parser.run prTitle "feat): foo"
/-- info: Except.error "offset 4: expected: :" -/
#guard_msgs in
#eval Parser.run prTitle "feat)(: foo"
/-- info: Except.error "offset 4: expected: :" -/
#guard_msgs in
#eval Parser.run prTitle "feat)(sdf): foo"
/-- info: Except.ok ("feat", some "sdf", "foo:") -/
#guard_msgs in
#eval Parser.run prTitle "feat(sdf): foo:"
/-- info: Except.error "offset 4: expected: :" -/
#guard_msgs in
#eval Parser.run prTitle "feat foo"
/-- info: Except.ok ("chore", none, "test") -/
#guard_msgs in
#eval Parser.run prTitle "chore: test"

/--
Check if `word` looks like an abbreviation, like `JSON` or `E2` or `W3C`.
-/
def isAbbreviation (word : String.Slice) : Bool :=
  word.all (fun c => c.isUpper || c.isDigit) && word.chars.length != 1

open Mathlib.Linter.TextBased in
/--
Check if `title` matches the mathlib conventions for PR titles
(documented at <https://leanprover-community.github.io/contribute/commit.html>).

Not all checks are implemented: for instance, no effort is made to verify if the title or body
are written in present imperative tense.
Return all error messages for violations found.
-/
public def validateTitle (title : String) : Array String := Id.run do
  -- The title should be of the form "abbrev: subject" or "abbrev(scope): subject".
  -- We use the parser above to extract abbrev, scope and PR subject,
  -- but give some custom errors in some easily detectable cases.
  if !title.contains ':' then
    return #["error: the PR title does not contain a colon"]
  let mut errors : Array String := #[]
  if title.startsWith " " then
    errors := #["error: the PR title starts with a space"]

  let knownKinds := ["feat", "chore", "perf", "refactor", "style", "fix", "doc", "test", "ci"]
  match Parser.run prTitle title.trimAsciiStart.copy with
  | Except.error _ =>
    return errors.push s!"error: the PR title should be of the form\n  kind: subject\n\
      or\n  kind(scope): subject\nAllowed values for `kind` are {knownKinds}"
  | Except.ok (_kind, scope?, subject) =>
    if subject.isEmpty then
      errors := errors.push s!"error: the PR title should not be empty"
    if let some scope := scope? then
      if scope.startsWith "Mathlib/" then
        errors := errors.push s!"error: a PR's scope must not start with 'Mathlib/'"
      if scope.contains " " then
        errors := errors.push s!"error: a PR's scope must not contain spaces"
      if scope.contains "\\" then
        errors := errors.push
          s!"error: a PR's scope must not contain backslashes; use forward slashes instead"
      if scope.endsWith ".lean" then
        errors := errors.push s!"error: a PR's scope must not end with '.lean'"
      else if scope.contains '.' then
        -- Exception: file endings `.md`, `.yml`, `.yaml` are fine.
        let extensions := #["bib", "json", "md", "py", "sh", "toml", "txt", "yaml", "yml"]
        let allOccurrences := scope.count '.'
        let mut recognised := 0
        for ext in extensions do
          if recognised == allOccurrences then break
          recognised := recognised + (scope.findAllSubstr ("." ++ ext)).size
        if scope.count '.' != recognised then
          errors := errors.push s!"error: a PR's scope should be a directory or file name, \
            not a module name\nhint: the scope contains a dot, use forward slashes instead"
      -- Future: we could check if `scope` describes a directory that actually exist.
      -- Should we allow special syntax such as `Data/*/Basic` or `{Set,Group}Theory`?

    -- Titles should be lower-cased (but we allow abbreviations).
    if subject.front.toLower != subject.front then
      let firstWord := subject.takeWhile (!·.isWhitespace)
      if !isAbbreviation firstWord then
        errors := errors.push "error: the PR subject should be lowercased"
    if subject.endsWith "." then
      errors := errors.push "error: the PR title should not end with a full stop"
    else if subject.endsWith " " then
      errors := errors.push "error: the PR title should not end with a space"
    if title.contains "  " then
      errors := errors.push
        "error: the PR title contains multiple consecutive spaces; please add just one"
    if title.contains "\t" then
      errors := errors.push
        "error: the PR title contains a tab; please use single spaces instead"
    -- Check for unicode characters which are not allowed: we don't want direction-changing
    -- characters, invisible spaces or so (for example). We re-use the code in the Unicode linter.
    let badChars := title.chars.filter (fun c ↦ !UnicodeLinter.isAllowedCharacter c && c != '\t')
    if !badChars.isEmpty then
      let err := ", ".intercalate <| badChars.map
        (fun c ↦ s!"'{c}' ({UnicodeLinter.Char.printCodepointHex c}).")|>.toList
      errors := errors.push s!"error: the PR contains {badChars.length} Unicode characters \
        which are not allowed: {err}"
    return errors
