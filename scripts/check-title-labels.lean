/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Cli.Basic
import Batteries.Data.HashMap
import Batteries.Data.String.Matcher

/-!
# Checker for well-formed title and labels

This script checks if a PR title matches mathlib's commit conventions,
and if the PR has any contradictory labels.
Not all checks from the commit conventions are implemented: for instance, no effort is made to
verify whether the title or body are written in present imperative tense.
-/

/-- Split a string in two, at a given position. Assumes `pos` is valid. -/
-- FIXME: this should be added to batteries, as a version of "splitOn"
def splitAtPos (s : String) (pos : String.Pos) : String × String :=
  let before := s.extract 0 pos
  let after := s.extract (s.next pos) s.endPos
  (before, after)

/--
Check if `title` matches the mathlib conventions for PR titles
(documented at https://leanprover-community.github.io/contribute/commit.html).
Not all checks are implemented: for instance, no effort is made to verify if the title or body
are written in present imperative tense.

Return all error messages for violations found.
-/
def validateTitle (title: String) : Array String := Id.run do
  -- The title should be of the form "abbrev: main title" or "abbrev(scope): main title".
  if !title.contains ':' then
    return #["error: the PR title does not contain a colon"]

  -- Split 'title' at the first occurrence of ':'.
  let (type, main) := splitAtPos title (title.find (· == ':'))
  let mut errors := #[]
  if main.endsWith "." then
    errors := errors.push "error: the PR title should not end with a full stop"

  if main.front != ' ' then
    errors := errors.push "error: the PR should have the form 'abbrev: main title', with a space"
  else if main.containsSubstr "  " then
    errors := errors.push "error: the PR title contains multiple consecutive spaces; please add just one"
  let main := main.removeLeadingSpaces
  if main.front.toLower != main.front then
    errors := errors.push "error: the main PR title should be lowercased"

  -- `type` should be of the form abbrev or abbrev(scope), where `scope` is of the form
  -- `Algebra/Basic`, without a leading `Mathlib` or a trailing `.lean`
  let N := (type.splitOn "(").length
  let M := (type.splitOn ")").length
  let known_types := ["feat", "chore", "perf", "refactor", "style", "fix", "doc", "test"]
  if (N, M) == (1, 1) then
    if !known_types.contains type then
      errors := errors.push s!"error: the PR type should be one of {", ".intercalate (known_types.map (s!"\"{·}\""))}"
  else if (N, M) == (2, 2) then
    if !type.endsWith ")" then
      errors := errors.push s!"error: the PR type should be of the form abbrev(scope)"
    let idx := type.find (· == '(')
    let idx2 := type.find (· == ')')
    if idx2 < idx then
      errors := errors.push "error: mismatched parentheses; the PR type should be of the form abbrev(scope)"
    let (type, scope) := (splitAtPos type idx)
    let scope := scope.dropRight 1
    if !known_types.contains type then
      errors := errors.push s!"error: the PR type should be one of {", ".intercalate (known_types.map (s!"\"{·}\""))}"
    if scope.startsWith "Mathlib/" then
      errors := errors.push s!"error: the PR scope must not start with 'Mathlib/'"
    if scope.endsWith ".lean" then
      errors := errors.push s!"error: a PR's scope must not end with '.lean'"
    -- Future: we could further validate the scope, that this is a valid module or directory
  else
    errors := errors.push "error: the PR type should be of the form abbrev or abbrev(scope)"
  return errors


/--
Check if a combination of PR labels is considered contradictory.
`labels` contains the names of this PR's labels.
-/
def hasContradictoryLabels (labels : Array String) : Bool := Id.run do
  -- Combine common labels.
  let substitutions := [
    ("ready-to-merge", "bors"), ("auto-merge-after-CI", "bors"),
    ("blocked-by-other-PR", "blocked"), ("blocked-by-core-PR", "blocked"),
    ("blocked-by-batt-PR", "blocked"), ("blocked-by-qq-PR", "blocked"),
  ]
  let mut canonicalise : Std.HashMap String String := .ofList substitutions
  let normalised_labels := labels.map fun label ↦ (canonicalise.getD label label)
  -- Test for contradictory label combinations.
  if normalised_labels.contains "awaiting-review-DONT-USE" then
    return true
  else if normalised_labels.contains "bors" &&
      ["awaiting-CI", "awaiting-zulip", "WIP"].any normalised_labels.contains then
    return true
  else if normalised_labels.contains "awaiting-zulip" &&
      ["delegated", "awaiting-zulip"].all normalised_labels.contains then
    return true
  else
    return false


open Cli in
/-- Implementation of the `check-title-labels` command line program.
The exit code is the number of violations found. -/
def checkTitleLabelsCLI (args : Parsed) : IO UInt32 := do
  let title := (args.positionalArg! "title").value
  let labels : Array String := args.variableArgsAs! String
  let mut numberErrors := 0
  if !labels.contains "WIP" then
    -- We do not complain about WIP PRs.
    -- The title should be of the form "abbrev: main title" or "abbrev(scope): main title".
    let titleErrors := validateTitle title
    for err in titleErrors do
      IO.println err
      numberErrors := numberErrors + 1
    -- TODO: can I use this, with some casting?
    -- numberErrors := numberErrors + titleErrors.size
    -- A feature PR should have a topic label.
    if title.startsWith "feat" && !labels.any
        (fun s ↦ s.startsWith "t-" || ["CI", "IMO"].contains s) then
      IO.println "error: feature PRs should have a 't-something' or the 'CI' label"
      numberErrors := numberErrors + 1
  -- Check for contradictory labels.
  if hasContradictoryLabels labels then
    IO.println "error: PR labels are contradictory"
    numberErrors := numberErrors + 1
  return numberErrors


open Cli in
/-- Setting up command line options and help text for `lake exe check-title-labels`. -/
def checkTitleLabels : Cmd := `[Cli|
  «check-title-labels» VIA checkTitleLabelsCLI; ["0.0.1"]
  "Check that a PR title matches the formatting requirements.
  If this PR is a feature PR, also verify that it has a topic label,
  and that there are no contradictory labels."

  ARGS:
    title : String; "this PR's title"
    ...labels : Array String; "list of label names of this PR"
]

/-- The entrypoint to the `lake exe check-title-labels` command. -/
def main (args : List String) : IO UInt32 := checkTitleLabels.validate args

-- Tests for the PR title validation logic.
open Lean in
/--
`#check_title title` takes as input the `String` `title`, expected to be a mathlib PR title.
It logs details of what the linter would report if the `title` is "malformed".
-/
elab "#check_title " title:str : command => do
  let title := title.getString
  for err in validateTitle title do
    logInfo m!"Message: '{err}'"

-- two well-formed examples
#guard_msgs in
#check_title "feat: my short PR title"

#guard_msgs in
#check_title "feat(Algebra): my short PR title"

/-- info: Message: 'error: the PR title does not contain a colon' -/
#guard_msgs in
#check_title "my short PR title"

/--
info: Message: 'error: the PR type should be one of "feat", "chore", "perf", "refactor", "style", "fix", "doc", "test"'
-/
#guard_msgs in
#check_title "fsdfs: bad title"

/-- info: Message: 'error: the PR title should not end with a full stop' -/
#guard_msgs in
#check_title "feat: bad title."

/-- info: Message: 'error: the main PR title should be lowercased' -/
#guard_msgs in
#check_title "feat: My Bad Title"

/--
info: Message: 'error: the PR title should not end with a full stop'
---
info: Message: 'error: the PR title contains multiple consecutive spaces; please add just one'
---
info: Message: 'error: the main PR title should be lowercased'
-/
#guard_msgs in
#check_title "chore: Bad   Title."

/--
info: Message: 'error: the PR type should be one of "feat", "chore", "perf", "refactor", "style", "fix", "doc", "test"'
-/
#guard_msgs in
#check_title " feat: bad title"

-- Brackets in the PR title are allowed.
#guard_msgs in
#check_title "feat: (confusing) but legal title"

/-- info: Message: 'error: the PR title does not contain a colon' -/
#guard_msgs in
#check_title "feat(test) (confusing) bad title"

/-- info: Message: 'error: the PR type should be of the form abbrev or abbrev(scope)' -/
#guard_msgs in
#check_title "feat(confusing) (forbidden): title"

/--
info: Message: 'error: the PR should have the form 'abbrev: main title', with a space'
---
info: Message: 'error: the PR type should be of the form abbrev(scope)'
-/
#guard_msgs in
#check_title "feat(test) :(confusing) bad title"

/-- info: Message: 'error: the PR type should be of the form abbrev(scope)' -/
#guard_msgs in
#check_title "feat(test) : (confusing) bad title"

/-- info: Message: 'error: the main PR title should be lowercased' -/
#guard_msgs in
#check_title "feat: My Bad Title"

/--
info: Message: 'error: the PR title should not end with a full stop'
---
info: Message: 'error: the PR title contains multiple consecutive spaces; please add just one'
---
info: Message: 'error: the main PR title should be lowercased'
-/
#guard_msgs in
#check_title "chore: Bad   Title."

/--
info: Message: 'error: the PR type should be one of "feat", "chore", "perf", "refactor", "style", "fix", "doc", "test"'
-/
#guard_msgs in
#check_title "  feat: bad title"

/-- info: Message: 'error: the PR scope must not start with 'Mathlib/'' -/
#guard_msgs in
#check_title "feat(Mathlib/Algebra): title"

/-- info: Message: 'error: a PR's scope must not end with '.lean'' -/
#guard_msgs in
#check_title "feat(Algebra.lean): title"

/--
info: Message: 'error: the PR title should not end with a full stop'
---
info: Message: 'error: the PR title contains multiple consecutive spaces; please add just one'
---
info: Message: 'error: the PR scope must not start with 'Mathlib/''
---
info: Message: 'error: a PR's scope must not end with '.lean''
-/
#guard_msgs in
#check_title "feat(Mathlib/Algebra.lean):  title."
