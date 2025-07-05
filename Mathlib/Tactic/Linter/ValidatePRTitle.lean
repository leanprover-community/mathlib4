/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

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
  -- Titles should be lower-cased: we don't enforce this for now.
  -- let main := main.removeLeadingSpaces
  -- if main.front.toLower != main.front then
  --  errors := errors.push "error: the main PR title should be lowercased"

  -- `type` should be of the form abbrev or abbrev(scope), where `scope` is of the form
  -- `Algebra/Basic`, without a leading `Mathlib` or a trailing `.lean`
  let N := (type.splitOn "(").length
  let M := (type.splitOn ")").length
  let known_types := ["feat", "chore", "perf", "refactor", "style", "fix", "doc", "test"]
  if (N, M) == (1, 1) then
    if !known_types.contains type then
      errors := errors.push s!"error: the PR type should be one of {", ".intercalate (known_types.map (s!"\"{·}\""))}"
  else if (N, M) == (2, 2) then
    let idx := type.find (· == '(')
    let idx2 := type.find (· == ')')
    if idx2 < idx then
      errors := errors.push "error: mismatched parentheses; the PR type should be of the form abbrev(scope)"
    else if !type.endsWith ")" then
      if type.back.isWhitespace then
        errors := errors.push s!"error: the PR type should not end with a space"
      else
        errors := errors.push s!"error: the PR type should be of the form abbrev(scope)"
    let (type, scope) := (splitAtPos type idx)
    let scope := scope.dropRight 1
    if !known_types.contains type then
      errors := errors.push s!"error: the PR type should be one of {", ".intercalate (known_types.map (s!"\"{·}\""))}"
    if scope.startsWith "Mathlib/" then
      errors := errors.push s!"error: the PR scope must not start with 'Mathlib/'"
    if scope.endsWith ".lean" then
      errors := errors.push s!"error: a PR's scope must not end with '.lean'"
    -- Disabling this for now, to reduce warning fatigue. Might enable this in the future.
    -- if scope.contains '.' then
    --  errors := errors.push s!"error: a PR's scope should be a directory, not a module"
    -- Future: we could check if `scope` describes a directory that actually exist.
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
  else if ["delegated", "awaiting-zulip"].all normalised_labels.contains then
    return true
  else
    return false
