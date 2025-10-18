/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

import Mathlib.Init

/-!
# Checker for well-formed title and labels
This script checks if a PR title matches mathlib's commit conventions,
and if the PR has any contradictory labels.
Not all checks from the commit conventions are implemented: for instance, no effort is made to
verify whether the title or body are written in present imperative tense.
-/

/-- Split a string in two, at a given position. Assumes `pos` is valid. -/
-- TODO: this should be added to batteries, as a version of `splitOn`
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
def validateTitle (title : String) : Array String := Id.run do
  -- The title should be of the form "abbrev: main title" or "abbrev(scope): main title".
  if !title.contains ':' then
    return #["error: the PR title does not contain a colon"]

  -- Split 'title' at the first occurrence of ':'.
  let (type, main) := splitAtPos title (title.find (· == ':'))
  let mut errors := #[]
  if main.endsWith "." then
    errors := errors.push "error: the PR title should not end with a full stop"

  let knownKinds := ["feat", "chore", "perf", "refactor", "style", "fix", "doc", "test"]
  let mut isFine := false
  for kind in knownKinds do
    if type.startsWith kind then isFine := true
  if isFine == false then
    errors := errors.push s!"error: the PR title should be of the form \
      \"kind: main title\" or \"kind(scope): main title\"\n
      Known PR title kinds are {knownKinds}"
  return errors
