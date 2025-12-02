/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/

module

import Mathlib.Init
import Std.Internal.Parsec.String

/-!
# Checker for well-formed title and labels
This script checks if a PR title matches
[mathlib's commit conventions](https://leanprover-community.github.io/contribute/commit.html).
Not all checks from the commit conventions are implemented: for instance, no effort is made to
verify whether the title or body are written in present imperative tense.
-/

open Std.Internal.Parsec String

/-- Basic parser for PR titles: given a title `feat(scope): main title` or `feat: title`,
extracts the `feat` and `scope` components. In the future, this will be extended to also parse
the main PR title. -/
-- TODO: also parse and return the main PR title
def prTitle : Parser (String × Option String) :=
  Prod.mk
    <$> (["feat", "chore", "perf", "refactor", "style", "fix", "doc", "test", "ci"].firstM pstring)
    <*> (
      (skipString "(" *> some <$> manyChars (notFollowedBy (skipString "):") *> any)
        <* skipString "): ")
      <|> (skipString ": " *> pure none)
    )

-- Some self-tests for the parser.
/-- info: Except.ok ("feat", some "x") -/
#guard_msgs in
#eval Parser.run prTitle "feat(x): foo"
/-- info: Except.ok ("feat", none) -/
#guard_msgs in
#eval Parser.run prTitle "feat: foo"
/-- info: Except.error "offset 10: expected: ): " -/
#guard_msgs in
#eval Parser.run prTitle "feat(: foo"
/-- info: Except.error "offset 4: expected: : " -/
#guard_msgs in
#eval Parser.run prTitle "feat): foo"
/-- info: Except.error "offset 4: expected: : " -/
#guard_msgs in
#eval Parser.run prTitle "feat)(: foo"
/-- info: Except.error "offset 4: expected: : " -/
#guard_msgs in
#eval Parser.run prTitle "feat)(sdf): foo"
/-- info: Except.ok ("feat", some "sdf") -/
#guard_msgs in
#eval Parser.run prTitle "feat(sdf): foo:"
/-- info: Except.error "offset 4: expected: : " -/
#guard_msgs in
#eval Parser.run prTitle "feat foo"
/-- info: Except.ok ("chore", none) -/
#guard_msgs in
#eval Parser.run prTitle "chore: test"

/--
Check if `title` matches the mathlib conventions for PR titles
(documented at <https://leanprover-community.github.io/contribute/commit.html>).

Not all checks are implemented: for instance, no effort is made to verify if the title or body
are written in present imperative tense.
Return all error messages for violations found.
-/
public def validateTitle (title : String) : Array String := Id.run do
  -- The title should be of the form "abbrev: main title" or "abbrev(scope): main title".
  -- We use the parser above to extract abbrev and scope ignoring the main title,
  -- but give some custom errors in some easily detectable cases.
  if !title.contains ':' then
    return #["error: the PR title does not contain a colon"]

  match Parser.run prTitle title with
  | Except.error _ =>
    return #[s!"error: the PR title should be of the form\n  abbrev: main title\nor\n  \
      abbrev(scope): main title"]
  | Except.ok (kind, _scope?) =>
    -- Future: also check scope (and the main PR title)
    let mut errors := #[]
    let knownKinds := ["feat", "chore", "perf", "refactor", "style", "fix", "doc", "test", "ci"]
    let mut isFine := false
    for k in knownKinds do
      isFine := isFine || kind.startsWith k
    if isFine == false then
      errors := errors.push s!"error: the PR title should be of the form \
        \"kind: main title\" or \"kind(scope): main title\"\n
        Known PR title kinds are {knownKinds}"
    return errors
