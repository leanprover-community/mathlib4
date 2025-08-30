import Mathlib.Tactic.Linter.ValidatePRTitle

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

-- Enable if/when we decide to enforce lower-cased titles.
-- /-- info: Message: 'error: the main PR title should be lowercased' -/
-- #guard_msgs in
-- #check_title "feat: My Bad Title"

-- Acronyms are valid PR titles, in any case.
#guard_msgs in
#check_title "feat: RPC acronyms are fine"

/--
info: Message: 'error: the PR title should not end with a full stop'
---
info: Message: 'error: the PR title contains multiple consecutive spaces; please add just one'
-/
#guard_msgs in
#check_title "chore: bad   Title."

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
info: Message: 'error: the PR type should not end with a space'
-/
#guard_msgs in
#check_title "feat(test) :(confusing) bad title"

/-- info: Message: 'error: the PR type should not end with a space' -/
#guard_msgs in
#check_title "feat(test) : bad title"

/-- info: Message: 'error: the PR type should be of the form abbrev(scope)' -/
#guard_msgs in
#check_title "feat(test) more things: bad title"

/--
info: Message: 'error: the PR title should not end with a full stop'
---
info: Message: 'error: the PR title contains multiple consecutive spaces; please add just one'
-/
#guard_msgs in
#check_title "chore: bad   Title."

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
