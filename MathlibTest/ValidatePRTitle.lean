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
#check_title ""

/-- info: Message: 'error: the PR title does not contain a colon' -/
#guard_msgs in
#check_title "my short PR title"

section kind

/--
info: Message: 'error: the PR title should be of the form
  kind: main title
or
  kind(scope): main title
Allowed values for `kind` are [feat, chore, perf, refactor, style, fix, doc, test, ci]'
-/
#guard_msgs in
#check_title "fsdfs: bad title"

/--
info: Message: 'error: the PR title should be of the form
  kind: main title
or
  kind(scope): main title
Allowed values for `kind` are [feat, chore, perf, refactor, style, fix, doc, test, ci]'
-/
#guard_msgs in
#check_title "feat(test) :(confusing) bad title"

/--
info: Message: 'error: the PR title should be of the form
  kind: main title
or
  kind(scope): main title
Allowed values for `kind` are [feat, chore, perf, refactor, style, fix, doc, test, ci]'
-/
#guard_msgs in
#check_title "feat(test) : bad title"

end kind

-- TODO: can this error message be more informative?
/--
info: Message: 'error: the PR title should be of the form
  kind: main title
or
  kind(scope): main title
Allowed values for `kind` are [feat, chore, perf, refactor, style, fix, doc, test, ci]'
-/
#guard_msgs in
#check_title "feat:"

-- TODO: can this error message be more informative?
/--
info: Message: 'error: the PR title should be of the form
  kind: main title
or
  kind(scope): main title
Allowed values for `kind` are [feat, chore, perf, refactor, style, fix, doc, test, ci]'
-/
#guard_msgs in
#check_title "feat: "

/--
info: Message: 'error: the PR title starts with a space'
---
info: Message: 'error: the PR title contains multiple consecutive spaces; please add just one'
-/
#guard_msgs in
#check_title "    feat: some PR title"

section scope

/-- info: Message: 'error: the PR scope must not start with 'Mathlib/'' -/
#guard_msgs in
#check_title "feat(Mathlib/Algebra): title"

/-- info: Message: 'error: a PR's scope must not end with '.lean'' -/
#guard_msgs in
#check_title "feat(Algebra.lean): title"

end scope

section mainTitle

/-- info: Message: 'error: the PR title should not end with a full stop' -/
#guard_msgs in
#check_title "feat: bad title."

/-- info: Message: 'error: the main PR title should be lowercased' -/
#guard_msgs in
#check_title "feat: My Bad Title"
-- Starting with an acronym is fine, however.
#guard_msgs in
#check_title "feat: RPC acronyms are fine"

-- This PR title is arguable not very bad (Lindelöf is a proper name),
-- a better fix is to start with a verb (which you should do anyway.)
/-- info: Message: 'error: the main PR title should be lowercased' -/
#guard_msgs in
#check_title "feat: Lindelöf spaces something something"

#guard_msgs in
#check_title "feat: add lemmas about Lindelöf spaces"

-- Tabs in PR titles are banned.
/-- info: Message: 'error: the PR title contains a tab; please use single spaces instead' -/
#guard_msgs in
#check_title "feat: PR title with a \t tab"

/-- info: Message: 'error: the PR title contains a tab; please use single spaces instead' -/
#guard_msgs in
#check_title "feat(\t): RPC acronyms are fine"

/--
info: Message: 'error: the PR title should not end with a full stop'
---
info: Message: 'error: the PR title contains multiple consecutive spaces; please add just one'
-/
#guard_msgs in
#check_title "chore: bad   Title."

/-- info: Message: 'error: the PR title starts with a space' -/
#guard_msgs in
#check_title " feat: bad title"

-- Brackets in the PR title are allowed.
#guard_msgs in
#check_title "feat: (confusing) but legal title"

/-- info: Message: 'error: the PR title does not contain a colon' -/
#guard_msgs in
#check_title "feat(test) (confusing) bad title"

-- TODO: should this error?
#guard_msgs in
#check_title "feat(confusing) (forbidden): title"

#guard_msgs in
#check_title "feat: umlauts such as Lindelöf spaces are allowed"

/--
info: Message: 'error: the PR contains 2 Unicode characters which are not allowed: '⁫' (U+206b)., '⁬' (U+206c).'
-/
#guard_msgs in
#check_title "feat: title with \u206B non-allowed unicode\u206C"

end mainTitle

/--
info: Message: 'error: the PR scope must not start with 'Mathlib/''
---
info: Message: 'error: a PR's scope must not end with '.lean''
---
info: Message: 'error: the PR title should not end with a full stop'
---
info: Message: 'error: the PR title contains multiple consecutive spaces; please add just one'
-/
#guard_msgs in
#check_title "feat(Mathlib/Algebra.lean):  title."
