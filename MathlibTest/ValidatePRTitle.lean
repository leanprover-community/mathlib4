import Mathlib.Tactic.Linter.ValidatePRTitle

/-! Tests for the PR title validation logic. -/
section title

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
  kind: subject
or
  kind(scope): subject
Allowed values for `kind` are [feat, chore, perf, refactor, style, fix, doc, test, ci]'
-/
#guard_msgs in
#check_title "fsdfs: bad title"

/--
info: Message: 'error: the PR title should be of the form
  kind: subject
or
  kind(scope): subject
Allowed values for `kind` are [feat, chore, perf, refactor, style, fix, doc, test, ci]'
-/
#guard_msgs in
#check_title "feat(test) :(confusing) bad title"

/--
info: Message: 'error: the PR title should be of the form
  kind: subject
or
  kind(scope): subject
Allowed values for `kind` are [feat, chore, perf, refactor, style, fix, doc, test, ci]'
-/
#guard_msgs in
#check_title "feat(test) : bad title"

end kind

/-- info: Message: 'error: the PR title should not be empty' -/
#guard_msgs in
#check_title "feat:"

/-- info: Message: 'error: the PR title should not be empty' -/
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

/-- info: Message: 'error: a PR's scope must not start with 'Mathlib/'' -/
#guard_msgs in
#check_title "feat(Mathlib/Algebra): title"

/-- info: Message: 'error: a PR's scope must not end with '.lean'' -/
#guard_msgs in
#check_title "feat(Algebra.lean): title"

/--
info: Message: 'error: a PR's scope should be a directory or file name, not a module name
hint: the scope contains a dot, use forward slashes instead'
-/
#guard_msgs in
#check_title "feat(Algebra.Topology): title"

/-- info: Message: 'error: a PR's scope must not contain spaces' -/
#guard_msgs in
#check_title "feat(Algebra Topology): title"

/--
info: Message: 'error: a PR's scope must not contain backslashes; use forward slashes instead'
-/
#guard_msgs in
#check_title "feat(Algebra\\Too): title"

#guard_msgs in
#check_title "feat(Algebra/Too): title"

#guard_msgs in
#check_title "doc(1000.yaml): add missing theorem"

#guard_msgs in
#check_title "doc(100.yml): add missing theorem"

#guard_msgs in
#check_title "doc(100.yml,README.md,foo.json): add missing theorem"

#guard_msgs in
#check_title "doc(README.md): fix typo"


end scope

section subject

/-- info: Message: 'error: the PR title should not end with a full stop' -/
#guard_msgs in
#check_title "feat: bad title."

/-- info: Message: 'error: the PR subject should be lowercased' -/
#guard_msgs in
#check_title "feat: My Bad Title"
-- Starting with an acronym is fine, however.
#guard_msgs in
#check_title "feat: RPC acronyms are fine"

-- This PR title is arguably not very bad (Lindelöf is a proper name),
-- a better fix is to start with a verb (which you should do anyway.)
/-- info: Message: 'error: the PR subject should be lowercased' -/
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

-- TODO: should this give a better error?
/-- info: Message: 'error: a PR's scope must not contain spaces' -/
#guard_msgs in
#check_title "feat(confusing) (forbidden): title"

#guard_msgs in
#check_title "feat: umlauts such as Lindelöf spaces are allowed"

/--
info: Message: 'error: the PR contains 2 Unicode characters which are not allowed: '⁫' (U+206b)., '⁬' (U+206c).'
-/
#guard_msgs in
#check_title "feat: title with \u206B non-allowed unicode\u206C"

end subject

/--
info: Message: 'error: a PR's scope must not start with 'Mathlib/''
---
info: Message: 'error: a PR's scope must not end with '.lean''
---
info: Message: 'error: the PR title should not end with a full stop'
---
info: Message: 'error: the PR title contains multiple consecutive spaces; please add just one'
-/
#guard_msgs in
#check_title "feat(Mathlib/Algebra.lean):  title."

end title

-- Tests for the PR description validation logic.
section description

open Lean in
/--
`#check_description desc` takes as input the `String` `desc`, expected to be a mathlib PR body.
It logs details of what the linter would report if the description is "malformed".
-/
elab "#check_description " desc:str : command => do
  let title := desc.getString
  for err in validatePRBody title false do
    logInfo m!"Message: '{err}'"

/-- info: Message: 'error: the PR description is empty' -/
#guard_msgs in
#check_description ""

/-- info: Message: 'error: the PR description is empty' -/
#guard_msgs in
#check_description "    " -- whitespace only PR bodies should also get linted

-- This description is virtually empty: just whitespace.
/-- info: Message: 'error: the PR description is empty' -/
#guard_msgs in
#check_description "\n\n---"

/-- info: Message: 'error: the PR description is empty' -/
#guard_msgs in
#check_description ".\n\n---"

/-- info: Message: 'error: there should be a blank line between the PR description and the fold' -/
#guard_msgs in
#check_description "A word\n----\n"

/-- info: Message: 'error: there should be a blank line between the PR description and the fold' -/
#guard_msgs in
#check_description "A word\n----\nSome content\nAnother fold\n"

-- Regression test against confusing errors with just a fold.
/-- info: Message: 'error: the PR description is empty' -/
#guard_msgs in
#check_description "---"

/--
info: Message: 'warning: your PR description is non-empty, but everything is after the '---' line
note: the final PR commit message only uses what is above that line'
-/
#guard_msgs in
#check_description "----\nA helpful description after the fold\n"

/-- info: Message: 'error: do not include a 'summary' header in the PR body' -/
#guard_msgs in
#check_description "## Summary\nSome other content\n"

/--
info: Message: 'error: usually, a section 'Testing plan' is superfluous (particularly if it only mentions checks done in CI anyway)
If you have done particular testing, please mention this --- but no need for the header.'
-/
#guard_msgs in
#check_description "Some actual PR body containing useful content.\n## Testing plan\nLake build passes\n"

/--
info: Message: 'error: do not include a 'summary' header in the PR body'
---
info: Message: 'error: usually, a section 'Testing plan' is superfluous (particularly if it only mentions checks done in CI anyway)
If you have done particular testing, please mention this --- but no need for the header.'
-/
#guard_msgs in
#check_description "Some actual PR body containing useful content.\n## Testing plan\n## Summary\nLake build passes\n"

-- Tests for false positives around a bug in recognising the "fold".
#guard_msgs in #check_description "First paragraph.\n\nSecond paragraph.\n"

#guard_msgs in #check_description "My description.\n\n---\n\nMeta info after the fold.\n"

end description
