# Universal cover — deferred review items

This file records review items raised during a self-review of the
universal-cover construction (PR #38292) against `mathlib-standards.md`,
deferred to a follow-up PR. The corresponding "fix-now" items have already
been addressed on this branch.

## Style and abstraction

- **Brittle `simpa` chains.** `BasedPath.lean` contains roughly twenty
  `simpa [endpoint, ofPath, …]`-style invocations with explicit unfold
  lists. These break under minor refactor. Replace with a small dedicated
  `@[simp]` set characterising `endpoint` and `ofPath`.
