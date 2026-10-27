module

import Mathlib.Init

/--
warning: Unnecessary focusing dot `·`: you should be able to remove it.
If this `·` follows a `<;>` combinator, consider using `all_goals` instead of `<;>`.

Note: This linter can be disabled with `set_option linter.style.terminalCDot false`
-/
#guard_msgs in
-- Test linting for superfluous focusing dots.
example : 1 = 1 ∧ 1 = 1 ∧ 1 = 1 := by
  refine ?_
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

/--
warning: Unnecessary focusing dot `·`: you should be able to remove it.
If this `·` follows a `<;>` combinator, consider using `all_goals` instead of `<;>`.

Note: This linter can be disabled with `set_option linter.style.terminalCDot false`
-/
#guard_msgs in
example : True := by
  · trivial

/--
warning: Unnecessary focusing dot `·`: you should be able to remove it.
If this `·` follows a `<;>` combinator, consider using `all_goals` instead of `<;>`.

Note: This linter can be disabled with `set_option linter.style.terminalCDot false`
---
warning: Unnecessary focusing dot `·`: you should be able to remove it.
If this `·` follows a `<;>` combinator, consider using `all_goals` instead of `<;>`.

Note: This linter can be disabled with `set_option linter.style.terminalCDot false`
-/
#guard_msgs in
example : True := by
  · · exact .intro

/--
warning: Unnecessary focusing dot `·`: you should be able to remove it.
If this `·` follows a `<;>` combinator, consider using `all_goals` instead of `<;>`.

Note: This linter can be disabled with `set_option linter.style.terminalCDot false`
---
warning: Unnecessary focusing dot `·`: you should be able to remove it.
If this `·` follows a `<;>` combinator, consider using `all_goals` instead of `<;>`.

Note: This linter can be disabled with `set_option linter.style.terminalCDot false`
-/
#guard_msgs in
example : True ∧ True := by
  constructor
  all_goals
  · simp

/--
warning: Unnecessary focusing dot `·`: you should be able to remove it.
If this `·` follows a `<;>` combinator, consider using `all_goals` instead of `<;>`.

Note: This linter can be disabled with `set_option linter.style.terminalCDot false`
---
warning: Unnecessary focusing dot `·`: you should be able to remove it.
If this `·` follows a `<;>` combinator, consider using `all_goals` instead of `<;>`.

Note: This linter can be disabled with `set_option linter.style.terminalCDot false`
-/
#guard_msgs in
example : True ∧ True := by
  constructor <;>
    · simp

-- Multiple focus dots in a row is allowed.
example (n : Nat) : True := by
  by_cases hn : n > 2
  · trivial
  · trivial

-- A focus dot that looks terminal but isn't is allowed
example : True ∧ True := by
  constructor
  (· simp)
  simp

-- A terminal focus dot is allowed when it actually focuses.
example (p : Nat → Prop) (h0 : p 0) : ∃ n, p n := by
  constructor
  · apply h0

-- We don't lint redundant non-terminal focus dots,
-- because then the unused tactic linter is triggered anyways.
/--
warning: Unused tactic linter: `skip` does nothing.

Note: This linter can be disabled with `set_option linter.unusedTactic false`
-/
#guard_msgs in
example : True := by
  · exact .intro
  skip
