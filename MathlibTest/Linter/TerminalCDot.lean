module

import Mathlib.Init

/--
warning: Unnecessary focusing dot `·`: you should be able to remove it, or move it earlier up in the proof, as necessary.

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
warning: Unnecessary focusing dot `·`: you should be able to remove it, or move it earlier up in the proof, as necessary.

Note: This linter can be disabled with `set_option linter.style.terminalCDot false`
-/
#guard_msgs in
example : True := by
  · trivial

/--
warning: Unnecessary focusing dot `·`: you should be able to remove it, or move it earlier up in the proof, as necessary.

Note: This linter can be disabled with `set_option linter.style.terminalCDot false`
---
warning: Unnecessary focusing dot `·`: you should be able to remove it, or move it earlier up in the proof, as necessary.

Note: This linter can be disabled with `set_option linter.style.terminalCDot false`
-/
#guard_msgs in
example : True := by
  · · exact .intro

-- Multiple focus dots in a row is allowed.
example (n : Nat) : True := by
  by_cases hn : n > 2
  · trivial
  · trivial
