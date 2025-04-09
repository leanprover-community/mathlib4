import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linter.DeprecatedSyntaxLinter

set_option linter.style.refine true
/--
warning:
The `refine'` tactic is discouraged: please strongly consider using `refine` or `apply` instead.
note: this linter can be disabled with `set_option linter.style.refine false`
---
warning:
The `refine'` tactic is discouraged: please strongly consider using `refine` or `apply` instead.
note: this linter can be disabled with `set_option linter.style.refine false`
-/
#guard_msgs in
example : True := by
  refine' (by refine' .intro)

set_option linter.style.refine false
-- This is quiet because `linter.style.refine` is now false
example : True := by
  refine' (by refine' .intro)

set_option linter.style.cases true
/--
warning: The `cases'` tactic is discouraged: please strongly consider using `obtain`, `rcases` or `cases` instead.
note: this linter can be disabled with `set_option linter.style.cases false`
---
warning: The `cases'` tactic is discouraged: please strongly consider using `obtain`, `rcases` or `cases` instead.
note: this linter can be disabled with `set_option linter.style.cases false`
-/
#guard_msgs in
example (a : (True ∨ True) ∨ (True ∨ True)): True := by
  cases' a with b b <;> cases' b <;> trivial

set_option linter.style.cases false
-- This is quiet because `linter.style.cases` is now false
example (a : (True ∨ True) ∨ (True ∨ True)): True := by
  cases' a with b b <;> cases' b <;> trivial
