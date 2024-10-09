import Mathlib.Tactic.Linter.RefineLinter

set_option linter.refine false
/--
warning:
The `refine'` tactic is discouraged: please strongly consider using `refine` or `apply` instead.
note: this linter can be disabled with `set_option linter.refine false`
---
warning:
The `refine'` tactic is discouraged: please strongly consider using `refine` or `apply` instead.
note: this linter can be disabled with `set_option linter.refine false`
-/
#guard_msgs in
set_option linter.refine true in
example : True := by
  refine' (by refine' .intro)
