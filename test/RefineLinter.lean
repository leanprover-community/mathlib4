import Mathlib.Tactic.Linter.RefineLinter

set_option linter.refine false
/--
warning: Please, use `refine` or `apply` instead of `refine'`!
note: this linter can be disabled with `set_option linter.refine false`
---
warning: Please, use `refine` or `apply` instead of `refine'`!
note: this linter can be disabled with `set_option linter.refine false`
-/
#guard_msgs in
set_option linter.refine true in
example : True := by
  refine' (by refine' .intro)
