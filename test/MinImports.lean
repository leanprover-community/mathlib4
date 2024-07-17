import Mathlib.Tactic.Linter.MinImports
import Mathlib.Tactic

/--
warning: Imports increased to
[Init.Guard, Lean.Parser.Term, Mathlib.Data.Int.Notation]
note: this linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
set_option linter.minImports true in
#guard (0 : ℤ) = 0

#guard_msgs in
-- no new imports needed here, so no message
set_option linter.minImports true in
#guard (0 : ℤ) = 0

set_option linter.minImports false in

#reset_min_imports

/--
warning: Imports increased to
[Init.Guard, Lean.Parser.Term, Mathlib.Data.Int.Notation]
note: this linter can be disabled with `set_option linter.minImports false`
-/
#guard_msgs in
-- again, the imports pick-up, after the reset
set_option linter.minImports true in
#guard (0 : ℤ) = 0
