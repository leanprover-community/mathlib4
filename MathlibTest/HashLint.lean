module

import Batteries.Tactic.Lint
import Mathlib.Init

/-! Checks that a basic `#lint` works. -/

/--
info: -- Found 0 errors in 0 declarations (plus 0 automatically generated ones) in the current file with 16 linters


-- All linting checks passed!
-/
#guard_msgs in
#lint
