module
import Mathlib.Tactic.Linter.Style

set_option linter.style.show true

-- Check that messages appear when errors with synthetic `sorry` occur

/-- error: Unknown identifier `arbitrary_ident` -/
#guard_msgs in
example : False := by show arbitrary_ident
