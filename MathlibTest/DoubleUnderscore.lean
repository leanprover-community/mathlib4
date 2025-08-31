import Mathlib.Tactic.Linter.Style

set_option linter.style.nameCheck true
variable (n : Nat)

-- this notation generates the declaration `«term__,»` that has a double underscore,
-- but is allowed by `linter.style.nameCheck`.
notation "_" n "," => Nat.succ n

/-- info: `«term__,» : Lean.Name -/
#guard_msgs in
#check `«term__,»

/--
warning: The declaration 'double__underscore' contains '__', which does not follow the mathlib naming conventions. Consider using single underscores instead.
note: this linter can be disabled with `set_option linter.style.nameCheck false`
-/
#guard_msgs in
def double__underscore : Unit := ()
