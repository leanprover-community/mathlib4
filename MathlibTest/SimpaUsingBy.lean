import Mathlib.Tactic.Linter.SimpaUsingBy
import Mathlib.Data.Nat.Notation

set_option linter.style.simpaUsingBy true

/--
warning: Please replace `simpa [foo] using by <tactic>` with `simp [foo]; <tactic>`.

Note: This linter can be disabled with `set_option linter.style.simpaUsingBy false`
-/
#guard_msgs in
example (a b : ℕ): b + a = a + b := by simpa using by lia
