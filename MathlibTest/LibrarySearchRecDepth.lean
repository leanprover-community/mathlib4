import Mathlib

-- If the tests fail, adjust this number until they pass
def limit := 70

-- this should not hit a recursion limit
/--
error: `exact?` could not close the goal. Try `apply?` to see partial suggestions.
-/
#guard_msgs in
example (n : Nat) : n = eval% limit := by
  exact?

-- but it is the greatest literal not to do so
/--
error: maximum recursion depth has been reached
use `set_option maxRecDepth <num>` to increase limit
use `set_option diagnostics true` to get diagnostic information
-/
#guard_msgs in
example (n : Nat) : n = eval% (limit + 1) := by
  exact?
