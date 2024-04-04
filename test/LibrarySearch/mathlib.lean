import Mathlib

-- We verify that `exact?` copes with all of Mathlib.
-- On `v4.7.0-rc1` this revealed a cache corruption problem.

/-- info: Try this: exact Nat.zero_lt_one -/
#guard_msgs in
example : 0 < 1 := by exact?
