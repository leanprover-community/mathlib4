import Mathlib

-- We verify that `exact?` copes with all of Mathlib.
-- On `v4.7.0-rc1` this revealed a cache corruption problem.

#guard_msgs
example : 0 < 1 := by exact?
