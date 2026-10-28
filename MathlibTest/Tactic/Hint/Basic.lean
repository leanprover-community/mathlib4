module

public import Mathlib.Tactic.Hint

/--
error: No suggestions available
-/
#guard_msgs in
example (h : 1 < 0) : False := by hint

register_hint 1000 trivial
/--
info: Try these:
  [apply] 🎉️ trivial
-/
#guard_msgs in
example (h : 1 < 0) : False := by hint

register_hint 1001 contradiction
/--
info: Try these:
  [apply] 🎉️ contradiction
-/
#guard_msgs in
example (h : 1 < 0) : False := by hint

register_hint 999 exact?
/--
info: Try these:
  [apply] 🎉️ contradiction
-/
#guard_msgs in
example (h : 1 < 0) : False := by hint

register_hint 1002 exact?
/--
info: Try these:
  [apply] 🎉️ exact Nat.not_succ_le_zero 1 h
-/
#guard_msgs in
example (h : 1 < 0) : False := by hint
