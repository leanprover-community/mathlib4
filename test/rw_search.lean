import Mathlib.Tactic.RewriteSearch

set_option autoImplicit true

-- You can enable tracing of the `rw_search` algorithm using
-- set_option trace.rw_search true

/-- info: Try this: rw [@List.length_append, Nat.add_comm] -/
#guard_msgs in
example (xs ys : List α) : (xs ++ ys).length = ys.length + xs.length := by
  rw_search

/-- info: Try this: rw [← @add_rotate, ← vadd_eq_add, ← @add_rotate, @add_right_comm] -/
#guard_msgs in
example [AddCommMonoid α] {a b c d : α} : (a + b) + (c + d) = a + d + c + b := by
  rw_search

/-- info: Try this: rw [@List.length_append, @List.length_append, Nat.two_mul, @add_rotate] -/
#guard_msgs in
example (xs ys : List α) :
    (xs ++ ys ++ ys).length = 2 * ys.length + xs.length := by
  rw_search

/-- info: Try this: rw [@add_sub, @eq_sub_iff_add_eq, ← @add_rotate, Int.add_right_comm] -/
#guard_msgs in
example {a b c : Int} : a + b = c + b + (a - c) := by
  rw_search

/-! A test of the current tokenization scheme. -/
/-- info: ["(", "[", "5", ",", "3", "]", ",", "4", "+", "(", "2", "*", "1", ")", ")"] -/
#guard_msgs in
open Mathlib.Tactic.RewriteSearch in
#eval ("([5, 3], 4 + (2 * 1))".splitOn.map splitDelimiters).join
