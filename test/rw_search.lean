import Mathlib.Tactic.RewriteSearch

set_option autoImplicit true

/-- info: Try this: rw [@List.length_append, Nat.add_comm] -/
#guard_msgs in
example (xs ys : List α) : (xs ++ ys).length = ys.length + xs.length := by
  rw_search

/-- info: Try this: rw [← @add_rotate, ← vadd_eq_add, ← @add_rotate, @add_right_comm] -/
#guard_msgs in
example [AddCommMonoid α] {a b c d : α} : (a + b) + (c + d) = a + d + c + b := by
  rw_search

/-- info: Try this: rw [@List.length_append, @List.length_append, @add_rotate, Nat.two_mul] -/
#guard_msgs in
example (xs ys : List α) :
    (xs ++ ys ++ ys).length = 2 * ys.length + xs.length := by
  rw_search
