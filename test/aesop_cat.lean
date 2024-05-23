import Mathlib.CategoryTheory.Category.Basic

structure Foo where
  x : Nat
  w : x = 37 := by aesop_cat

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : Foo where
  x := sorry

/--
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
⊢ 35 = 37
-/
#guard_msgs in
example : Foo where
  x := 35
