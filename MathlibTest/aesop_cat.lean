import Mathlib.CategoryTheory.Category.Basic

structure Foo where
  x : Nat
  w : x = 37 := by cat_disch

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : Foo where
  x := sorry

/--
error: could not synthesize default value for field 'w' of 'Foo' using tactics
---
error: tactic 'aesop' failed, failed to prove the goal after exhaustive search.
Initial goal:
  ⊢ 35 = 37
Remaining goals after safe rules:
  ⊢ False
-/
#guard_msgs in
example : Foo where
  x := 35
