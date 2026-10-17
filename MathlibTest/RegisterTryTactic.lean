import Mathlib.Tactic.Module

-- Register module as a try? helper
register_try?_tactic module

-- Try a Module goal with ring scalar multiplication
#guard_msgs in
example {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M) :
    ((r * s) • x : M) + r • x = r • ((s + 1) • x) := by
  fail_if_success simp only []
  fail_if_success grind only []
  module

-- Verify try? on this `module` goal
/--
info: Try this:
  [apply] module
-/
#guard_msgs in
example {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M) :
    ((r * s) • x : M) + r • x = r • ((s + 1) • x) := by
  try?
