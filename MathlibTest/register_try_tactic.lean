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

-- Unfortunately at present `try?` is calling `simp_all? +suggestions`,
-- which often blows up in Mathlib.
-- For now, we disable library suggestions for this test.
-- After https://github.com/leanprover/lean4/pull/11172 this line can be removed.
set_library_suggestions fun _ _ => pure #[]

-- Verify try? on this `module` goal
/--
info: Try this:
  [apply] module
-/
#guard_msgs in
example {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (r s : R) (x : M) :
    ((r * s) • x : M) + r • x = r • ((s + 1) • x) := by
  try?
