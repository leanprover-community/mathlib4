import Mathlib.Tactic.Rewrites
import Mathlib.Data.Nat.Prime
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.List.Basic
import Mathlib.Algebra.Group.Basic

private axiom test_sorry : ∀ {α}, α
set_option autoImplicit true
set_option pp.proofs.withType false

-- To see the (sorted) list of lemmas that `rw?` will try rewriting by, use:
-- set_option trace.Tactic.rewrites.lemmas true

-- Recall that `rw?` caches the discrimination tree on disk.
-- If you are modifying the way that `rewrites` indexes lemmas,
-- while testing you will probably want to delete
-- `build/lib/MathlibExtras/Rewrites.extra`
-- so that the cache is rebuilt.

set_option autoImplicit true

open CategoryTheory

/--
info: Try this: rw [@Category.id_comp]
-- "no goals"
-/
#guard_msgs in
example [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ 𝟙 _ ≫ g = f ≫ g := by
  rw?

#guard_msgs(drop info) in
example : ∀ (x y : ℕ), x ≤ y := by
  intros x y
  rw? -- Used to be an error here https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/panic.20and.20error.20with.20rw.3F/near/370495531
  exact test_sorry

example : ∀ (x y : ℕ), x ≤ y := by
  -- Used to be a panic here https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/panic.20and.20error.20with.20rw.3F/near/370495531
  success_if_fail_with_msg "Could not find any lemmas which can rewrite the goal" rw?
  exact test_sorry

axiom K : Type
@[instance] axiom K.ring : Ring K

noncomputable def foo : K → K := test_sorry

#guard_msgs(drop info) in
example : foo x = 1 ↔ ∃ k : ℤ, x = k := by
  rw? -- Used to panic, see https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/panic.20and.20error.20with.20rw.3F/near/370598036
  exact test_sorry

-- check we can look inside let expressions
/-- info: Try this: rw [@AddCommMonoidWithOne.add_comm]
-- "no goals"
-/
#guard_msgs in
example (n : ℕ) : let y := 3; n + y = 3 + n := by
  rw?

def zero : Nat := 0

-- This used to (incorrectly!) succeed because `rw?` would try `rfl`,
-- rather than `withReducible` `rfl`.
#guard_msgs(drop info) in
example : zero = 0 := by
  rw?  -- expected not to close the goal
  exact test_sorry
