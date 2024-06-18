import Mathlib.Data.Nat.Prime
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Data.List.InsertNth
import Mathlib.Algebra.Group.Basic

-- This is partially duplicative with the tests for `rw?` in Lean.
-- It's useful to re-test here with a larger environment.

private axiom test_sorry : ∀ {α}, α

-- To see the (sorted) list of lemmas that `rw?` will try rewriting by, use:
-- set_option trace.Tactic.rewrites.lemmas true

set_option autoImplicit true

/--
info: Try this: rw [List.map_append]
-- "no goals"
-/
#guard_msgs in
example (f : α → β) (L M : List α) : (L ++ M).map f = L.map f ++ M.map f := by
  rw?

open CategoryTheory

/--
info: Try this: rw [Category.id_comp]
-- "no goals"
-/
#guard_msgs in
example [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ 𝟙 _ ≫ g = f ≫ g := by
  rw?

/--
info: Try this: rw [mul_left_eq_self]
-- "no goals"
-/
#guard_msgs in
example [Group G] (h : G) : 1 * h = h := by
  rw?

-- Adaptation note: nightly-2024-03-27
-- `rw?` upstream no longer uses `MVarId.applyRefl`, so it can't deal with `Iff` goals.
-- I'm out of time to deal with this, so I'll just drop the test for now.
-- This may need to wait until the next release.
-- /--
-- info: Try this: rw [Nat.prime_iff]
-- -- "no goals"
-- -/
-- #guard_msgs in
-- lemma prime_of_prime (n : ℕ) : Prime n ↔ Nat.Prime n := by
--   rw?

#guard_msgs(drop info) in
example [Group G] (h : G) (hyp : g * 1 = h) : g = h := by
  rw? at hyp
  assumption

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

lemma six_eq_seven : 6 = 7 := test_sorry

-- This test also verifies that we are removing duplicate results;
-- it previously also reported `Nat.cast_ofNat`
#guard_msgs(drop info) in
example : ∀ (x : ℕ), x ≤ 6 := by
  rw?
  guard_target = ∀ (x : ℕ), x ≤ 7
  exact test_sorry

#guard_msgs(drop info) in
example : ∀ (x : ℕ) (_w : x ≤ 6), x ≤ 8 := by
  rw?
  guard_target = ∀ (x : ℕ) (_w : x ≤ 7), x ≤ 8
  exact test_sorry

-- check we can look inside let expressions
#guard_msgs(drop info) in
example (n : ℕ) : let y := 3; n + y = 3 + n := by
  rw?

axiom α : Type
axiom f : α → α
axiom z : α
axiom f_eq (n) : f n = z

-- Check that the same lemma isn't used multiple times.
-- This used to report two redundant copies of `f_eq`.
-- It be lovely if `rw?` could produce two *different* rewrites by `f_eq` here!
#guard_msgs(drop info) in
lemma test : f n = f m := by
  fail_if_success rw? [-f_eq] -- Check that we can forbid lemmas.
  rw?
  rw [f_eq]

-- Check that we can rewrite by local hypotheses.
#guard_msgs(drop info) in
example (h : 1 = 2) : 2 = 1 := by
  rw?

def testConst : Nat := 4

-- This used to (incorrectly!) succeed because `rw?` would try `rfl`,
-- rather than `withReducible` `rfl`.
#guard_msgs(drop info) in
example : testConst = 4 := by
  rw?
  exact test_sorry

-- Discharge side conditions from local hypotheses.
/--
info: Try this: rw [h p]
-- "no goals"
-/
#guard_msgs in
example {P : Prop} (p : P) (h : P → 1 = 2) : 2 = 1 := by
  rw?

-- Use `solve_by_elim` to discharge side conditions.
/--
info: Try this: rw [h (f p)]
-- "no goals"
-/
#guard_msgs in
example {P Q : Prop} (p : P) (f : P → Q) (h : Q → 1 = 2) : 2 = 1 := by
  rw?


-- Rewrite in reverse, discharging side conditions from local hypotheses.
/--
info: Try this: rw [← h₁ p]
-- Q a
-/
#guard_msgs in
example {P : Prop} (p : P) (Q : α → Prop) (a b : α) (h₁ : P → a = b) (w : Q a) : Q b := by
  rw?
  exact w
