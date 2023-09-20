import Mathlib.Tactic.Rewrites
import Std.Tactic.GuardMsgs
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Prime

private axiom test_sorry : ∀ {α}, α
set_option autoImplicit true
set_option pp.proofs.withType false

attribute [refl] Eq.refl

/--
info: Try this: rw [@List.map_append]
-- "no goals"
-/
#guard_msgs in
example (f : α → β) (L M : List α) : (L ++ M).map f = L.map f ++ M.map f := by
  rw?

/--
info: Try this: rw [@mul_left_eq_self]
-- "no goals"
-/
#guard_msgs in
example [Group G] (h : G) : 1 * h = h := by
  rw?

/--
info: Try this: rw [← @Nat.prime_iff]
-- "no goals"
-/
#guard_msgs in
lemma prime_of_prime (n : ℕ) : Prime n ↔ Nat.Prime n := by
  rw?

lemma six_eq_seven : 6 = 7 := test_sorry

-- This test also verifies that we are removing duplicate results;
-- it previously also reported `Nat.cast_ofNat`
/--
info: Try this: rw [six_eq_seven]
-- ∀ (x : ℕ), x ≤ 7
---
info: Try this: rw [← @Nat.cast_eq_ofNat]
-- ∀ (x : ℕ), x ≤ ↑6
-/
#guard_msgs in
example : ∀ (x : ℕ), x ≤ 6 := by
  rw?
  guard_target = ∀ (x : ℕ), x ≤ 7
  exact test_sorry

/--
info: Try this: rw [six_eq_seven]
-- ∀ (x : ℕ), x ≤ 7 → x ≤ 8
---
info: Try this: rw [← @Nat.cast_eq_ofNat]
-- ∀ (x : ℕ), x ≤ ↑6 → x ≤ 8
-/
#guard_msgs in
example : ∀ (x : ℕ) (_w : x ≤ 6), x ≤ 8 := by
  rw?
  guard_target = ∀ (x : ℕ) (_w : x ≤ 7), x ≤ 8
  exact test_sorry

axiom α : Type
axiom f : α → α
axiom z : α
axiom f_eq (n) : f n = z

-- Check that the same lemma isn't used multiple times.
-- This used to report two redundant copies of `f_eq`.
-- It be lovely if `rw?` could produce two *different* rewrites by `f_eq` here!
/-- info: Try this: rw [f_eq]
-- z = f m
-/
#guard_msgs in
lemma test : f n = f m := by
  rw?
  rw [f_eq]

-- Check that we can rewrite by local hypotheses.
/-- info: Try this: rw [h]
-- "no goals"
-/
#guard_msgs in
example (h : 1 = 2) : 2 = 1 := by
  rw?
