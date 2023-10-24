import Std.Data.List.Basic
import Mathlib.Tactic.Propose
import Mathlib.Tactic.GuardHypNums
import Mathlib.Algebra.Associated

-- For debugging, you may find these options useful:
-- set_option trace.Tactic.propose true
-- set_option trace.Meta.Tactic.solveByElim true
set_option autoImplicit true

theorem foo (L M : List α) (w : L.Disjoint M) (m : a ∈ L) : a ∉ M := fun h => w m h

/--
info: Try this: have : List.Disjoint M L := List.disjoint_symm w
---
info: Try this: have : List.Disjoint K M := List.disjoint_of_subset_left m w
-/
#guard_msgs in
example (K L M : List α) (w : L.Disjoint M) (m : K ⊆ L) : True := by
  have? using w
  -- have : List.Disjoint K M := List.disjoint_of_subset_left m w
  -- have : List.Disjoint M L := List.disjoint_symm w
  trivial

/--
info: Try this: have : List.Disjoint K M := List.disjoint_of_subset_left m w
---
info: Try this: have : List.Disjoint K M := List.disjoint_of_subset_left m w
-/
#guard_msgs in
example (K L M : List α) (w : L.Disjoint M) (m : K ⊆ L) : True := by
  have? using w, m
  -- have : List.Disjoint K M := List.disjoint_of_subset_left m w
  have?! using w, m
  guard_hyp List.disjoint_of_subset_left : List.Disjoint K M :=
    _root_.List.disjoint_of_subset_left m w
  fail_if_success
    have : M.Disjoint L := by assumption
  have : K.Disjoint M := by assumption
  trivial

def bar (n : Nat) (x : String) : Nat × String := (n + x.length, x)

-- FIXME notice a bug here: should not generate `let this✝` with an inaccessible name.
/--
info: Try this: let this✝ : ℕ × String := bar p.1 p.2
---
info: Try this: let this✝ : ℕ × String := bar p.1 p.2
-/
#guard_msgs in
example (p : Nat × String) : True := by
  fail_if_success have? using p
  have? : Nat × String using p.1, p.2
  have? : Nat × _ using p.1, p.2
  trivial

/--
info: Try this: have : List.Disjoint M L := List.disjoint_symm w
---
info: Try this: have : ¬a ∈ M := foo L M w m
-/
#guard_msgs in
example (K L M : List α) (w : L.Disjoint M) (m : a ∈ L) : True := by
  have?! using w
  guard_hyp List.disjoint_symm : List.Disjoint M L := _root_.List.disjoint_symm w
  have : a ∉ M := by assumption
  trivial

/--
info: Try this: have : IsUnit p := isUnit_of_dvd_one h
---
info: Try this: have : p ≠ 1 := ne_one hp
---
info: Try this: have : p ∣ p * p ↔ p ∣ p ∨ p ∣ p := dvd_mul hp
---
info: Try this: have : p ≠ 0 := ne_zero hp
---
info: Try this: have : ¬p ∣ 1 := not_dvd_one hp
---
info: Try this: have : ¬IsUnit p := not_unit hp
-/
#guard_msgs in
-- From Mathlib.Algebra.Associated:
variable {α : Type} [CommMonoidWithZero α] in
open Prime in
theorem dvd_of_dvd_pow (hp : Prime p) {a : α} {n : ℕ} (h : p ∣ a ^ n) : p ∣ a := by
  induction' n with n ih
  · rw [pow_zero] at h
    -- In mathlib, we proceed by two `have` statements:
    -- have := isUnit_of_dvd_one h
    -- have := not_unit hp
    -- `propose!` successfully guesses them both:
    have?! using h
    guard_hyp isUnit_of_dvd_one : IsUnit p := _root_.isUnit_of_dvd_one h
    have?! using hp
    guard_hyp Prime.not_unit : ¬IsUnit p := not_unit hp
    contradiction
  rw [pow_succ] at h
  cases' dvd_or_dvd hp h with dvd_a dvd_pow
  · assumption
  exact ih dvd_pow
