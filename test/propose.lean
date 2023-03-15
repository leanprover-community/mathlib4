import Std.Data.List.Basic
import Mathlib.Tactic.Propose
import Mathlib.Tactic.GuardHypNums
import Mathlib.Algebra.Associated

theorem foo (L M : List α) (w : L.Disjoint M) (m : a ∈ L) : a ∉ M := fun h => w m h

example (K L M : List α) (w : L.Disjoint M) (m : K ⊆ L) : True := by
  propose using w
  -- have : List.Disjoint K M := List.disjoint_of_subset_left m w
  -- have : List.Disjoint M L := List.disjoint_symm w
  trivial

example (K L M : List α) (w : L.Disjoint M) (m : K ⊆ L) : True := by
  propose using w, m
  -- have : List.Disjoint K M := List.disjoint_of_subset_left m w
  propose! using w, m
  fail_if_success
    have : M.Disjoint L := by assumption
  have : K.Disjoint M := by assumption
  trivial

def bar (n : Nat) (x : String) : Nat × String := (n + x.length, x)

example (p : Nat × String) : True := by
  fail_if_success propose using p
  propose : Nat × String using p.1, p.2
  propose : Nat × _ using p.1, p.2
  trivial

example (K L M : List α) (w : L.Disjoint M) (m : a ∈ L) : True := by
  propose! using w
  have : a ∉ M := by assumption
  trivial

-- From Mathlib.Algebra.Associated:
variable {α : Type} [CommMonoidWithZero α]
open Prime in
theorem dvd_of_dvd_pow (hp : Prime p) {a : α} {n : ℕ} (h : p ∣ a ^ n) : p ∣ a := by
  induction' n with n ih
  · rw [pow_zero] at h
    -- In mathlib, we proceed by two `have` statements:
    -- have := isUnit_of_dvd_one  h
    -- have := not_unit hp
    -- `propose!` successfully guesses them both:
    propose! using h
    propose! using hp
    contradiction
  rw [pow_succ] at h
  cases' dvd_or_dvd hp h with dvd_a dvd_pow
  · assumption
  exact ih dvd_pow
