/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Prime.Defs
import Mathlib.Algebra.Ring.Units
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Prime elements in rings
This file contains lemmas about prime elements of commutative rings.
-/


section CancelCommMonoidWithZero

variable {R : Type*} [CancelCommMonoidWithZero R]

open Finset

/-- If `x * y = a * ∏ i ∈ s, p i` where `p i` is always prime, then
`x` and `y` can both be written as a divisor of `a` multiplied by
a product over a subset of `s` -/
theorem mul_eq_mul_prime_prod {α : Type*} [DecidableEq α] {x y a : R} {s : Finset α} {p : α → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hx : x * y = a * ∏ i ∈ s, p i) :
    ∃ (t u : Finset α) (b c : R),
      t ∪ u = s ∧ Disjoint t u ∧ a = b * c ∧ (x = b * ∏ i ∈ t, p i) ∧ y = c * ∏ i ∈ u, p i := by
  induction' s using Finset.induction with i s his ih generalizing x y a
  · exact ⟨∅, ∅, x, y, by simp [hx]⟩
  · rw [prod_insert his, ← mul_assoc] at hx
    have hpi : Prime (p i) := hp i (mem_insert_self _ _)
    rcases ih (fun i hi ↦ hp i (mem_insert_of_mem hi)) hx with
      ⟨t, u, b, c, htus, htu, hbc, rfl, rfl⟩
    have hit : i ∉ t := fun hit ↦ his (htus ▸ mem_union_left _ hit)
    have hiu : i ∉ u := fun hiu ↦ his (htus ▸ mem_union_right _ hiu)
    obtain ⟨d, rfl⟩ | ⟨d, rfl⟩ : p i ∣ b ∨ p i ∣ c := hpi.dvd_or_dvd ⟨a, by rw [← hbc, mul_comm]⟩
    · rw [mul_assoc, mul_comm a, mul_right_inj' hpi.ne_zero] at hbc
      exact ⟨insert i t, u, d, c, by rw [insert_union, htus], disjoint_insert_left.2 ⟨hiu, htu⟩, by
          simp [hbc, prod_insert hit, mul_assoc, mul_comm, mul_left_comm]⟩
    · rw [← mul_assoc, mul_right_comm b, mul_left_inj' hpi.ne_zero] at hbc
      exact ⟨t, insert i u, b, d, by rw [union_insert, htus], disjoint_insert_right.2 ⟨hit, htu⟩, by
          simp [← hbc, prod_insert hiu, mul_assoc, mul_comm, mul_left_comm]⟩

/-- If `x * y = a * p ^ n` where `p` is prime, then `x` and `y` can both be written
  as the product of a power of `p` and a divisor of `a`. -/
theorem mul_eq_mul_prime_pow {x y a p : R} {n : ℕ} (hp : Prime p) (hx : x * y = a * p ^ n) :
    ∃ (i j : ℕ) (b c : R), i + j = n ∧ a = b * c ∧ x = b * p ^ i ∧ y = c * p ^ j := by
  rcases mul_eq_mul_prime_prod (fun _ _ ↦ hp)
    (show x * y = a * (range n).prod fun _ ↦ p by simpa) with
      ⟨t, u, b, c, htus, htu, rfl, rfl, rfl⟩
  exact ⟨#t, #u, b, c, by rw [← card_union_of_disjoint htu, htus, card_range], by simp⟩

end CancelCommMonoidWithZero

section CommRing

variable {α : Type*} [CommRing α]

theorem Prime.neg {p : α} (hp : Prime p) : Prime (-p) := by
  obtain ⟨h1, h2, h3⟩ := hp
  exact ⟨neg_ne_zero.mpr h1, by rwa [IsUnit.neg_iff], by simpa [neg_dvd] using h3⟩

theorem Prime.abs [LinearOrder α] {p : α} (hp : Prime p) : Prime (abs p) := by
  obtain h | h := abs_choice p <;> rw [h]
  · exact hp
  · exact hp.neg

end CommRing
