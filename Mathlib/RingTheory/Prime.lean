/-
Copyright (c) 2020 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathlib.Algebra.Associated
import Mathlib.Algebra.BigOperators.Basic

#align_import ring_theory.prime from "leanprover-community/mathlib"@"008205aa645b3f194c1da47025c5f110c8406eab"

/-!
# Prime elements in rings
This file contains lemmas about prime elements of commutative rings.
-/


section CancelCommMonoidWithZero

variable {R : Type*} [CancelCommMonoidWithZero R]

open Finset

open BigOperators

/-- If `x * y = a * ∏ i in s, p i` where `p i` is always prime, then
  `x` and `y` can both be written as a divisor of `a` multiplied by
  a product over a subset of `s`  -/
theorem mul_eq_mul_prime_prod {α : Type*} [DecidableEq α] {x y a : R} {s : Finset α} {p : α → R}
    (hp : ∀ i ∈ s, Prime (p i)) (hx : x * y = a * ∏ i in s, p i) :
    ∃ (t u : Finset α) (b c : R),
      t ∪ u = s ∧ Disjoint t u ∧ a = b * c ∧ (x = b * ∏ i in t, p i) ∧ y = c * ∏ i in u, p i := by
  induction' s using Finset.induction with i s his ih generalizing x y a
  -- ⊢ ∃ t u b c, t ∪ u = ∅ ∧ Disjoint t u ∧ a = b * c ∧ x = b * ∏ i in t, p i ∧ y  …
  · exact ⟨∅, ∅, x, y, by simp [hx]⟩
    -- 🎉 no goals
  · rw [prod_insert his, ← mul_assoc] at hx
    -- ⊢ ∃ t u b c, t ∪ u = insert i s ∧ Disjoint t u ∧ a = b * c ∧ x = b * ∏ i in t, …
    have hpi : Prime (p i) := hp i (mem_insert_self _ _)
    -- ⊢ ∃ t u b c, t ∪ u = insert i s ∧ Disjoint t u ∧ a = b * c ∧ x = b * ∏ i in t, …
    rcases ih (fun i hi ↦ hp i (mem_insert_of_mem hi)) hx with
      ⟨t, u, b, c, htus, htu, hbc, rfl, rfl⟩
    have hit : i ∉ t := fun hit ↦ his (htus ▸ mem_union_left _ hit)
    -- ⊢ ∃ t_1 u_1 b_1 c_1, t_1 ∪ u_1 = insert i s ∧ Disjoint t_1 u_1 ∧ a = b_1 * c_1 …
    have hiu : i ∉ u := fun hiu ↦ his (htus ▸ mem_union_right _ hiu)
    -- ⊢ ∃ t_1 u_1 b_1 c_1, t_1 ∪ u_1 = insert i s ∧ Disjoint t_1 u_1 ∧ a = b_1 * c_1 …
    obtain ⟨d, rfl⟩ | ⟨d, rfl⟩ : p i ∣ b ∨ p i ∣ c
    exact hpi.dvd_or_dvd ⟨a, by rw [← hbc, mul_comm]⟩
    -- ⊢ ∃ t_1 u_1 b c_1, t_1 ∪ u_1 = insert i s ∧ Disjoint t_1 u_1 ∧ a = b * c_1 ∧ p …
    · rw [mul_assoc, mul_comm a, mul_right_inj' hpi.ne_zero] at hbc
      -- ⊢ ∃ t_1 u_1 b c_1, t_1 ∪ u_1 = insert i s ∧ Disjoint t_1 u_1 ∧ a = b * c_1 ∧ p …
      exact ⟨insert i t, u, d, c, by rw [insert_union, htus], disjoint_insert_left.2 ⟨hiu, htu⟩, by
          simp [hbc, prod_insert hit, mul_assoc, mul_comm, mul_left_comm]⟩
    · rw [← mul_assoc, mul_right_comm b, mul_left_inj' hpi.ne_zero] at hbc
      -- ⊢ ∃ t_1 u_1 b_1 c, t_1 ∪ u_1 = insert i s ∧ Disjoint t_1 u_1 ∧ a = b_1 * c ∧ b …
      exact ⟨t, insert i u, b, d, by rw [union_insert, htus], disjoint_insert_right.2 ⟨hit, htu⟩, by
          simp [← hbc, prod_insert hiu, mul_assoc, mul_comm, mul_left_comm]⟩
#align mul_eq_mul_prime_prod mul_eq_mul_prime_prod

/-- If ` x * y = a * p ^ n` where `p` is prime, then `x` and `y` can both be written
  as the product of a power of `p` and a divisor of `a`. -/
theorem mul_eq_mul_prime_pow {x y a p : R} {n : ℕ} (hp : Prime p) (hx : x * y = a * p ^ n) :
    ∃ (i j : ℕ) (b c : R), i + j = n ∧ a = b * c ∧ x = b * p ^ i ∧ y = c * p ^ j := by
  rcases mul_eq_mul_prime_prod (fun _ _ ↦ hp)
    (show x * y = a * (range n).prod fun _ ↦ p by simpa) with
      ⟨t, u, b, c, htus, htu, rfl, rfl, rfl⟩
  exact ⟨t.card, u.card, b, c, by rw [← card_disjoint_union htu, htus, card_range], by simp⟩
  -- 🎉 no goals
#align mul_eq_mul_prime_pow mul_eq_mul_prime_pow

end CancelCommMonoidWithZero

section CommRing

variable {α : Type*} [CommRing α]

theorem Prime.neg {p : α} (hp : Prime p) : Prime (-p) := by
  obtain ⟨h1, h2, h3⟩ := hp
  -- ⊢ Prime (-p)
  exact ⟨neg_ne_zero.mpr h1, by rwa [IsUnit.neg_iff], by simpa [neg_dvd] using h3⟩
  -- 🎉 no goals
#align prime.neg Prime.neg

theorem Prime.abs [LinearOrder α] {p : α} (hp : Prime p) : Prime (abs p) := by
  obtain h | h := abs_choice p <;> rw [h]
  -- ⊢ Prime |p|
                                   -- ⊢ Prime p
                                   -- ⊢ Prime (-p)
  · exact hp
    -- 🎉 no goals
  · exact hp.neg
    -- 🎉 no goals
#align prime.abs Prime.abs

end CommRing
