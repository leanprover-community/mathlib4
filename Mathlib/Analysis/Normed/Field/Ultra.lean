/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Ultra

/-!
## Sufficient contidition to have an ultrametric norm on a field

This file provides ways of constructing an instance of `IsUltrametricDist` based on
facts about the existing norm.

## Main results

* `isUltrametricDist_of_forall_norm_natCast_le_one`: a norm in a field is ultrametric if the norm
  of the image of a natural is less than or equal to one

## Implementation details

The proof relies on a bounded-from-above argument, so the imports need to include `rpow`

## Tags

ultrametric, nonarchimedean
-/
open Metric IsUltrametricDist NNReal

namespace IsUltrametricDist

section sufficient

variable {R F : Type*} [NormedDivisionRing R] [NormedField F]

lemma isUltrametricDist_of_forall_norm_add_one_le_max_norm_one
    (h : ∀ x : R, ‖x + 1‖ ≤ max ‖x‖ 1) : IsUltrametricDist R := by
  apply isUltrametricDist_of_forall_norm_add_le_max_norm
  intro x y
  rcases eq_or_ne y 0 with rfl|hy
  · simp
  rw [← div_le_div_right (c := ‖y‖) (by simpa using hy), ← norm_div, add_div, div_self hy,
      ← max_div_div_right (norm_nonneg _), div_self (by simp [hy]), ← norm_div]
  exact h _

lemma isUltrametricDist_of_forall_norm_sub_one_of_norm_le_one
    (h : ∀ x : R, ‖x‖ ≤ 1 → ‖x - 1‖ ≤ 1) : IsUltrametricDist R := by
  have : ∀ x : R, ‖x‖ ≤ 1 → ‖x + 1‖ ≤ 1 := by
    intro x hx
    specialize h (-x) (by simpa using hx)
    rwa [← neg_add', norm_neg] at h
  apply isUltrametricDist_of_forall_norm_add_one_le_max_norm_one
  intro x
  cases le_or_lt ‖x‖ 1 with
  | inl h => simpa [h] using this _ h
  | inr h =>
    suffices ‖x + 1‖ ≤ ‖x‖ by simp [this]
    rw [← div_le_div_right (c := ‖x‖) (h.trans' zero_lt_one), div_self (h.trans' zero_lt_one).ne',
        ← norm_div, add_div, div_self (by simpa using (h.trans' zero_lt_one)), add_comm]
    apply this
    simp [inv_le_one_iff, h.le]

lemma isUltrametricDist_of_forall_norm_natCast_le_one
    (h : ∀ n : ℕ, ‖(n : F)‖ ≤ 1) : IsUltrametricDist F := by
  refine isUltrametricDist_of_forall_norm_add_one_le_max_norm_one fun x => ?_
  rw [max_comm]
  have key : ∀ m : ℕ, ‖x + 1‖ ^ m ≤ ∑ k ∈ Finset.range (m + 1), ‖x‖ ^ k := by
    intro
    simp_rw [← norm_pow, add_pow, one_pow, mul_one]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intros i hi
    simp only [norm_mul, norm_pow]
    rcases (norm_nonneg x).eq_or_lt with hx|hx
    · cases i <;> simp [hx.symm]
    · rw [mul_le_iff_le_one_right]
      · exact h _
      · exact pow_pos hx ?_
  replace key : ∀ m : ℕ, ‖x + 1‖ ^ m ≤ (m + 1) • max 1 (‖x‖ ^ m) := by
    intro m
    refine (key m).trans ?_
    rw [← Finset.card_range (m + 1), ← Finset.sum_const, Finset.card_range]
    rcases max_cases 1 (‖x‖ ^ m) with (⟨hm, hx⟩|⟨hm, hx⟩)
    · rw [hm]
      refine Finset.sum_le_sum ?_
      rintro (_|i) hi
      · simp
      refine pow_le_one₀ (norm_nonneg _) ?_
      rw [← one_pow m] at hx
      refine le_of_pow_le_pow_left ?_ zero_le_one hx
      rintro rfl
      simp at hi
    · rw [hm]
      refine Finset.sum_le_sum ?_
      intro i hi
      refine pow_le_pow_right₀ ?_ (by simpa [Nat.lt_succ] using hi)
      contrapose! hx
      exact pow_le_one₀ (norm_nonneg _) hx.le
  refine le_of_forall_le_of_dense ?_
  intro a ha
  have ha' : 1 < a := (max_lt_iff.mp ha).left
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (a / (max 1 ‖x‖)) ^ m > ((m + 1) : ℕ) := by
    apply_mod_cast Real.exists_natCast_add_one_lt_pow_of_one_lt
    rwa [one_lt_div (by positivity)]
  have hp : max 1 ‖x‖ ^ m = max 1 (‖x‖ ^ m) := by
    rcases max_cases 1 ‖x‖ with (⟨hm, hx⟩|⟨hm, hx⟩)
    · rw [hm, one_pow, eq_comm, max_eq_left_iff]
      exact (pow_le_pow_left (norm_nonneg _) hx _).trans_eq (one_pow _)
    · rw [hm, eq_comm, max_eq_right_iff]
      exact (pow_le_pow_left zero_le_one hx.le _).trans_eq' (one_pow _).symm
  rw [div_pow, gt_iff_lt, lt_div_iff₀ (by positivity), ← nsmul_eq_mul, hp] at hm
  refine le_of_pow_le_pow_left ?_ (zero_lt_one.trans ha').le ((key _).trans hm.le)
  rintro rfl
  simp at hm

end sufficient

end IsUltrametricDist
