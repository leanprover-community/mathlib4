/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Group.Ultra

/-!
## Sufficient conditions to have an ultrametric norm on a field

This file provides ways of constructing an instance of `IsUltrametricDist` based on
facts about the existing norm.

## Main results

* `isUltrametricDist_of_forall_norm_natCast_le_one`: a norm in a field is ultrametric if the norm
  of the image of a natural is less than or equal to one

## Implementation details

The proof relies on a bounded-from-above argument.

## Tags

ultrametric, nonarchimedean
-/
open Metric NNReal

namespace IsUltrametricDist

section sufficient

variable {R F : Type*} [NormedDivisionRing R] [NormedField F]

lemma isUltrametricDist_of_forall_norm_add_one_le_max_norm_one
    (h : ∀ x : R, ‖x + 1‖ ≤ max ‖x‖ 1) : IsUltrametricDist R := by
  refine isUltrametricDist_of_forall_norm_add_le_max_norm (fun x y ↦ ?_)
  rcases eq_or_ne y 0 with rfl | hy
  · simpa only [add_zero] using le_max_left _ _
  · have p : 0 < ‖y‖ := norm_pos_iff.mpr hy
    simpa only [div_add_one hy, norm_div, div_le_iff₀ p, max_mul_of_nonneg _ _ p.le, one_mul,
      div_mul_cancel₀ _ p.ne'] using h (x / y)

lemma isUltrametricDist_of_forall_norm_add_one_of_norm_le_one
    (h : ∀ x : R, ‖x‖ ≤ 1 → ‖x + 1‖ ≤ 1) : IsUltrametricDist R := by
  refine isUltrametricDist_of_forall_norm_add_one_le_max_norm_one fun x ↦ ?_
  rcases le_or_lt ‖x‖ 1 with H|H
  · exact (h _ H).trans (le_max_right _ _)
  · suffices ‖x + 1‖ ≤ ‖x‖ from this.trans (le_max_left _ _)
    rw [← div_le_div_right (c := ‖x‖) (H.trans' zero_lt_one), div_self (H.trans' zero_lt_one).ne',
        ← norm_div, add_div, div_self (by simpa using (H.trans' zero_lt_one)), add_comm]
    apply h
    simp [inv_le_one_iff₀, H.le]

lemma isUltrametricDist_of_forall_norm_sub_one_of_norm_le_one
    (h : ∀ x : R, ‖x‖ ≤ 1 → ‖x - 1‖ ≤ 1) : IsUltrametricDist R := by
  have (x : R) (hx : ‖x‖ ≤ 1) : ‖x + 1‖ ≤ 1 := by
    simpa only [← neg_add', norm_neg] using h (-x) (norm_neg x ▸ hx)
  exact isUltrametricDist_of_forall_norm_add_one_of_norm_le_one this

/-- This technical lemma is used in the proof of
`isUltrametricDist_of_forall_norm_natCast_le_one`. -/
lemma isUltrametricDist_of_forall_pow_norm_le_nsmul_pow_max_one_norm
    (h : ∀ (x : R) (m : ℕ), ‖x + 1‖ ^ m ≤ (m + 1) • max 1 ‖x‖ ^ m) :
    IsUltrametricDist R := by
  -- it will suffice to prove that `‖x + 1‖ ≤ max 1 ‖x‖`
  refine isUltrametricDist_of_forall_norm_add_one_le_max_norm_one fun x => ?_
  -- using this more powerful statement in the hypothesis by morally taking the `m`-th root
  -- to get an inequality of the form `‖x + 1‖ ≤ C • max 1 ‖x‖` where the `C : ℝ` is arbitrary.
  -- specifically, we will use `C = m + 1` and approach `m = 0` from above.
  -- we rely on the denseness of the reals to approach `max 1 ‖x‖` from above by values `a : ℝ`
  -- and show that any such value must be greater than or equal to our LHS: `‖x + 1‖ ≤ a`.
  rw [max_comm]
  refine le_of_forall_le_of_dense ?_
  intro a ha
  have ha' : 1 < a := (max_lt_iff.mp ha).left
  -- `max 1 ‖x‖ < a`, so there must be some `m : ℕ` such that `m + 1 < (a / max 1 ‖x‖) ^ m`
  -- by the virtue of exponential growth being faster than linear growth
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (a / (max 1 ‖x‖)) ^ m > ((m + 1) : ℕ) := by
    apply_mod_cast Real.exists_natCast_add_one_lt_pow_of_one_lt
    rwa [one_lt_div (by positivity)]
  -- and we rearrange again to get `(m + 1) • max 1 ‖x‖ ^ m < a ^ m`
  rw [div_pow, gt_iff_lt, lt_div_iff₀ (by positivity), ← nsmul_eq_mul] at hm
  -- which squeezes down to get our `‖x + 1‖ ≤ a` using our to-be-proven hypothesis of
  -- `‖x + 1‖ ^ m ≤ (m + 1) • max 1 ‖x‖ ^ m`, so we're done
  refine le_of_pow_le_pow_left ?_ (zero_lt_one.trans ha').le ((h _ _).trans hm.le)
  rintro rfl
  simp at hm

/-- To prove that a normed field is nonarchimedean, it suffices to prove that the norm
of the image of any natural is less than or equal to one. -/
lemma isUltrametricDist_of_forall_norm_natCast_le_one
    (h : ∀ n : ℕ, ‖(n : F)‖ ≤ 1) : IsUltrametricDist F := by
  -- we first use our hypothesis about the norm of naturals to have that multiplication by
  -- naturals keeps the norm small
  replace h (x : F) (n : ℕ) : ‖n • x‖ ≤ ‖x‖ := by
    rw [nsmul_eq_mul, norm_mul]
    rcases (norm_nonneg x).eq_or_lt with hx|hx
    · simp [← hx]
    · rw [mul_le_iff_le_one_left hx]
      exact h _
  -- it will suffice to prove that `‖x + 1‖ ≤ max 1 ‖x‖`
  -- which we will do by "complicating" the goal:
  -- proving it for all powers `m`, `‖x + 1‖ ^ m ≤ (m + 1) • max 1 ‖x‖ ^ m`,
  suffices ∀ (x : F) (m : ℕ), ‖x + 1‖ ^ m ≤ (m + 1) • max 1 ‖x‖ ^ m from
    isUltrametricDist_of_forall_pow_norm_le_nsmul_pow_max_one_norm this
  intro x m
  -- we can distribute powers into the right term of `max` here
  have hp : max 1 ‖x‖ ^ m = max 1 (‖x‖ ^ m) := by
    rcases max_cases 1 ‖x‖ with (⟨hm, hx⟩|⟨hm, hx⟩)
    · rw [hm, one_pow, eq_comm, max_eq_left_iff]
      exact (pow_le_pow_left (norm_nonneg _) hx _).trans_eq (one_pow _)
    · rw [hm, eq_comm, max_eq_right_iff]
      exact (pow_le_pow_left zero_le_one hx.le _).trans_eq' (one_pow _).symm
  rw [hp]; clear hp
  -- we distribute the LHS using the binomial theorem  where all terms in the sum
  -- will be of the form `k • x ^ i` for some binomial coefficient `k : ℕ`
  -- and the terminal terms with powers `0` and `m` will have the binomial coefficient as `1`
  have key : ∀ m : ℕ, ‖x + 1‖ ^ m ≤ ∑ k ∈ Finset.range (m + 1), ‖x‖ ^ k := by
    -- the nature of the norm means that one of `1` and `‖x‖ ^ m` is the largest of the two,
    -- so the other terms in the binomial expansion are insignificant,
    -- since by our hypothesis, we have that `‖k • x ^ i‖ ≤ ‖x ^ i‖`.
    -- That is, either the power `0` or `m` dominates the other terms.
    intro
    simp_rw [← norm_pow, add_pow, one_pow, mul_one]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intros
    rw [mul_comm, ← nsmul_eq_mul]
    exact h _ _
  -- we now suffice to show that the sum of powers of norms is less than the
  -- multiple of the larger of the two
  refine (key m).trans ?_
  -- and the number of terms in the sum is precisely `m + 1`
  rw [← Finset.card_range (m + 1), ← Finset.sum_const, Finset.card_range]
  rcases max_cases 1 (‖x‖ ^ m) with (⟨hm, hx⟩|⟨hm, hx⟩) <;> rw [hm] <;>
  -- which we show by comparing the terms in the sum one by one
  refine Finset.sum_le_sum fun i hi ↦ ?_
  · rcases i with (_|i)
    · simp
    refine pow_le_one₀ (norm_nonneg _) ?_
    rw [← one_pow m] at hx
    refine le_of_pow_le_pow_left ?_ zero_le_one hx
    rintro rfl
    simp at hi
  · refine pow_le_pow_right₀ ?_ (by simpa [Nat.lt_succ] using hi)
    contrapose! hx
    exact pow_le_one₀ (norm_nonneg _) hx.le

end sufficient

end IsUltrametricDist
