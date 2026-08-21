/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Analysis.Complex.Arg
public import Mathlib.Analysis.Convex.TriangleEquality

/-!
# Triangle equality for sums of complex numbers

Over `ℂ`, lying on a common closed ray means sharing a phase. So the triangle inequality
`‖∑ i ∈ s, v i‖ ≤ ∑ i ∈ s, ‖v i‖` is an equality exactly when every nonzero summand has the same
phase as the sum, equivalently when every summand is a nonnegative real multiple of one complex
number of norm one. This is the finite-family form of `Complex.norm_add_eq_iff`; the statement in
a general strictly convex space is `norm_sum_eq_iff_pairwise_sameRay`.

## Main statements

* `Complex.aligned_of_pairwise_sameRay`: if the summands pairwise lie on a common closed ray, then
  every nonzero summand has the same phase as the sum.
* `Complex.triangle_equality_iff_aligned`: triangle equality holds iff every summand is a
  nonnegative real multiple of a single complex number of norm one.

## Implementation notes

`aligned_of_pairwise_sameRay` is the division form of `SameRay.inv_norm_smul_eq`: over `ℂ` the
phase `z / ↑‖z‖` is easier to work with downstream than the scalar action `‖z‖⁻¹ • z`, which is
how Mathlib states the general result.

## Tags

triangle inequality, triangle equality, same ray, phase, argument
-/

public section

namespace Complex

open Finset

variable {ι : Type*} {s : Finset ι} {i : ι} {v : ι → ℂ}

/-- If the summands pairwise lie on a common closed ray and one of them is nonzero, then it has
the same phase as the sum. -/
lemma aligned_of_pairwise_sameRay (hp : ∀ i ∈ s, ∀ j ∈ s, SameRay ℝ (v i) (v j)) (hi : i ∈ s)
    (hvi : v i ≠ 0) : v i / (‖v i‖ : ℂ) = (∑ j ∈ s, v j) / (‖∑ j ∈ s, v j‖ : ℂ) :=
  aligned_of_sameRay hvi (sum_ne_zero_of_pairwise_sameRay hp hi hvi)
    (sameRay_sum fun j hj ↦ hp i hi j hj)

/-- **Triangle equality** over `ℂ`: the norm of a finite sum equals the sum of the norms exactly
when every summand is a nonnegative real multiple of one complex number of norm one. -/
theorem triangle_equality_iff_aligned :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i ∈ s, v i = (‖v i‖ : ℂ) * c := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases eq_or_ne (∑ i ∈ s, v i) 0 with h0 | h0
    · refine ⟨1, norm_one, fun i hi ↦ ?_⟩
      simp [eq_zero_of_sum_norm_eq_zero (by rw [← h, h0, norm_zero]) hi]
    · refine ⟨(∑ i ∈ s, v i) / (‖∑ i ∈ s, v i‖ : ℂ), ?_, fun i hi ↦ ?_⟩
      · rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 h0)]
      · rcases eq_or_ne (v i) 0 with hv | hv
        · simp [hv]
        · rw [← aligned_of_pairwise_sameRay (norm_sum_eq_iff_pairwise_sameRay.1 h) hi hv,
            mul_div_cancel₀ _ (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hv))]
  · rintro ⟨c, hc, hvc⟩
    have hsum : ∑ i ∈ s, v i = ((∑ i ∈ s, ‖v i‖ : ℝ) : ℂ) * c := by
      rw [ofReal_sum, sum_mul]
      exact sum_congr rfl hvc
    rw [hsum, norm_mul, hc, mul_one,
      Complex.norm_of_nonneg (sum_nonneg fun i _ ↦ norm_nonneg (v i))]

end Complex
