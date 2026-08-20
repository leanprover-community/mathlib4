/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Analysis.Complex.Arg

/-!
# Triangle equality for sums of complex numbers

The triangle inequality `‖∑ i ∈ s, v i‖ ≤ ∑ i ∈ s, ‖v i‖` is an equality exactly when the
summands pairwise lie on a common closed ray, in which case all the nonzero summands share a
single phase. This extends `Complex.norm_add_eq_iff` from two summands to finite families, and is
the finite-sum form of `sameRay_iff_norm_add`.

## Main results

* `Complex.norm_sum_eq_iff_pairwise_sameRay`: triangle equality holds iff the summands pairwise
  lie on a common closed ray.
* `Complex.sameRay_sum`: a number on the same ray as every summand is on the same ray as the sum.
* `Complex.aligned_of_pairwise_sameRay`: pairwise alignment gives every nonzero summand the same
  phase as the sum.
* `Complex.triangle_equality_iff_aligned`: triangle equality holds iff every term is a
  nonnegative real multiple of a single unit.

## References

See `Complex.norm_add_eq_iff` in `Mathlib/Analysis/Complex/Arg.lean` for two summands, and
`sameRay_iff_norm_add` for the two-vector statement in a strictly convex space.
-/

public section

namespace Complex

open Finset

variable {ι : Type*} {v : ι → ℂ} {s : Finset ι} {i : ι}

private lemma eq_zero_of_sum_norm_eq_zero (h : ∑ j ∈ s, ‖v j‖ = 0) (hi : i ∈ s) : v i = 0 :=
  norm_eq_zero.1 <| (sum_eq_zero_iff_of_nonneg fun j _ ↦ norm_nonneg (v j)).1 h i hi

lemma sameRay_sum {x : ℂ} (h : ∀ j ∈ s, SameRay ℝ x (v j)) : SameRay ℝ x (∑ j ∈ s, v j) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    simpa using (h a (mem_cons_self ..)).add_right (ih fun j hj ↦ h j (mem_cons_of_mem hj))

theorem norm_sum_eq_iff_pairwise_sameRay :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ ↔ ∀ i ∈ s, ∀ j ∈ s, SameRay ℝ (v i) (v j) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    simp only [sum_cons, mem_cons]
    refine ⟨fun h ↦ ?_, fun hp ↦ ?_⟩
    · have ht : ‖∑ j ∈ t, v j‖ = ∑ j ∈ t, ‖v j‖ :=
        le_antisymm (norm_sum_le _ _) (by linarith [norm_add_le (v a) (∑ j ∈ t, v j)])
      have hp := ih.1 ht
      have key : ∀ j ∈ t, SameRay ℝ (v a) (v j) := fun j hj ↦
        (sameRay_iff_norm_add.2 (by rw [h, ht])).trans
          (sameRay_sum fun k hk ↦ hp j hj k hk).symm fun h0 ↦
            Or.inr (eq_zero_of_sum_norm_eq_zero (by rw [← ht, h0, norm_zero]) hj)
      rintro i (rfl | hi) j (rfl | hj)
      · exact SameRay.rfl
      · exact key j hj
      · exact (key i hi).symm
      · exact hp i hi j hj
    · rw [(sameRay_sum fun j hj ↦ hp a (Or.inl rfl) j (Or.inr hj)).norm_add,
        ih.2 fun i hi j hj ↦ hp i (Or.inr hi) j (Or.inr hj)]

lemma coeff_of_nonneg_smul {u : ℂ} {k : ℝ} (hk : 0 ≤ k) (hu : u ≠ 0) :
    k = ‖(k : ℂ) * u‖ / ‖u‖ := by
  rw [norm_mul, Complex.norm_of_nonneg hk, mul_div_assoc,
    div_self (norm_ne_zero_iff.2 hu), mul_one]

lemma aligned_of_pairwise_sameRay (hp : ∀ i ∈ s, ∀ j ∈ s, SameRay ℝ (v i) (v j)) (hi : i ∈ s)
    (hvi : v i ≠ 0) : v i / (‖v i‖ : ℂ) = (∑ j ∈ s, v j) / (‖∑ j ∈ s, v j‖ : ℂ) :=
  aligned_of_sameRay hvi
    (fun h0 ↦ hvi (eq_zero_of_sum_norm_eq_zero
      (by rw [← norm_sum_eq_iff_pairwise_sameRay.2 hp, h0, norm_zero]) hi))
    (sameRay_sum fun j hj ↦ hp i hi j hj)

theorem triangle_equality_iff_aligned :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ i ∈ s, v i = (‖v i‖ : ℂ) * c := by
  refine ⟨fun h ↦ ?_, fun ⟨c, hc, hvc⟩ ↦ ?_⟩
  · rcases eq_or_ne (∑ i ∈ s, v i) 0 with h0 | h0
    · exact ⟨1, norm_one, fun i hi ↦ by
        simp [eq_zero_of_sum_norm_eq_zero (by rw [← h, h0, norm_zero]) hi]⟩
    · refine ⟨(∑ i ∈ s, v i) / (‖∑ i ∈ s, v i‖ : ℂ), ?_, fun i hi ↦ ?_⟩
      · rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.2 h0)]
      · rcases eq_or_ne (v i) 0 with hv | hv
        · simp [hv]
        · rw [← aligned_of_pairwise_sameRay (norm_sum_eq_iff_pairwise_sameRay.1 h) hi hv,
            mul_div_cancel₀ _ (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hv))]
  · rw [show ∑ i ∈ s, v i = ((∑ i ∈ s, ‖v i‖ : ℝ) : ℂ) * c by
        rw [ofReal_sum, sum_mul]; exact sum_congr rfl hvc,
      norm_mul, hc, mul_one, Complex.norm_of_nonneg (sum_nonneg fun i _ ↦ norm_nonneg (v i))]

end Complex
