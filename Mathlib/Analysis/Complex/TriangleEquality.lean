/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Analysis.Complex.Arg

/-!
# Triangle equality for finite sums

The triangle inequality `‖∑ i ∈ s, v i‖ ≤ ∑ i ∈ s, ‖v i‖` is an equality exactly when the
summands pairwise lie on a common closed ray: this is `norm_sum_eq_iff_pairwise_sameRay`, which
extends the two-vector statement `sameRay_iff_norm_add` to finite families.

Over `ℂ`, lying on a common ray means sharing a phase, so triangle equality says that every
summand is a nonnegative real multiple of one complex number of norm one. That is
`Complex.triangle_equality_iff_aligned`, the finite-family form of `Complex.norm_add_eq_iff`.

## Main results

* `sameRay_sum`: an element on the same ray as every summand is on the same ray as the sum.
* `norm_sum_eq_of_pairwise_sameRay` and `pairwise_sameRay_of_norm_sum_eq`, packaged as
  `norm_sum_eq_iff_pairwise_sameRay`: triangle equality holds iff the summands pairwise lie on a
  common closed ray.
* `Complex.aligned_of_pairwise_sameRay`: if the summands pairwise lie on a common ray, every
  nonzero summand has the same phase as the sum.
* `Complex.triangle_equality_iff_aligned`: triangle equality holds iff every summand is a
  nonnegative real multiple of a single complex number of norm one.

## Implementation notes

The finite-sum results are proved by induction on the `Finset`, using `sameRay_iff_norm_add` on
the two vectors `v a` and `∑ j ∈ t, v j` at each step; no inner-product structure is involved.
Each is stated with the weakest structure it needs: `sameRay_sum` in an ordered module,
`norm_sum_eq_of_pairwise_sameRay` in a seminormed space, and only the converse
`pairwise_sameRay_of_norm_sum_eq` in a strictly convex space.

`Complex.triangle_equality_iff_aligned` is stated over `ℂ` rather than in a general strictly
convex space on purpose: the norm-one element it produces exists only if the space is nontrivial,
so generalising it would trade `ℂ` for a `Nontrivial` hypothesis.

## TODO

The results above that do not mention `ℂ` belong in a normed-space file, next to
`sameRay_iff_norm_add`; they live here for now because that is where they arose.

## Tags

triangle inequality, triangle equality, same ray, phase, strictly convex space
-/

public section

open Finset

variable {ι : Type*} {s : Finset ι} {i : ι}

theorem sameRay_sum {R M : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [AddCommMonoid M] [Module R M] {x : M} {v : ι → M} (h : ∀ j ∈ s, SameRay R x (v j)) :
    SameRay R x (∑ j ∈ s, v j) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    simpa using (h a (mem_cons_self ..)).add_right (ih fun j hj ↦ h j (mem_cons_of_mem hj))

theorem eq_zero_of_sum_norm_eq_zero {E : Type*} [NormedAddCommGroup E] {v : ι → E}
    (h : ∑ j ∈ s, ‖v j‖ = 0) (hi : i ∈ s) : v i = 0 :=
  norm_eq_zero.1 <| (sum_eq_zero_iff_of_nonneg fun j _ ↦ norm_nonneg (v j)).1 h i hi

theorem norm_sum_eq_of_pairwise_sameRay {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ι → E} (hp : ∀ i ∈ s, ∀ j ∈ s, SameRay ℝ (v i) (v j)) :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    rw [sum_cons, sum_cons,
      (sameRay_sum fun j hj ↦ hp a (mem_cons_self ..) j (mem_cons_of_mem hj)).norm_add,
      ih fun i hi j hj ↦ hp i (mem_cons_of_mem hi) j (mem_cons_of_mem hj)]

section StrictConvex
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {v : ι → E}

theorem pairwise_sameRay_of_norm_sum_eq (h : ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖) :
    ∀ i ∈ s, ∀ j ∈ s, SameRay ℝ (v i) (v j) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    simp only [sum_cons, mem_cons] at h ⊢
    have ht : ‖∑ j ∈ t, v j‖ = ∑ j ∈ t, ‖v j‖ :=
      le_antisymm (norm_sum_le _ _) (by linarith [norm_add_le (v a) (∑ j ∈ t, v j)])
    have hp := ih ht
    have key : ∀ j ∈ t, SameRay ℝ (v a) (v j) := fun j hj ↦
      (sameRay_iff_norm_add.2 (by rw [h, ht])).trans
        (sameRay_sum fun k hk ↦ hp j hj k hk).symm fun h0 ↦
          Or.inr (eq_zero_of_sum_norm_eq_zero (by rw [← ht, h0, norm_zero]) hj)
    rintro i (rfl | hi) j (rfl | hj)
    · exact SameRay.rfl
    · exact key j hj
    · exact (key i hi).symm
    · exact hp i hi j hj

theorem norm_sum_eq_iff_pairwise_sameRay :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ ↔ ∀ i ∈ s, ∀ j ∈ s, SameRay ℝ (v i) (v j) :=
  ⟨pairwise_sameRay_of_norm_sum_eq, norm_sum_eq_of_pairwise_sameRay⟩

end StrictConvex

namespace Complex

variable {v : ι → ℂ}

lemma coeff_of_nonneg_smul {u : ℂ} {k : ℝ} (hk : 0 ≤ k) (hu : u ≠ 0) :
    k = ‖(k : ℂ) * u‖ / ‖u‖ := by
  rw [norm_mul, Complex.norm_of_nonneg hk, mul_div_assoc,
    div_self (norm_ne_zero_iff.2 hu), mul_one]

lemma aligned_of_pairwise_sameRay (hp : ∀ i ∈ s, ∀ j ∈ s, SameRay ℝ (v i) (v j)) (hi : i ∈ s)
    (hvi : v i ≠ 0) : v i / (‖v i‖ : ℂ) = (∑ j ∈ s, v j) / (‖∑ j ∈ s, v j‖ : ℂ) :=
  aligned_of_sameRay hvi
    (fun h0 ↦ hvi (eq_zero_of_sum_norm_eq_zero
      (by rw [← norm_sum_eq_of_pairwise_sameRay hp, h0, norm_zero]) hi))
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
        · rw [← aligned_of_pairwise_sameRay (pairwise_sameRay_of_norm_sum_eq h) hi hv,
            mul_div_cancel₀ _ (ofReal_ne_zero.2 (norm_ne_zero_iff.2 hv))]
  · rw [show ∑ i ∈ s, v i = ((∑ i ∈ s, ‖v i‖ : ℝ) : ℂ) * c by
        rw [ofReal_sum, sum_mul]; exact sum_congr rfl hvc,
      norm_mul, hc, mul_one, Complex.norm_of_nonneg (sum_nonneg fun i _ ↦ norm_nonneg (v i))]

end Complex
