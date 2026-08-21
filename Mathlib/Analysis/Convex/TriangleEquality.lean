/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace

/-!
# Triangle equality for finite sums

The triangle inequality `‖∑ i ∈ s, v i‖ ≤ ∑ i ∈ s, ‖v i‖` is an equality exactly when the
summands pairwise lie on a common closed ray. This extends `sameRay_iff_norm_add`, the two-vector
statement in a strictly convex space, to finite families.

## Main statements

* `norm_sum_eq_of_pairwise_sameRay`: summands that pairwise lie on a common closed ray have
  additive norm; this needs no strict convexity.
* `norm_sum_eq_iff_pairwise_sameRay`: in a strictly convex space the converse holds as well.
* `sum_ne_zero_of_pairwise_sameRay`: one nonzero summand on a common ray forces the whole sum to
  be nonzero.

## Implementation notes

The results are proved by induction on the `Finset`, applying `sameRay_iff_norm_add` to the two
vectors `v a` and `∑ j ∈ t, v j` at each step, so no inner-product structure is involved. Each is
stated with the weakest structure it needs, which is why the forcing direction is separated from
the iff: only it can fail without strict convexity.

## Tags

triangle inequality, triangle equality, same ray, strictly convex space
-/

public section

open Finset

variable {ι : Type*} {s : Finset ι} {i : ι}

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {v : ι → E}

/-- If the summands pairwise lie on a common closed ray, the norm of their sum is the sum of
their norms. -/
lemma norm_sum_eq_of_pairwise_sameRay (hp : ∀ i ∈ s, ∀ j ∈ s, SameRay ℝ (v i) (v j)) :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    rw [sum_cons, sum_cons,
      (sameRay_sum fun j hj ↦ hp a (mem_cons_self ..) j (mem_cons_of_mem hj)).norm_add,
      ih fun i hi j hj ↦ hp i (mem_cons_of_mem hi) j (mem_cons_of_mem hj)]

end Seminormed

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {v : ι → E}

omit [NormedSpace ℝ E] [StrictConvexSpace ℝ E] in
/-- If the norms of a finite family sum to zero, then every member of the family vanishes. -/
lemma eq_zero_of_sum_norm_eq_zero (h : ∑ j ∈ s, ‖v j‖ = 0) (hi : i ∈ s) : v i = 0 :=
  norm_eq_zero.1 <| (sum_eq_zero_iff_of_nonneg fun j _ ↦ norm_nonneg (v j)).1 h i hi

omit [StrictConvexSpace ℝ E] in
/-- A single nonzero summand forces the sum to be nonzero, provided the summands pairwise lie on
a common closed ray. -/
lemma sum_ne_zero_of_pairwise_sameRay (hp : ∀ i ∈ s, ∀ j ∈ s, SameRay ℝ (v i) (v j)) (hi : i ∈ s)
    (hvi : v i ≠ 0) : ∑ j ∈ s, v j ≠ 0 := fun h0 ↦
  hvi <| eq_zero_of_sum_norm_eq_zero
    (by rw [← norm_sum_eq_of_pairwise_sameRay hp, h0, norm_zero]) hi

/-- **Triangle equality** for a finite sum: the norm of the sum equals the sum of the norms
exactly when the summands pairwise lie on a common closed ray. -/
theorem norm_sum_eq_iff_pairwise_sameRay :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ ↔ ∀ i ∈ s, ∀ j ∈ s, SameRay ℝ (v i) (v j) := by
  refine ⟨?_, norm_sum_eq_of_pairwise_sameRay⟩
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    simp only [sum_cons, mem_cons]
    intro h
    have ht : ‖∑ j ∈ t, v j‖ = ∑ j ∈ t, ‖v j‖ :=
      le_antisymm (norm_sum_le _ _) (by linarith [norm_add_le (v a) (∑ j ∈ t, v j)])
    have hp := ih ht
    have hat : SameRay ℝ (v a) (∑ j ∈ t, v j) := sameRay_iff_norm_add.2 (by rw [h, ht])
    have key : ∀ j ∈ t, SameRay ℝ (v a) (v j) := fun j hj ↦
      hat.trans (sameRay_sum fun k hk ↦ hp j hj k hk).symm fun h0 ↦
        Or.inr (eq_zero_of_sum_norm_eq_zero (by rw [← ht, h0, norm_zero]) hj)
    rintro i (rfl | hi) j (rfl | hj)
    · exact SameRay.rfl
    · exact key j hj
    · exact (key i hi).symm
    · exact hp i hi j hj

end Normed
