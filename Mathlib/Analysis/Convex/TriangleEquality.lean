/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Triangle equality for finite sums

The triangle inequality `‖∑ i ∈ s, v i‖ ≤ ∑ i ∈ s, ‖v i‖` is an equality exactly when the
summands pairwise lie on a common closed ray (`SameRay`). This extends `sameRay_iff_norm_add`, the two-vector
statement in a strictly convex space, to finite families. Equivalently, the nonzero summands all
have the same `NormedSpace.normalize`, i.e. every summand is a nonnegative real multiple of a
single vector.

## Main statements

* `norm_sum_eq_of_pairwise_sameRay`: summands that pairwise lie on a common closed ray have
  additive norm; this needs no strict convexity.
* `norm_sum_eq_iff_pairwise_sameRay`: in a strictly convex space the converse holds as well.
* `sum_ne_zero_of_pairwise_sameRay`: one nonzero summand on a common ray forces the whole sum to
  be nonzero.
* `normalize_eq_of_pairwise_sameRay`: if the summands pairwise lie on a common closed ray, then
  every nonzero summand has the same normalization as the sum.
* `norm_sum_eq_iff_pairwise_normalize_eq`: for nonzero summands, triangle equality holds iff all
  the summands have the same normalization.
* `norm_sum_eq_iff_exists_smul`: triangle equality holds iff every summand is a nonnegative real
  multiple of a single vector.

## Tags

triangle inequality, triangle equality, same ray, strictly convex space
-/

public section

open scoped Function

open Finset

variable {ι : Type*} {s : Finset ι} {i : ι}

section Seminormed

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {v : ι → E}

/-- If the summands pairwise lie on a common closed ray, the norm of their sum is the sum of
their norms. -/
lemma norm_sum_eq_of_pairwise_sameRay (hp : (s : Set ι).Pairwise (SameRay ℝ on v)) :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    simp only [coe_cons, Set.pairwise_insert_of_symm_of_notMem ha, SetLike.mem_coe] at hp
    rw [sum_cons, sum_cons, (SameRay.sum_right hp.2).norm_add, ih hp.1]

end Seminormed

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {v : ι → E}

omit [StrictConvexSpace ℝ E] in
lemma sum_ne_zero_of_pairwise_sameRay (hp : (s : Set ι).Pairwise (SameRay ℝ on v)) (hi : i ∈ s)
    (hvi : v i ≠ 0) : ∑ j ∈ s, v j ≠ 0 := by
  rw [← norm_pos_iff, norm_sum_eq_of_pairwise_sameRay hp]
  exact (norm_pos_iff.2 hvi).trans_le (single_le_sum (fun j _ ↦ norm_nonneg (v j)) hi)

/-- **Triangle equality** for a finite sum: the norm of the sum equals the sum of the norms
exactly when the summands pairwise lie on a common closed ray. -/
theorem norm_sum_eq_iff_pairwise_sameRay :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ ↔ (s : Set ι).Pairwise (SameRay ℝ on v) := by
  refine ⟨fun h i hi j hj hij ↦ ?_, norm_sum_eq_of_pairwise_sameRay⟩
  classical
  have : {i, j} ⊆ s := by grind
  rw [← sum_sdiff this, ← sum_sdiff this, sum_pair hij, sum_pair hij] at h
  grind [sameRay_iff_norm_add, norm_sum_le, norm_add_le]

omit [StrictConvexSpace ℝ E] in
/-- If the summands pairwise lie on a common closed ray and one of them is nonzero, then it has
the same normalization as the sum. -/
lemma normalize_eq_of_pairwise_sameRay (hp : (s : Set ι).Pairwise (SameRay ℝ on v)) (hi : i ∈ s)
    (hvi : v i ≠ 0) :
    NormedSpace.normalize (v i) = NormedSpace.normalize (∑ j ∈ s, v j) :=
  (sameRay_sum_right_of_pairwise hp hi).normalize_eq hvi (sum_ne_zero_of_pairwise_sameRay hp hi hvi)

/-- **Triangle equality** for nonzero summands: the norm of the sum equals the sum of the norms
exactly when all the summands have the same normalization. -/
theorem norm_sum_eq_iff_pairwise_normalize_eq (hv : ∀ i ∈ s, v i ≠ 0) :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ ↔
      ∀ i ∈ s, ∀ j ∈ s, NormedSpace.normalize (v i) = NormedSpace.normalize (v j) := by
  simp +contextual only [norm_sum_eq_iff_pairwise_sameRay,
    ← NormedSpace.sameRay_iff_normalize_eq_of_ne (hv _ _) (hv _ _)]
  exact ⟨fun h i hi j hj ↦ h.forall₂ hi hj, fun h i hi j hj hij ↦ h _ hi _ hj⟩

/-- **Triangle equality**: the norm of a finite sum equals the sum of the norms exactly when every
summand is a nonnegative real multiple of a single vector. -/
theorem norm_sum_eq_iff_exists_smul :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ ↔ ∃ c : E, ∀ i ∈ s, v i = ‖v i‖ • c := by
  rw [norm_sum_eq_iff_pairwise_sameRay]
  refine ⟨fun h ↦ ⟨NormedSpace.normalize (∑ i ∈ s, v i), fun i hi ↦ ?_⟩, ?_⟩
  · rcases eq_or_ne (v i) 0 with hv | hv
    · simp [hv]
    · rw [← normalize_eq_of_pairwise_sameRay h hi hv, NormedSpace.norm_smul_normalize]
  · rintro ⟨c, hvc⟩ i hi j hj _
    rw [Function.onFun, hvc i hi, hvc j hj]
    exact (SameRay.sameRay_nonneg_smul_left c (norm_nonneg _)).nonneg_smul_right (norm_nonneg _)

end Normed
