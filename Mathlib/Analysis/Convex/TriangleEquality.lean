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
summands pairwise lie on a common closed ray. This extends `sameRay_iff_norm_add`, the two-vector
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

## Implementation notes

The results are proved by induction on the `Finset`, applying `sameRay_iff_norm_add` to the two
vectors `v a` and `∑ j ∈ t, v j` at each step, so no inner-product structure is involved. Each is
stated with the weakest structure it needs, which is why the forcing direction is separated from
the iff: only it can fail without strict convexity.

## Tags

triangle inequality, triangle equality, same ray, strictly convex space
-/

public section

open scoped Function

open Finset

variable {ι : Type*} {s : Finset ι} {i : ι}

variable {R M : Type*} [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
  [AddCommMonoid M] [Module R M]

instance : Std.Refl (SameRay R (M := M)) where
  refl := .refl

instance : Std.Symm (SameRay R (M := M)) where
  symm _ _ := .symm

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
    rw [sum_cons, sum_cons, (sum_induction v _ (fun _ _ ↦ SameRay.add_right)
      (SameRay.zero_right _) hp.2).norm_add, ih hp.1]

end Seminormed

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {v : ι → E}

omit [NormedSpace ℝ E] [StrictConvexSpace ℝ E] in
lemma eq_zero_of_sum_norm_eq_zero (h : ∑ j ∈ s, ‖v j‖ = 0) (hi : i ∈ s) : v i = 0 :=
  norm_eq_zero.1 <| (sum_eq_zero_iff_of_nonneg fun j _ ↦ norm_nonneg (v j)).1 h i hi

omit [StrictConvexSpace ℝ E] in
lemma sum_ne_zero_of_pairwise_sameRay (hp : (s : Set ι).Pairwise (SameRay ℝ on v)) (hi : i ∈ s)
    (hvi : v i ≠ 0) : ∑ j ∈ s, v j ≠ 0 := fun h0 ↦
  hvi <| eq_zero_of_sum_norm_eq_zero
    (by rw [← norm_sum_eq_of_pairwise_sameRay hp , h0, norm_zero] ) hi

/-- **Triangle equality** for a finite sum: the norm of the sum equals the sum of the norms
exactly when the summands pairwise lie on a common closed ray. -/
theorem norm_sum_eq_iff_pairwise_sameRay :
        ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ ↔ (s : Set ι).Pairwise (SameRay ℝ on v) := by
  refine ⟨?_, norm_sum_eq_of_pairwise_sameRay⟩
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a t ha ih =>
    simp only [sum_cons, coe_cons, Set.pairwise_insert_of_symm_of_notMem ha]
    intro h
    have ht : ‖∑ j ∈ t, v j‖ = ∑ j ∈ t, ‖v j‖ :=
      le_antisymm (norm_sum_le _ _) (by linarith [norm_add_le (v a) (∑ j ∈ t, v j)])
    refine ⟨ih ht, ?_⟩
    have hat : SameRay ℝ (v a) (∑ j ∈ t, v j) := sameRay_iff_norm_add.2 (by rw [h, ht])
    exact fun j hj ↦ hat.trans (sameRay_sum (ih ht) hj).symm
      fun h ↦ Or.inr <| eq_zero_of_sum_norm_eq_zero (by simpa [h] using ht.symm) hj

omit [StrictConvexSpace ℝ E] in
/-- If the summands pairwise lie on a common closed ray and one of them is nonzero, then it has
the same normalization as the sum. -/
lemma normalize_eq_of_pairwise_sameRay (hp : (s : Set ι).Pairwise (SameRay ℝ on v)) (hi : i ∈ s)
    (hvi : v i ≠ 0) :
    NormedSpace.normalize (v i) = NormedSpace.normalize (∑ j ∈ s, v j) :=
  (sameRay_sum hp hi).normalize_eq hvi (sum_ne_zero_of_pairwise_sameRay hp hi hvi)

/-- **Triangle equality** for nonzero summands: the norm of the sum equals the sum of the norms
exactly when all the summands have the same normalization. -/
theorem norm_sum_eq_iff_pairwise_normalize_eq (hv : ∀ i ∈ s, v i ≠ 0) :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ ↔
      ∀ i ∈ s, ∀ j ∈ s, NormedSpace.normalize (v i) = NormedSpace.normalize (v j) := by
  rw [norm_sum_eq_iff_pairwise_sameRay]
  exact ⟨fun h i hi j hj ↦ (NormedSpace.sameRay_iff_normalize_eq (hv i hi) (hv j hj)).1
      (h.forall₂ hi hj),
    fun h i hi j hj _ ↦ (NormedSpace.sameRay_iff_normalize_eq (hv i hi) (hv j hj)).2 (h i hi j hj)⟩

/-- **Triangle equality**: the norm of a finite sum equals the sum of the norms exactly when every
summand is a nonnegative real multiple of a single vector. -/
theorem norm_sum_eq_iff_exists_smul :
    ‖∑ i ∈ s, v i‖ = ∑ i ∈ s, ‖v i‖ ↔ ∃ c : E, ∀ i ∈ s, v i = ‖v i‖ • c := by
  refine ⟨fun h ↦ ⟨NormedSpace.normalize (∑ i ∈ s, v i), fun i hi ↦ ?_⟩, ?_⟩
  · rcases eq_or_ne (v i) 0 with hv | hv
    · simp [hv]
    · rw [← normalize_eq_of_pairwise_sameRay (norm_sum_eq_iff_pairwise_sameRay.1 h) hi hv,
        NormedSpace.norm_smul_normalize]
  · rintro ⟨c, hvc⟩
    rw [norm_sum_eq_iff_pairwise_sameRay]
    intro i hi j hj _
    change SameRay ℝ (v i) (v j)
    rw [hvc i hi, hvc j hj]
    exact (SameRay.sameRay_nonneg_smul_left c (norm_nonneg _)).nonneg_smul_right (norm_nonneg _)

end Normed
