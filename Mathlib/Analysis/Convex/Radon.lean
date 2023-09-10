/-
Copyright (c) 2023 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.Independent

/-!
# Radon's convexity theorem

Radon's theorem on convex sets states that any affine dependent set can be partitioned into two sets
whose convex hulls intersect.

## Main results

* `Radon_partition`: Radon convexity theorem

## Tags

convex hull, radon

-/


open Set Finset
open BigOperators

universe u

variable {𝕜 : Type*} {E : Type u} [LinearOrderedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- Any family `f` of affine dependent vectors contains a set `I` with the property that
convex hulls of `I` and `Iᶜ` intersect. -/
theorem radon_partition {ι : Type*} {f : ι → E} (h : ¬AffineIndependent 𝕜 f) :
    ∃ (I : Set ι), (convexHull 𝕜 (f '' I) ∩ convexHull 𝕜 (f '' Iᶜ)).Nonempty := by
  rw [affineIndependent_iff] at h; push_neg at h
  rcases h with ⟨s1, w, h_wsum, h_vsum, nonzero_w_index, h1, h2⟩
  let I : Finset ι := s1.filter (fun i ↦ 0 ≤ w i)
  let J : Finset ι := s1.filter (fun i ↦ w i < 0)
  use I

  let w' : ι → 𝕜 := fun i ↦ |w i|
  let p : E := centerMass I w' f -- point of intersection
  let p' : E := centerMass J w' f

  have h6 : ∀ v, 0 ≤ w' v := by
    intro; positivity

  let weights_sum_I := ∑ i in I, w' i
  let weights_sum_J := ∑ i in J, w' i

  have h3 : weights_sum_J = weights_sum_I := by
    simp; rw [@sum_congr _ _ J _ _ (fun i ↦ -w i) _ rfl, @sum_congr _ _ I _ _ w _ rfl,
      sum_neg_distrib, neg_eq_iff_add_eq_zero]
    · simpa only [← add_eq_zero_iff_eq_neg, not_le, ← h_wsum, add_comm]
      using sum_filter_add_sum_filter_not s1 (fun i ↦ 0 ≤ w i) w
    all_goals intro i hi
    · rw [abs_eq_self.mpr]; exact (mem_filter.mp hi).2
    · rw [abs_eq_neg_self.mpr]; exact le_of_lt (mem_filter.mp hi).2

  have h_I_pos : 0 < weights_sum_I := by
    rcases exists_pos_of_sum_zero_of_exists_nonzero _ h_wsum ⟨nonzero_w_index, h1, h2⟩
      with ⟨pos_w_index, h1', h2'⟩
    exact sum_pos' (fun i _ => h6 i)
      ⟨pos_w_index, by simp only [mem_filter, h1', h2'.le], abs_pos_of_pos h2'⟩

  have h4 : p = p' := by
    apply eq_of_sub_eq_zero
    simp only [centerMass]; simp_rw [h3, ← smul_sub]
    apply smul_eq_zero.mpr; right
    rw [@sum_congr _ _ J _ _ (fun i ↦ -(w i • f i)) _ rfl,
      @sum_congr _ _ I _ _ (fun i ↦ w i • f i) _ rfl, sum_neg_distrib, sub_neg_eq_add]
    · simp_rw [← h_vsum, ← sum_filter_add_sum_filter_not s1 (fun i ↦ 0 ≤ w i) (fun i ↦ w i • f i)]
      simp only [not_le]
    all_goals intro i hi
    · rw [abs_eq_self.mpr]; exact (mem_filter.mp hi).2
    · rw [abs_eq_neg_self.mpr, neg_smul]; exact le_of_lt (mem_filter.mp hi).2

  use p
  apply Set.mem_inter
  · apply Convex.centerMass_mem (convex_convexHull _ _) (fun i _ => h6 i) h_I_pos
    exact fun i hi ↦ subset_convexHull _ _ (Set.mem_image_of_mem _ hi)
  · rw [h4]
    apply Convex.centerMass_mem (convex_convexHull _ _) (fun i _ => h6 i)
    simp_rw [h3]; exact h_I_pos
    intro i hi1
    apply subset_convexHull _ _ (Set.mem_image_of_mem _ _)
    intro hi2
    exact not_lt_of_le (mem_filter.mp hi2).2 (mem_filter.mp hi1).2

/-- If `s` is a set of affine dependent vectors, it has subset `I` with the property that
convex hulls of `I` and `s \ I` intersect. -/
theorem radon_set_partition (s : Set E)
    (h : ¬AffineIndependent 𝕜 ((↑) : s → E)) : ∃ (I : Set E), (I ⊆ s) ∧
    (Set.Nonempty ((convexHull 𝕜 I) ∩ (convexHull 𝕜 (s \ I)))) := by
  obtain ⟨I, hI⟩ := radon_partition h
  refine ⟨(↑) '' I, Subtype.coe_image_subset _ _, ?_⟩
  rwa [compl_eq_univ_diff, image_diff Subtype.val_injective, image_univ, Subtype.range_coe] at hI
