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
theorem radon_partition {ι : Type*} {f : ι → E}
    (h : ¬AffineIndependent 𝕜 f) : ∃ (I : Set ι),
    (Set.Nonempty ((convexHull 𝕜 (f '' I)) ∩ (convexHull 𝕜 (f '' Iᶜ)))) := by
  rw [affineIndependent_iff] at h; push_neg at h
  rcases h with ⟨s1, w, h_wsum, h_vsum, nonzero_w_index, h1, h2⟩
  let I : Finset ι := s1.filter (fun i ↦ 0 ≤ w i)
  let J : Finset ι := s1.filter (fun i ↦ w i < 0)
  use (I : Set ι)

  let weights_sum_I := ∑ i in I, w i
  let weights_sum_J := ∑ i in J, w i
  have h3 : weights_sum_I + weights_sum_J = 0 := by
    simpa only [← h_wsum, not_le] using sum_filter_add_sum_filter_not s1 (fun i ↦ 0 ≤ w i) w

  have h_I_pos : 0 < weights_sum_I := by
    rcases exists_pos_of_sum_zero_of_exists_nonzero _ h_wsum ⟨nonzero_w_index, h1, h2⟩
      with ⟨pos_w_index, h1', h2'⟩
    exact sum_pos'
      (by simp only [mem_filter, and_imp, imp_self, implies_true])
      ⟨pos_w_index, by simp only [mem_filter, h1', h2'.le], h2'⟩

  let w' : ι → 𝕜 := fun i ↦ |w i| / weights_sum_I
  let p : E := ∑ i in I, (w' i) • (f i) -- point of intersection
  let p' : E := ∑ i in J, (w' i) • (f i)

  have h4 : p = p' := by
    apply eq_of_sub_eq_zero
    simp_rw [div_eq_inv_mul, mul_smul, ← smul_sum, ← smul_sub, sub_eq_add_neg, ← sum_neg_distrib]
    apply smul_eq_zero_of_right
    rw [← h_vsum, ← sum_filter_add_sum_filter_not s1 (fun i ↦ 0 ≤ w i) (fun i ↦ w i • f i)]
    congr 1 <;>
    refine sum_congr (by simp only [not_le]) fun i hi ↦ ?_
    · rw [mem_filter] at hi
      rw [abs_eq_self.mpr hi.2]
    · rw [mem_filter, not_le] at hi
      rw [abs_eq_neg_self.mpr hi.2.le, neg_smul, neg_neg]

  have h5_I : ∑ i in I, w' i = 1 := by
    rw [← sum_div, div_eq_one_iff_eq h_I_pos.ne.symm]
    exact sum_congr rfl (by simp)

  have h5_J : ∑ i in J, w' i = 1 := by
    rw [← sum_div, div_eq_one_iff_eq h_I_pos.ne.symm, eq_neg_of_add_eq_zero_left h3,
      ← sum_neg_distrib]
    refine sum_congr rfl ?_
    intro i hi
    simp only [abs_eq_neg_self, (mem_filter.mp hi).2.le]

  have h6 : ∀ v, 0 ≤ w' v := by
    intro; exact div_nonneg (abs_nonneg _) h_I_pos.le

  use p
  apply Set.mem_inter
  · apply (convex_convexHull 𝕜 _).sum_mem (fun i _ ↦ h6 i) h5_I
    exact fun i hi ↦ subset_convexHull _ _ (Set.mem_image_of_mem _ hi)
  · rw [h4]
    apply (convex_convexHull 𝕜 _).sum_mem (fun i _ ↦ h6 i) h5_J
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
  use (↑) '' I; constructor
  · exact Subtype.coe_image_subset _ _
  · rwa [compl_eq_univ_diff, image_diff Subtype.val_injective, image_univ, Subtype.range_coe] at hI