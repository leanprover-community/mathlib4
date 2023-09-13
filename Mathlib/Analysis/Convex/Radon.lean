/-
Copyright (c) 2023 Vasily Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Nesterov
-/
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.Independent
import Mathlib.Tactic.Linarith

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

lemma radon_partition_aux {ι : Type*} {z : ι → E} (w : ι → 𝕜) (I J : Finset ι) (h_disj : Disjoint I J)
    (h_wsum_zero : ∑ i in I, w i + ∑ j in J, w j = 0) (h_wsum_I_pos : ∑ i in I, w i ≠ 0)
    (h_vsum : ∑ i in I, w i • z i + ∑ j in J, w j • z j = 0) :
    (centerMass I w z = centerMass J w z) := by
  ---have h_wsum_J_pos : ∑ i in I, w i > 0
  simp only [centerMass]
  rw [inv_smul_eq_iff₀, smul_comm]; symm; rw [inv_smul_eq_iff₀]
  all_goals simp only [eq_neg_of_add_eq_zero_right h_wsum_zero,
    Iff.mp add_eq_zero_iff_eq_neg h_vsum, neg_smul_neg, neg_ne_zero]
  all_goals assumption

/-- Any family `f` of affine dependent vectors contains a set `I` with the property that
convex hulls of `I` and `Iᶜ` intersect. -/
theorem radon_partition {ι : Type*} {f : ι → E} (h : ¬AffineIndependent 𝕜 f) :
    ∃ (I : Set ι), (convexHull 𝕜 (f '' I) ∩ convexHull 𝕜 (f '' Iᶜ)).Nonempty := by
  rw [affineIndependent_iff] at h; push_neg at h
  rcases h with ⟨s1, w, h_wsum, h_vsum, nonzero_w_index, h1, h2⟩
  let I : Finset ι := s1.filter (fun i ↦ 0 ≤ w i)
  let J : Finset ι := s1.filter (fun i ↦ w i < 0)
  use I

  let p : E := centerMass I w f -- point of intersection
  let w' : ι → 𝕜 := fun i ↦ -1 * (w i)
  let p' : E := centerMass J w' f

  have h_sum_I_J : ∑ j in J, w j + ∑ i in I, w i = 0 := by
    simpa only [← h_wsum, not_lt] using sum_filter_add_sum_filter_not s1 (fun i ↦ w i < 0) w

  have h_I_pos : 0 < ∑ i in I, w i := by
    rcases exists_pos_of_sum_zero_of_exists_nonzero _ h_wsum ⟨nonzero_w_index, h1, h2⟩
      with ⟨pos_w_index, h1', h2'⟩
    exact sum_pos'
      (by simp only [mem_filter, and_imp, imp_self, implies_true])
      ⟨pos_w_index, by simp only [mem_filter, h1', h2'.le, and_self, h2']⟩

  have h3 : p' = p := by
    let p'' : E := centerMass J w f
    calc
      p' = p'' := Finset.centerMass_mul _ _ _ neg_one_lt_zero.ne
      p'' = p := by 
        apply radon_partition_aux
        · rw [Finset.disjoint_left]
          simp [mem_filter]; intros; assumption
        · exact h_sum_I_J
        · simp only [ne_eq]; linarith
        · simpa only [← h_vsum, not_lt] using sum_filter_add_sum_filter_not s1 (fun i ↦ w i < 0) _

  use p
  apply Set.mem_inter
  · exact Convex.centerMass_mem (convex_convexHull _ _) (fun _ hi ↦ (mem_filter.mp hi).2) h_I_pos
      (fun _ hi ↦ subset_convexHull _ _ (Set.mem_image_of_mem _ hi))
  · rw [←h3]
    apply Convex.centerMass_mem (convex_convexHull _ _)
    · simp only [neg_mul, one_mul, Left.nonneg_neg_iff]
      exact fun _ hi ↦ (mem_filter.mp hi).2.le
    · simp only [neg_mul, one_mul, sum_neg_distrib, Left.neg_pos_iff]; linarith
    · intro i hi1
      apply subset_convexHull _ _ (Set.mem_image_of_mem _ _)
      intro hi2
      exact not_lt_of_le (mem_filter.mp hi2).2 (mem_filter.mp hi1).2