/-
Copyright (c) 2025 Chu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chu Zheng
-/

import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Topology.MetricSpace.Similarity

/-!
# Triangle Similarity

This file contains theorems about similarity of triangles, including conditions
for similarity based on sides and angles.

-/

open scoped Congruent EuclideanGeometry

open Similar NNReal Affine

namespace EuclideanGeometry

variable {ι V₁ V₂ P₁ P₂ : Type*}
  [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
  [InnerProductSpace ℝ V₁] [InnerProductSpace ℝ V₂]
  [MetricSpace P₁] [MetricSpace P₂]
  [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
  {v₁ : ι → P₁} {v₂ : ι → P₂}
  {a b c : P₁} {a' b' c' : P₂}

/-- If two triangles have two pairs equal angles, then the triangles are similar. -/
theorem similar_of_angle_angle (h_not_col : ¬ Collinear ℝ {a, b, c})
    (h_not_col' : ¬ Collinear ℝ {a', b', c'})
    (h₁ : ∠ a b c = ∠ a' b' c')
    (h₂ : ∠ b c a = ∠ b' c' a') :
    ![a, b, c] ∼ ![a', b', c'] := by
  have h_pos1 : 0 < dist a b := by simp [dist_pos, ne₁₂_of_not_collinear h_not_col]
  have h_pos1' : 0 < dist a' b' := by simp [dist_pos, ne₁₂_of_not_collinear h_not_col']
  have h_pos2 : 0 < dist b c := by simp [dist_pos, ne₂₃_of_not_collinear h_not_col]
  have h_pos2' : 0 < dist b' c' := by simp [dist_pos, ne₂₃_of_not_collinear h_not_col']
  have h₃ : ∠ c a b = ∠ c' a' b' := by
    have h1 := angle_add_angle_add_angle_eq_pi c (ne₁₂_of_not_collinear h_not_col)
    have h2 := angle_add_angle_add_angle_eq_pi c' (ne₁₂_of_not_collinear h_not_col')
    rw [← h2] at h1
    rw [angle_comm] at h₁ h₂
    rw [h₁, h₂, angle_comm b' c', angle_comm a' b' c'] at h1
    simp_rw [add_left_inj] at h1
    rw [angle_comm, angle_comm b' a' c'] at h1
    exact h1
  have hangle_1 : Real.sin (∠ b c a) ≠ 0 := by
    apply sin_ne_zero_of_not_collinear
    rw [Set.pair_comm, Set.insert_comm]
    exact h_not_col
  have hangle_2 : Real.sin (∠ c a b) ≠ 0 := by
    apply sin_ne_zero_of_not_collinear
    rw [Set.insert_comm, Set.pair_comm]
    exact h_not_col
  have h_sin1 := law_sin c a b
  have h_sin1' := law_sin c' a' b'
  rw [← eq_div_iff_mul_eq (by positivity)] at h_sin1 h_sin1'
  rw [← h₃, ← h₂] at h_sin1'
  rw [h_sin1', mul_div_assoc, mul_div_assoc, mul_right_inj' hangle_1] at h_sin1
  rw [div_eq_div_iff (by positivity) (by positivity), mul_comm] at h_sin1
  have h_sin2 := law_sin a b c
  have h_sin2' := law_sin a' b' c'
  rw [← eq_div_iff_mul_eq (by positivity)] at h_sin2 h_sin2'
  rw [← h₁, ← h₃] at h_sin2'
  rw [h_sin2', mul_div_assoc, mul_div_assoc, mul_right_inj' hangle_2] at h_sin2
  rw [div_eq_div_iff (by positivity) (by positivity), mul_comm] at h_sin2
  apply Similar.reverse_of_three
  apply Similar.comm_left
  exact similar_of_side_side (by positivity) (by positivity) h_sin2 h_sin1.symm

/-- If two triangles have proportional adjacent sides and an equal included angle, then the
triangles are similar. -/
theorem similar_of_side_angle_side (h_not_col : ¬ Collinear ℝ {a, b, c})
    (h_not_col' : ¬ Collinear ℝ {a', b', c'}) (h : ∠ a b c = ∠ a' b' c')
    (hd : dist a b * dist b' c' = dist b c * dist a' b') :
    ![a, b, c] ∼ ![a', b', c'] := by
  have dist_a'b' : dist a' b' ≠ 0 := by simp [ne₁₂_of_not_collinear h_not_col']
  have dist_b'c' : dist b' c' ≠ 0 := by simp [ne₂₃_of_not_collinear h_not_col']
  rw [← div_eq_div_iff dist_a'b' dist_b'c'] at hd
  set k := (dist a b / dist a' b') with hk
  have k_ne : 0 < k := by
    rw [hk]
    apply div_pos
    · simp [dist_pos, ne₁₂_of_not_collinear h_not_col]
    · simp [dist_pos, ne₁₂_of_not_collinear h_not_col']
  have h_ab : dist a b = k * dist a' b' := by
    rw [hk, div_mul, div_self dist_a'b', div_one]
  have h_bc : dist b c = k * dist b' c' := by
    rw [hd, div_mul, div_self dist_b'c', div_one]
  have hcos := law_cos a b c
  rw [dist_comm b _ , dist_comm b' _] at h_bc
  rw [h_ab, h_bc] at hcos
  field_simp at hcos
  rw [h] at hcos
  have hcos' := law_cos a' b' c'
  field_simp at hcos'
  rw [← hcos', ← mul_pow] at hcos
  have dist_ac : 0 < dist a c := by
    simp [dist_pos, ne₁₃_of_not_collinear h_not_col]
  have dist_a'c' : 0 < dist a' c' := by
    simp [dist_pos, ne₁₃_of_not_collinear h_not_col']
  have k_dist_a'c' : 0 ≤ k * dist a' c' := by positivity
  rw [pow_left_inj₀ (le_of_lt dist_ac) k_dist_a'c' (by norm_num)] at hcos
  rw [dist_comm c _, dist_comm c' _] at h_bc
  rw [dist_comm a _, dist_comm a' _] at hcos
  rw [similar_iff_exists_pos_pairwise_dist_eq]
  use k
  refine ⟨k_ne, ?_⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> try {rw [dist_self, dist_self, mul_zero]}
  all_goals simp; grind [dist_comm]

/-- For two similar triangles, the corresponding angles are equal. -/
theorem _root_.Similar.angle_eq (h : ![a, b, c] ∼ ![a', b', c']) :
    ∠ a b c = ∠ a' b' c' := by
  rw [similar_iff_exists_pos_dist_eq] at h
  rcases h with ⟨r, hr_pos, hdist⟩
  have h_ab : dist a b = r * dist a' b' := hdist 0 1
  have h_cb : dist c b = r * dist c' b' := hdist 2 1
  have h_ac : dist a c = r * dist a' c' := hdist 0 2
  have h_cos := law_cos a b c
  rw [h_ab, h_cb, h_ac] at h_cos
  field_simp at h_cos
  have h_cos' := law_cos a' b' c'
  field_simp at h_cos'
  rw [h_cos', sub_right_inj] at h_cos
  by_cases heq : dist a' b' * dist c' b' * 2 = 0
  · rw [mul_eq_zero_iff_right (by norm_num), mul_eq_zero] at heq
    rcases heq with h1 | h2
    · have h_dist_ab : dist a b = 0 := by
        rw [h_ab, h1, mul_zero]
      rw [dist_eq_zero] at h_dist_ab h1
      simp_rw [h_dist_ab, h1, angle_self_left]
    · have h_dist_cb : dist c b = 0 := by
        rw [h_cb, h2, mul_zero]
      rw [dist_eq_zero] at h_dist_cb h2
      simp_rw [h_dist_cb, h2, angle_self_right]
  rw [mul_right_inj' heq] at h_cos
  apply Real.injOn_cos at h_cos
  · rw [h_cos]
  repeat exact ⟨angle_nonneg _ _ _, angle_le_pi _ _ _ ⟩

/-- In two similar triangles, all three corresponding angles are equal. -/
theorem _root_.Similar.angle_eq_all (h : ![a, b, c] ∼ ![a', b', c']) :
    ∠ a b c = ∠ a' b' c' ∧ ∠ b c a = ∠ b' c' a' ∧ ∠ c a b = ∠ c' a' b' := by
  have h2 := h.comm_right.angle_eq
  rw [angle_comm, angle_comm a'] at h2
  have h3 := h.comm_left.angle_eq
  rw [angle_comm, angle_comm b'] at h3
  exact ⟨h.angle_eq, h2, h3⟩

end EuclideanGeometry
