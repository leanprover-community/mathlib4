/-
Copyright (c) 2025 Chu Zheng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chu Zheng, Wang Ying
-/
module

public import Mathlib.Geometry.Euclidean.Triangle
public import Mathlib.Topology.MetricSpace.Similarity
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle

/-!
# Triangle Similarity

This file contains theorems about similarity of triangles, including conditions
for similarity based on sides and angles.

-/

public section

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
theorem similar_of_angle_angle (h_not_col : ¬ Collinear ℝ {a, b, c}) (h₁ : ∠ a b c = ∠ a' b' c')
    (h₂ : ∠ b c a = ∠ b' c' a') :
    ![a, b, c] ∼ ![a', b', c'] := by
  have hne_pi_div_two : ∠ a b c ≠ Real.pi / 2 ∨ ∠ b c a ≠ Real.pi / 2 := by
    by_contra! hq
    have := angle_lt_pi_div_two_of_angle_eq_pi_div_two hq.1 (ne₂₃_of_not_collinear h_not_col).symm
    grind
  have not_all_eq : a' ≠ b' ∨ b' ≠ c' ∨ a' ≠ c' := by grind [angle_self_left]
  have h_not_col' : ¬ Collinear ℝ {a', b', c'} := by
    grind only [collinear_iff_eq_or_eq_or_angle_eq_zero_or_angle_eq_pi, angle_self_right,
      angle_self_left, Set.insert_comm, Set.pair_comm]
  have h_pos1 : 0 < dist a b := by simp [dist_pos, ne₁₂_of_not_collinear h_not_col]
  have h_pos1' : 0 < dist a' b' := by simp [dist_pos, ne₁₂_of_not_collinear h_not_col']
  have h_pos2 : 0 < dist b c := by simp [dist_pos, ne₂₃_of_not_collinear h_not_col]
  have h_pos2' : 0 < dist b' c' := by simp [dist_pos, ne₂₃_of_not_collinear h_not_col']
  have h₃ : ∠ c a b = ∠ c' a' b' := by
    have hsum := angle_add_angle_add_angle_eq_pi c (ne₁₂_of_not_collinear h_not_col)
    have hsum' := angle_add_angle_add_angle_eq_pi c' (ne₁₂_of_not_collinear h_not_col')
    grind [angle_comm]
  have h_sin_ne1 : Real.sin (∠ b c a) ≠ 0 := by
    grind only [sin_ne_zero_of_not_collinear, Set.pair_comm, Set.insert_comm]
  have h_sin_ne2 : Real.sin (∠ c a b) ≠ 0 := by
    grind only [sin_ne_zero_of_not_collinear, Set.pair_comm, Set.insert_comm]
  have h_sin1 := law_sin c a b
  have h_sin1' := law_sin c' a' b'
  rw [← eq_div_iff_mul_eq (by positivity)] at h_sin1 h_sin1'
  rw [← h₃, ← h₂] at h_sin1'
  rw [h_sin1', mul_div_assoc, mul_div_assoc, mul_right_inj' h_sin_ne1,
    div_eq_div_iff (by positivity) (by positivity), mul_comm] at h_sin1
  have h_sin2 := law_sin a b c
  have h_sin2' := law_sin a' b' c'
  rw [← eq_div_iff_mul_eq (by positivity)] at h_sin2 h_sin2'
  rw [← h₁, ← h₃] at h_sin2'
  rw [h_sin2', mul_div_assoc, mul_div_assoc, mul_right_inj' h_sin_ne2,
    div_eq_div_iff (by positivity) (by positivity), mul_comm] at h_sin2
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
  have k_pos : 0 < k := by
    rw [hk]
    apply div_pos
    · simp [dist_pos, ne₁₂_of_not_collinear h_not_col]
    · simp [dist_pos, ne₁₂_of_not_collinear h_not_col']
  have h_ab : dist a b = k * dist a' b' := by grind
  have h_bc : dist b c = k * dist b' c' := by grind
  have hcos := law_cos a b c
  rw [dist_comm b _, dist_comm b' _] at h_bc
  rw [h_ab, h_bc] at hcos
  field_simp at hcos
  rw [h] at hcos
  have hcos' := law_cos a' b' c'
  field_simp at hcos'
  rw [← hcos', ← mul_pow] at hcos
  have dist_ac_pos : 0 < dist a c := by grind [dist_pos, ne₁₃_of_not_collinear]
  have k_dist_a'c' : 0 ≤ k * dist a' c' := by positivity
  rw [pow_left_inj₀ (le_of_lt dist_ac_pos) k_dist_a'c' (by norm_num), dist_comm a _,
    dist_comm a' _] at hcos
  rw [dist_comm c _, dist_comm c' _] at h_bc
  rw [similar_iff_exists_pos_pairwise_dist_eq]
  use k
  refine ⟨k_pos, ?_⟩
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
    · have h_dist_ab : dist a b = 0 := by grind
      rw [dist_eq_zero] at h_dist_ab h1
      simp_rw [h_dist_ab, h1, angle_self_left]
    · have h_dist_cb : dist c b = 0 := by grind
      rw [dist_eq_zero] at h_dist_cb h2
      simp_rw [h_dist_cb, h2, angle_self_right]
  rw [mul_right_inj' heq] at h_cos
  apply Real.injOn_cos at h_cos
  repeat grind [angle_nonneg, angle_le_pi]

/-- In two similar triangles, all three corresponding angles are equal. -/
theorem _root_.Similar.angle_eq_all (h : ![a, b, c] ∼ ![a', b', c']) :
    ∠ a b c = ∠ a' b' c' ∧ ∠ b c a = ∠ b' c' a' ∧ ∠ c a b = ∠ c' a' b' :=
  ⟨h.angle_eq, h.comm_left.comm_right.angle_eq, h.comm_right.comm_left.angle_eq⟩

end EuclideanGeometry

namespace Orientation
open Module EuclideanGeometry
variable {ι V₁ V₂ P₁ P₂ : Type*}
  [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
  [InnerProductSpace ℝ V₁] [InnerProductSpace ℝ V₂]
  [MetricSpace P₁] [MetricSpace P₂]
  [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
  [Fact (finrank ℝ V₁ = 2)] [Fact (finrank ℝ V₂ = 2)]
  [Oriented ℝ V₁ (Fin 2)] [Oriented ℝ V₂ (Fin 2)]
  {v₁ : ι → P₁} {v₂ : ι → P₂}
  {a b c : P₁} {a' b' c' : P₂}

/-- If two triangles have two pairs equal oangles, then the triangles are similar. -/
theorem similar_of_oangle_oangle (h_not_col : ¬ Collinear ℝ {a, b, c}) (h₁ : ∡ a b c = ∡ a' b' c')
    (h₂ : ∡ b c a = ∡ b' c' a') : ![a, b, c] ∼ ![a', b', c'] := by
  have h_not_col2: ¬ Collinear ℝ ({a', b', c'} : Set P₂) := by
    rwa [← oangle_eq_zero_or_eq_pi_iff_collinear, ← h₁, oangle_eq_zero_or_eq_pi_iff_collinear]
  apply similar_of_angle_angle h_not_col
  · rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (ne₁₂_of_not_collinear h_not_col)
      (ne₂₃_of_not_collinear h_not_col).symm, EuclideanGeometry.angle_eq_abs_oangle_toReal
      (ne₁₂_of_not_collinear h_not_col2) (ne₂₃_of_not_collinear h_not_col2).symm, h₁]
  · rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (ne₂₃_of_not_collinear h_not_col)
      (ne₁₃_of_not_collinear h_not_col), EuclideanGeometry.angle_eq_abs_oangle_toReal
      (ne₂₃_of_not_collinear h_not_col2) (ne₁₃_of_not_collinear h_not_col2), h₂]

/-- If two triangles have two pairs contrary oangles, then the triangles are similar. -/
theorem similar_of_oangle_oangle_neg (h_not_col : ¬ Collinear ℝ {a, b, c})
    (h₁ : ∡ a b c = -∡ a' b' c') (h₂ : ∡ b c a = -∡ b' c' a') : ![a, b, c] ∼ ![a', b', c'] := by
  rw [← neg_eq_iff_eq_neg] at h₁ h₂
  have h_not_col2: ¬ Collinear ℝ ({a', b', c'} : Set P₂) := by
    rwa [← oangle_eq_zero_or_eq_pi_iff_collinear, ← h₁, ← EuclideanGeometry.oangle_rev,
      EuclideanGeometry.oangle_eq_zero_iff_oangle_rev_eq_zero,
      EuclideanGeometry.oangle_eq_pi_iff_oangle_rev_eq_pi, oangle_eq_zero_or_eq_pi_iff_collinear]
  apply similar_of_angle_angle h_not_col
  · rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (ne₁₂_of_not_collinear h_not_col)
      (ne₂₃_of_not_collinear h_not_col).symm, EuclideanGeometry.angle_eq_abs_oangle_toReal
      (ne₁₂_of_not_collinear h_not_col2) (ne₂₃_of_not_collinear h_not_col2).symm, ← h₁]
    simp only [Real.Angle.abs_toReal_neg]
  · rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (ne₂₃_of_not_collinear h_not_col)
      (ne₁₃_of_not_collinear h_not_col), EuclideanGeometry.angle_eq_abs_oangle_toReal
      (ne₂₃_of_not_collinear h_not_col2) (ne₁₃_of_not_collinear h_not_col2), ← h₂]
    simp only [Real.Angle.abs_toReal_neg]

/-- If two triangles have proportional adjacent sides and an equal included oangle, then the
triangles are similar. -/
theorem similar_of_side_oangle_side (h_not_col : ¬ Collinear ℝ {a, b, c})
    (h : ∡ a b c = ∡ a' b' c') (hd : dist a b * dist b' c' = dist b c * dist a' b') :
    ![a, b, c] ∼ ![a', b', c'] := by
  have h_not_col' : ¬ Collinear ℝ {a', b', c'} := by
    rwa [← oangle_eq_zero_or_eq_pi_iff_collinear, ← h, oangle_eq_zero_or_eq_pi_iff_collinear]
  refine similar_of_side_angle_side h_not_col h_not_col' ?_ hd
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (ne₁₂_of_not_collinear h_not_col)
    (ne₂₃_of_not_collinear h_not_col).symm, EuclideanGeometry.angle_eq_abs_oangle_toReal
    (ne₁₂_of_not_collinear h_not_col') (ne₂₃_of_not_collinear h_not_col').symm, h]

/-- If two triangles have proportional adjacent sides and an contrary included oangle, then the
triangles are similar. -/
theorem similar_of_side_oangle_neg_side (h_not_col : ¬ Collinear ℝ {a, b, c})
    (h : ∡ a b c = -∡ a' b' c') (hd : dist a b * dist b' c' = dist b c * dist a' b') :
    ![a, b, c] ∼ ![a', b', c'] := by
  have h_not_col' : ¬ Collinear ℝ {a', b', c'} := by
    rw [← neg_eq_iff_eq_neg] at h
    rwa [← oangle_eq_zero_or_eq_pi_iff_collinear, ← h, ← EuclideanGeometry.oangle_rev,
      EuclideanGeometry.oangle_eq_zero_iff_oangle_rev_eq_zero,
      EuclideanGeometry.oangle_eq_pi_iff_oangle_rev_eq_pi, oangle_eq_zero_or_eq_pi_iff_collinear]
  refine similar_of_side_angle_side h_not_col h_not_col' ?_ hd
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal (ne₁₂_of_not_collinear h_not_col)
    (ne₂₃_of_not_collinear h_not_col).symm, EuclideanGeometry.angle_eq_abs_oangle_toReal
    (ne₁₂_of_not_collinear h_not_col') (ne₂₃_of_not_collinear h_not_col').symm, h,
    Real.Angle.abs_toReal_neg]

/-- For two similar triangles, the corresponding oangles are equal or contrary. -/
theorem _root_.Similar.oangle_eq_or_neg (h : ![a, b, c] ∼ ![a', b', c'])
    (h_not_col : ¬ Collinear ℝ {a, b, c}) (h_not_col' : ¬ Collinear ℝ {a', b', c'}) :
    ∡ a b c = ∡ a' b' c' ∨ ∡ a b c = -∡ a' b' c' := by
  have h1 := h.angle_eq
  have h_1 := EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle (ne₁₂_of_not_collinear h_not_col)
    (ne₂₃_of_not_collinear h_not_col).symm
  have h_2 := EuclideanGeometry.oangle_eq_angle_or_eq_neg_angle (ne₁₂_of_not_collinear h_not_col')
    (ne₂₃_of_not_collinear h_not_col').symm
  rcases h_1 with h₁ | h₁ <;> rcases h_2 with h₂ | h₂
  · left; rw [h₁, h₂, h1]
  · right; rw [h₁, h₂, h1, neg_neg]
  · right; rw [h₁, h₂, h1]
  · left; rw [h₁, h₂, h1]

/-- In two similar triangles, all three corresponding oangles are equal if the signs are equal. -/
theorem _root_.Similar.oangle_eq_all_if_sign_eq (h : ![a, b, c] ∼ ![a', b', c'])
    (h_not_col : ¬ Collinear ℝ {a, b, c}) (h_not_col' : ¬ Collinear ℝ {a', b', c'})
    (h₁ : (∡ a b c).sign = (∡ a' b' c').sign) :
    ∡ a b c = ∡ a' b' c' ∧ ∡ b c a = ∡ b' c' a' ∧ ∡ c a b = ∡ c' a' b' := by
  have h_ab := ne₁₂_of_not_collinear h_not_col
  have h_bc := ne₂₃_of_not_collinear h_not_col
  have h_ac := ne₁₃_of_not_collinear h_not_col
  have h_ab' := ne₁₂_of_not_collinear h_not_col'
  have h_bc' := ne₂₃_of_not_collinear h_not_col'
  have h_ac' := ne₁₃_of_not_collinear h_not_col'
  have h_sum := oangle_add_oangle_add_oangle_eq_pi h_ab.symm h_bc.symm h_ac
  have h_sum' := oangle_add_oangle_add_oangle_eq_pi h_ab'.symm h_bc'.symm h_ac'
  have h_bca : ¬ Collinear ℝ {b, c, a} := by rwa [Set.insert_comm, Set.pair_comm] at h_not_col
  have h_bca' : ¬ Collinear ℝ {b', c', a'} := by rwa [Set.insert_comm, Set.pair_comm] at h_not_col'
  have h1 : ∡ a b c = ∡ a' b' c' := by
    have h_eq_or_neg := h.oangle_eq_or_neg h_not_col h_not_col'
    rcases h_eq_or_neg with h_eq | h_eq_neg
    · exact h_eq
    · simp only [h_eq_neg, Real.Angle.sign_neg, SignType.neg_eq_self_iff,
        oangle_sign_eq_zero_iff_collinear, h_not_col'] at h₁
  have h₂ : (∡ b c a).sign = (∡ b' c' a').sign := by
    nth_rw 2 [oangle_rotate_sign]
    rwa [oangle_rotate_sign]
  have h2 : ∡ b c a = ∡ b' c' a' := by
    have h_eq_or_neg := h.comm_left.comm_right.oangle_eq_or_neg h_bca h_bca'
    rcases h_eq_or_neg with h_eq | h_eq_neg
    · exact h_eq
    · simp only [h_eq_neg, Real.Angle.sign_neg, SignType.neg_eq_self_iff,
        oangle_sign_eq_zero_iff_collinear, h_bca'] at h₂
  have h3 : ∡ c a b = ∡ c' a' b' := by grind only
  refine ⟨h1, h2, h3⟩

/-- In two similar triangles, all three corresponding oangles are contrary if the signs are
contrary. -/
theorem _root_.Similar.oangle_neg_all_if_sign_neg (h : ![a, b, c] ∼ ![a', b', c'])
    (h_not_col : ¬ Collinear ℝ {a, b, c}) (h_not_col' : ¬ Collinear ℝ {a', b', c'})
    (h₁ : (∡ a b c).sign = -(∡ a' b' c').sign) :
    ∡ a b c = -∡ a' b' c' ∧ ∡ b c a = -∡ b' c' a' ∧ ∡ c a b = -∡ c' a' b' := by
  have h_ab := ne₁₂_of_not_collinear h_not_col
  have h_bc := ne₂₃_of_not_collinear h_not_col
  have h_ac := ne₁₃_of_not_collinear h_not_col
  have h_ab' := ne₁₂_of_not_collinear h_not_col'
  have h_bc' := ne₂₃_of_not_collinear h_not_col'
  have h_ac' := ne₁₃_of_not_collinear h_not_col'
  have h_sum := oangle_add_oangle_add_oangle_eq_pi h_ab.symm h_bc.symm h_ac
  have h_sum' := oangle_add_oangle_add_oangle_eq_pi h_ab'.symm h_bc'.symm h_ac'
  have h_bca : ¬ Collinear ℝ {b, c, a} := by rwa [Set.insert_comm, Set.pair_comm] at h_not_col
  have h_bca' : ¬ Collinear ℝ {b', c', a'} := by rwa [Set.insert_comm, Set.pair_comm] at h_not_col'
  have h1 : ∡ a b c = -∡ a' b' c' := by
    have h_eq_or_neg := h.oangle_eq_or_neg h_not_col h_not_col'
    rcases h_eq_or_neg with h_eq | h_eq_neg
    · simp only [h_eq] at h₁
      symm at h₁
      simp only [SignType.neg_eq_self_iff, oangle_sign_eq_zero_iff_collinear, h_not_col'] at h₁
    · exact h_eq_neg
  have h₂ : (∡ b c a).sign = -(∡ b' c' a').sign := by
    nth_rw 2 [oangle_rotate_sign]
    rwa [oangle_rotate_sign]
  have h2 : ∡ b c a = -∡ b' c' a' := by
    have h_eq_or_neg := h.comm_left.comm_right.oangle_eq_or_neg h_bca h_bca'
    rcases h_eq_or_neg with h_eq | h_eq_neg
    · simp only [h_eq] at h₂
      symm at h₂
      simp only [SignType.neg_eq_self_iff, oangle_sign_eq_zero_iff_collinear, h_bca'] at h₂
    · exact h_eq_neg
  have h3 : ∡ c a b = -∡ c' a' b' := by grind only [= Real.Angle.coe_pi_add_coe_pi]
  refine ⟨h1, h2, h3⟩

end Orientation
