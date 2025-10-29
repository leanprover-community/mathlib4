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

/-- Two triangles are similar if and only if all the distances between corresponding vertices are
proportional with a positive real ratio. -/
theorem triangle_similar_iff_exists_dist_eq {t₁ : Fin 3 → P₁} {t₂ : Fin 3 → P₂} :
    t₁ ∼ t₂ ↔ ∃ r : ℝ, r > 0 ∧ ∀ (i j : Fin 3), dist (t₁ i) (t₁ j) = r * dist (t₂ i) (t₂ j) := by
  rw [similar_iff_exists_dist_eq]
  constructor
  · intro h
    rcases h with ⟨r_nn, hr_ne, hdist⟩
    set r : ℝ := r_nn.toReal with hr
    have hr_pos : r > 0 := by positivity
    use r
  · intro h
    rcases h with ⟨r, hr_pos, hdist⟩
    set r_nn : ℝ≥0 := Real.toNNReal r with hr_nn
    have hr_ne : r_nn ≠ 0 := by
      rw [hr_nn]
      simp
      linarith
    have hr : r = r_nn.toReal := by
      rw [hr_nn]
      simp
      positivity
    use r_nn
    refine ⟨hr_ne, ?_⟩
    simp_rw [hdist]
    simp [hr]

/-- If all the corresponding sides of two triangles are proportional with a positive `ℝ≥0` ratio,
then the triangles are similar. -/
theorem similar_of_side_side_side_nnreal (h : ∃ r : ℝ≥0, r ≠ 0 ∧ dist a b = r * dist a' b' ∧
    dist b c = r * dist b' c' ∧ dist c a = r * dist c' a') :
    ![a, b, c] ∼ ![a', b', c'] := by
  rw [similar_iff_exists_dist_eq]
  rcases h with ⟨r, hr⟩
  use r
  obtain ⟨hr0, hd₁, hd₂, hd₃⟩ := hr
  apply And.intro hr0
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [dist_comm]

/-- If all the corresponding sides are proportional, then the two triangles are similar. -/
theorem similar_of_side_side_side (h : ∃ r : ℝ, r > 0 ∧ dist a b = r * dist a' b' ∧
    dist b c = r * dist b' c' ∧ dist c a = r * dist c' a') :
    ![a, b, c] ∼ ![a', b', c'] := by
  rcases h with ⟨r, hr_pos, hd₁, hd₂, hd₃⟩
  set r_nn : ℝ≥0 := Real.toNNReal r with hr_nn
  apply similar_of_side_side_side_nnreal
  use r_nn
  have h_ne : r_nn ≠ 0 := by
    rw [hr_nn]
    simp
    linarith
  have hr : r = r_nn.toReal := by
    rw [hr_nn]
    simp
    positivity
  rw [hr] at hd₁ hd₂ hd₃
  exact ⟨h_ne, hd₁, hd₂, hd₃⟩

/-- If two triangles have two pairs of proportional adjacent sides, then the triangles are similar.
-/
theorem similar_of_side_side (h_not_col : ¬ Collinear ℝ {a, b, c})
    (h_not_col' : ¬ Collinear ℝ {a', b', c'}) (h1 : dist a b * dist b' c' = dist b c * dist a' b')
    (h2 : dist b c * dist c' a' = dist c a * dist b' c') :
    ![a, b, c] ∼ ![a', b', c'] := by
  have h_pos1 : 0 < dist a b := by simp [dist_pos, ne₁₂_of_not_collinear h_not_col]
  have h_pos1' : 0 < dist a' b' := by simp [dist_pos, ne₁₂_of_not_collinear h_not_col']
  have h_pos2' : 0 < dist b' c' := by simp [dist_pos, ne₂₃_of_not_collinear h_not_col']
  have h_pos3' : 0 < dist c' a' := by simp [dist_pos, dist_comm, ne₁₃_of_not_collinear h_not_col']
  rw [← div_eq_div_iff (by positivity) (by positivity)] at h1 h2
  set r : ℝ := (dist a b / dist a' b') with hr
  have r_ne : r > 0 := by aesop
  apply similar_of_side_side_side
  grind

/-- If two triangles have two pairs equal angles, then the triangles are similar. -/
theorem similar_of_angle_angle (h_not_col : ¬ Collinear ℝ {a, b, c})
    (h_not_col' : ¬ Collinear ℝ {a', b', c'}) (h₁ : ∠ a b c = ∠ a' b' c')
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
  exact similar_of_side_side h_not_col h_not_col' h_sin1 h_sin2

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
  have k_ne : k > 0 := by
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
  apply similar_of_side_side_side
  use k

/-- For two similar triangles, there exists a positive ratio such that the distances between
corresponding vertices are proportional. -/
theorem exist_dist_eq_mul_dist_of_similar {t₁ : Fin 3 → P₁} {t₂ : Fin 3 → P₂} (h : t₁ ∼ t₂)
    (i j : Fin 3) :
    ∃ r : ℝ, r > 0 ∧ dist (t₁ i) (t₁ j) = r * dist (t₂ i) (t₂ j) := by
  rw [triangle_similar_iff_exists_dist_eq] at h
  rcases h with ⟨r, hr_pos, hdist⟩
  use r
  exact ⟨hr_pos, hdist i j⟩

/-- For two similar triangles, the corresponding angles are equal. -/
theorem angle_eq_of_similar (h : ![a, b, c] ∼ ![a', b', c']) :
    ∠ a b c = ∠ a' b' c' := by
  rw [triangle_similar_iff_exists_dist_eq] at h
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

/-- Reindexing both triangles by the same permutation preserves similarity. -/
theorem similar_reindex {t₁ : ι → P₁} {t₂ : ι → P₂} (e : Equiv.Perm (ι)) :
    t₁ ∼ t₂ ↔ (t₁ ∘ e) ∼ (t₂ ∘ e) := by
  simp_rw [similar_iff_exists_dist_eq]
  constructor
  · rintro ⟨r, hr0, hdist⟩
    refine ⟨r, hr0, ?_⟩
    intro i j
    simpa using hdist (e i) (e j)
  · rintro ⟨r, hr0, hdist⟩
    refine ⟨r, hr0, ?_⟩
    intro i j
    simpa using hdist (e.symm i) (e.symm j)

theorem similar_comm_left (h : ![a, b, c] ∼ ![a', b', c']) :
    ![b, a, c] ∼ ![b', a', c'] := by
  have hl : ![b, a, c] = ![a, b, c] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp; rfl
  have hr : ![b', a', c'] = ![a', b', c'] ∘ Equiv.swap 0 1 := by
    ext i
    fin_cases i <;> simp; rfl
  grind [similar_reindex]

theorem similar_comm_right (h : ![a, b, c] ∼ ![a', b', c']) :
    ![a, c, b] ∼ ![a', c', b'] := by
  have hl : ![a, c, b] = ![a, b, c] ∘ Equiv.swap 1 2 := by
    ext i
    fin_cases i <;> simp; rfl
  have hr : ![a', c', b'] = ![a', b', c'] ∘ Equiv.swap 1 2 := by
    ext i
    fin_cases i <;> simp; rfl
  grind [similar_reindex]

theorem similar_reverse (h : ![a, b, c] ∼ ![a', b', c']) :
    ![c, b, a] ∼ ![c', b', a'] := by
  have hl : ![c, b, a] = ![a, b, c] ∘ Equiv.swap 0 2 := by
    ext i
    fin_cases i <;> simp; rfl
  have hr : ![c', b', a'] = ![a', b', c'] ∘ Equiv.swap 0 2 := by
    ext i
    fin_cases i <;> simp; rfl
  grind [similar_reindex]

/-- In two similar triangles, all three corresponding angles are equal. -/
theorem Similar.angle_eq_all (h : ![a, b, c] ∼ ![a', b', c']) :
    ∠ a b c = ∠ a' b' c' ∧ ∠ b c a = ∠ b' c' a' ∧ ∠ c a b = ∠ c' a' b' := by
  have h1 := angle_eq_of_similar h
  have h2 := angle_eq_of_similar (similar_comm_right h)
  rw [angle_comm, angle_comm a'] at h2
  have h3 := angle_eq_of_similar (similar_comm_left h)
  rw [angle_comm, angle_comm b'] at h3
  exact ⟨h1, h2, h3⟩

end EuclideanGeometry
