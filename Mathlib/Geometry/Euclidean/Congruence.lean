/-
Copyright (c) 2023 Jovan Gerbscheid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jovan Gerbscheid, Chu Zheng
-/

import Mathlib.Topology.MetricSpace.Congruence
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
import Mathlib.Geometry.Euclidean.Triangle

/-!
# Triangle congruence

This file proves the classical triangle congruence criteria for (possibly degenerate) triangles
in real inner product spaces and Euclidean affine spaces.
We prove SSS, SAS ASA, and AAS congruence.

## Implementation notes

Side–Side–Side (SSS) congruence is proved using the definition of `Congruent`.
Side–Angle–Side (SAS) congruence is proved via the law of cosines.
Angle–Side–Angle (ASA) congruence is reduced to SAS using the law of sines.
Angle–Angle–Side (AAS) congruence uses the fact that the sum of the angles in a triangle equals π,
then reduces to ASA.

## References

* https://en.wikipedia.org/wiki/Congruence_(geometry)

-/

open scoped Congruent

namespace EuclideanGeometry

variable {ι V₁ V₂ P₁ P₂ : Type*}
  [NormedAddCommGroup V₁] [NormedAddCommGroup V₂]
  [InnerProductSpace ℝ V₁] [InnerProductSpace ℝ V₂]
  [MetricSpace P₁] [MetricSpace P₂]
  [NormedAddTorsor V₁ P₁] [NormedAddTorsor V₂ P₂]
  {v₁ : ι → P₁} {v₂ : ι → P₂}
  {a b c : P₁} {a' b' c' : P₂}

lemma triangle_congruent_iff_dist_eq {t₁ : Fin 3 → P₁} {t₂ : Fin 3 → P₂} :
    t₁ ≅ t₂ ↔ ∀ (i j : Fin 3),dist (t₁ i) (t₁ j) = dist (t₂ i) (t₂ j) := congruent_iff_dist_eq

/-- Side Side Side, possibly degenerate. -/
theorem side_side_side (hd₁ : dist a b = dist a' b') (hd₂ : dist b c = dist b' c')
    (hd₃ : dist c a = dist c' a') :
  ![a, b, c] ≅ ![a', b', c'] := by
  rw [triangle_congruent_iff_dist_eq]
  intro i j
  fin_cases i <;> fin_cases j <;> simp_all [dist_comm]

/-- Side Angle Side, possibly degenerate. -/
theorem side_angle_side (h : ∠ a b c = ∠ a' b' c') (hd₁ : dist a b = dist a' b')
    (hd₂ : dist b c = dist b' c') : ![a,b,c] ≅ ![a',b',c'] := by
  apply side_side_side hd₁ hd₂
  rw [dist_comm, dist_comm c' a', ← sq_eq_sq₀ (by positivity) (by positivity), pow_two, pow_two,
    EuclideanGeometry.law_cos a b c, EuclideanGeometry.law_cos a' b' c']
  field_simp [h, hd₁, hd₂, dist_comm]

/-- Angle Side Angle, require not collinear. -/
theorem angle_side_angle (h : ¬ Collinear ℝ {a, b, c}) (h' : ¬ Collinear ℝ {a', b', c'})
    (ha₁ : ∠ a b c = ∠ a' b' c') (hd : dist b c = dist b' c') (ha₂ : ∠ b c a = ∠ b' c' a') :
    ![a, b, c] ≅ ![a', b', c'] := by
  have ha₃ := angle_add_angle_add_angle_eq_pi b (ne₁₃_of_not_collinear h)
  have ha₃' := angle_add_angle_add_angle_eq_pi b' (ne₁₃_of_not_collinear h')
  simp only [← ha₃', ha₁, ha₂, angle_comm b' c' a', add_right_cancel_iff] at ha₃
  have h_bac : ¬ Collinear ℝ {b, a, c} := by simpa [Set.insert_comm] using h
  have h_bac' : ¬ Collinear ℝ {b', a', c'} := by simpa [Set.insert_comm] using h'
  have dist_ab_eq: dist a b = dist a' b' := by
    rw [dist_comm a b, dist_comm a' b', dist_eq_dist_mul_sin_angle_div_sin_angle h_bac,
      dist_eq_dist_mul_sin_angle_div_sin_angle h_bac', dist_comm c b, dist_comm c' b', hd,
      angle_comm, ha₂, angle_comm b' c' a', angle_comm b a c, ha₃, angle_comm b' a' c']
  exact side_angle_side ha₁ dist_ab_eq hd

/-- Angle Angle Side, require not collinear. -/
theorem angle_angle_side (h : ¬ Collinear ℝ {a, b, c}) (h' : ¬ Collinear ℝ {a', b', c'})
    (ha₁ : ∠ a b c = ∠ a' b' c') (ha₂ : ∠ b c a = ∠ b' c' a') (hd : dist c a = dist c' a') :
    ![a, b, c] ≅ ![a', b', c'] := by
  have ha₃ := angle_add_angle_add_angle_eq_pi b (ne₁₃_of_not_collinear h)
  have ha₃' := angle_add_angle_add_angle_eq_pi b' (ne₁₃_of_not_collinear h')
  simp only [← ha₃', ha₁, ha₂, angle_comm b' c' a', add_right_cancel_iff] at ha₃
  have h_bca : ¬ Collinear ℝ {b, c, a} := by rwa [Set.insert_comm, Set.pair_comm] at h
  have h_bca' : ¬ Collinear ℝ {b', c', a'} := by rwa [Set.insert_comm, Set.pair_comm] at h'
  have h1 := angle_side_angle h_bca h_bca' ha₂ hd ha₃
  exact angle_side_angle h h' ha₁ (h1.dist_eq 0 1) ha₂

include V₁ V₂

/-- Corresponding angles are equal for congruent triangles. -/
theorem angle_eq_of_congruent (h : v₁ ≅ v₂) (i j k : ι) :
    ∠ (v₁ i) (v₁ j) (v₁ k) = ∠ (v₂ i) (v₂ j) (v₂ k) := by
  unfold EuclideanGeometry.angle
  unfold InnerProductGeometry.angle
  have key := abs_le.1 (abs_real_inner_div_norm_mul_norm_le_one (v₁ i -ᵥ v₁ j) (v₁ k -ᵥ v₁ j))
  have key' := abs_le.1 (abs_real_inner_div_norm_mul_norm_le_one (v₂ i -ᵥ v₂ j) (v₂ k -ᵥ v₂ j))
  rw [Real.arccos_inj key.1 key.2 key'.1 key'.2]
  simp only [real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, ←
    dist_eq_norm_vsub, h.dist_eq, vsub_sub_vsub_cancel_right]

end EuclideanGeometry
