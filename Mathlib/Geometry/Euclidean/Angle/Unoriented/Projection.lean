/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine
public import Mathlib.Geometry.Euclidean.Projection

/-!
# Angles and orthogonal projection.

This file proves lemmas relating to angles involving orthogonal projections.

-/

@[expose] public section


namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

open scoped Real

@[simp] lemma angle_self_orthogonalProjection (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (h : p' ∈ s) :
    haveI : Nonempty s := ⟨p', h⟩
    ∠ p (orthogonalProjection s p) p' = π / 2 := by
  haveI : Nonempty s := ⟨p', h⟩
  rw [angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
  exact Submodule.inner_left_of_mem_orthogonal (K := s.direction)
    (AffineSubspace.vsub_mem_direction h (orthogonalProjection_mem _))
    (vsub_orthogonalProjection_mem_direction_orthogonal _ _)

@[simp] lemma angle_orthogonalProjection_self (p : P) {p' : P} {s : AffineSubspace ℝ P}
    [s.direction.HasOrthogonalProjection] (h : p' ∈ s) :
    haveI : Nonempty s := ⟨p', h⟩
    ∠ p' (orthogonalProjection s p) p = π / 2 := by
  rw [angle_comm, angle_self_orthogonalProjection p h]

@[simp] lemma sameray_orthogonalProjection_vsub_of_angle_lt {p p₁ p₂ : P} (h : ∠ p p₁ p₂ < π / 2) :
    SameRay ℝ (p₂ -ᵥ p₁) (↑(orthogonalProjection line[ℝ, p₁, p₂] p) -ᵥ p₁) := by
  set v := p₂ -ᵥ p₁ with hv
  rw [orthogonalProjection_apply_mem _ (left_mem_affineSpan_pair _ _ _), vadd_vsub]
  have h_dir : (line[ℝ, p₁, p₂]).direction = ℝ ∙ - v := by
    rw [direction_affineSpan, vectorSpan_pair, hv, neg_vsub_eq_vsub_rev]
  rw [Submodule.coe_orthogonalProjection_apply]
  simp only [h_dir, Submodule.starProjection_singleton,
    inner_neg_left, norm_neg, RCLike.ofReal_real_eq_id, id_eq, smul_neg]
  rw [← neg_smul, ← neg_div, neg_neg, hv]
  apply SameRay.sameRay_nonneg_smul_right
  suffices hpos : 0 ≤ inner ℝ (p₂ -ᵥ p₁) (p -ᵥ p₁) by
    exact div_nonneg hpos (by simp)
  rw [← InnerProductGeometry.cos_angle_mul_norm_mul_norm]
  refine mul_nonneg ?_ (by positivity)
  rw [← angle, angle_comm]
  apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le ?_ (by grind)
  suffices 0 ≤ ∠ p p₁ p₂ by grind
  grind [angle_nonneg]

end EuclideanGeometry
