/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Angle.Unoriented.RightAngle
import Mathlib.Geometry.Euclidean.Projection

/-!
# Angle bisectors.

This file proves lemmas relating to bisecting angles.

-/


namespace EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

/-- Auxiliary lemma for the degenerate case of `dist_orthogonalProjection_eq_iff_angle_eq` where
`p` lies in `s₁`. -/
private lemma dist_orthogonalProjection_eq_iff_angle_eq_aux₁ {p p' : P}
    {s₁ s₂ : AffineSubspace ℝ P}
    [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (hp' : p' ∈ s₁ ⊓ s₂) (h' : p ∈ s₁) :
    haveI : Nonempty s₁ := ⟨p', hp'.1⟩
    haveI : Nonempty s₂ := ⟨p', hp'.2⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'.1⟩
  have : Nonempty s₂ := ⟨p', hp'.2⟩
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [orthogonalProjection_eq_self_iff.2 h'] at h ⊢
    rw [dist_self, zero_eq_dist, eq_comm, orthogonalProjection_eq_self_iff] at h
    rw [orthogonalProjection_eq_self_iff.2 h]
  · rw [orthogonalProjection_eq_self_iff.2 h'] at h ⊢
    rw [dist_self, zero_eq_dist, eq_comm, orthogonalProjection_eq_self_iff]
    by_cases hpp' : p = p'
    · subst hpp'
      exact hp'.2
    · by_contra hn
      rw [angle_self_of_ne hpp', angle_comm, angle_eq_arcsin_of_angle_eq_pi_div_two,
        Real.zero_eq_arcsin_iff, div_eq_zero_iff] at h
      · simp only [dist_eq_zero, hpp', or_false] at h
        rw [eq_comm] at h
        simp [orthogonalProjection_eq_self_iff, hn] at h
      · rw [angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
        exact Submodule.inner_left_of_mem_orthogonal (K := s₂.direction)
          (AffineSubspace.vsub_mem_direction hp'.2 (orthogonalProjection_mem _))
          (vsub_orthogonalProjection_mem_direction_orthogonal _ _)
      · exact .inl (Ne.symm (orthogonalProjection_eq_self_iff.symm.not.1 hn))

/-- Auxiliary lemma for the degenerate case of `dist_orthogonalProjection_eq_iff_angle_eq` where
`p` lies in `s₁` or `s₂`. -/
private lemma dist_orthogonalProjection_eq_iff_angle_eq_aux {p p' : P}
    {s₁ s₂ : AffineSubspace ℝ P}
    [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (hp' : p' ∈ s₁ ⊓ s₂) (h' : p ∈ s₁ ∨ p ∈ s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'.1⟩
    haveI : Nonempty s₂ := ⟨p', hp'.2⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'.1⟩
  have : Nonempty s₂ := ⟨p', hp'.2⟩
  rcases h' with h' | h'
  · exact dist_orthogonalProjection_eq_iff_angle_eq_aux₁ hp' h'
  · nth_rw 1 [eq_comm]
    nth_rw 2 [eq_comm]
    rw [inf_comm] at hp'
    exact dist_orthogonalProjection_eq_iff_angle_eq_aux₁ hp' h'

/-- A point `p` is equidistant to two affine subspaces if and only if the angles at a point `p'`
in their intersection between `p` and its orthogonal projections onto the subspaces are equal. -/
lemma dist_orthogonalProjection_eq_iff_angle_eq {p p' : P} {s₁ s₂ : AffineSubspace ℝ P}
    [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (hp' : p' ∈ s₁ ⊓ s₂) :
    haveI : Nonempty s₁ := ⟨p', hp'.1⟩
    haveI : Nonempty s₂ := ⟨p', hp'.2⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∠ p p' (orthogonalProjection s₁ p) = ∠ p p' (orthogonalProjection s₂ p) := by
  have : Nonempty s₁ := ⟨p', hp'.1⟩
  have : Nonempty s₂ := ⟨p', hp'.2⟩
  by_cases h' : p ∈ s₁ ∨ p ∈ s₂
  · exact dist_orthogonalProjection_eq_iff_angle_eq_aux hp' h'
  rw [not_or] at h'
  rw [angle_comm,
    angle_eq_arcsin_of_angle_eq_pi_div_two ?_
      (.inl (Ne.symm (orthogonalProjection_eq_self_iff.symm.not.1 h'.1))),
    angle_comm,
    angle_eq_arcsin_of_angle_eq_pi_div_two ?_
      (.inl (Ne.symm (orthogonalProjection_eq_self_iff.symm.not.1 h'.2)))]
  · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [h]
    · have hp : p ≠ p' := by
        rintro rfl
        exact h'.1 hp'.1
      have hpd : 0 < dist p p' := dist_pos.2 hp
      rw [Real.arcsin_inj (le_trans (by norm_num : (-1 : ℝ) ≤ 0) (by positivity))
        ((div_le_one hpd).2 ?_)
        (le_trans (by norm_num : (-1 : ℝ) ≤ 0) (by positivity)) ((div_le_one hpd).2 ?_)] at h
      · rwa [div_left_inj' hpd.ne'] at h
      · rw [dist_orthogonalProjection_eq_infDist]
        exact Metric.infDist_le_dist_of_mem (SetLike.mem_coe.1 hp'.1)
      · rw [dist_orthogonalProjection_eq_infDist]
        exact Metric.infDist_le_dist_of_mem (SetLike.mem_coe.1 hp'.2)
  · rw [angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    exact Submodule.inner_left_of_mem_orthogonal (K := s₂.direction)
      (AffineSubspace.vsub_mem_direction hp'.2 (orthogonalProjection_mem _))
      (vsub_orthogonalProjection_mem_direction_orthogonal _ _)
  · rw [angle, ← InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    exact Submodule.inner_left_of_mem_orthogonal (K := s₁.direction)
      (AffineSubspace.vsub_mem_direction hp'.1 (orthogonalProjection_mem _))
      (vsub_orthogonalProjection_mem_direction_orthogonal _ _)

end EuclideanGeometry
