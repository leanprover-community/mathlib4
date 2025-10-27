/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Projection
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
      rw [angle_self_of_ne hpp', angle_comm,
        angle_eq_arcsin_of_angle_eq_pi_div_two (angle_self_orthogonalProjection p hp'.2),
        Real.zero_eq_arcsin_iff, div_eq_zero_iff] at h
      · simp only [dist_eq_zero, hpp', or_false] at h
        rw [eq_comm] at h
        simp [orthogonalProjection_eq_self_iff, hn] at h
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
    angle_eq_arcsin_of_angle_eq_pi_div_two (angle_self_orthogonalProjection p hp'.1)
      (.inl (Ne.symm (orthogonalProjection_eq_self_iff.symm.not.1 h'.1))),
    angle_comm,
    angle_eq_arcsin_of_angle_eq_pi_div_two (angle_self_orthogonalProjection p hp'.2)
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

section Oriented

open Module

variable [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]

/-- A point `p` is equidistant to two affine subspaces (typically lines, for this version of the
lemma) if the oriented angles at a point `p'` in their intersection between `p` and its orthogonal
projections onto the subspaces are equal. -/
lemma dist_orthogonalProjection_eq_of_oangle_eq {p p' : P} {s₁ s₂ : AffineSubspace ℝ P}
    [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (hp' : p' ∈ s₁ ⊓ s₂)
    (hp₁ : haveI : Nonempty s₁ := ⟨p', hp'.1⟩; orthogonalProjection s₁ p ≠ p')
    (hp₂ : haveI : Nonempty s₂ := ⟨p', hp'.2⟩; orthogonalProjection s₂ p ≠ p')
    (h : haveI : Nonempty s₁ := ⟨p', hp'.1⟩; haveI : Nonempty s₂ := ⟨p', hp'.2⟩;
      ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p)) :
    haveI : Nonempty s₁ := ⟨p', hp'.1⟩
    haveI : Nonempty s₂ := ⟨p', hp'.2⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) := by
  rw [dist_orthogonalProjection_eq_iff_angle_eq hp', angle_comm,
      angle_eq_iff_oangle_eq_or_wbtw hp₁ hp₂]
  exact .inl h

/-- The oriented angles at a point `p'` in their intersection between `p` and its orthogonal
projections onto two affine subspaces (typically lines, for this version of the lemma) are equal
if `p` is equidistant to the two subspaces. -/
lemma oangle_eq_of_dist_orthogonalProjection_eq {p p' : P} {s₁ s₂ : AffineSubspace ℝ P}
    [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (hp' : p' ∈ s₁ ⊓ s₂)
    (hne : haveI : Nonempty s₁ := ⟨p', hp'.1⟩; haveI : Nonempty s₂ := ⟨p', hp'.2⟩;
      (orthogonalProjection s₁ p : P) ≠ orthogonalProjection s₂ p)
    (h : haveI : Nonempty s₁ := ⟨p', hp'.1⟩; haveI : Nonempty s₂ := ⟨p', hp'.2⟩;
      dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p)) :
    haveI : Nonempty s₁ := ⟨p', hp'.1⟩
    haveI : Nonempty s₂ := ⟨p', hp'.2⟩
    ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) := by
  haveI : Nonempty s₁ := ⟨p', hp'.1⟩
  haveI : Nonempty s₂ := ⟨p', hp'.2⟩
  haveI : Nonempty (s₁ ⊓ s₂ : AffineSubspace ℝ P) := ⟨p', hp'⟩
  haveI : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by simp [hd2.out])
  have hp₁ : orthogonalProjection s₁ p ≠ p' := by
    intro hp
    rw [hp, ← sq_eq_sq₀ dist_nonneg dist_nonneg, pow_two, pow_two, dist_comm p p',
      dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p hp'.2,
      add_eq_right, mul_eq_zero, dist_eq_zero, or_self] at h
    grind
  have hp₂ : orthogonalProjection s₂ p ≠ p' := by
    intro hp
    rw [hp, ← sq_eq_sq₀ dist_nonneg dist_nonneg, pow_two, pow_two, dist_comm p p',
      dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p hp'.1,
      right_eq_add, mul_eq_zero, dist_eq_zero, or_self] at h
    grind
  have hc : ¬ Collinear ℝ {p', (orthogonalProjection s₁ p : P),
      (orthogonalProjection s₂ p : P)} := by
    intro hc
    have h₁ : (orthogonalProjection s₁ p : P) ∈ line[ℝ, p', (orthogonalProjection s₂ p : P)] :=
      hc.mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) (by grind)
    have h₁' : (orthogonalProjection s₁ p : P) ∈ s₁ ⊓ s₂ :=
      ⟨orthogonalProjection_mem _,
        SetLike.le_def.1 (affineSpan_pair_le_of_mem_of_mem hp'.2 (orthogonalProjection_mem _)) h₁⟩
    have h₁'' : (orthogonalProjection s₁ p : P) = (orthogonalProjection (s₁ ⊓ s₂) p : P) := by
      rw [← orthogonalProjection_orthogonalProjection_of_le inf_le_left, eq_comm,
        orthogonalProjection_eq_self_iff]
      grind
    have h₂ : (orthogonalProjection s₂ p : P) ∈ line[ℝ, p', (orthogonalProjection s₁ p : P)] :=
      hc.mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) (by grind)
    have h₂' : (orthogonalProjection s₂ p : P) ∈ s₁ ⊓ s₂ :=
      ⟨SetLike.le_def.1 (affineSpan_pair_le_of_mem_of_mem hp'.1 (orthogonalProjection_mem _)) h₂,
        orthogonalProjection_mem _⟩
    have h₂'' : (orthogonalProjection s₂ p : P) = (orthogonalProjection (s₁ ⊓ s₂) p : P) := by
      rw [← orthogonalProjection_orthogonalProjection_of_le inf_le_right, eq_comm,
        orthogonalProjection_eq_self_iff]
      grind
    apply hne
    rw [h₁'', h₂'']
  rw [dist_orthogonalProjection_eq_iff_angle_eq hp', angle_comm,
    angle_eq_iff_oangle_eq_or_wbtw hp₁ hp₂] at h
  rcases h with h | h | h
  · exact h
  · exfalso
    exact hc h.collinear
  · exfalso
    have h' := h.collinear
    rw [Set.pair_comm] at h'
    exact hc h'

/-- A point `p` is equidistant to two affine subspaces (typically lines, for this version of the
lemma) if and only if the oriented angles at a point `p'` in their intersection between `p` and
its orthogonal projections onto the subspaces are equal. -/
lemma dist_orthogonalProjection_eq_iff_oangle_eq {p p' : P} {s₁ s₂ : AffineSubspace ℝ P}
    [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (hp' : p' ∈ s₁ ⊓ s₂)
    (hne : haveI : Nonempty s₁ := ⟨p', hp'.1⟩; haveI : Nonempty s₂ := ⟨p', hp'.2⟩;
      (orthogonalProjection s₁ p : P) ≠ orthogonalProjection s₂ p)
    (hp₁ : haveI : Nonempty s₁ := ⟨p', hp'.1⟩; orthogonalProjection s₁ p ≠ p')
    (hp₂ : haveI : Nonempty s₂ := ⟨p', hp'.2⟩; orthogonalProjection s₂ p ≠ p') :
    haveI : Nonempty s₁ := ⟨p', hp'.1⟩
    haveI : Nonempty s₂ := ⟨p', hp'.2⟩
    dist p (orthogonalProjection s₁ p) = dist p (orthogonalProjection s₂ p) ↔
      ∡ (orthogonalProjection s₁ p : P) p' p = ∡ p p' (orthogonalProjection s₂ p) :=
  ⟨oangle_eq_of_dist_orthogonalProjection_eq hp' hne,
   dist_orthogonalProjection_eq_of_oangle_eq hp' hp₁ hp₂⟩

end Oriented

end EuclideanGeometry
