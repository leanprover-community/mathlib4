/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Angle.Bisector
import Mathlib.Geometry.Euclidean.Incenter

/-!
# Angles and incenters and excenters.

This file proves lemmas relating incenters and excenters of a simplex to angle bisection.

-/


open EuclideanGeometry Module
open scoped Real

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

namespace Affine

namespace Simplex

variable {n : ℕ} [NeZero n] (s : Simplex ℝ P n)

variable {s} in
/-- An excenter of a simplex bisects the angle at a point shared between two faces, as measured
between that excenter and its touchpoints on those faces. -/
lemma ExcenterExists.angle_excenter_touchpoint_eq {signs : Finset (Fin (n + 1))}
    (h : s.ExcenterExists signs) {p : P} {i₁ i₂ : Fin (n + 1)}
    (hp : p ∈ affineSpan ℝ (Set.range (s.faceOpposite i₁).points) ⊓
      affineSpan ℝ (Set.range (s.faceOpposite i₂).points)) :
    ∠ (s.excenter signs) p (s.touchpoint signs i₁) =
      ∠ (s.excenter signs) p (s.touchpoint signs i₂) :=
  (dist_orthogonalProjection_eq_iff_angle_eq hp).1 (h.dist_excenter_eq_dist_excenter i₁ i₂)

variable {s} in
/-- The incenter of a simplex bisects the angle at a point shared between two faces, as measured
between the incenter and its touchpoints on those faces. -/
lemma angle_incenter_touchpoint_eq {p : P} {i₁ i₂ : Fin (n + 1)}
    (hp : p ∈ affineSpan ℝ (Set.range (s.faceOpposite i₁).points) ⊓
      affineSpan ℝ (Set.range (s.faceOpposite i₂).points)) :
    ∠ s.incenter p (s.touchpoint ∅ i₁) =
      ∠ s.incenter p (s.touchpoint ∅ i₂) :=
  s.excenterExists_empty.angle_excenter_touchpoint_eq hp

variable {s} in
/-- Given a face of a simplex, if a point bisects the angle between that face and each other face,
as measured at points shared between those faces between that point and its projections onto the
faces, that point is an excenter of the simplex. -/
lemma exists_excenterExists_and_eq_excenter_of_forall_angle_orthogonalProjectionSpan_eq {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) {i₁ : Fin (n + 1)}
    (h : ∀ i₂, i₂ ≠ i₁ → ∃ p' : P, p' ∈ affineSpan ℝ (Set.range (s.faceOpposite i₁).points) ⊓
      affineSpan ℝ (Set.range (s.faceOpposite i₂).points) ∧
      ∠ p p' ((s.faceOpposite i₁).orthogonalProjectionSpan p) =
        ∠ p p' ((s.faceOpposite i₂).orthogonalProjectionSpan p)) :
    ∃ signs, s.ExcenterExists signs ∧ p = s.excenter signs := by
  rw [← s.exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter hp]
  refine ⟨dist p ((s.faceOpposite i₁).orthogonalProjectionSpan p), ?_⟩
  intro i
  by_cases hi : i = i₁
  · rw [hi]
  obtain ⟨p', hp', ha⟩ := h i hi
  exact ((dist_orthogonalProjection_eq_iff_angle_eq hp').2 ha).symm

end Simplex

namespace Triangle

open Simplex

variable [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]
variable (t : Triangle ℝ P)

variable {t} in
/-- A point `p` is equidistant to two sides of a triangle if and only if the oriented angles at
their common vertex are equal modulo `π`. -/
lemma dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq {p : P}
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    dist p ((t.faceOpposite i₃).orthogonalProjectionSpan p) =
      dist p ((t.faceOpposite i₂).orthogonalProjectionSpan p) ↔
        (2 : ℤ) • ∡ (t.points i₂) (t.points i₁) p = (2 : ℤ) • ∡ p (t.points i₁) (t.points i₃) := by
  have ha : AffineIndependent ℝ ![t.points i₁, t.points i₂, t.points i₃] := by
    convert t.independent.comp_embedding ⟨![i₁, i₂, i₃], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
    ext i
    fin_cases i <;> rfl
  rw [orthogonalProjectionSpan, orthogonalProjectionSpan,
    ← dist_orthogonalProjection_eq_iff_two_zsmul_oangle_eq ha]
  simp only [range_faceOpposite_points]
  simp_rw [(by grind : ({i₃}ᶜ : Set (Fin 3)) = {i₁, i₂}),
    (by grind : ({i₂}ᶜ : Set (Fin 3)) = {i₁, i₃}), Set.image_insert_eq, Set.image_singleton]

/-- An excenter of a triangle bisects the angle at a vertex modulo `π`. -/
lemma two_zsmul_oangle_excenter_eq (signs : Finset (Fin 3)) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    (2 : ℤ) • ∡ (t.points i₂) (t.points i₁) (t.excenter signs) =
      (2 : ℤ) • ∡ (t.excenter signs) (t.points i₁) (t.points i₃) := by
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃,
    ← touchpoint, ← touchpoint, (t.excenterExists signs).dist_excenter_eq_dist_excenter]

/-- The incenter of a triangle bisects the angle at a vertex. -/
lemma oangle_incenter_eq {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) :
    ∡ (t.points i₂) (t.points i₁) t.incenter = ∡ t.incenter (t.points i₁) (t.points i₃) := by
  rw [← (t.sbtw_touchpoint_empty h₁₃ h₁₂ h₂₃.symm).oangle_eq_left,
    ← (t.sbtw_touchpoint_empty h₁₂ h₁₃ h₂₃).oangle_eq_right]
  have hd := t.dist_incenter_eq_dist_incenter i₃ i₂
  simp_rw [touchpoint, orthogonalProjectionSpan] at hd ⊢
  refine oangle_eq_of_dist_orthogonalProjection_eq ⟨mem_affineSpan _ ?_, mem_affineSpan _ ?_⟩
    (t.touchpoint_empty_injective.ne h₂₃.symm) hd
  · simp
    grind
  · simp
    grind

/-- The excenter of a triangle opposite a vertex bisects the angle at that vertex. -/
lemma oangle_excenter_singleton_eq {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) :
    ∡ (t.points i₂) (t.points i₁) (t.excenter {i₁}) =
      ∡ (t.excenter {i₁}) (t.points i₁) (t.points i₃) := by
  rw [(t.touchpoint_singleton_sbtw h₁₃ h₁₂ h₂₃.symm).symm.oangle_eq_left,
    (t.touchpoint_singleton_sbtw h₁₂ h₁₃ h₂₃).symm.oangle_eq_right]
  have hd := (t.excenterExists_singleton i₁).dist_excenter_eq_dist_excenter i₃ i₂
  simp_rw [touchpoint, orthogonalProjectionSpan] at hd ⊢
  refine oangle_eq_of_dist_orthogonalProjection_eq ⟨mem_affineSpan _ ?_, mem_affineSpan _ ?_⟩
    ((t.excenterExists_singleton i₁).touchpoint_injective.ne h₂₃.symm) hd
  · simp
    grind
  · simp
    grind

/-- The excenter of a triangle opposite a vertex bisects the exterior angle at another vertex
(that is, the interior angles between vertices and the excenter differ by `π`). -/
lemma oangle_excenter_singleton_eq_add_pi {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) :
    ∡ (t.points i₁) (t.points i₂) (t.excenter {i₁}) =
      ∡ (t.excenter {i₁}) (t.points i₂) (t.points i₃) + π := by
  rw [(t.touchpoint_singleton_sbtw h₁₃ h₁₂ h₂₃.symm).symm.oangle_eq_add_pi_left
        ((t.excenterExists_singleton _).excenter_ne_point _),
    ← (t.sbtw_touchpoint_singleton h₁₂.symm h₂₃ h₁₃).oangle_eq_right, add_left_inj]
  have hd := (t.excenterExists_singleton i₁).dist_excenter_eq_dist_excenter i₃ i₁
  simp_rw [touchpoint, orthogonalProjectionSpan] at hd ⊢
  refine oangle_eq_of_dist_orthogonalProjection_eq ⟨mem_affineSpan _ ?_, mem_affineSpan _ ?_⟩
    ((t.excenterExists_singleton i₁).touchpoint_injective.ne h₁₃.symm) hd
  · simp
    grind
  · simp
    grind

variable {t} in
/-- A point lying on angle bisectors from two vertices is an excenter. -/
lemma eq_excenter_of_two_zsmul_oangle_eq {p : P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃)
    (h₁ : (2 : ℤ) • ∡ (t.points i₂) (t.points i₁) p = (2 : ℤ) • ∡ p (t.points i₁) (t.points i₃))
    (h₂ : (2 : ℤ) • ∡ (t.points i₃) (t.points i₂) p = (2 : ℤ) • ∡ p (t.points i₂) (t.points i₁)) :
    ∃ signs : Finset (Fin 3), p = t.excenter signs := by
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃] at h₁
  rw [← dist_orthogonalProjectionSpan_faceOpposite_eq_iff_two_zsmul_oangle_eq h₂₃ h₁₂.symm h₁₃.symm]
    at h₂
  have hp : p ∈ affineSpan ℝ (Set.range t.points) := by
    convert AffineSubspace.mem_top ℝ V p
    haveI : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by simp [hd2.out])
    rw [t.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one]
    simp [hd2.out]
  have hr : ∃ r : ℝ, ∀ i, dist p ((t.faceOpposite i).orthogonalProjectionSpan p) = r := by
    refine ⟨dist p ((faceOpposite t i₃).orthogonalProjectionSpan p), ?_⟩
    intro i
    have h : i = i₁ ∨ i = i₂ ∨ i = i₃ := by clear h₁ h₂; decide +revert
    rcases h with rfl | rfl | rfl <;> grind
  obtain ⟨signs, -, hp⟩ :=
    (t.exists_forall_dist_eq_iff_exists_excenterExists_and_eq_excenter hp).1 hr
  exact ⟨signs, hp⟩

variable {t} in
/-- An excenter lying on the internal angle bisector from a vertex is either the incenter or the
excenter opposite that vertex. -/
lemma eq_incenter_or_eq_excenter_singleton_of_oangle_eq {signs : Finset (Fin 3)}
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (h : ∡ (t.points i₂) (t.points i₁) (t.excenter signs) =
      ∡ (t.excenter signs) (t.points i₁) (t.points i₃)) :
    t.excenter signs = t.incenter ∨ t.excenter signs = t.excenter {i₁} := by
  have hs := t.excenter_eq_incenter_or_excenter_singleton_of_ne signs h₁₂ h₁₃ h₂₃
  rcases hs with hs | hs | hs | hs
  · exact .inl hs
  · exact .inr hs
  · rw [hs, t.oangle_excenter_singleton_eq_add_pi h₁₂.symm h₂₃ h₁₃] at h
    simp [Real.Angle.pi_ne_zero] at h
  · rw [hs, oangle_rev (t.points i₃), t.oangle_excenter_singleton_eq_add_pi h₁₃.symm h₂₃.symm h₁₂,
      oangle_rev] at h
    simp [Real.Angle.pi_ne_zero] at h

variable {t} in
/-- An excenter lying on the external angle bisector from a vertex is the excenter opposite
another vertex. -/
lemma eq_excenter_singleton_of_oangle_eq_add_pi {signs : Finset (Fin 3)}
    {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (h : ∡ (t.points i₂) (t.points i₁) (t.excenter signs) =
      ∡ (t.excenter signs) (t.points i₁) (t.points i₃) + π) :
    t.excenter signs = t.excenter {i₂} ∨ t.excenter signs = t.excenter {i₃} := by
  have hs := t.excenter_eq_incenter_or_excenter_singleton_of_ne signs h₁₂ h₁₃ h₂₃
  rcases hs with hs | hs | hs | hs
  · rw [hs, t.oangle_incenter_eq h₁₂ h₁₃ h₂₃] at h
    simp [Real.Angle.pi_ne_zero] at h
  · rw [hs, t.oangle_excenter_singleton_eq h₁₂ h₁₃ h₂₃] at h
    simp [Real.Angle.pi_ne_zero] at h
  · exact .inl hs
  · exact .inr hs

variable {t} in
/-- A point lying on two internal angle bisectors is the incenter. -/
lemma eq_incenter_of_oangle_eq {p : P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃)
    (h₂₃ : i₂ ≠ i₃) (h₁ : ∡ (t.points i₂) (t.points i₁) p = ∡ p (t.points i₁) (t.points i₃))
    (h₂ : ∡ (t.points i₃) (t.points i₂) p = ∡ p (t.points i₂) (t.points i₁)) :
    p = t.incenter := by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁]) (by rw [h₂])
  have h₁' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' | h₁'
  · exact h₁'
  rcases h₂' with h₂' | h₂'
  · exact h₂'
  rw [h₁'] at h₂'
  exfalso
  exact t.excenter_singleton_injective.ne h₁₂ h₂'

variable {t} in
/-- A point lying on the internal angle bisector from vertex `i₁` and the external angle bisector
from another vertex is the excenter opposite vertex `i₁`. -/
lemma eq_excenter_singleton_of_oangle_eq_of_oangle_eq_add_pi {p : P} {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (h₁ : ∡ (t.points i₂) (t.points i₁) p = ∡ p (t.points i₁) (t.points i₃))
    (h₂ : ∡ (t.points i₃) (t.points i₂) p = ∡ p (t.points i₂) (t.points i₁) + π) :
    p = t.excenter {i₁} := by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁])
    (by rw [h₂]; simp)
  have h₁' := t.eq_incenter_or_eq_excenter_singleton_of_oangle_eq h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' | h₁'
  · rcases h₂' with h₂' | h₂'
    · rw [h₁'] at h₂'
      exfalso
      exact (t.excenter_singleton_ne_incenter _).symm h₂'
    · exact h₂'
  · exact h₁'

variable {t} in
/-- A point lying on two external angle bisectors is the excenter opposite the third vertex. -/
lemma eq_excenter_singleton_of_oangle_eq_add_pi_of_oangle_eq_add_pi {p : P} {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    (h₁ : ∡ (t.points i₂) (t.points i₁) p = ∡ p (t.points i₁) (t.points i₃) + π)
    (h₂ : ∡ (t.points i₃) (t.points i₂) p = ∡ p (t.points i₂) (t.points i₁) + π) :
    p = t.excenter {i₃} := by
  obtain ⟨signs, rfl⟩ := t.eq_excenter_of_two_zsmul_oangle_eq h₁₂ h₁₃ h₂₃ (by rw [h₁]; simp)
    (by rw [h₂]; simp)
  have h₁' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₁₂ h₁₃ h₂₃ h₁
  have h₂' := t.eq_excenter_singleton_of_oangle_eq_add_pi h₂₃ h₁₂.symm h₁₃.symm h₂
  rcases h₁' with h₁' | h₁'
  · rcases h₂' with h₂' | h₂'
    · exact h₂'
    rw [h₂'] at h₁'
    exfalso
    exact t.excenter_singleton_injective.ne h₁₂ h₁'
  · exact h₁'

end Triangle

end Affine
