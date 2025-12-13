/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Bisector
public import Mathlib.Geometry.Euclidean.Angle.Sphere
public import Mathlib.Geometry.Euclidean.Circumcenter
public import Mathlib.Geometry.Euclidean.Incenter
public import Mathlib.Geometry.Euclidean.Sphere.SecondInter
public import Mathlib.Geometry.Euclidean.Triangle

/-!
# Angles and incenters and excenters.

This file proves lemmas relating incenters and excenters of a simplex to angle bisection.

-/

@[expose] public section


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

section Oriented

variable [hd2 : Fact (finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]
variable (t : Triangle ℝ P)

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

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

end Oriented

section Unoriented

variable (t : Triangle ℝ P)

/-- Auxiliary lemma for dist_secondInter_point_eq_dist_secondInter_excenter in an oriented
two-dimensional space. -/
private lemma dist_secondInter_point_eq_dist_secondInter_excenter_aux [Fact (finrank ℝ V = 2)]
    [Module.Oriented ℝ V (Fin 2)] (signs : Finset (Fin 3)) {i₁ i₂ i₃ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    dist (t.circumsphere.secondInter (t.points i₁) (t.excenter signs -ᵥ t.points i₁))
      (t.points i₂) =
      dist (t.circumsphere.secondInter (t.points i₁) (t.excenter signs -ᵥ t.points i₁))
        (t.excenter signs) := by
  let A := t.points i₁
  let B := t.points i₂
  let C := t.points i₃
  let I := t.excenter signs
  let X := t.circumsphere.secondInter A (I -ᵥ A)
  change dist X B = dist X I
  have I_ne_A : I ≠ A := (t.excenterExists signs).excenter_ne_point i₁
  have I_ne_B : I ≠ B := (t.excenterExists signs).excenter_ne_point i₂
  have I_ne_C : I ≠ C := (t.excenterExists signs).excenter_ne_point i₃
  have A_ne_B : A ≠ B := t.independent.injective.ne h₁₂
  have A_ne_C : A ≠ C := t.independent.injective.ne h₁₃
  have B_ne_C : B ≠ C := t.independent.injective.ne h₂₃
  have A_mem : A ∈ t.circumsphere := t.mem_circumsphere i₁
  have B_mem : B ∈ t.circumsphere := t.mem_circumsphere i₂
  have C_mem : C ∈ t.circumsphere := t.mem_circumsphere i₃
  have X_mem : X ∈ t.circumsphere := (t.circumsphere.secondInter_mem _).2 A_mem
  have two_zsmul_IAC_eq_two_zsmul_BAI : (2 : ℤ) • ∡ I A C = (2 : ℤ) • ∡ B A I :=
    (t.two_zsmul_oangle_excenter_eq signs h₁₂ h₁₃ h₂₃).symm
  have two_zsmul_CBI_eq_two_zsmul_IBA : (2 : ℤ) • ∡ C B I = (2 : ℤ) • ∡ I B A :=
    t.two_zsmul_oangle_excenter_eq signs h₂₃ h₁₂.symm h₁₃.symm
  have two_zsmul_ICB_eq_two_zsmul_ACI : (2 : ℤ) • ∡ I C B = (2 : ℤ) • ∡ A C I :=
    (t.two_zsmul_oangle_excenter_eq signs h₁₃.symm h₂₃.symm h₁₂).symm
  have collinear_AIX : Collinear ℝ {A, I, X} := t.circumsphere.secondInter_collinear _ _
  have ha : AffineIndependent ℝ ![I, X, B] := by
    rw [affineIndependent_iff_not_collinear_set]
    intro h
    have ha : AffineIndependent ℝ ![A, B, I] := by
      refine affineIndependent_of_ne_of_mem_of_mem_of_notMem (s := line[ℝ, A, B]) A_ne_B
        (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _) ?_
      convert (t.excenterExists signs).excenter_notMem_affineSpan_faceOpposite i₃
      have hc : ({i₃}ᶜ : Set (Fin 3)) = {i₁, i₂} := by grind
      simp [A, B, hc, Set.image_insert_eq]
    have hA : X ∈ line[ℝ, A, I] := t.circumsphere.secondInter_vsub_mem_affineSpan _ _
    have hB : X ∈ line[ℝ, B, I] :=
      h.mem_affineSpan_of_mem_of_ne (by grind) (by grind) (by grind) I_ne_B.symm
    have hAB : affineSpan ℝ {A, I} ⊓ affineSpan ℝ {B, I} = affineSpan ℝ {I} := by
      have h0 : ({0, 2} ∩ {1, 2} : Set (Fin 3)) = {2} := by grind
      convert ha.inf_affineSpan_eq_affineSpan_inter {0, 2} {1, 2} <;>
        simp [Set.image_insert_eq, h0]
    have hX : X ∈ affineSpan ℝ {I} := by
      rw [← hAB]
      exact ⟨hA, hB⟩
    rw [AffineSubspace.mem_affineSpan_singleton] at hX
    have hBIC : (2 : ℤ) • ∡ B I C = (2 : ℤ) • ∡ B A C :=
      t.circumsphere.two_zsmul_oangle_eq B_mem (hX ▸ X_mem) A_mem C_mem I_ne_B I_ne_C A_ne_B A_ne_C
    have hBICπ := oangle_add_oangle_add_oangle_eq_pi I_ne_C.symm B_ne_C I_ne_B
    have hBACπ := oangle_add_oangle_add_oangle_eq_pi A_ne_C.symm B_ne_C A_ne_B
    have hBIC' : (2 : ℤ) • ∡ I C B + (2 : ℤ) • ∡ C B I = (2 : ℤ) • ∡ A C B + (2 : ℤ) • ∡ C B A := by
      rw [← hBACπ] at hBICπ
      apply_fun ((2 : ℤ) • ·) at hBICπ
      simpa [smul_add, hBIC] using hBICπ
    have hBIC'' : (2 : ℤ) • ∡ A C I + (2 : ℤ) • ∡ I B A =
        (2 : ℤ) • ∡ A C B + (2 : ℤ) • ∡ C B A := by
      rwa [two_zsmul_CBI_eq_two_zsmul_IBA, two_zsmul_ICB_eq_two_zsmul_ACI] at hBIC'
    have h0 : ((2 : ℤ) • ∡ A C B + (2 : ℤ) • ∡ C B A) + ((2 : ℤ) • ∡ A C B + (2 : ℤ) • ∡ C B A) =
        (2 : ℤ) • ∡ A C B + (2 : ℤ) • ∡ C B A := by
      nth_rw 1 [← hBIC']
      nth_rw 1 [← hBIC'']
      suffices (2 : ℤ) • (∡ A C I + ∡ I C B) + (2 : ℤ) • (∡ C B I + ∡ I B A) =
          (2 : ℤ) • ∡ A C B + (2 : ℤ) • ∡ C B A by
        rw [← this]
        abel
      rw [oangle_add A_ne_C I_ne_C B_ne_C, oangle_add B_ne_C.symm I_ne_B A_ne_B]
    rw [add_eq_left, ← smul_add] at h0
    apply_fun ((2 : ℤ) • ·) at hBACπ
    rw [smul_add, h0, zero_add, Real.Angle.two_zsmul_coe_pi, Real.Angle.two_zsmul_eq_zero_iff,
      oangle_eq_zero_or_eq_pi_iff_collinear] at hBACπ
    have hABC := affineIndependent_iff_not_collinear.1 t.independent
    apply hABC
    convert hBACπ
    calc Set.range t.points = t.points '' {0, 1, 2} := by
          rw [← Set.image_univ]
          congr
          ext i
          fin_cases i <;> simp
      _ = t.points '' {i₂, i₁, i₃} := by
          congr 1
          ext i
          suffices i ∈ ({0, 1, 2} : Finset (Fin 3)) ↔ i ∈ ({i₂, i₁, i₃} : Finset (Fin 3)) by
            simpa using this
          clear! A B C
          decide +revert
      _ = {B, A, C} := by simp [Set.image_insert_eq, B, A, C]
  have X_ne_B : X ≠ B := ha.injective.ne (show 1 ≠ 2 by decide)
  have X_ne_I : X ≠ I := ha.injective.ne (show 1 ≠ 0 by decide)
  suffices (2 : ℤ) • ∡ X B I = (2 : ℤ) • ∡ B I X by
    rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent] at ha
    exact dist_eq_of_two_zsmul_oangle_eq this ha.1 ha.2
  have two_zsmul_XBC_eq_two_zsmul_IAC : (2 : ℤ) • ∡ X B C = (2 : ℤ) • ∡ I A C := by
    -- A can equal X in the case of an excenter of an isosceles triangle; only this step of the
    -- proof needs special handling for that case.
    rcases eq_or_ne A X with A_eq_X | A_ne_X
    · have orth := t.circumsphere.secondInter_eq_self_iff.1 A_eq_X.symm
      have A_ne_O : A ≠ t.circumcenter := (t.circumcenter_ne_point i₁).symm
      simp only [Simplex.circumsphere_center, ← o.eq_zero_or_oangle_eq_iff_inner_eq_zero,
        vsub_eq_zero_iff_eq, I_ne_A, A_ne_O, ← Real.Angle.two_zsmul_eq_pi_iff, false_or] at orth
      have two_zsmul_IAO_eq_pi : (2 : ℤ) • ∡ I A t.circumcenter = π := by
        rw [oangle, ← o.two_zsmul_oangle_neg_right, neg_vsub_eq_vsub_rev, orth]
      calc (2 : ℤ) • ∡ X B C = (2 : ℤ) • ∡ A B C := by rw [A_eq_X]
        _ = -((2 : ℤ) • ∡ C B A) := by rw [oangle_rev, smul_neg]
        _ = -∡ C (t.circumcenter) A := by
          rw [← t.circumsphere_center, t.circumsphere.oangle_center_eq_two_zsmul_oangle C_mem
            B_mem A_mem B_ne_C A_ne_B.symm]
        _ = (2 : ℤ) • ∡ t.circumcenter A C + π := by
          rw [← t.circumsphere_center, t.circumsphere.oangle_eq_pi_sub_two_zsmul_oangle_center_left
            C_mem A_mem A_ne_C.symm, neg_sub, Real.Angle.sub_coe_pi_eq_add_coe_pi]
        _ = (2 : ℤ) • ∡ I A C := by
          rw [← two_zsmul_IAO_eq_pi, add_comm, ← smul_add, oangle_add I_ne_A A_ne_O.symm
            A_ne_C.symm]
    · calc (2 : ℤ) • ∡ X B C = (2 : ℤ) • ∡ X A C :=
          t.circumsphere.two_zsmul_oangle_eq X_mem B_mem A_mem C_mem X_ne_B.symm B_ne_C A_ne_X
            A_ne_C
        _ = (2 : ℤ) • ∡ I A C := by
          have h : Collinear ℝ {X, A, I} := by convert collinear_AIX using 1; grind
          rw [h.two_zsmul_oangle_eq_left A_ne_X.symm I_ne_A]
  calc (2 : ℤ) • ∡ X B I = (2 : ℤ) • ∡ X B C + (2 : ℤ) • ∡ C B I := by
        rw [← smul_add, oangle_add X_ne_B B_ne_C.symm I_ne_B]
    _ = (2 : ℤ) • ∡ I A C + (2 : ℤ) • ∡ C B I := by
        rw [two_zsmul_XBC_eq_two_zsmul_IAC]
    _ = (2 : ℤ) • ∡ B A I + (2 : ℤ) • ∡ C B I := by rw [two_zsmul_IAC_eq_two_zsmul_BAI]
    _ = (2 : ℤ) • ∡ B A I + (2 : ℤ) • ∡ I B A := by rw [two_zsmul_CBI_eq_two_zsmul_IBA]
    _ = (2 : ℤ) • ∡ B I A := by
        rw [← sub_eq_zero, sub_eq_add_neg, ← smul_neg, ← oangle_rev, ← smul_add, ← smul_add,
          add_assoc, add_comm (∡ I B A), ← add_assoc,
          oangle_add_oangle_add_oangle_eq_pi A_ne_B I_ne_A I_ne_B.symm, Real.Angle.two_zsmul_coe_pi]
    _ = (2 : ℤ) • ∡ B I X := by
        rw [collinear_AIX.two_zsmul_oangle_eq_right I_ne_A.symm X_ne_I]

/-- The **incenter-excenter lemma**, **trillium theorem** or **trident lemma**: given a triangle
ABC, suppose an angle bisector from A through the incenter or excenter I meets the circumcircle
again at X (including the case of an external bisector at A tangent to the circle, in which case
X = A). Then XB = XI (= XC, by applying this lemma again). -/
lemma dist_secondInter_point_eq_dist_secondInter_excenter (signs : Finset (Fin 3)) {i₁ i₂ : Fin 3}
    (h₁₂ : i₁ ≠ i₂) :
    dist (t.circumsphere.secondInter (t.points i₁) (t.excenter signs -ᵥ t.points i₁))
      (t.points i₂) =
      dist (t.circumsphere.secondInter (t.points i₁) (t.excenter signs -ᵥ t.points i₁))
        (t.excenter signs) := by
  let S : AffineSubspace ℝ P := affineSpan ℝ (Set.range t.points)
  let t' : Triangle ℝ S := t.restrict S le_rfl
  have hf2 : Fact (finrank ℝ S.direction = 2) := ⟨by
    simp_rw [S]
    rw [direction_affineSpan, t.independent.finrank_vectorSpan]
    simp⟩
  have : Module.Oriented ℝ S.direction (Fin 2) :=
    ⟨Basis.orientation (finBasisOfFinrankEq _ _ hf2.out)⟩
  suffices dist ((t'.circumsphere.secondInter (t'.points i₁)
        (t'.excenter signs -ᵥ t'.points i₁)) : P)
      (t'.points i₂) =
      dist ((t'.circumsphere.secondInter (t'.points i₁) (t'.excenter signs -ᵥ t'.points i₁)) : P)
        (t'.excenter signs) by
    simpa [t', Sphere.coe_secondInter, t.excenterExists] using this
  simp_rw [← Subtype.dist_eq]
  obtain ⟨i₃, h₁₃, h₂₃⟩ : ∃ i₃, i₁ ≠ i₃ ∧ i₂ ≠ i₃ := by decide +revert
  exact t'.dist_secondInter_point_eq_dist_secondInter_excenter_aux signs h₁₂ h₁₃ h₂₃

/-- The **incenter-excenter lemma**, **trillium theorem** or **trident lemma**: given a triangle
ABC, suppose the angle bisector from A through the incenter I meets the circumcircle again at X.
Then XB = XI (= XC, by applying this lemma again). -/
lemma dist_secondInter_point_eq_dist_secondInter_incenter {i₁ i₂ : Fin 3} (h₁₂ : i₁ ≠ i₂) :
    dist (t.circumsphere.secondInter (t.points i₁) (t.incenter -ᵥ t.points i₁)) (t.points i₂) =
      dist (t.circumsphere.secondInter (t.points i₁) (t.incenter -ᵥ t.points i₁))
        (t.incenter) :=
  t.dist_secondInter_point_eq_dist_secondInter_excenter ∅ h₁₂

end Unoriented

end Triangle

end Affine
