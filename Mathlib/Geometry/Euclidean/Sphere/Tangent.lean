/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Geometry.Euclidean.Sphere.Basic

/-!
# Tangency for spheres.

This file defines notions of spheres being tangent to affine subspaces and other spheres.

## Main definitions

* `EuclideanGeometry.Sphere.orthRadius`: the affine subspace orthogonal to the radius vector at
  a point (the tangent space, if that point lies in the sphere).

* `EuclideanGeometry.Sphere.IsTangentAt`: the property of an affine subspace being tangent to a
  sphere at a given point.

* `EuclideanGeometry.Sphere.IsTangent`: the property of an affine subspace being tangent to a
  sphere at some point.

* `EuclideanGeometry.Sphere.tangentSet`: the set of all maximal tangent spaces to a given sphere.

* `EuclideanGeometry.Sphere.tangentsFrom`: the set of all maximal tangent spaces to a given
  sphere and containing a given point.

* `EuclideanGeometry.Sphere.commonTangents`: the set of all maximal common tangent spaces to two
  given spheres.

* `EuclideanGeometry.Sphere.commonIntTangents`: the set of all maximal common internal tangent
  spaces to two given spheres.

* `EuclideanGeometry.Sphere.commonExtTangents`: the set of all maximal common external tangent
  spaces to two given spheres.

* `EuclideanGeometry.Sphere.IsExtTangentAt`: the property of two spheres being externally tangent
  at a given point.

* `EuclideanGeometry.Sphere.IsIntTangentAt`: the property of two spheres being internally tangent
  at a given point.

* `EuclideanGeometry.Sphere.IsExtTangent`: the property of two spheres being externally tangent.

* `EuclideanGeometry.Sphere.IsIntTangent`: the property of two spheres being internally tangent.

-/


namespace EuclideanGeometry

namespace Sphere

open AffineSubspace RealInnerProductSpace

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- The affine subspace orthogonal to the radius vector of the sphere `s` at the point `p` (in
the typical cases, `p` lies in `s` and this is the tangent space). -/
def orthRadius (s : Sphere P) (p : P) : AffineSubspace ℝ P := .mk' p (ℝ ∙ (p -ᵥ s.center))ᗮ

lemma self_mem_orthRadius (s : Sphere P) (p : P) : p ∈ s.orthRadius p :=
  self_mem_mk' _ _

lemma mem_orthRadius_iff_inner_left {s : Sphere P} {p x : P} :
    x ∈ s.orthRadius p ↔ ⟪x -ᵥ p, p -ᵥ s.center⟫ = 0 := by
  rw [orthRadius, mem_mk'_iff_vsub_mem, Submodule.mem_orthogonal_singleton_iff_inner_left]

lemma mem_orthRadius_iff_inner_right {s : Sphere P} {p x : P} :
    x ∈ s.orthRadius p ↔ ⟪p -ᵥ s.center, x -ᵥ p⟫ = 0 := by
  rw [mem_orthRadius_iff_inner_left, inner_eq_zero_symm]

@[simp] lemma direction_orthRadius (s : Sphere P) (p : P) :
    (s.orthRadius p).direction = (ℝ ∙ (p -ᵥ s.center))ᗮ := by
  rw [orthRadius, direction_mk']

@[simp] lemma orthRadius_center (s : Sphere P) : s.orthRadius s.center = ⊤ := by
  simp [orthRadius]

@[simp] lemma center_mem_orthRadius_iff {s : Sphere P} {p : P} :
    s.center ∈ s.orthRadius p ↔ p = s.center := by
  rw [mem_orthRadius_iff_inner_left, ← neg_vsub_eq_vsub_rev, inner_neg_left]
  simp

lemma orthRadius_le_orthRadius_iff {s : Sphere P} {p q : P} :
    s.orthRadius p ≤ s.orthRadius q ↔ p = q ∨ q = s.center := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := direction_le h
    simp only [direction_orthRadius] at h'
    have h'' := Submodule.orthogonal_le h'
    simp only [Submodule.orthogonal_orthogonal, Submodule.span_singleton_le_iff_mem,
      Submodule.mem_span_singleton] at h''
    rcases h'' with ⟨r, hr⟩
    have hp : p ∈ s.orthRadius q := h (s.self_mem_orthRadius p)
    rw [mem_orthRadius_iff_inner_left, ← vsub_sub_vsub_cancel_right p q s.center, ← hr,
      inner_sub_left, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← sub_mul,
      mul_eq_zero] at hp
    rcases hp with hp | hp
    · nth_rw 1 [← one_mul r] at hp
      rw [← sub_mul, mul_eq_zero] at hp
      rcases hp with hp | rfl
      · rw [sub_eq_zero] at hp
        rw [← hp, one_smul, vsub_left_cancel_iff] at hr
        exact .inl hr
      · rw [zero_smul, eq_comm, vsub_eq_zero_iff_eq] at hr
        exact .inr hr
    · simp only [inner_self_eq_zero, vsub_eq_zero_iff_eq] at hp
      rw [hp, vsub_self, smul_zero, eq_comm, vsub_eq_zero_iff_eq] at hr
      exact .inr hr
  · rcases h with rfl | rfl <;> simp

@[simp] lemma orthRadius_eq_orthRadius_iff {s : Sphere P} {p q : P} :
    s.orthRadius p = s.orthRadius q ↔ p = q := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hpq := orthRadius_le_orthRadius_iff.1 h.le
  have hqp := orthRadius_le_orthRadius_iff.1 h.symm.le
  grind

/-- The affine subspace `as` is tangent to the sphere `s` at the point `p`. -/
structure IsTangentAt (s : Sphere P) (p : P) (as : AffineSubspace ℝ P) : Prop where
  mem_sphere : p ∈ s
  mem_space : p ∈ as
  le_orthRadius : as ≤ s.orthRadius p

@[simp] lemma isTangentAt_orthRadius_iff_mem {s : Sphere P} {p : P} :
    s.IsTangentAt p (s.orthRadius p) ↔ p ∈ s :=
  ⟨fun h ↦ h.mem_sphere, fun h ↦ ⟨h, self_mem_orthRadius _ _, le_rfl⟩⟩

lemma IsTangentAt.inner_left_eq_zero_of_mem {s : Sphere P} {p : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) {x : P} (hx : x ∈ as) : ⟪x -ᵥ p, p -ᵥ s.center⟫ = 0 :=
  mem_orthRadius_iff_inner_left.1 (h.le_orthRadius hx)

lemma IsTangentAt.inner_right_eq_zero_of_mem {s : Sphere P} {p : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) {x : P} (hx : x ∈ as) : ⟪p -ᵥ s.center, x -ᵥ p⟫ = 0 :=
  mem_orthRadius_iff_inner_right.1 (h.le_orthRadius hx)

lemma IsTangentAt.eq_of_isTangentAt {s : Sphere P} {p q : P} {as : AffineSubspace ℝ P}
    (hp : s.IsTangentAt p as) (hq : s.IsTangentAt q as) : p = q := by
  have hqp := hp.inner_left_eq_zero_of_mem hq.mem_space
  have hpq := hq.inner_left_eq_zero_of_mem hp.mem_space
  rw [← neg_vsub_eq_vsub_rev, inner_neg_left, neg_eq_zero, ← hpq, ← sub_eq_zero,
    ← inner_sub_right, vsub_sub_vsub_cancel_right] at hqp
  simpa using hqp

lemma isTangentAt_center_iff {s : Sphere P} {as : AffineSubspace ℝ P} :
    s.IsTangentAt s.center as ↔ s.radius = 0 ∧ s.center ∈ as := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hr, hm, -⟩
    rw [center_mem_iff] at hr
    exact ⟨hr, hm⟩
  · rintro ⟨hr, hm⟩
    refine ⟨?_, hm, ?_⟩
    · rw [center_mem_iff, hr]
    · simp

lemma IsTangentAt.dist_sq_eq_of_mem {s : Sphere P} {p q : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) (hq : q ∈ as) :
    (dist q s.center) ^ 2 = s.radius ^ 2 + (dist q p) ^ 2 := by
  rw [← h.mem_sphere]
  simp_rw [dist_eq_norm_vsub, pow_two]
  rw [← vsub_add_vsub_cancel q p s.center]
  conv_rhs => rw [add_comm]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact h.inner_left_eq_zero_of_mem hq

lemma IsTangentAt.mem_and_mem_iff_eq {s : Sphere P} {p q : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) : (q ∈ s ∧ q ∈ as) ↔ q = p := by
  refine ⟨fun ⟨hs, has⟩ ↦ ?_, ?_⟩
  · have hd := h.dist_sq_eq_of_mem has
    rw [hs] at hd
    simpa using hd
  · rintro rfl
    exact ⟨h.mem_sphere, h.mem_space⟩

lemma IsTangentAt.eq_of_mem_of_mem {s : Sphere P} {p q : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) (hs : q ∈ s) (has : q ∈ as) : q = p :=
  h.mem_and_mem_iff_eq.1 ⟨hs, has⟩

/-- The affine subspace `as` is tangent to the sphere `s` at some point. -/
def IsTangent (s : Sphere P) (as : AffineSubspace ℝ P) : Prop :=
  ∃ p, s.IsTangentAt p as

lemma IsTangentAt.isTangent {s : Sphere P} {p : P} {as : AffineSubspace ℝ P}
    (h : s.IsTangentAt p as) : s.IsTangent as :=
  ⟨p, h⟩

@[simp] lemma isTangent_orthRadius_iff_mem {s : Sphere P} {p : P} :
    s.IsTangent (s.orthRadius p) ↔ p ∈ s := by
  refine ⟨?_, fun h ↦ (isTangentAt_orthRadius_iff_mem.2 h).isTangent⟩
  rintro ⟨q, hs, hsp, hle⟩
  rw [orthRadius_le_orthRadius_iff] at hle
  rcases hle with rfl | rfl
  · exact hs
  · rw [center_mem_orthRadius_iff] at hsp
    rwa [← hsp] at hs

lemma IsTangent.infDist_eq_radius {s : Sphere P} {as : AffineSubspace ℝ P} (h : s.IsTangent as) :
    Metric.infDist s.center as = s.radius := by
  obtain ⟨p, h⟩ := h
  refine le_antisymm ?_ ?_
  · convert Metric.infDist_le_dist_of_mem h.mem_space
    rw [mem_sphere'.1 h.mem_sphere]
  · rw [Metric.infDist_eq_iInf]
    have : Nonempty as := ⟨⟨p, h.mem_space⟩⟩
    refine le_ciInf fun x ↦ le_of_sq_le_sq ?_ dist_nonneg
    rw [dist_comm, h.dist_sq_eq_of_mem x.property, le_add_iff_nonneg_right]
    exact sq_nonneg _

lemma IsTangent.notMem_of_dist_lt {s : Sphere P} {as : AffineSubspace ℝ P} (h : s.IsTangent as)
    {p : P} (hp : dist s.center p < s.radius) : p ∉ as := by
  rw [← h.infDist_eq_radius] at hp
  exact Metric.notMem_of_dist_lt_infDist hp

lemma dist_orthogonalProjection_eq_radius_iff_isTangentAt {s : Sphere P} {as : AffineSubspace ℝ P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] :
    dist s.center (orthogonalProjection as s.center) = s.radius ↔
      s.IsTangentAt (orthogonalProjection as s.center) as := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine ⟨?_, orthogonalProjection_mem _, fun p hp ↦ ?_⟩
    · rwa [mem_sphere']
    · rw [SetLike.mem_coe, mem_orthRadius_iff_inner_left]
      exact orthogonalProjection_vsub_mem_direction_orthogonal as s.center _
        (vsub_orthogonalProjection_mem_direction s.center hp)
  · rw [dist_orthogonalProjection_eq_infDist, h.isTangent.infDist_eq_radius]

lemma dist_orthogonalProjection_eq_radius_iff_isTangent {s : Sphere P} {as : AffineSubspace ℝ P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] :
    dist s.center (orthogonalProjection as s.center) = s.radius ↔ s.IsTangent as := by
  refine ⟨fun h ↦ (dist_orthogonalProjection_eq_radius_iff_isTangentAt.1 h).isTangent, fun h ↦ ?_⟩
  rw [dist_orthogonalProjection_eq_infDist, h.infDist_eq_radius]

lemma infDist_eq_radius_iff_isTangent {s : Sphere P} {as : AffineSubspace ℝ P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] :
    Metric.infDist s.center as = s.radius ↔ s.IsTangent as := by
  rw [← dist_orthogonalProjection_eq_infDist, dist_orthogonalProjection_eq_radius_iff_isTangent]

lemma isTangent_iff_isTangentAt_orthogonalProjection {s : Sphere P} {as : AffineSubspace ℝ P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] :
    s.IsTangent as ↔ s.IsTangentAt (orthogonalProjection as s.center) as := by
  rw [← dist_orthogonalProjection_eq_radius_iff_isTangent,
    dist_orthogonalProjection_eq_radius_iff_isTangentAt]

alias ⟨IsTangent.isTangentAt, _⟩ := isTangent_iff_isTangentAt_orthogonalProjection

lemma IsTangentAt.eq_orthogonalProjection {s : Sphere P} {p : P} {as : AffineSubspace ℝ P}
    [Nonempty as] [as.direction.HasOrthogonalProjection] (h : s.IsTangentAt p as) :
    p = orthogonalProjection as s.center := by
  refine h.eq_of_isTangentAt ?_
  have h' := h.isTangent
  rwa [isTangent_iff_isTangentAt_orthogonalProjection] at h'

/-- The set of all maximal tangent spaces to the sphere `s`. -/
def tangentSet (s : Sphere P) : Set (AffineSubspace ℝ P) :=
  s.orthRadius '' s

lemma mem_tangentSet_iff {as : AffineSubspace ℝ P} {s : Sphere P} :
    as ∈ s.tangentSet ↔ ∃ p, p ∈ s ∧ s.orthRadius p = as :=
  Iff.rfl

lemma isTangent_of_mem_tangentSet {as : AffineSubspace ℝ P} {s : Sphere P}
    (h : as ∈ s.tangentSet) : s.IsTangent as := by
  rcases h with ⟨p, hps, rfl⟩
  exact isTangent_orthRadius_iff_mem.2 hps

/-- The set of all maximal tangent spaces to the sphere `s` containing the point `p`. -/
def tangentsFrom (s : Sphere P) (p : P) : Set (AffineSubspace ℝ P) :=
  {as ∈ s.tangentSet | p ∈ as}

lemma mem_tangentsFrom_iff {as : AffineSubspace ℝ P} {s : Sphere P} {p : P} :
    as ∈ s.tangentsFrom p ↔ as ∈ s.tangentSet ∧ p ∈ as :=
  Iff.rfl

lemma mem_tangentSet_of_mem_tangentsFrom {as : AffineSubspace ℝ P} {s : Sphere P} {p : P}
    (h : as ∈ s.tangentsFrom p) : as ∈ s.tangentSet :=
  h.1

lemma mem_of_mem_tangentsFrom {as : AffineSubspace ℝ P} {s : Sphere P} {p : P}
    (h : as ∈ s.tangentsFrom p) : p ∈ as :=
  h.2

lemma isTangent_of_mem_tangentsFrom {as : AffineSubspace ℝ P} {s : Sphere P} {p : P}
    (h : as ∈ s.tangentsFrom p) : s.IsTangent as :=
  isTangent_of_mem_tangentSet h.1

/-- The set of all maximal common tangent spaces to the spheres `s₁` and `s₂`. -/
def commonTangents (s₁ s₂ : Sphere P) : Set (AffineSubspace ℝ P) :=
  s₁.tangentSet ∩ s₂.tangentSet

lemma mem_commonTangents_iff {as : AffineSubspace ℝ P} {s₁ s₂ : Sphere P} :
    as ∈ s₁.commonTangents s₂ ↔ as ∈ s₁.tangentSet ∧ as ∈ s₂.tangentSet :=
  Iff.rfl

lemma commonTangents_comm (s₁ s₂ : Sphere P) : s₁.commonTangents s₂ = s₂.commonTangents s₁ :=
  Set.inter_comm _ _

/-- The set of all maximal common internal tangent spaces to the spheres `s₁` and `s₂`: tangent
spaces containing a point weakly between the centers of the spheres. -/
def commonIntTangents (s₁ s₂ : Sphere P) : Set (AffineSubspace ℝ P) :=
  {as ∈ s₁.commonTangents s₂ | ∃ p ∈ as, Wbtw ℝ s₁.center p s₂.center}

/-- The set of all maximal common external tangent spaces to the spheres `s₁` and `s₂`: tangent
spaces not containing a point strictly between the centers of the spheres. (In the degenerate case
where the two spheres are the same sphere with radius 0, the space is considered both an internal
and an external common tangent.) -/
def commonExtTangents (s₁ s₂ : Sphere P) : Set (AffineSubspace ℝ P) :=
  {as ∈ s₁.commonTangents s₂ | ∀ p ∈ as, ¬Sbtw ℝ s₁.center p s₂.center}

lemma mem_commonIntTangents_iff {as : AffineSubspace ℝ P} {s₁ s₂ : Sphere P} :
    as ∈ s₁.commonIntTangents s₂ ↔
      as ∈ s₁.commonTangents s₂ ∧ ∃ p ∈ as, Wbtw ℝ s₁.center p s₂.center :=
  Iff.rfl

lemma mem_commonExtTangents_iff {as : AffineSubspace ℝ P} {s₁ s₂ : Sphere P} :
    as ∈ s₁.commonExtTangents s₂ ↔
      as ∈ s₁.commonTangents s₂ ∧ ∀ p ∈ as, ¬Sbtw ℝ s₁.center p s₂.center :=
  Iff.rfl

@[simp] lemma commonIntTangents_union_commonExtTangents (s₁ s₂ : Sphere P) :
    s₁.commonIntTangents s₂ ∪ s₁.commonExtTangents s₂ = s₁.commonTangents s₂ := by
  ext as
  rw [Set.mem_union, mem_commonIntTangents_iff, mem_commonExtTangents_iff, ← and_or_left,
    and_iff_left_iff_imp]
  rintro -
  by_cases h : ∃ p ∈ as, Wbtw ℝ s₁.center p s₂.center
  · exact .inl h
  · refine .inr ?_
    simp_rw [not_exists, not_and] at h
    rintro p hp
    exact mt Sbtw.wbtw (h p hp)

/-- The spheres `s₁` and `s₂` are externally tangent at the point `p`. -/
structure IsExtTangentAt (s₁ s₂ : Sphere P) (p : P) : Prop where
  mem_left : p ∈ s₁
  mem_right : p ∈ s₂
  wbtw : Wbtw ℝ s₁.center p s₂.center

lemma IsExtTangentAt.symm {s₁ s₂ : Sphere P} {p : P} (h : s₁.IsExtTangentAt s₂ p) :
    s₂.IsExtTangentAt s₁ p where
  mem_left := h.mem_right
  mem_right := h.mem_left
  wbtw := h.wbtw.symm

lemma isExtTangentAt_comm {s₁ s₂ : Sphere P} {p : P} :
    s₁.IsExtTangentAt s₂ p ↔ s₂.IsExtTangentAt s₁ p :=
  ⟨IsExtTangentAt.symm, IsExtTangentAt.symm⟩

lemma isExtTangentAt_center_iff {s₁ s₂ : Sphere P} :
    s₁.IsExtTangentAt s₂ s₁.center ↔ s₁.radius = 0 ∧ s₁.center ∈ s₂ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂, -⟩
    rw [center_mem_iff] at h₁
    exact ⟨h₁, h₂⟩
  · rintro ⟨hr, hc⟩
    refine ⟨?_, hc, ?_⟩
    · rw [center_mem_iff, hr]
    · simp

/-- The sphere `s₁` is internally tangent to the sphere `s₂` at the point `p` (that is, `s₁` lies
inside `s₂` and is tangent to it at that point). This includes the degenerate case where the
spheres are the same. -/
structure IsIntTangentAt (s₁ s₂ : Sphere P) (p : P) : Prop where
  mem_left : p ∈ s₁
  mem_right : p ∈ s₂
  wbtw : Wbtw ℝ s₂.center s₁.center p

lemma isIntTangentAt_center_iff {s₁ s₂ : Sphere P} :
    s₁.IsIntTangentAt s₂ s₁.center ↔ s₁.radius = 0 ∧ s₁.center ∈ s₂ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, h₂, -⟩
    rw [center_mem_iff] at h₁
    exact ⟨h₁, h₂⟩
  · rintro ⟨hr, hc⟩
    refine ⟨?_, hc, ?_⟩
    · rw [center_mem_iff, hr]
    · simp

@[simp] lemma isIntTangentAt_self_iff_mem {s : Sphere P} {p : P} :
    s.IsIntTangentAt s p ↔ p ∈ s :=
  ⟨fun ⟨h, _, _⟩ ↦ h, fun h ↦ ⟨h, h, by simp⟩⟩

/-- The spheres `s₁` and `s₂` are externally tangent at some point. -/
def IsExtTangent (s₁ s₂ : Sphere P) : Prop :=
  ∃ p, s₁.IsExtTangentAt s₂ p

lemma IsExtTangent.symm {s₁ s₂ : Sphere P} (h : s₁.IsExtTangent s₂) : s₂.IsExtTangent s₁ := by
  rcases h with ⟨p, hp⟩
  exact ⟨p, hp.symm⟩

lemma isExtTangent_comm {s₁ s₂ : Sphere P} : s₁.IsExtTangent s₂ ↔ s₂.IsExtTangent s₁ :=
  ⟨IsExtTangent.symm, IsExtTangent.symm⟩

/-- The sphere `s₁` is internally tangent to the sphere `s₂` at some point. -/
def IsIntTangent (s₁ s₂ : Sphere P) : Prop :=
  ∃ p, s₁.IsIntTangentAt s₂ p

lemma IsExtTangentAt.isExtTangent {s₁ s₂ : Sphere P} {p : P} (h : s₁.IsExtTangentAt s₂ p) :
    s₁.IsExtTangent s₂ :=
  ⟨p, h⟩

lemma IsIntTangentAt.isIntTangent {s₁ s₂ : Sphere P} {p : P} (h : s₁.IsIntTangentAt s₂ p) :
    s₁.IsIntTangent s₂ :=
  ⟨p, h⟩

@[simp] lemma isIntTangent_self_iff [Nontrivial V] {s : Sphere P} :
    s.IsIntTangent s ↔ 0 ≤ s.radius := by
  simp_rw [IsIntTangent, isIntTangentAt_self_iff_mem]
  rw [← nonempty_iff]
  simp [Set.Nonempty]

lemma IsExtTangent.dist_center {s₁ s₂ : Sphere P} (h : s₁.IsExtTangent s₂) :
    dist s₁.center s₂.center = s₁.radius + s₂.radius := by
  rcases h with ⟨p, h₁, h₂, h⟩
  rw [← dist_add_dist_eq_iff] at h
  rw [← h, mem_sphere'.1 h₁, h₂]

lemma IsIntTangent.dist_center {s₁ s₂ : Sphere P} (h : s₁.IsIntTangent s₂) :
    dist s₁.center s₂.center = s₂.radius - s₁.radius := by
  rcases h with ⟨p, h₁, h₂, h⟩
  rw [← dist_add_dist_eq_iff, mem_sphere'.1 h₁, mem_sphere'.1 h₂] at h
  simp [← h, dist_comm]

lemma isExtTangent_iff_dist_center {s₁ s₂ : Sphere P} : s₁.IsExtTangent s₂ ↔
    dist s₁.center s₂.center = s₁.radius + s₂.radius ∧ 0 ≤ s₁.radius ∧ 0 ≤ s₂.radius := by
  refine ⟨fun h ↦ ⟨h.dist_center, ?_⟩, ?_⟩
  · rcases h with ⟨p, h₁, h₂, h⟩
    exact ⟨radius_nonneg_of_mem h₁, radius_nonneg_of_mem h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    refine ⟨AffineMap.lineMap s₁.center s₂.center (s₁.radius / (s₁.radius + s₂.radius)), ?_⟩
    by_cases h0 : s₁.radius + s₂.radius = 0
    · simp only [h0, div_zero, AffineMap.lineMap_apply_zero, isExtTangentAt_center_iff, mem_sphere]
      exact ⟨by linarith, by linarith⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp only [mem_sphere, dist_lineMap_left, norm_div, Real.norm_eq_abs, h, abs_of_nonneg h₁,
          abs_of_nonneg (add_nonneg h₁ h₂)]
        field_simp
      · simp only [mem_sphere, dist_lineMap_right, Real.norm_eq_abs, h]
        rw [one_sub_div h0, add_sub_cancel_left, abs_div, abs_of_nonneg h₂,
          abs_of_nonneg (add_nonneg h₁ h₂)]
        field_simp
      · simp only [wbtw_lineMap_iff]
        refine .inr ⟨?_, ?_⟩
        · positivity
        · rw [div_le_one (by positivity)]
          linarith

lemma isIntTangent_iff_dist_center [Nontrivial V] {s₁ s₂ : Sphere P} : s₁.IsIntTangent s₂ ↔
    dist s₁.center s₂.center = s₂.radius - s₁.radius ∧ 0 ≤ s₁.radius ∧ 0 ≤ s₂.radius := by
  refine ⟨fun h ↦ ⟨h.dist_center, ?_⟩, ?_⟩
  · rcases h with ⟨p, h₁, h₂, h⟩
    exact ⟨radius_nonneg_of_mem h₁, radius_nonneg_of_mem h₂⟩
  · rintro ⟨h, h₁, h₂⟩
    by_cases h0 : s₁.center = s₂.center
    · rw [h0, dist_self, eq_comm, sub_eq_zero, eq_comm] at h
      have hs : s₁ = s₂ := by
        ext <;> assumption
      simp [hs, h₂]
    · rw [dist_comm] at h
      have ha : |s₂.radius - s₁.radius| = s₂.radius - s₁.radius := by
        refine abs_of_nonneg ?_
        rw [← h]
        exact dist_nonneg
      have hr0 : s₂.radius - s₁.radius ≠ 0 := by
        intro hr0
        rw [hr0, dist_eq_zero] at h
        exact h0 h.symm
      refine ⟨AffineMap.lineMap s₂.center s₁.center (s₂.radius / (s₂.radius - s₁.radius)),
              ?_, ?_, ?_⟩
      · simp only [mem_sphere, dist_lineMap_right, Real.norm_eq_abs, h, one_sub_div hr0, abs_div,
          sub_sub_cancel_left, abs_neg, abs_of_nonneg h₁, ha]
        field_simp
      · simp only [mem_sphere, dist_lineMap_left, norm_div, Real.norm_eq_abs, h, ha,
          abs_of_nonneg h₂]
        field_simp
      · rw [wbtw_iff_left_eq_or_right_mem_image_Ici]
        simp only [Ne.symm h0, Set.mem_image, Set.mem_Ici, AffineMap.lineMap_eq_lineMap_iff,
          false_or, exists_eq_right]
        rw [one_le_div]
        · linarith
        · rw [← h]
          simp [Ne.symm h0]

end Sphere

end EuclideanGeometry
