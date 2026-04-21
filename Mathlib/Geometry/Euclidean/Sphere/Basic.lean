/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Convex.StrictConvexBetween
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.Normed.Affine.Convex
public import Mathlib.Geometry.Euclidean.Basic
public import Mathlib.Geometry.Euclidean.Projection

/-!
# Spheres

This file defines and proves basic results about spheres and cospherical sets of points in
Euclidean affine spaces.

## Main definitions

* `EuclideanGeometry.Sphere` bundles a `center` and a `radius`.

* `EuclideanGeometry.Sphere.IsDiameter` is the property of two points being the two endpoints
  of a diameter of a sphere.

* `EuclideanGeometry.Sphere.ofDiameter` constructs the sphere on a given diameter.

* `EuclideanGeometry.Cospherical` is the property of a set of points being equidistant from some
  point.

* `EuclideanGeometry.Concyclic` is the property of a set of points being cospherical and
  coplanar.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type*} (P : Type*)

open Module

/-- A `Sphere P` bundles a `center` and `radius`. This definition does not require the radius to
be positive; that should be given as a hypothesis to lemmas that require it. -/
@[ext]
structure Sphere [MetricSpace P] where
  /-- center of this sphere -/
  center : P
  /-- radius of the sphere; not required to be positive -/
  radius : ℝ

variable {P}

section MetricSpace

variable [MetricSpace P]

instance [Nonempty P] : Nonempty (Sphere P) :=
  ⟨⟨Classical.arbitrary P, 0⟩⟩

instance : Coe (Sphere P) (Set P) :=
  ⟨fun s => Metric.sphere s.center s.radius⟩

instance : Membership P (Sphere P) :=
  ⟨fun s p => p ∈ (s : Set P)⟩

theorem Sphere.mk_center (c : P) (r : ℝ) : (⟨c, r⟩ : Sphere P).center = c :=
  rfl

theorem Sphere.mk_radius (c : P) (r : ℝ) : (⟨c, r⟩ : Sphere P).radius = r :=
  rfl

@[simp]
theorem Sphere.mk_center_radius (s : Sphere P) : (⟨s.center, s.radius⟩ : Sphere P) = s := by
  ext <;> rfl

@[simp]
theorem Sphere.coe_mk (c : P) (r : ℝ) : ↑(⟨c, r⟩ : Sphere P) = Metric.sphere c r :=
  rfl

-- simp-normal form is `Sphere.mem_coe'`
theorem Sphere.mem_coe {p : P} {s : Sphere P} : p ∈ (s : Set P) ↔ p ∈ s :=
  Iff.rfl

@[simp]
theorem Sphere.mem_coe' {p : P} {s : Sphere P} : dist p s.center = s.radius ↔ p ∈ s :=
  Iff.rfl

theorem mem_sphere {p : P} {s : Sphere P} : p ∈ s ↔ dist p s.center = s.radius :=
  Iff.rfl

theorem mem_sphere' {p : P} {s : Sphere P} : p ∈ s ↔ dist s.center p = s.radius :=
  Metric.mem_sphere'

theorem subset_sphere {ps : Set P} {s : Sphere P} : ps ⊆ s ↔ ∀ p ∈ ps, p ∈ s :=
  Iff.rfl

theorem dist_of_mem_subset_sphere {p : P} {ps : Set P} {s : Sphere P} (hp : p ∈ ps)
    (hps : ps ⊆ (s : Set P)) : dist p s.center = s.radius :=
  mem_sphere.1 (Sphere.mem_coe.1 (Set.mem_of_mem_of_subset hp hps))

theorem dist_of_mem_subset_mk_sphere {p c : P} {ps : Set P} {r : ℝ} (hp : p ∈ ps)
    (hps : ps ⊆ ↑(⟨c, r⟩ : Sphere P)) : dist p c = r :=
  dist_of_mem_subset_sphere hp hps

theorem Sphere.ne_iff {s₁ s₂ : Sphere P} :
    s₁ ≠ s₂ ↔ s₁.center ≠ s₂.center ∨ s₁.radius ≠ s₂.radius := by
  rw [← not_and_or, ← Sphere.ext_iff]

theorem Sphere.center_eq_iff_eq_of_mem {s₁ s₂ : Sphere P} {p : P} (hs₁ : p ∈ s₁) (hs₂ : p ∈ s₂) :
    s₁.center = s₂.center ↔ s₁ = s₂ := by
  refine ⟨fun h => Sphere.ext h ?_, fun h => h ▸ rfl⟩
  rw [mem_sphere] at hs₁ hs₂
  rw [← hs₁, ← hs₂, h]

theorem Sphere.center_ne_iff_ne_of_mem {s₁ s₂ : Sphere P} {p : P} (hs₁ : p ∈ s₁) (hs₂ : p ∈ s₂) :
    s₁.center ≠ s₂.center ↔ s₁ ≠ s₂ :=
  (Sphere.center_eq_iff_eq_of_mem hs₁ hs₂).not

theorem dist_center_eq_dist_center_of_mem_sphere {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : dist p₁ s.center = dist p₂ s.center := by
  rw [mem_sphere.1 hp₁, mem_sphere.1 hp₂]

theorem dist_center_eq_dist_center_of_mem_sphere' {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : dist s.center p₁ = dist s.center p₂ := by
  rw [mem_sphere'.1 hp₁, mem_sphere'.1 hp₂]

lemma Sphere.radius_nonneg_of_mem {s : Sphere P} {p : P} (h : p ∈ s) : 0 ≤ s.radius :=
  Metric.nonneg_of_mem_sphere h

@[simp] lemma Sphere.center_mem_iff {s : Sphere P} : s.center ∈ s ↔ s.radius = 0 := by
  simp [mem_sphere, eq_comm]

/-- A set of points is cospherical if they are equidistant from some
point. In two dimensions, this is the same thing as being
concyclic. -/
def Cospherical (ps : Set P) : Prop :=
  ∃ (center : P) (radius : ℝ), ∀ p ∈ ps, dist p center = radius

/-- The definition of `Cospherical`. -/
theorem cospherical_def (ps : Set P) :
    Cospherical ps ↔ ∃ (center : P) (radius : ℝ), ∀ p ∈ ps, dist p center = radius :=
  Iff.rfl

/-- A set of points is cospherical if and only if they lie in some sphere. -/
theorem cospherical_iff_exists_sphere {ps : Set P} :
    Cospherical ps ↔ ∃ s : Sphere P, ps ⊆ (s : Set P) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨c, r, h⟩
    exact ⟨⟨c, r⟩, h⟩
  · rcases h with ⟨s, h⟩
    exact ⟨s.center, s.radius, h⟩

/-- The set of points in a sphere is cospherical. -/
theorem Sphere.cospherical (s : Sphere P) : Cospherical (s : Set P) :=
  cospherical_iff_exists_sphere.2 ⟨s, Set.Subset.rfl⟩

/-- A subset of a cospherical set is cospherical. -/
theorem Cospherical.subset {ps₁ ps₂ : Set P} (hs : ps₁ ⊆ ps₂) (hc : Cospherical ps₂) :
    Cospherical ps₁ := by
  rcases hc with ⟨c, r, hcr⟩
  exact ⟨c, r, fun p hp => hcr p (hs hp)⟩

/-- The empty set is cospherical. -/
theorem cospherical_empty [Nonempty P] : Cospherical (∅ : Set P) :=
  let ⟨p⟩ := ‹Nonempty P›
  ⟨p, 0, fun _ => False.elim⟩

/-- A single point is cospherical. -/
theorem cospherical_singleton (p : P) : Cospherical ({p} : Set P) := by
  use p
  simp

/-- If `ps` is cospherical, then any of its isometric images is cospherical. -/
theorem _root_.Isometry.cospherical {E F : Type*} [MetricSpace E] [MetricSpace F] {f : E → F}
    (hf : Isometry f) {ps : Set E} (hps : Cospherical ps) : Cospherical (f '' ps) := by
  rcases hps with ⟨c, r, hc⟩
  refine ⟨f c, r, ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  rw [hf.dist_eq, hc p hp]

end MetricSpace

section NormedSpace

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- If a set of points is cospherical, then its image under the inclusion of any affine subspace
containing it is cospherical. -/
theorem Cospherical.inclusion {S₁ S₂ : AffineSubspace ℝ P} [Nonempty S₁] {ps : Set S₁}
    (hps : Cospherical ps) (hS : S₁ ≤ S₂) :
    Cospherical (AffineSubspace.inclusion hS '' ps) := by
  refine Isometry.cospherical ?_ hps
  exact S₁.subtypeₐᵢ.isometry

/-- If a set of points in an affine subspace is cospherical, then its image under the coercion
to the ambient space is cospherical. -/
theorem Cospherical.subtype_val {S : AffineSubspace ℝ P} [Nonempty S] {ps : Set S}
    (hps : Cospherical ps) : Cospherical (Subtype.val '' ps) :=
  Isometry.cospherical S.subtypeₐᵢ.isometry hps

lemma Sphere.nonempty_iff [Nontrivial V] {s : Sphere P} : (s : Set P).Nonempty ↔ 0 ≤ s.radius := by
  refine ⟨fun ⟨p, hp⟩ ↦ radius_nonneg_of_mem hp, fun h ↦ ?_⟩
  obtain ⟨v, hv⟩ := (NormedSpace.sphere_nonempty (x := (0 : V)) (r := s.radius)).2 h
  refine ⟨v +ᵥ s.center, ?_⟩
  simpa [mem_sphere] using hv

include V in
/-- Two points are cospherical. -/
theorem cospherical_pair (p₁ p₂ : P) : Cospherical ({p₁, p₂} : Set P) :=
  ⟨midpoint ℝ p₁ p₂, ‖(2 : ℝ)‖⁻¹ * dist p₁ p₂, by
    rintro p (rfl | rfl | _)
    · rw [dist_comm, dist_midpoint_left (𝕜 := ℝ)]
    · rw [dist_comm, dist_midpoint_right (𝕜 := ℝ)]⟩

/-- A set of points is concyclic if it is cospherical and coplanar. (Most results are stated
directly in terms of `Cospherical` instead of using `Concyclic`.) -/
structure Concyclic (ps : Set P) : Prop where
  Cospherical : Cospherical ps
  Coplanar : Coplanar ℝ ps

/-- A subset of a concyclic set is concyclic. -/
theorem Concyclic.subset {ps₁ ps₂ : Set P} (hs : ps₁ ⊆ ps₂) (h : Concyclic ps₂) : Concyclic ps₁ :=
  ⟨h.1.subset hs, h.2.subset hs⟩

/-- The empty set is concyclic. -/
theorem concyclic_empty : Concyclic (∅ : Set P) :=
  ⟨cospherical_empty, coplanar_empty ℝ P⟩

/-- A single point is concyclic. -/
theorem concyclic_singleton (p : P) : Concyclic ({p} : Set P) :=
  ⟨cospherical_singleton p, coplanar_singleton ℝ p⟩

/-- Two points are concyclic. -/
theorem concyclic_pair (p₁ p₂ : P) : Concyclic ({p₁, p₂} : Set P) :=
  ⟨cospherical_pair p₁ p₂, coplanar_pair ℝ p₁ p₂⟩

namespace Sphere

/-- `s.IsDiameter p₁ p₂` says that `p₁` and `p₂` are the two endpoints of a diameter of `s`. -/
structure IsDiameter (s : Sphere P) (p₁ p₂ : P) : Prop where
  left_mem : p₁ ∈ s
  midpoint_eq_center : midpoint ℝ p₁ p₂ = s.center

variable {s : Sphere P} {p₁ p₂ p₃ : P}

lemma IsDiameter.right_mem (h : s.IsDiameter p₁ p₂) : p₂ ∈ s := by
  rw [mem_sphere, ← mem_sphere.1 h.left_mem, ← h.midpoint_eq_center,
    dist_left_midpoint_eq_dist_right_midpoint]

protected lemma IsDiameter.symm (h : s.IsDiameter p₁ p₂) : s.IsDiameter p₂ p₁ :=
  ⟨h.right_mem, midpoint_comm (R := ℝ) p₁ p₂ ▸ h.midpoint_eq_center⟩

lemma isDiameter_comm : s.IsDiameter p₁ p₂ ↔ s.IsDiameter p₂ p₁ :=
  ⟨IsDiameter.symm, IsDiameter.symm⟩

lemma isDiameter_iff_left_mem_and_midpoint_eq_center :
    s.IsDiameter p₁ p₂ ↔ p₁ ∈ s ∧ midpoint ℝ p₁ p₂ = s.center :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma isDiameter_iff_right_mem_and_midpoint_eq_center :
    s.IsDiameter p₁ p₂ ↔ p₂ ∈ s ∧ midpoint ℝ p₁ p₂ = s.center :=
  ⟨fun h ↦ ⟨h.right_mem, h.2⟩, fun h ↦ IsDiameter.symm ⟨h.1, midpoint_comm (R := ℝ) p₁ p₂ ▸ h.2⟩⟩

lemma IsDiameter.pointReflection_center_left (h : s.IsDiameter p₁ p₂) :
    Equiv.pointReflection s.center p₁ = p₂ := by
  rw [← h.midpoint_eq_center, Equiv.pointReflection_midpoint_left]

lemma IsDiameter.pointReflection_center_right (h : s.IsDiameter p₁ p₂) :
    Equiv.pointReflection s.center p₂ = p₁ := by
  rw [← h.midpoint_eq_center, Equiv.pointReflection_midpoint_right]

lemma isDiameter_iff_left_mem_and_pointReflection_center_left :
    s.IsDiameter p₁ p₂ ↔ p₁ ∈ s ∧ Equiv.pointReflection s.center p₁ = p₂ :=
  ⟨fun h ↦ ⟨h.1, h.pointReflection_center_left⟩, fun h ↦ ⟨h.1, by simp [← h.2]⟩⟩

lemma isDiameter_iff_right_mem_and_pointReflection_center_right :
    s.IsDiameter p₁ p₂ ↔ p₂ ∈ s ∧ Equiv.pointReflection s.center p₂ = p₁ := by
  rw [isDiameter_comm, isDiameter_iff_left_mem_and_pointReflection_center_left]

lemma IsDiameter.right_eq_of_isDiameter (h₁₂ : s.IsDiameter p₁ p₂) (h₁₃ : s.IsDiameter p₁ p₃) :
    p₂ = p₃ := by
  rw [← h₁₂.pointReflection_center_left, ← h₁₃.pointReflection_center_left]

lemma IsDiameter.left_eq_of_isDiameter (h₁₃ : s.IsDiameter p₁ p₃) (h₂₃ : s.IsDiameter p₂ p₃) :
    p₁ = p₂ := by
  rw [← h₁₃.pointReflection_center_right, ← h₂₃.pointReflection_center_right]

lemma IsDiameter.dist_left_right (h : s.IsDiameter p₁ p₂) : dist p₁ p₂ = 2 * s.radius := by
  rw [← mem_sphere.1 h.left_mem, ← h.midpoint_eq_center, dist_left_midpoint]
  simp

lemma IsDiameter.dist_left_right_div_two (h : s.IsDiameter p₁ p₂) :
    (dist p₁ p₂) / 2 = s.radius := by
  simp [h.dist_left_right]

lemma IsDiameter.left_eq_right_iff (h : s.IsDiameter p₁ p₂) : p₁ = p₂ ↔ s.radius = 0 := by
  rw [← dist_eq_zero, h.dist_left_right]
  simp

lemma IsDiameter.left_ne_right_iff_radius_ne_zero (h : s.IsDiameter p₁ p₂) :
    p₁ ≠ p₂ ↔ s.radius ≠ 0 :=
  h.left_eq_right_iff.not

lemma IsDiameter.left_ne_right_iff_radius_pos (h : s.IsDiameter p₁ p₂) :
    p₁ ≠ p₂ ↔ 0 < s.radius := by
  rw [h.left_ne_right_iff_radius_ne_zero, lt_iff_le_and_ne]
  simp [radius_nonneg_of_mem h.left_mem, eq_comm]

protected lemma IsDiameter.wbtw (h : s.IsDiameter p₁ p₂) : Wbtw ℝ p₁ s.center p₂ := by
  rw [← h.midpoint_eq_center]
  exact wbtw_midpoint _ _ _

protected lemma IsDiameter.sbtw (h : s.IsDiameter p₁ p₂) (hr : s.radius ≠ 0) :
    Sbtw ℝ p₁ s.center p₂ := by
  rw [← h.midpoint_eq_center]
  exact sbtw_midpoint_of_ne _ (h.left_ne_right_iff_radius_ne_zero.2 hr)

/-- Construct the sphere with the given diameter. -/
protected def ofDiameter (p₁ p₂ : P) : Sphere P :=
  ⟨midpoint ℝ p₁ p₂, (dist p₁ p₂) / 2⟩

lemma isDiameter_ofDiameter (p₁ p₂ : P) : (Sphere.ofDiameter p₁ p₂).IsDiameter p₁ p₂ :=
  ⟨by simp [Sphere.ofDiameter, mem_sphere, inv_mul_eq_div], rfl⟩

lemma IsDiameter.ofDiameter_eq (h : s.IsDiameter p₁ p₂) : .ofDiameter p₁ p₂ = s := by
  ext
  · simp [Sphere.ofDiameter, h.midpoint_eq_center]
  · simp [Sphere.ofDiameter, ← h.dist_left_right_div_two]

lemma isDiameter_iff_ofDiameter_eq : s.IsDiameter p₁ p₂ ↔ .ofDiameter p₁ p₂ = s :=
  ⟨IsDiameter.ofDiameter_eq, by rintro rfl; exact isDiameter_ofDiameter _ _⟩

end Sphere

end NormedSpace

section EuclideanSpace

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- A set of points in an affine subspace is cospherical if and only if its image in the ambient
space is cospherical. -/
@[simp]
theorem Cospherical.subtype_val_iff {S : AffineSubspace ℝ P} [Nonempty S]
    [S.direction.HasOrthogonalProjection] {ps : Set S} :
    Cospherical (Subtype.val '' ps) ↔ Cospherical ps := by
  refine ⟨fun h => ?_, Cospherical.subtype_val⟩
  rcases ps.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact cospherical_empty
  · rcases h with ⟨c, r, hr⟩
    let c' : S := orthogonalProjection S c
    refine ⟨c', dist p₀ c', fun p hp => ?_⟩
    have hp_dist : dist (p : P) c = r := by grind
    have hp₀_dist : dist (p₀ : P) c = r := by grind
    have hpp₀ : dist (p : P) (c : P) = dist (p₀ : P) (c : P) := hp_dist.trans hp₀_dist.symm
    exact (dist_eq_iff_dist_orthogonalProjection_eq (s := S) (p₃ := c) p.2 p₀.2).1 hpp₀

/-- A set of points is cospherical in an affine subspace `S₁` if and only if its image under the
inclusion into a larger affine subspace `S₂` is cospherical. -/
theorem Cospherical.inclusion_iff {S₁ S₂ : AffineSubspace ℝ P} [Nonempty S₁] {ps : Set S₁}
    [S₁.direction.HasOrthogonalProjection] [S₂.direction.HasOrthogonalProjection] (hS : S₁ ≤ S₂) :
    Cospherical (AffineSubspace.inclusion hS '' ps) ↔ Cospherical ps := by
  haveI : Nonempty S₂ := by obtain ⟨p⟩ := ‹Nonempty S₁›; exact ⟨⟨p, hS p.property⟩⟩
  simp [(Cospherical.subtype_val_iff (S := S₂) (ps := AffineSubspace.inclusion hS '' ps)).symm,
    Set.image_image]

/-- Any three points in a cospherical set are affinely independent. -/
theorem Cospherical.affineIndependent {s : Set P} (hs : Cospherical s) {p : Fin 3 → P}
    (hps : Set.range p ⊆ s) (hpi : Function.Injective p) : AffineIndependent ℝ p := by
  rw [affineIndependent_iff_not_collinear]
  intro hc
  rw [collinear_iff_of_mem (Set.mem_range_self (0 : Fin 3))] at hc
  rcases hc with ⟨v, hv⟩
  rw [Set.forall_mem_range] at hv
  have hv0 : v ≠ 0 := by
    intro h
    have he : p 1 = p 0 := by simpa [h] using hv 1
    exact (by decide : (1 : Fin 3) ≠ 0) (hpi he)
  rcases hs with ⟨c, r, hs⟩
  have hs' := fun i => hs (p i) (Set.mem_of_mem_of_subset (Set.mem_range_self _) hps)
  choose f hf using hv
  have hsd : ∀ i, dist (f i • v +ᵥ p 0) c = r := by
    intro i
    rw [← hf]
    exact hs' i
  have hf0 : f 0 = 0 := by
    have hf0' := hf 0
    rw [eq_comm, ← @vsub_eq_zero_iff_eq V, vadd_vsub, smul_eq_zero] at hf0'
    simpa [hv0] using hf0'
  have hfi : Function.Injective f := by
    intro i j h
    have hi := hf i
    rw [h, ← hf j] at hi
    exact hpi hi
  simp_rw [← hsd 0, hf0, zero_smul, zero_vadd, dist_smul_vadd_eq_dist (p 0) c hv0] at hsd
  have hfn0 : ∀ i, i ≠ 0 → f i ≠ 0 := fun i => (hfi.ne_iff' hf0).2
  have hfn0' : ∀ i, i ≠ 0 → f i = -2 * ⟪v, p 0 -ᵥ c⟫ / ⟪v, v⟫ := by
    intro i hi
    have hsdi := hsd i
    simpa [hfn0, hi] using hsdi
  have hf12 : f 1 = f 2 := by rw [hfn0' 1 (by decide), hfn0' 2 (by decide)]
  exact (by decide : (1 : Fin 3) ≠ 2) (hfi hf12)

/-- Any three points in a cospherical set are affinely independent. -/
theorem Cospherical.affineIndependent_of_mem_of_ne {s : Set P} (hs : Cospherical s) {p₁ p₂ p₃ : P}
    (h₁ : p₁ ∈ s) (h₂ : p₂ ∈ s) (h₃ : p₃ ∈ s) (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) :
    AffineIndependent ℝ ![p₁, p₂, p₃] := by
  refine hs.affineIndependent ?_ ?_
  · simp [h₁, h₂, h₃, Set.insert_subset_iff]
  · erw [Fin.cons_injective_iff, Fin.cons_injective_iff]
    simp [h₁₂, h₁₃, h₂₃, Function.Injective, eq_iff_true_of_subsingleton]

/-- The three points of a cospherical set are affinely independent. -/
theorem Cospherical.affineIndependent_of_ne {p₁ p₂ p₃ : P} (hs : Cospherical ({p₁, p₂, p₃} : Set P))
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) : AffineIndependent ℝ ![p₁, p₂, p₃] :=
  hs.affineIndependent_of_mem_of_ne (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) h₁₂ h₁₃ h₂₃

/-- Suppose that `p₁` and `p₂` lie in spheres `s₁` and `s₂`. Then the vector between the centers
of those spheres is orthogonal to that between `p₁` and `p₂`; this is a version of
`inner_vsub_vsub_of_dist_eq_of_dist_eq` for bundled spheres. (In two dimensions, this says that
the diagonals of a kite are orthogonal.) -/
theorem inner_vsub_vsub_of_mem_sphere_of_mem_sphere {p₁ p₂ : P} {s₁ s₂ : Sphere P} (hp₁s₁ : p₁ ∈ s₁)
    (hp₂s₁ : p₂ ∈ s₁) (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂) :
    ⟪s₂.center -ᵥ s₁.center, p₂ -ᵥ p₁⟫ = 0 :=
  inner_vsub_vsub_of_dist_eq_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere hp₁s₁ hp₂s₁)
    (dist_center_eq_dist_center_of_mem_sphere hp₁s₂ hp₂s₂)

/-- The vector from the midpoint of a chord to the center of the sphere is
orthogonal to the chord. -/
theorem Sphere.inner_vsub_center_midpoint_vsub {p₁ p₂ : P} {s : Sphere P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) :
    ⟪s.center -ᵥ midpoint ℝ p₁ p₂, p₂ -ᵥ p₁⟫ = 0 :=
  inner_vsub_vsub_of_dist_eq_of_dist_eq
    (dist_left_midpoint_eq_dist_right_midpoint p₁ p₂)
    (dist_center_eq_dist_center_of_mem_sphere hp₁ hp₂)

/-- The distance from the center of a sphere to any point strictly between
two points on the sphere is strictly less than the radius. -/
theorem Sphere.dist_center_lt_radius_of_sbtw {p₁ p₂ p : P} {s : Sphere P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp : Sbtw ℝ p₁ p p₂) :
    dist s.center p < s.radius := by
  set o := s.center
  obtain ⟨⟨t, ⟨ht₀, ht₁⟩, hpt⟩, hne₁, hne₂⟩ := hp
  have ht₀' : 0 < t := lt_of_le_of_ne ht₀ fun h => hne₁ <| by
    rw [← hpt, ← h, AffineMap.lineMap_apply_zero]
  have ht₁' : t < 1 := lt_of_le_of_ne ht₁ fun h => hne₂ <| by
    rw [← hpt, h, AffineMap.lineMap_apply_one]
  set u := p₁ -ᵥ o; set v := p₂ -ᵥ o
  have hu : ‖u‖ = s.radius := by rw [← dist_eq_norm_vsub]; exact mem_sphere.mp hp₁
  have hv : ‖v‖ = s.radius := by rw [← dist_eq_norm_vsub]; exact mem_sphere.mp hp₂
  have huv : u ≠ v := fun h => hne₁ <| by
    rw [← hpt, vsub_left_cancel h, AffineMap.lineMap_same, AffineMap.const_apply]
  have hpo : p -ᵥ o = (1 - t) • u + t • v := by
    rw [show p = (AffineMap.lineMap p₁ p₂) t from hpt.symm, AffineMap.lineMap_apply,
      vadd_vsub_assoc, show (p₂ -ᵥ p₁ : V) = v - u from
      (vsub_sub_vsub_cancel_right p₂ p₁ o).symm]
    module
  rw [dist_comm, dist_eq_norm_vsub, hpo]
  have hmem := (strictConvex_closedBall ℝ (0 : V) s.radius)
    (by simp [Metric.mem_closedBall, hu]) (by simp [Metric.mem_closedBall, hv])
    huv (sub_pos.mpr ht₁') ht₀' (sub_add_cancel 1 t)
  rwa [interior_closedBall _ (fun h : s.radius = 0 => huv <|
      (norm_eq_zero.mp (hu.trans h)).trans (norm_eq_zero.mp (hv.trans h)).symm),
    Metric.mem_ball, dist_zero_right] at hmem

/-- The distance from the center of a sphere to the midpoint of a chord
with distinct endpoints is strictly less than the radius. -/
theorem Sphere.dist_center_midpoint_lt_radius {p₁ p₂ : P} {s : Sphere P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₁p₂ : p₁ ≠ p₂) :
    dist s.center (midpoint ℝ p₁ p₂) < s.radius :=
  s.dist_center_lt_radius_of_sbtw hp₁ hp₂ (sbtw_midpoint_of_ne ℝ hp₁p₂)

/-- Two spheres intersect in at most two points in a two-dimensional subspace containing their
centers; this is a version of `eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two` for bundled
spheres. -/
theorem eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two {s : AffineSubspace ℝ P}
    [FiniteDimensional ℝ s.direction] (hd : finrank ℝ s.direction = 2) {s₁ s₂ : Sphere P}
    {p₁ p₂ p : P} (hs₁ : s₁.center ∈ s) (hs₂ : s₂.center ∈ s) (hp₁s : p₁ ∈ s) (hp₂s : p₂ ∈ s)
    (hps : p ∈ s) (hs : s₁ ≠ s₂) (hp : p₁ ≠ p₂) (hp₁s₁ : p₁ ∈ s₁) (hp₂s₁ : p₂ ∈ s₁) (hps₁ : p ∈ s₁)
    (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂) (hps₂ : p ∈ s₂) : p = p₁ ∨ p = p₂ :=
  eq_of_dist_eq_of_dist_eq_of_mem_of_finrank_eq_two hd hs₁ hs₂ hp₁s hp₂s hps
    ((Sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs) hp hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂

/-- Two spheres intersect in at most two points in two-dimensional space; this is a version of
`eq_of_dist_eq_of_dist_eq_of_finrank_eq_two` for bundled spheres. -/
theorem eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = 2) {s₁ s₂ : Sphere P} {p₁ p₂ p : P} (hs : s₁ ≠ s₂) (hp : p₁ ≠ p₂)
    (hp₁s₁ : p₁ ∈ s₁) (hp₂s₁ : p₂ ∈ s₁) (hps₁ : p ∈ s₁) (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂)
    (hps₂ : p ∈ s₂) : p = p₁ ∨ p = p₂ :=
  eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd ((Sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs) hp
    hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂

/-- Given a point on a sphere and a point not outside it, the inner product between the
difference of those points and the radius vector is positive unless the points are equal. -/
theorem inner_pos_or_eq_of_dist_le_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : dist p₂ s.center ≤ s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ ∨ p₁ = p₂ := by
  by_cases h : p₁ = p₂; · exact Or.inr h
  refine Or.inl ?_
  rw [mem_sphere] at hp₁
  rw [← vsub_sub_vsub_cancel_right p₁ p₂ s.center, inner_sub_left,
    real_inner_self_eq_norm_mul_norm, sub_pos]
  refine lt_of_le_of_ne
    ((real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))) ?_
  · rwa [← dist_eq_norm_vsub, ← dist_eq_norm_vsub, hp₁]
  · rcases hp₂.lt_or_eq with (hp₂' | hp₂')
    · refine ((real_inner_le_norm _ _).trans_lt (mul_lt_mul_of_pos_right ?_ ?_)).ne
      · rwa [← hp₁, @dist_eq_norm_vsub V, @dist_eq_norm_vsub V] at hp₂'
      · rw [norm_pos_iff, vsub_ne_zero]
        rintro rfl
        rw [← hp₁] at hp₂'
        refine (dist_nonneg.not_gt : ¬dist p₂ s.center < 0) ?_
        simpa using hp₂'
    · rw [← hp₁, @dist_eq_norm_vsub V, @dist_eq_norm_vsub V] at hp₂'
      nth_rw 1 [← hp₂']
      rw [Ne, inner_eq_norm_mul_iff_real, hp₂', ← sub_eq_zero, ← smul_sub,
        vsub_sub_vsub_cancel_right, ← Ne, smul_ne_zero_iff, vsub_ne_zero,
        and_iff_left (Ne.symm h), norm_ne_zero_iff, vsub_ne_zero]
      rintro rfl
      refine h (Eq.symm ?_)
      simpa using hp₂'

/-- Given a point on a sphere and a point not outside it, the inner product between the
difference of those points and the radius vector is nonnegative. -/
theorem inner_nonneg_of_dist_le_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : dist p₂ s.center ≤ s.radius) : 0 ≤ ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ := by
  rcases inner_pos_or_eq_of_dist_le_radius hp₁ hp₂ with (h | rfl)
  · exact h.le
  · simp

/-- Given a point on a sphere and a point inside it, the inner product between the difference of
those points and the radius vector is positive. -/
theorem inner_pos_of_dist_lt_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : dist p₂ s.center < s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ := by
  by_cases h : p₁ = p₂
  · rw [h, mem_sphere] at hp₁
    exact False.elim (hp₂.ne hp₁)
  exact (inner_pos_or_eq_of_dist_le_radius hp₁ hp₂.le).resolve_right h

/-- Given two distinct points on a sphere, the inner product of the chord with
the radius vector at one endpoint is negative. -/
theorem inner_vsub_center_vsub_pos {p₁ p₂ : P} {s : Sphere P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₁p₂ : p₁ ≠ p₂) :
    0 < ⟪p₂ -ᵥ p₁, s.center -ᵥ p₁⟫ := by
  have hp₁' : ‖p₁ -ᵥ s.center‖ = s.radius := by rw [← dist_eq_norm_vsub']; exact mem_sphere'.mp hp₁
  have hp₂' : ‖p₂ -ᵥ s.center‖ = s.radius := by rw [← dist_eq_norm_vsub']; exact mem_sphere'.mp hp₂
  have hd : ‖p₂ -ᵥ s.center‖ ^ 2 =
      ‖p₂ -ᵥ p₁‖ ^ 2 + 2 * ⟪p₂ -ᵥ p₁, p₁ -ᵥ s.center⟫ + ‖p₁ -ᵥ s.center‖ ^ 2 := by
    rw [← vsub_add_vsub_cancel p₂ p₁ s.center, norm_add_sq_real]
  rw [hp₂', hp₁', ← neg_vsub_eq_vsub_rev s.center p₁, inner_neg_right] at hd
  nlinarith [sq_pos_of_pos (norm_pos_iff.mpr (vsub_ne_zero.mpr hp₁p₂.symm))]

/-- Given three collinear points, two on a sphere and one not outside it, the one not outside it
is weakly between the other two points. -/
theorem wbtw_of_collinear_of_dist_center_le_radius {s : Sphere P} {p₁ p₂ p₃ : P}
    (h : Collinear ℝ ({p₁, p₂, p₃} : Set P)) (hp₁ : p₁ ∈ s) (hp₂ : dist p₂ s.center ≤ s.radius)
    (hp₃ : p₃ ∈ s) (hp₁p₃ : p₁ ≠ p₃) : Wbtw ℝ p₁ p₂ p₃ :=
  h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂ hp₃ hp₁p₃

/-- Given three collinear points, two on a sphere and one inside it, the one inside it is
strictly between the other two points. -/
theorem sbtw_of_collinear_of_dist_center_lt_radius {s : Sphere P} {p₁ p₂ p₃ : P}
    (h : Collinear ℝ ({p₁, p₂, p₃} : Set P)) (hp₁ : p₁ ∈ s) (hp₂ : dist p₂ s.center < s.radius)
    (hp₃ : p₃ ∈ s) (hp₁p₃ : p₁ ≠ p₃) : Sbtw ℝ p₁ p₂ p₃ :=
  h.sbtw_of_dist_eq_of_dist_lt hp₁ hp₂ hp₃ hp₁p₃

namespace Sphere

variable {s : Sphere P} {p₁ p₂ : P}

lemma isDiameter_iff_mem_and_mem_and_dist :
    s.IsDiameter p₁ p₂ ↔ p₁ ∈ s ∧ p₂ ∈ s ∧ dist p₁ p₂ = 2 * s.radius := by
  refine ⟨fun h ↦ ⟨h.left_mem, h.right_mem, h.dist_left_right⟩, fun ⟨h₁, h₂, hr⟩ ↦ ⟨h₁, ?_⟩⟩
  rw [midpoint_eq_iff, AffineEquiv.pointReflection_apply, eq_comm, eq_vadd_iff_vsub_eq]
  apply eq_of_norm_eq_of_norm_add_eq
  · simp_rw [← dist_eq_norm_vsub, mem_sphere'.1 h₁, mem_sphere.1 h₂]
  · simp_rw [vsub_add_vsub_cancel, ← dist_eq_norm_vsub, mem_sphere'.1 h₁, mem_sphere.1 h₂]
    rw [dist_comm, hr, two_mul]

lemma isDiameter_iff_mem_and_mem_and_wbtw :
    s.IsDiameter p₁ p₂ ↔ p₁ ∈ s ∧ p₂ ∈ s ∧ Wbtw ℝ p₁ s.center p₂ := by
  refine ⟨fun h ↦ ⟨h.left_mem, h.right_mem, h.wbtw⟩, fun ⟨h₁, h₂, hr⟩ ↦ ?_⟩
  have hd := hr.dist_add_dist
  rw [mem_sphere.1 h₁, mem_sphere'.1 h₂, ← two_mul, eq_comm] at hd
  exact isDiameter_iff_mem_and_mem_and_dist.2 ⟨h₁, h₂, hd⟩

end Sphere

end EuclideanSpace

end EuclideanGeometry
