/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers

! This file was ported from Lean 3 source module geometry.euclidean.sphere.basic
! leanprover-community/mathlib commit 46b633fd842bef9469441c0209906f6dddd2b4f5
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Convex.StrictConvexBetween
import Mathbin.Geometry.Euclidean.Basic

/-!
# Spheres

This file defines and proves basic results about spheres and cospherical sets of points in
Euclidean affine spaces.

## Main definitions

* `euclidean_geometry.sphere` bundles a `center` and a `radius`.

* `euclidean_geometry.cospherical` is the property of a set of points being equidistant from some
  point.

* `euclidean_geometry.concyclic` is the property of a set of points being cospherical and
  coplanar.

-/


noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type _} (P : Type _)

open FiniteDimensional

/-- A `sphere P` bundles a `center` and `radius`. This definition does not require the radius to
be positive; that should be given as a hypothesis to lemmas that require it. -/
@[ext]
structure Sphere [MetricSpace P] where
  center : P
  radius : ℝ
#align euclidean_geometry.sphere EuclideanGeometry.Sphere

variable {P}

section MetricSpace

variable [MetricSpace P]

instance [Nonempty P] : Nonempty (Sphere P) :=
  ⟨⟨Classical.arbitrary P, 0⟩⟩

instance : Coe (Sphere P) (Set P) :=
  ⟨fun s => Metric.sphere s.center s.radius⟩

instance : Membership P (Sphere P) :=
  ⟨fun p s => p ∈ (s : Set P)⟩

theorem Sphere.mk_center (c : P) (r : ℝ) : (⟨c, r⟩ : Sphere P).center = c :=
  rfl
#align euclidean_geometry.sphere.mk_center EuclideanGeometry.Sphere.mk_center

theorem Sphere.mk_radius (c : P) (r : ℝ) : (⟨c, r⟩ : Sphere P).radius = r :=
  rfl
#align euclidean_geometry.sphere.mk_radius EuclideanGeometry.Sphere.mk_radius

@[simp]
theorem Sphere.mk_center_radius (s : Sphere P) : (⟨s.center, s.radius⟩ : Sphere P) = s := by
  ext <;> rfl
#align euclidean_geometry.sphere.mk_center_radius EuclideanGeometry.Sphere.mk_center_radius

theorem Sphere.coe_def (s : Sphere P) : (s : Set P) = Metric.sphere s.center s.radius :=
  rfl
#align euclidean_geometry.sphere.coe_def EuclideanGeometry.Sphere.coe_def

@[simp]
theorem Sphere.coe_mk (c : P) (r : ℝ) : ↑(⟨c, r⟩ : Sphere P) = Metric.sphere c r :=
  rfl
#align euclidean_geometry.sphere.coe_mk EuclideanGeometry.Sphere.coe_mk

@[simp]
theorem Sphere.mem_coe {p : P} {s : Sphere P} : p ∈ (s : Set P) ↔ p ∈ s :=
  Iff.rfl
#align euclidean_geometry.sphere.mem_coe EuclideanGeometry.Sphere.mem_coe

theorem mem_sphere {p : P} {s : Sphere P} : p ∈ s ↔ dist p s.center = s.radius :=
  Iff.rfl
#align euclidean_geometry.mem_sphere EuclideanGeometry.mem_sphere

theorem mem_sphere' {p : P} {s : Sphere P} : p ∈ s ↔ dist s.center p = s.radius :=
  Metric.mem_sphere'
#align euclidean_geometry.mem_sphere' EuclideanGeometry.mem_sphere'

theorem subset_sphere {ps : Set P} {s : Sphere P} : ps ⊆ s ↔ ∀ p ∈ ps, p ∈ s :=
  Iff.rfl
#align euclidean_geometry.subset_sphere EuclideanGeometry.subset_sphere

theorem dist_of_mem_subset_sphere {p : P} {ps : Set P} {s : Sphere P} (hp : p ∈ ps)
    (hps : ps ⊆ (s : Set P)) : dist p s.center = s.radius :=
  mem_sphere.1 (Sphere.mem_coe.1 (Set.mem_of_mem_of_subset hp hps))
#align euclidean_geometry.dist_of_mem_subset_sphere EuclideanGeometry.dist_of_mem_subset_sphere

theorem dist_of_mem_subset_mk_sphere {p c : P} {ps : Set P} {r : ℝ} (hp : p ∈ ps)
    (hps : ps ⊆ ↑(⟨c, r⟩ : Sphere P)) : dist p c = r :=
  dist_of_mem_subset_sphere hp hps
#align euclidean_geometry.dist_of_mem_subset_mk_sphere EuclideanGeometry.dist_of_mem_subset_mk_sphere

theorem Sphere.ne_iff {s₁ s₂ : Sphere P} :
    s₁ ≠ s₂ ↔ s₁.center ≠ s₂.center ∨ s₁.radius ≠ s₂.radius := by
  rw [← not_and_or, ← sphere.ext_iff]
#align euclidean_geometry.sphere.ne_iff EuclideanGeometry.Sphere.ne_iff

theorem Sphere.center_eq_iff_eq_of_mem {s₁ s₂ : Sphere P} {p : P} (hs₁ : p ∈ s₁) (hs₂ : p ∈ s₂) :
    s₁.center = s₂.center ↔ s₁ = s₂ :=
  by
  refine' ⟨fun h => sphere.ext _ _ h _, fun h => h ▸ rfl⟩
  rw [mem_sphere] at hs₁ hs₂
  rw [← hs₁, ← hs₂, h]
#align euclidean_geometry.sphere.center_eq_iff_eq_of_mem EuclideanGeometry.Sphere.center_eq_iff_eq_of_mem

theorem Sphere.center_ne_iff_ne_of_mem {s₁ s₂ : Sphere P} {p : P} (hs₁ : p ∈ s₁) (hs₂ : p ∈ s₂) :
    s₁.center ≠ s₂.center ↔ s₁ ≠ s₂ :=
  (Sphere.center_eq_iff_eq_of_mem hs₁ hs₂).Not
#align euclidean_geometry.sphere.center_ne_iff_ne_of_mem EuclideanGeometry.Sphere.center_ne_iff_ne_of_mem

theorem dist_center_eq_dist_center_of_mem_sphere {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : dist p₁ s.center = dist p₂ s.center := by
  rw [mem_sphere.1 hp₁, mem_sphere.1 hp₂]
#align euclidean_geometry.dist_center_eq_dist_center_of_mem_sphere EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere

theorem dist_center_eq_dist_center_of_mem_sphere' {p₁ p₂ : P} {s : Sphere P} (hp₁ : p₁ ∈ s)
    (hp₂ : p₂ ∈ s) : dist s.center p₁ = dist s.center p₂ := by
  rw [mem_sphere'.1 hp₁, mem_sphere'.1 hp₂]
#align euclidean_geometry.dist_center_eq_dist_center_of_mem_sphere' EuclideanGeometry.dist_center_eq_dist_center_of_mem_sphere'

/-- A set of points is cospherical if they are equidistant from some
point.  In two dimensions, this is the same thing as being
concyclic. -/
def Cospherical (ps : Set P) : Prop :=
  ∃ (center : P)(radius : ℝ), ∀ p ∈ ps, dist p center = radius
#align euclidean_geometry.cospherical EuclideanGeometry.Cospherical

/-- The definition of `cospherical`. -/
theorem cospherical_def (ps : Set P) :
    Cospherical ps ↔ ∃ (center : P)(radius : ℝ), ∀ p ∈ ps, dist p center = radius :=
  Iff.rfl
#align euclidean_geometry.cospherical_def EuclideanGeometry.cospherical_def

/-- A set of points is cospherical if and only if they lie in some sphere. -/
theorem cospherical_iff_exists_sphere {ps : Set P} :
    Cospherical ps ↔ ∃ s : Sphere P, ps ⊆ (s : Set P) :=
  by
  refine' ⟨fun h => _, fun h => _⟩
  · rcases h with ⟨c, r, h⟩
    exact ⟨⟨c, r⟩, h⟩
  · rcases h with ⟨s, h⟩
    exact ⟨s.center, s.radius, h⟩
#align euclidean_geometry.cospherical_iff_exists_sphere EuclideanGeometry.cospherical_iff_exists_sphere

/-- The set of points in a sphere is cospherical. -/
theorem Sphere.cospherical (s : Sphere P) : Cospherical (s : Set P) :=
  cospherical_iff_exists_sphere.2 ⟨s, Set.Subset.rfl⟩
#align euclidean_geometry.sphere.cospherical EuclideanGeometry.Sphere.cospherical

/-- A subset of a cospherical set is cospherical. -/
theorem Cospherical.subset {ps₁ ps₂ : Set P} (hs : ps₁ ⊆ ps₂) (hc : Cospherical ps₂) :
    Cospherical ps₁ := by
  rcases hc with ⟨c, r, hcr⟩
  exact ⟨c, r, fun p hp => hcr p (hs hp)⟩
#align euclidean_geometry.cospherical.subset EuclideanGeometry.Cospherical.subset

/-- The empty set is cospherical. -/
theorem cospherical_empty [Nonempty P] : Cospherical (∅ : Set P) :=
  let ⟨p⟩ := ‹Nonempty P›
  ⟨p, 0, fun p => False.elim⟩
#align euclidean_geometry.cospherical_empty EuclideanGeometry.cospherical_empty

/-- A single point is cospherical. -/
theorem cospherical_singleton (p : P) : Cospherical ({p} : Set P) :=
  by
  use p
  simp
#align euclidean_geometry.cospherical_singleton EuclideanGeometry.cospherical_singleton

end MetricSpace

section NormedSpace

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

include V

/-- Two points are cospherical. -/
theorem cospherical_pair (p₁ p₂ : P) : Cospherical ({p₁, p₂} : Set P) :=
  ⟨midpoint ℝ p₁ p₂, ‖(2 : ℝ)‖⁻¹ * dist p₁ p₂,
    by
    rintro p (rfl | rfl | _)
    · rw [dist_comm, dist_midpoint_left]
    · rw [dist_comm, dist_midpoint_right]⟩
#align euclidean_geometry.cospherical_pair EuclideanGeometry.cospherical_pair

/-- A set of points is concyclic if it is cospherical and coplanar. (Most results are stated
directly in terms of `cospherical` instead of using `concyclic`.) -/
structure Concyclic (ps : Set P) : Prop where
  Cospherical : Cospherical ps
  Coplanar : Coplanar ℝ ps
#align euclidean_geometry.concyclic EuclideanGeometry.Concyclic

/-- A subset of a concyclic set is concyclic. -/
theorem Concyclic.subset {ps₁ ps₂ : Set P} (hs : ps₁ ⊆ ps₂) (h : Concyclic ps₂) : Concyclic ps₁ :=
  ⟨h.1.Subset hs, h.2.Subset hs⟩
#align euclidean_geometry.concyclic.subset EuclideanGeometry.Concyclic.subset

/-- The empty set is concyclic. -/
theorem concyclic_empty : Concyclic (∅ : Set P) :=
  ⟨cospherical_empty, coplanar_empty ℝ P⟩
#align euclidean_geometry.concyclic_empty EuclideanGeometry.concyclic_empty

/-- A single point is concyclic. -/
theorem concyclic_singleton (p : P) : Concyclic ({p} : Set P) :=
  ⟨cospherical_singleton p, coplanar_singleton ℝ p⟩
#align euclidean_geometry.concyclic_singleton EuclideanGeometry.concyclic_singleton

/-- Two points are concyclic. -/
theorem concyclic_pair (p₁ p₂ : P) : Concyclic ({p₁, p₂} : Set P) :=
  ⟨cospherical_pair p₁ p₂, coplanar_pair ℝ p₁ p₂⟩
#align euclidean_geometry.concyclic_pair EuclideanGeometry.concyclic_pair

end NormedSpace

section EuclideanSpace

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

include V

/-- Any three points in a cospherical set are affinely independent. -/
theorem Cospherical.affineIndependent {s : Set P} (hs : Cospherical s) {p : Fin 3 → P}
    (hps : Set.range p ⊆ s) (hpi : Function.Injective p) : AffineIndependent ℝ p :=
  by
  rw [affineIndependent_iff_not_collinear]
  intro hc
  rw [collinear_iff_of_mem (Set.mem_range_self (0 : Fin 3))] at hc
  rcases hc with ⟨v, hv⟩
  rw [Set.forall_range_iff] at hv
  have hv0 : v ≠ 0 := by
    intro h
    have he : p 1 = p 0 := by simpa [h] using hv 1
    exact (by decide : (1 : Fin 3) ≠ 0) (hpi he)
  rcases hs with ⟨c, r, hs⟩
  have hs' := fun i => hs (p i) (Set.mem_of_mem_of_subset (Set.mem_range_self _) hps)
  choose f hf using hv
  have hsd : ∀ i, dist (f i • v +ᵥ p 0) c = r :=
    by
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
  have hfn0' : ∀ i, i ≠ 0 → f i = -2 * ⟪v, p 0 -ᵥ c⟫ / ⟪v, v⟫ :=
    by
    intro i hi
    have hsdi := hsd i
    simpa [hfn0, hi] using hsdi
  have hf12 : f 1 = f 2 := by rw [hfn0' 1 (by decide), hfn0' 2 (by decide)]
  exact (by decide : (1 : Fin 3) ≠ 2) (hfi hf12)
#align euclidean_geometry.cospherical.affine_independent EuclideanGeometry.Cospherical.affineIndependent

/-- Any three points in a cospherical set are affinely independent. -/
theorem Cospherical.affineIndependent_of_mem_of_ne {s : Set P} (hs : Cospherical s) {p₁ p₂ p₃ : P}
    (h₁ : p₁ ∈ s) (h₂ : p₂ ∈ s) (h₃ : p₃ ∈ s) (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) :
    AffineIndependent ℝ ![p₁, p₂, p₃] :=
  by
  refine' hs.affine_independent _ _
  · simp [h₁, h₂, h₃, Set.insert_subset]
  · erw [Fin.cons_injective_iff, Fin.cons_injective_iff]
    simp [h₁₂, h₁₃, h₂₃, Function.Injective]
#align euclidean_geometry.cospherical.affine_independent_of_mem_of_ne EuclideanGeometry.Cospherical.affineIndependent_of_mem_of_ne

/-- The three points of a cospherical set are affinely independent. -/
theorem Cospherical.affineIndependent_of_ne {p₁ p₂ p₃ : P} (hs : Cospherical ({p₁, p₂, p₃} : Set P))
    (h₁₂ : p₁ ≠ p₂) (h₁₃ : p₁ ≠ p₃) (h₂₃ : p₂ ≠ p₃) : AffineIndependent ℝ ![p₁, p₂, p₃] :=
  hs.affineIndependent_of_mem_of_ne (Set.mem_insert _ _)
    (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))) h₁₂ h₁₃ h₂₃
#align euclidean_geometry.cospherical.affine_independent_of_ne EuclideanGeometry.Cospherical.affineIndependent_of_ne

/-- Suppose that `p₁` and `p₂` lie in spheres `s₁` and `s₂`.  Then the vector between the centers
of those spheres is orthogonal to that between `p₁` and `p₂`; this is a version of
`inner_vsub_vsub_of_dist_eq_of_dist_eq` for bundled spheres.  (In two dimensions, this says that
the diagonals of a kite are orthogonal.) -/
theorem inner_vsub_vsub_of_mem_sphere_of_mem_sphere {p₁ p₂ : P} {s₁ s₂ : Sphere P} (hp₁s₁ : p₁ ∈ s₁)
    (hp₂s₁ : p₂ ∈ s₁) (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂) :
    ⟪s₂.center -ᵥ s₁.center, p₂ -ᵥ p₁⟫ = 0 :=
  inner_vsub_vsub_of_dist_eq_of_dist_eq (dist_center_eq_dist_center_of_mem_sphere hp₁s₁ hp₂s₁)
    (dist_center_eq_dist_center_of_mem_sphere hp₁s₂ hp₂s₂)
#align euclidean_geometry.inner_vsub_vsub_of_mem_sphere_of_mem_sphere EuclideanGeometry.inner_vsub_vsub_of_mem_sphere_of_mem_sphere

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
#align euclidean_geometry.eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_mem_of_finrank_eq_two

/-- Two spheres intersect in at most two points in two-dimensional space; this is a version of
`eq_of_dist_eq_of_dist_eq_of_finrank_eq_two` for bundled spheres. -/
theorem eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two [FiniteDimensional ℝ V]
    (hd : finrank ℝ V = 2) {s₁ s₂ : Sphere P} {p₁ p₂ p : P} (hs : s₁ ≠ s₂) (hp : p₁ ≠ p₂)
    (hp₁s₁ : p₁ ∈ s₁) (hp₂s₁ : p₂ ∈ s₁) (hps₁ : p ∈ s₁) (hp₁s₂ : p₁ ∈ s₂) (hp₂s₂ : p₂ ∈ s₂)
    (hps₂ : p ∈ s₂) : p = p₁ ∨ p = p₂ :=
  eq_of_dist_eq_of_dist_eq_of_finrank_eq_two hd ((Sphere.center_ne_iff_ne_of_mem hps₁ hps₂).2 hs) hp
    hp₁s₁ hp₂s₁ hps₁ hp₁s₂ hp₂s₂ hps₂
#align euclidean_geometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two EuclideanGeometry.eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two

/-- Given a point on a sphere and a point not outside it, the inner product between the
difference of those points and the radius vector is positive unless the points are equal. -/
theorem inner_pos_or_eq_of_dist_le_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : dist p₂ s.center ≤ s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ ∨ p₁ = p₂ :=
  by
  by_cases h : p₁ = p₂; · exact Or.inr h
  refine' Or.inl _
  rw [mem_sphere] at hp₁
  rw [← vsub_sub_vsub_cancel_right p₁ p₂ s.center, inner_sub_left,
    real_inner_self_eq_norm_mul_norm,--, ←dist_eq_norm_vsub, hp₁
    sub_pos]
  refine'
    lt_of_le_of_ne ((real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right _ (norm_nonneg _))) _
  · rwa [← dist_eq_norm_vsub, ← dist_eq_norm_vsub, hp₁]
  · rcases hp₂.lt_or_eq with (hp₂' | hp₂')
    · refine' ((real_inner_le_norm _ _).trans_lt (mul_lt_mul_of_pos_right _ _)).Ne
      · rwa [← hp₁, @dist_eq_norm_vsub V, @dist_eq_norm_vsub V] at hp₂'
      · rw [norm_pos_iff, vsub_ne_zero]
        rintro rfl
        rw [← hp₁] at hp₂'
        refine' (dist_nonneg.not_lt : ¬dist p₂ s.center < 0) _
        simpa using hp₂'
    · rw [← hp₁, @dist_eq_norm_vsub V, @dist_eq_norm_vsub V] at hp₂'
      nth_rw 1 [← hp₂']
      rw [Ne.def, inner_eq_norm_mul_iff_real, hp₂', ← sub_eq_zero, ← smul_sub,
        vsub_sub_vsub_cancel_right, ← Ne.def, smul_ne_zero_iff, vsub_ne_zero,
        and_iff_left (Ne.symm h), norm_ne_zero_iff, vsub_ne_zero]
      rintro rfl
      refine' h (Eq.symm _)
      simpa using hp₂'
#align euclidean_geometry.inner_pos_or_eq_of_dist_le_radius EuclideanGeometry.inner_pos_or_eq_of_dist_le_radius

/-- Given a point on a sphere and a point not outside it, the inner product between the
difference of those points and the radius vector is nonnegative. -/
theorem inner_nonneg_of_dist_le_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : dist p₂ s.center ≤ s.radius) : 0 ≤ ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ :=
  by
  rcases inner_pos_or_eq_of_dist_le_radius hp₁ hp₂ with (h | rfl)
  · exact h.le
  · simp
#align euclidean_geometry.inner_nonneg_of_dist_le_radius EuclideanGeometry.inner_nonneg_of_dist_le_radius

/-- Given a point on a sphere and a point inside it, the inner product between the difference of
those points and the radius vector is positive. -/
theorem inner_pos_of_dist_lt_radius {s : Sphere P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s)
    (hp₂ : dist p₂ s.center < s.radius) : 0 < ⟪p₁ -ᵥ p₂, p₁ -ᵥ s.center⟫ :=
  by
  by_cases h : p₁ = p₂
  · rw [h, mem_sphere] at hp₁
    exact False.elim (hp₂.ne hp₁)
  exact (inner_pos_or_eq_of_dist_le_radius hp₁ hp₂.le).resolve_right h
#align euclidean_geometry.inner_pos_of_dist_lt_radius EuclideanGeometry.inner_pos_of_dist_lt_radius

/-- Given three collinear points, two on a sphere and one not outside it, the one not outside it
is weakly between the other two points. -/
theorem wbtw_of_collinear_of_dist_center_le_radius {s : Sphere P} {p₁ p₂ p₃ : P}
    (h : Collinear ℝ ({p₁, p₂, p₃} : Set P)) (hp₁ : p₁ ∈ s) (hp₂ : dist p₂ s.center ≤ s.radius)
    (hp₃ : p₃ ∈ s) (hp₁p₃ : p₁ ≠ p₃) : Wbtw ℝ p₁ p₂ p₃ :=
  h.wbtw_of_dist_eq_of_dist_le hp₁ hp₂ hp₃ hp₁p₃
#align euclidean_geometry.wbtw_of_collinear_of_dist_center_le_radius EuclideanGeometry.wbtw_of_collinear_of_dist_center_le_radius

/-- Given three collinear points, two on a sphere and one inside it, the one inside it is
strictly between the other two points. -/
theorem sbtw_of_collinear_of_dist_center_lt_radius {s : Sphere P} {p₁ p₂ p₃ : P}
    (h : Collinear ℝ ({p₁, p₂, p₃} : Set P)) (hp₁ : p₁ ∈ s) (hp₂ : dist p₂ s.center < s.radius)
    (hp₃ : p₃ ∈ s) (hp₁p₃ : p₁ ≠ p₃) : Sbtw ℝ p₁ p₂ p₃ :=
  h.sbtw_of_dist_eq_of_dist_lt hp₁ hp₂ hp₃ hp₁p₃
#align euclidean_geometry.sbtw_of_collinear_of_dist_center_lt_radius EuclideanGeometry.sbtw_of_collinear_of_dist_center_lt_radius

end EuclideanSpace

end EuclideanGeometry

