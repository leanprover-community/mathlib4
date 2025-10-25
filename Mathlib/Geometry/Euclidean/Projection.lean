/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Algebra.ContinuousAffineMap

/-!
# Orthogonal projection in Euclidean affine spaces

This file defines orthogonal projection onto an affine subspace in a Euclidean affine space,
and reflection of a point in an affine subspace.

## Main definitions

* `EuclideanGeometry.orthogonalProjection` is the orthogonal
  projection of a point onto an affine subspace.

* `EuclideanGeometry.reflection` is the reflection of a point in an
  affine subspace.

-/

noncomputable section

open RealInnerProductSpace

namespace EuclideanGeometry

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

open AffineSubspace Module

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete, as an unbundled function. This
definition is only intended for use in setting up the bundled version
`orthogonalProjection` and should not be used once that is
defined. -/
def orthogonalProjectionFn (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : P :=
  Classical.choose <|
    inter_eq_singleton_of_nonempty_of_isCompl (nonempty_subtype.mp ‹_›)
      (mk'_nonempty p s.directionᗮ)
      (by
        rw [direction_mk' p s.directionᗮ]
        exact Submodule.isCompl_orthogonal_of_hasOrthogonalProjection)

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonalProjectionFn` of that
point onto the subspace. This lemma is only intended for use in
setting up the bundled version and should not be used once that is
defined. -/
theorem inter_eq_singleton_orthogonalProjectionFn {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    (s : Set P) ∩ mk' p s.directionᗮ = {orthogonalProjectionFn s p} :=
  Classical.choose_spec <|
    inter_eq_singleton_of_nonempty_of_isCompl (nonempty_subtype.mp ‹_›)
      (mk'_nonempty p s.directionᗮ)
      (by
        rw [direction_mk' p s.directionᗮ]
        exact Submodule.isCompl_orthogonal_of_hasOrthogonalProjection)

/-- The `orthogonalProjectionFn` lies in the given subspace. This
lemma is only intended for use in setting up the bundled version and
should not be used once that is defined. -/
theorem orthogonalProjectionFn_mem {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : orthogonalProjectionFn s p ∈ s := by
  rw [← mem_coe, ← Set.singleton_subset_iff, ← inter_eq_singleton_orthogonalProjectionFn]
  exact Set.inter_subset_left

/-- The `orthogonalProjectionFn` lies in the orthogonal
subspace. This lemma is only intended for use in setting up the
bundled version and should not be used once that is defined. -/
theorem orthogonalProjectionFn_mem_orthogonal {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    orthogonalProjectionFn s p ∈ mk' p s.directionᗮ := by
  rw [← mem_coe, ← Set.singleton_subset_iff, ← inter_eq_singleton_orthogonalProjectionFn]
  exact Set.inter_subset_right

/-- Subtracting `p` from its `orthogonalProjectionFn` produces a
result in the orthogonal direction. This lemma is only intended for
use in setting up the bundled version and should not be used once that
is defined. -/
theorem orthogonalProjectionFn_vsub_mem_direction_orthogonal {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    orthogonalProjectionFn s p -ᵥ p ∈ s.directionᗮ :=
  direction_mk' p s.directionᗮ ▸
    vsub_mem_direction (orthogonalProjectionFn_mem_orthogonal p) (self_mem_mk' _ _)

/-- Auxiliary definition for setting up the orthogonal projection. This one is a bundled affine
map; the final `orthogonalProjection` is a continuous affine map. -/
nonrec def orthogonalProjectionAux (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] : P →ᵃ[ℝ] s where
  toFun p := ⟨orthogonalProjectionFn s p, orthogonalProjectionFn_mem p⟩
  linear := s.direction.orthogonalProjection
  map_vadd' p v := by
    have hs : s.direction.starProjection v +ᵥ orthogonalProjectionFn s p ∈ s :=
      vadd_mem_of_mem_direction (s.direction.orthogonalProjection v).2
        (orthogonalProjectionFn_mem p)
    have ho :
      s.direction.starProjection v +ᵥ orthogonalProjectionFn s p ∈
        mk' (v +ᵥ p) s.directionᗮ := by
      rw [← vsub_right_mem_direction_iff_mem (self_mem_mk' _ _) _, direction_mk',
        vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm, add_sub_assoc]
      refine Submodule.add_mem _ (orthogonalProjectionFn_vsub_mem_direction_orthogonal p) ?_
      rw [Submodule.mem_orthogonal']
      intro w hw
      rw [← neg_sub, inner_neg_left, Submodule.starProjection_inner_eq_zero _ w hw, neg_zero]
    have hm :
      (s.direction.orthogonalProjection v : V) +ᵥ orthogonalProjectionFn s p ∈
        ({orthogonalProjectionFn s (v +ᵥ p)} : Set P) := by
      rw [← inter_eq_singleton_orthogonalProjectionFn (v +ᵥ p)]
      exact Set.mem_inter hs ho
    rw [Set.mem_singleton_iff] at hm
    ext
    exact hm.symm

/-- The orthogonal projection of a point onto a nonempty affine
subspace, whose direction is complete. The corresponding linear map
(mapping a vector to the difference between the projections of two
points whose difference is that vector) is the `orthogonalProjection`
for real inner product spaces, onto the direction of the affine
subspace being projected onto. -/
nonrec def orthogonalProjection (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] : P →ᴬ[ℝ] s where
  __ := orthogonalProjectionAux s
  cont := AffineMap.continuous_linear_iff.1 s.direction.orthogonalProjection.cont

@[simp]
theorem orthogonalProjectionFn_eq {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    orthogonalProjectionFn s p = orthogonalProjection s p :=
  rfl

/-- Since both instance arguments are propositions, allow `simp` to rewrite them
alongside the `s` argument.

Note that without the coercion to `P`, the LHS and RHS would have different types. -/
@[congr]
theorem orthogonalProjection_congr {s₁ s₂ : AffineSubspace ℝ P} {p₁ p₂ : P}
    [Nonempty s₁] [s₁.direction.HasOrthogonalProjection]
    (h : s₁ = s₂) (hp : p₁ = p₂) :
    letI : Nonempty s₂ := h ▸ ‹_›
    letI : s₂.direction.HasOrthogonalProjection := h ▸ ‹_›
    (orthogonalProjection s₁ p₁ : P) = (orthogonalProjection s₂ p₂ : P) := by
  subst h hp
  rfl

/-- The linear map corresponding to `orthogonalProjection`. -/
@[simp]
theorem orthogonalProjection_linear {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] :
    (orthogonalProjection s).linear = s.direction.orthogonalProjection :=
  rfl

/-- The continuous linear map corresponding to `orthogonalProjection`. -/
@[simp]
theorem orthogonalProjection_contLinear {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] :
    (orthogonalProjection s).contLinear = s.direction.orthogonalProjection :=
  rfl

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonalProjection` of that point
onto the subspace. -/
theorem inter_eq_singleton_orthogonalProjection {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    (s : Set P) ∩ mk' p s.directionᗮ = {↑(orthogonalProjection s p)} := by
  rw [← orthogonalProjectionFn_eq]
  exact inter_eq_singleton_orthogonalProjectionFn p

/-- The `orthogonalProjection` lies in the given subspace. -/
theorem orthogonalProjection_mem {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : ↑(orthogonalProjection s p) ∈ s :=
  (orthogonalProjection s p).2

/-- The `orthogonalProjection` lies in the orthogonal subspace. -/
theorem orthogonalProjection_mem_orthogonal (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    ↑(orthogonalProjection s p) ∈ mk' p s.directionᗮ :=
  orthogonalProjectionFn_mem_orthogonal p

/-- Subtracting a point in the given subspace from the
`orthogonalProjection` produces a result in the direction of the
given subspace. -/
theorem orthogonalProjection_vsub_mem_direction {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (hp₁ : p₁ ∈ s) :
    ↑(orthogonalProjection s p₂ -ᵥ ⟨p₁, hp₁⟩ : s.direction) ∈ s.direction :=
  (orthogonalProjection s p₂ -ᵥ ⟨p₁, hp₁⟩ : s.direction).2

/-- Subtracting the `orthogonalProjection` from a point in the given
subspace produces a result in the direction of the given subspace. -/
theorem vsub_orthogonalProjection_mem_direction {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (hp₁ : p₁ ∈ s) :
    ↑((⟨p₁, hp₁⟩ : s) -ᵥ orthogonalProjection s p₂ : s.direction) ∈ s.direction :=
  ((⟨p₁, hp₁⟩ : s) -ᵥ orthogonalProjection s p₂ : s.direction).2

/-- A point equals its orthogonal projection if and only if it lies in
the subspace. -/
theorem orthogonalProjection_eq_self_iff {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} : ↑(orthogonalProjection s p) = p ↔ p ∈ s := by
  constructor
  · exact fun h => h ▸ orthogonalProjection_mem p
  · intro h
    have hp : p ∈ (s : Set P) ∩ mk' p s.directionᗮ := ⟨h, self_mem_mk' p _⟩
    rw [inter_eq_singleton_orthogonalProjection p] at hp
    symm
    exact hp

@[simp]
theorem orthogonalProjection_mem_subspace_eq_self {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : s) : orthogonalProjection s p = p := by
  ext
  rw [orthogonalProjection_eq_self_iff]
  exact p.2

/-- Orthogonal projection is idempotent. -/
theorem orthogonalProjection_orthogonalProjection (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    orthogonalProjection s (orthogonalProjection s p) = orthogonalProjection s p :=
  orthogonalProjection_mem_subspace_eq_self ((orthogonalProjection s) p)

theorem eq_orthogonalProjection_of_eq_subspace {s s' : AffineSubspace ℝ P} [Nonempty s]
    [Nonempty s'] [s.direction.HasOrthogonalProjection] [s'.direction.HasOrthogonalProjection]
    (h : s = s') (p : P) : (orthogonalProjection s p : P) = (orthogonalProjection s' p : P) := by
  subst h
  rfl

@[simp] lemma orthogonalProjection_affineSpan_singleton (p₁ p₂ : P) :
    orthogonalProjection (affineSpan ℝ {p₁}) p₂ = p₁ := by
  have h := SetLike.coe_mem (orthogonalProjection (affineSpan ℝ {p₁}) p₂)
  rwa [mem_affineSpan_singleton] at h

/-- The distance to a point's orthogonal projection is 0 iff it lies in the subspace. -/
theorem dist_orthogonalProjection_eq_zero_iff {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} :
    dist p (orthogonalProjection s p) = 0 ↔ p ∈ s := by
  rw [dist_comm, dist_eq_zero, orthogonalProjection_eq_self_iff]

/-- The distance between a point and its orthogonal projection is
nonzero if it does not lie in the subspace. -/
theorem dist_orthogonalProjection_ne_zero_of_notMem {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} (hp : p ∉ s) :
    dist p (orthogonalProjection s p) ≠ 0 :=
  mt dist_orthogonalProjection_eq_zero_iff.mp hp

@[deprecated (since := "2025-05-23")]
alias dist_orthogonalProjection_ne_zero_of_not_mem := dist_orthogonalProjection_ne_zero_of_notMem

/-- Subtracting `p` from its `orthogonalProjection` produces a result
in the orthogonal direction. -/
theorem orthogonalProjection_vsub_mem_direction_orthogonal (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    (orthogonalProjection s p : P) -ᵥ p ∈ s.directionᗮ :=
  orthogonalProjectionFn_vsub_mem_direction_orthogonal p

/-- Subtracting the `orthogonalProjection` from `p` produces a result
in the orthogonal direction. -/
theorem vsub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : p -ᵥ orthogonalProjection s p ∈ s.directionᗮ :=
  direction_mk' p s.directionᗮ ▸
    vsub_mem_direction (self_mem_mk' _ _) (orthogonalProjection_mem_orthogonal s p)

/-- Subtracting the `orthogonalProjection` from `p` produces a result in the kernel of the linear
part of the orthogonal projection. -/
theorem orthogonalProjection_vsub_orthogonalProjection (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    s.direction.orthogonalProjection (p -ᵥ orthogonalProjection s p) = 0 := by
  apply Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
  intro c hc
  rw [← neg_vsub_eq_vsub_rev, inner_neg_right,
    orthogonalProjection_vsub_mem_direction_orthogonal s p c hc, neg_zero]

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector was
in the orthogonal direction. -/
theorem orthogonalProjection_vadd_eq_self {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} (hp : p ∈ s) {v : V} (hv : v ∈ s.directionᗮ) :
    orthogonalProjection s (v +ᵥ p) = ⟨p, hp⟩ := by
  have h := vsub_orthogonalProjection_mem_direction_orthogonal s (v +ᵥ p)
  rw [vadd_vsub_assoc, Submodule.add_mem_iff_right _ hv] at h
  refine (eq_of_vsub_eq_zero ?_).symm
  ext
  refine Submodule.disjoint_def.1 s.direction.orthogonal_disjoint _ ?_ h
  exact (_ : s.direction).2

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point. -/
theorem orthogonalProjection_vadd_smul_vsub_orthogonalProjection {s : AffineSubspace ℝ P}
    [Nonempty s] [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (r : ℝ) (hp : p₁ ∈ s) :
    orthogonalProjection s (r • (p₂ -ᵥ orthogonalProjection s p₂ : V) +ᵥ p₁) = ⟨p₁, hp⟩ :=
  orthogonalProjection_vadd_eq_self hp
    (Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal s _))

/-- The square of the distance from a point in `s` to `p₂` equals the
sum of the squares of the distances of the two points to the
`orthogonalProjection`. -/
theorem dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq
    {s : AffineSubspace ℝ P} [Nonempty s] [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P)
    (hp₁ : p₁ ∈ s) :
    dist p₁ p₂ * dist p₁ p₂ =
      dist p₁ (orthogonalProjection s p₂) * dist p₁ (orthogonalProjection s p₂) +
        dist p₂ (orthogonalProjection s p₂) * dist p₂ (orthogonalProjection s p₂) := by
  rw [dist_comm p₂ _, dist_eq_norm_vsub V p₁ _, dist_eq_norm_vsub V p₁ _, dist_eq_norm_vsub V _ p₂,
    ← vsub_add_vsub_cancel p₁ (orthogonalProjection s p₂) p₂,
    norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact Submodule.inner_right_of_mem_orthogonal (vsub_orthogonalProjection_mem_direction p₂ hp₁)
    (orthogonalProjection_vsub_mem_direction_orthogonal s p₂)

/-- The distance between a point and its orthogonal projection to a subspace equals the distance
to that subspace as given by `Metric.infDist`. This is not a `simp` lemma since the simplest form
depends on the context (if any calculations are to be done with the distance, the version with
the orthogonal projection gives access to more lemmas about orthogonal projections that may be
useful). -/
lemma dist_orthogonalProjection_eq_infDist (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    dist p (orthogonalProjection s p) = Metric.infDist p s := by
  refine le_antisymm ?_ (Metric.infDist_le_dist_of_mem (orthogonalProjection_mem _))
  rw [Metric.infDist_eq_iInf]
  refine le_ciInf fun x ↦ le_of_sq_le_sq ?_ dist_nonneg
  rw [dist_comm _ (x : P)]
  simp_rw [pow_two,
    dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p x.property]
  simp [mul_self_nonneg]

/-- The nonnegative distance between a point and its orthogonal projection to a subspace equals
the distance to that subspace as given by `Metric.infNndist`. This is not a `simp` lemma since
the simplest form depends on the context (if any calculations are to be done with the distance,
the version with the orthogonal projection gives access to more lemmas about orthogonal
projections that may be useful). -/
lemma dist_orthogonalProjection_eq_infNndist (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    nndist p (orthogonalProjection s p) = Metric.infNndist p s := by
  rw [← NNReal.coe_inj]
  simp [dist_orthogonalProjection_eq_infDist]

/-- The square of the distance between two points constructed by
adding multiples of the same orthogonal vector to points in the same
subspace. -/
theorem dist_sq_smul_orthogonal_vadd_smul_orthogonal_vadd {s : AffineSubspace ℝ P} {p₁ p₂ : P}
    (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (r₁ r₂ : ℝ) {v : V} (hv : v ∈ s.directionᗮ) :
    dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) * dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) =
      dist p₁ p₂ * dist p₁ p₂ + (r₁ - r₂) * (r₁ - r₂) * (‖v‖ * ‖v‖) :=
  calc
    dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) * dist (r₁ • v +ᵥ p₁) (r₂ • v +ᵥ p₂) =
        ‖p₁ -ᵥ p₂ + (r₁ - r₂) • v‖ * ‖p₁ -ᵥ p₂ + (r₁ - r₂) • v‖ := by
      rw [dist_eq_norm_vsub V (r₁ • v +ᵥ p₁), vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, sub_smul,
        add_comm, add_sub_assoc]
    _ = ‖p₁ -ᵥ p₂‖ * ‖p₁ -ᵥ p₂‖ + ‖(r₁ - r₂) • v‖ * ‖(r₁ - r₂) • v‖ :=
      (norm_add_sq_eq_norm_sq_add_norm_sq_real
        (Submodule.inner_right_of_mem_orthogonal (vsub_mem_direction hp₁ hp₂)
          (Submodule.smul_mem _ _ hv)))
    _ = ‖(p₁ -ᵥ p₂ : V)‖ * ‖(p₁ -ᵥ p₂ : V)‖ + |r₁ - r₂| * |r₁ - r₂| * ‖v‖ * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      ring
    _ = dist p₁ p₂ * dist p₁ p₂ + (r₁ - r₂) * (r₁ - r₂) * (‖v‖ * ‖v‖) := by
      rw [dist_eq_norm_vsub V p₁, abs_mul_abs_self, mul_assoc]

/-- `p` is equidistant from two points in `s` if and only if its
`orthogonalProjection` is. -/
theorem dist_eq_iff_dist_orthogonalProjection_eq {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ p₂ : P} (p₃ : P) (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) :
    dist p₁ p₃ = dist p₂ p₃ ↔
      dist p₁ (orthogonalProjection s p₃) = dist p₂ (orthogonalProjection s p₃) := by
  rw [← mul_self_inj_of_nonneg dist_nonneg dist_nonneg, ←
    mul_self_inj_of_nonneg dist_nonneg dist_nonneg,
    dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₃ hp₁,
    dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq p₃ hp₂]
  simp

/-- `p` is equidistant from a set of points in `s` if and only if its
`orthogonalProjection` is. -/
theorem dist_set_eq_iff_dist_orthogonalProjection_eq {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {ps : Set P} (hps : ps ⊆ s) (p : P) :
    (Set.Pairwise ps fun p₁ p₂ => dist p₁ p = dist p₂ p) ↔
      Set.Pairwise ps fun p₁ p₂ =>
        dist p₁ (orthogonalProjection s p) = dist p₂ (orthogonalProjection s p) :=
  ⟨fun h _ hp₁ _ hp₂ hne =>
    (dist_eq_iff_dist_orthogonalProjection_eq p (hps hp₁) (hps hp₂)).1 (h hp₁ hp₂ hne),
    fun h _ hp₁ _ hp₂ hne =>
    (dist_eq_iff_dist_orthogonalProjection_eq p (hps hp₁) (hps hp₂)).2 (h hp₁ hp₂ hne)⟩

/-- There exists `r` such that `p` has distance `r` from all the
points of a set of points in `s` if and only if there exists (possibly
different) `r` such that its `orthogonalProjection` has that distance
from all the points in that set. -/
theorem exists_dist_eq_iff_exists_dist_orthogonalProjection_eq {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {ps : Set P} (hps : ps ⊆ s) (p : P) :
    (∃ r, ∀ p₁ ∈ ps, dist p₁ p = r) ↔ ∃ r, ∀ p₁ ∈ ps, dist p₁ ↑(orthogonalProjection s p) = r := by
  have h := dist_set_eq_iff_dist_orthogonalProjection_eq hps p
  simp_rw [Set.pairwise_eq_iff_exists_eq] at h
  exact h

/-- Reflection in an affine subspace, which is expected to be nonempty
and complete. The word "reflection" is sometimes understood to mean
specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point. The
definition here, of reflection in an affine subspace, is a more
general sense of the word that includes both those common cases. -/
def reflection (s : AffineSubspace ℝ P) [Nonempty s] [s.direction.HasOrthogonalProjection] :
    P ≃ᵃⁱ[ℝ] P :=
  AffineIsometryEquiv.mk'
    (fun p => (↑(orthogonalProjection s p) -ᵥ p) +ᵥ (orthogonalProjection s p : P))
    s.direction.reflection (↑(Classical.arbitrary s))
    (by
      intro p
      let v := p -ᵥ ↑(Classical.arbitrary s)
      let a : V := s.direction.orthogonalProjection v
      let b : P := ↑(Classical.arbitrary s)
      have key : ((a +ᵥ b) -ᵥ (v +ᵥ b)) +ᵥ (a +ᵥ b) = (a + a - v) +ᵥ (b -ᵥ b) +ᵥ b := by
        rw [← add_vadd, vsub_vadd_eq_vsub_sub, vsub_vadd, vadd_vsub]
        congr 1
        abel
      dsimp only
      rwa [Submodule.reflection_apply, (vsub_vadd p b).symm, ContinuousAffineMap.map_vadd,
        orthogonalProjection_contLinear, vadd_vsub, orthogonalProjection_mem_subspace_eq_self,
        two_smul])

/-- The result of reflecting. -/
theorem reflection_apply (s : AffineSubspace ℝ P) [Nonempty s] [s.direction.HasOrthogonalProjection]
    (p : P) :
    reflection s p = (↑(orthogonalProjection s p) -ᵥ p) +ᵥ (orthogonalProjection s p : P) :=
  rfl

theorem eq_reflection_of_eq_subspace {s s' : AffineSubspace ℝ P} [Nonempty s] [Nonempty s']
    [s.direction.HasOrthogonalProjection] [s'.direction.HasOrthogonalProjection] (h : s = s')
    (p : P) : (reflection s p : P) = (reflection s' p : P) := by
  subst h
  rfl

/-- Reflecting twice in the same subspace. -/
@[simp]
theorem reflection_reflection (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : reflection s (reflection s p) = p := by
  have : ∀ a : s, ∀ b : V, s.direction.orthogonalProjection b = 0 →
      reflection s (reflection s (b +ᵥ (a : P))) = b +ᵥ (a : P) := by
    intro _ _ h
    simp [reflection]
  rw [← vsub_vadd p (orthogonalProjection s p)]
  exact this (orthogonalProjection s p) _ (orthogonalProjection_vsub_orthogonalProjection s p)

/-- Reflection is its own inverse. -/
@[simp]
theorem reflection_symm (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] : (reflection s).symm = reflection s := by
  ext
  rw [← (reflection s).injective.eq_iff]
  simp

/-- Reflection is involutive. -/
theorem reflection_involutive (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] : Function.Involutive (reflection s) :=
  reflection_reflection s

/-- A point is its own reflection if and only if it is in the subspace. -/
theorem reflection_eq_self_iff {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : reflection s p = p ↔ p ∈ s := by
  rw [← orthogonalProjection_eq_self_iff, reflection_apply]
  constructor
  · intro h
    rw [← @vsub_eq_zero_iff_eq V, vadd_vsub_assoc, ← two_smul ℝ (↑(orthogonalProjection s p) -ᵥ p),
      smul_eq_zero] at h
    norm_num at h
    exact h
  · intro h
    simp [h]

/-- Reflecting a point in two subspaces produces the same result if
and only if the point has the same orthogonal projection in each of
those subspaces. -/
theorem reflection_eq_iff_orthogonalProjection_eq (s₁ s₂ : AffineSubspace ℝ P) [Nonempty s₁]
    [Nonempty s₂] [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (p : P) :
    reflection s₁ p = reflection s₂ p ↔
      (orthogonalProjection s₁ p : P) = orthogonalProjection s₂ p := by
  rw [reflection_apply, reflection_apply]
  constructor
  · intro h
    rw [← @vsub_eq_zero_iff_eq V, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm, add_sub_assoc,
      vsub_sub_vsub_cancel_right, ←
      two_smul ℝ ((orthogonalProjection s₁ p : P) -ᵥ orthogonalProjection s₂ p), smul_eq_zero] at h
    norm_num at h
    exact h
  · intro h
    rw [h]

/-- The distance between `p₁` and the reflection of `p₂` equals that
between the reflection of `p₁` and `p₂`. -/
theorem dist_reflection (s : AffineSubspace ℝ P) [Nonempty s] [s.direction.HasOrthogonalProjection]
    (p₁ p₂ : P) : dist p₁ (reflection s p₂) = dist (reflection s p₁) p₂ := by
  conv_lhs => rw [← reflection_reflection s p₁]
  exact (reflection s).dist_map _ _

/-- A point in the subspace is equidistant from another point and its
reflection. -/
theorem dist_reflection_eq_of_mem (s : AffineSubspace ℝ P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (hp₁ : p₁ ∈ s) (p₂ : P) :
    dist p₁ (reflection s p₂) = dist p₁ p₂ := by
  rw [← reflection_eq_self_iff p₁] at hp₁
  convert (reflection s).dist_map p₁ p₂
  rw [hp₁]

/-- The reflection of a point in a subspace is contained in any larger
subspace containing both the point and the subspace reflected in. -/
theorem reflection_mem_of_le_of_mem {s₁ s₂ : AffineSubspace ℝ P} [Nonempty s₁]
    [s₁.direction.HasOrthogonalProjection] (hle : s₁ ≤ s₂) {p : P} (hp : p ∈ s₂) :
    reflection s₁ p ∈ s₂ := by
  rw [reflection_apply]
  have ho : ↑(orthogonalProjection s₁ p) ∈ s₂ := hle (orthogonalProjection_mem p)
  exact vadd_mem_of_mem_direction (vsub_mem_direction ho hp) ho

/-- Reflecting an orthogonal vector plus a point in the subspace
produces the negation of that vector plus the point. -/
theorem reflection_orthogonal_vadd {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} (hp : p ∈ s) {v : V} (hv : v ∈ s.directionᗮ) :
    reflection s (v +ᵥ p) = -v +ᵥ p := by
  rw [reflection_apply, orthogonalProjection_vadd_eq_self hp hv, vsub_vadd_eq_vsub_sub]
  simp

/-- Reflecting a vector plus a point in the subspace produces the
negation of that vector plus the point if the vector is a multiple of
the result of subtracting a point's orthogonal projection from that
point. -/
theorem reflection_vadd_smul_vsub_orthogonalProjection {s : AffineSubspace ℝ P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (r : ℝ) (hp₁ : p₁ ∈ s) :
    reflection s (r • (p₂ -ᵥ orthogonalProjection s p₂) +ᵥ p₁) =
      -(r • (p₂ -ᵥ orthogonalProjection s p₂)) +ᵥ p₁ :=
  reflection_orthogonal_vadd hp₁
    (Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal s _))

end EuclideanGeometry

namespace Affine

namespace Simplex

open EuclideanGeometry

variable {V : Type*} {P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

/-- The orthogonal projection of a point `p` onto the hyperplane spanned by the simplex's points. -/
def orthogonalProjectionSpan {n : ℕ} (s : Simplex ℝ P n) :
    P →ᴬ[ℝ] affineSpan ℝ (Set.range s) :=
  orthogonalProjection (affineSpan ℝ (Set.range s))

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point. -/
theorem orthogonalProjection_vadd_smul_vsub_orthogonalProjection {n : ℕ} (s : Simplex ℝ P n)
    {p₁ : P} (p₂ : P) (r : ℝ) (hp : p₁ ∈ affineSpan ℝ (Set.range s)) :
    s.orthogonalProjectionSpan (r • (p₂ -ᵥ s.orthogonalProjectionSpan p₂ : V) +ᵥ p₁) = ⟨p₁, hp⟩ :=
  EuclideanGeometry.orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ _

theorem coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection {n : ℕ} {r₁ : ℝ}
    (s : Simplex ℝ P n) {p p₁o : P} (hp₁o : p₁o ∈ affineSpan ℝ (Set.range s)) :
    ↑(s.orthogonalProjectionSpan (r₁ • (p -ᵥ ↑(s.orthogonalProjectionSpan p)) +ᵥ p₁o)) = p₁o :=
  congrArg ((↑) : _ → P) (orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ _ hp₁o)

theorem dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq {n : ℕ}
    (s : Simplex ℝ P n) {p₁ : P} (p₂ : P) (hp₁ : p₁ ∈ affineSpan ℝ (Set.range s)) :
    dist p₁ p₂ * dist p₁ p₂ =
      dist p₁ (s.orthogonalProjectionSpan p₂) * dist p₁ (s.orthogonalProjectionSpan p₂) +
        dist p₂ (s.orthogonalProjectionSpan p₂) * dist p₂ (s.orthogonalProjectionSpan p₂) := by
  rw [PseudoMetricSpace.dist_comm p₂ _, dist_eq_norm_vsub V p₁ _, dist_eq_norm_vsub V p₁ _,
    dist_eq_norm_vsub V _ p₂, ← vsub_add_vsub_cancel p₁ (s.orthogonalProjectionSpan p₂) p₂,
    norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact
    Submodule.inner_right_of_mem_orthogonal (vsub_orthogonalProjection_mem_direction p₂ hp₁)
      (orthogonalProjection_vsub_mem_direction_orthogonal _ p₂)

@[simp]
lemma orthogonalProjectionSpan_eq_point (s : Simplex ℝ P 0) (p : P) :
    s.orthogonalProjectionSpan p = s 0 := by
  rw [orthogonalProjectionSpan]
  convert orthogonalProjection_affineSpan_singleton _ _
  simp [Fin.fin_one_eq_zero]

lemma orthogonalProjectionSpan_faceOpposite_eq_point_rev (s : Simplex ℝ P 1) (i : Fin 2)
    (p : P) : (s.faceOpposite i).orthogonalProjectionSpan p = s i.rev := by
  simp [faceOpposite_point_eq_point_rev]

end Simplex

end Affine
