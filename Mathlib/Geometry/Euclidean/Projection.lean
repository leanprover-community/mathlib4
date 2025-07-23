/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Manuel Candales
-/

import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Normed.Affine.ContinuousAffineMap
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Orthogonal projection in affine spaces

This file defines orthogonal projection onto an affine subspace,
and reflection of a point in an affine subspace.

## Main definitions

* `EuclideanGeometry.orthogonalProjection` is the orthogonal
  projection of a point onto an affine subspace.

* `EuclideanGeometry.reflection` is the reflection of a point in an
  affine subspace.

-/

noncomputable section

namespace EuclideanGeometry

variable {𝕜 : Type*} {V : Type*} {P : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]

open AffineSubspace

section PseudoMetricSpace

variable [PseudoMetricSpace P] [NormedAddTorsor V P]

/-- The orthogonal projection of a point onto a nonempty affine subspace. -/
def orthogonalProjection (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] : P →ᴬ[𝕜] s :=
  letI x := Classical.arbitrary s
  AffineIsometryEquiv.vaddConst 𝕜 x
    |>.toContinuousAffineEquiv.toContinuousAffineMap.comp
      s.direction.orthogonalProjection.toContinuousAffineMap
    |>.comp <| AffineIsometryEquiv.vaddConst 𝕜 (x : P) |>.symm

theorem orthogonalProjection_apply (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p} :
    orthogonalProjection s p = s.direction.orthogonalProjection (p -ᵥ Classical.arbitrary s)
      +ᵥ Classical.arbitrary s :=
  rfl

theorem orthogonalProjection_apply' (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p} :
    (orthogonalProjection s p : P) =
      (s.direction.orthogonalProjection (p -ᵥ Classical.arbitrary s) : V) +ᵥ
      (Classical.arbitrary s : P) :=
  rfl

theorem orthogonalProjection_apply_mem (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p x} (hx : x ∈ s) :
    orthogonalProjection s p = (s.direction.orthogonalProjection (p -ᵥ x) : V) +ᵥ x := by
  rw [orthogonalProjection_apply, coe_vadd, vadd_eq_vadd_iff_sub_eq_vsub, ← Submodule.coe_sub,
    ← map_sub, vsub_sub_vsub_cancel_left, Submodule.coe_orthogonalProjection_apply,
    Submodule.starProjection_eq_self_iff]
  exact s.vsub_mem_direction (SetLike.coe_mem _) hx

/-- Since both instance arguments are propositions, allow `simp` to rewrite them
alongside the `s` argument.

Note that without the coercion to `P`, the LHS and RHS would have different types. -/
@[congr]
theorem orthogonalProjection_congr {s₁ s₂ : AffineSubspace 𝕜 P} {p₁ p₂ : P}
    [Nonempty s₁] [s₁.direction.HasOrthogonalProjection]
    (h : s₁ = s₂) (hp : p₁ = p₂) :
    letI : Nonempty s₂ := h ▸ ‹_›
    letI : s₂.direction.HasOrthogonalProjection := h ▸ ‹_›
    (orthogonalProjection s₁ p₁ : P) = (orthogonalProjection s₂ p₂ : P) := by
  subst h hp
  rfl

/-- The linear map corresponding to `orthogonalProjection`. -/
@[simp]
theorem orthogonalProjection_linear {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] :
    (orthogonalProjection s).linear = s.direction.orthogonalProjection :=
  rfl

/-- The continuous linear map corresponding to `orthogonalProjection`. -/
@[simp]
theorem orthogonalProjection_contLinear {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] :
    (orthogonalProjection s).contLinear = s.direction.orthogonalProjection :=
  rfl

/-- The `orthogonalProjection` lies in the given subspace. -/
theorem orthogonalProjection_mem {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : ↑(orthogonalProjection s p) ∈ s :=
  (orthogonalProjection s p).2

/-- The `orthogonalProjection` lies in the orthogonal subspace. -/
theorem orthogonalProjection_mem_orthogonal (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    ↑(orthogonalProjection s p) ∈ mk' p s.directionᗮ := by
  rw [mem_mk', orthogonalProjection_apply, coe_vadd, vadd_vsub_eq_sub_vsub,
    ← Submodule.neg_mem_iff, neg_sub]
  apply Submodule.sub_starProjection_mem_orthogonal

/-- The intersection of the subspace and the orthogonal subspace
through the given point is the `orthogonalProjection` of that point
onto the subspace. -/
theorem inter_eq_singleton_orthogonalProjection {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    (s : Set P) ∩ mk' p s.directionᗮ = {↑(orthogonalProjection s p)} := by
  obtain ⟨q, hq⟩ := inter_eq_singleton_of_nonempty_of_isCompl (nonempty_subtype.mp ‹_›)
    (mk'_nonempty p s.directionᗮ)
    (by
      rw [direction_mk' p s.directionᗮ]
      exact Submodule.isCompl_orthogonal_of_completeSpace)
  rwa [Set.eq_singleton_iff_nonempty_unique_mem.1 hq |>.2 _
    ⟨orthogonalProjection_mem _, orthogonalProjection_mem_orthogonal _ _⟩]

/-- Subtracting a point in the given subspace from the
`orthogonalProjection` produces a result in the direction of the
given subspace. -/
theorem orthogonalProjection_vsub_mem_direction {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (hp₁ : p₁ ∈ s) :
    ↑(orthogonalProjection s p₂ -ᵥ ⟨p₁, hp₁⟩ : s.direction) ∈ s.direction :=
  (orthogonalProjection s p₂ -ᵥ ⟨p₁, hp₁⟩ : s.direction).2

/-- Subtracting the `orthogonalProjection` from a point in the given
subspace produces a result in the direction of the given subspace. -/
theorem vsub_orthogonalProjection_mem_direction {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (hp₁ : p₁ ∈ s) :
    ↑((⟨p₁, hp₁⟩ : s) -ᵥ orthogonalProjection s p₂ : s.direction) ∈ s.direction :=
  ((⟨p₁, hp₁⟩ : s) -ᵥ orthogonalProjection s p₂ : s.direction).2

/-- A point equals its orthogonal projection if and only if it lies in
the subspace. -/
theorem orthogonalProjection_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} : ↑(orthogonalProjection s p) = p ↔ p ∈ s := by
  constructor
  · exact fun h => h ▸ orthogonalProjection_mem p
  · intro h
    have hp : p ∈ (s : Set P) ∩ mk' p s.directionᗮ := ⟨h, self_mem_mk' p _⟩
    rw [inter_eq_singleton_orthogonalProjection p] at hp
    symm
    exact hp

@[simp]
theorem orthogonalProjection_mem_subspace_eq_self {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : s) : orthogonalProjection s p = p := by
  ext
  rw [orthogonalProjection_eq_self_iff]
  exact p.2

/-- Orthogonal projection is idempotent. -/
theorem orthogonalProjection_orthogonalProjection (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    orthogonalProjection s (orthogonalProjection s p) = orthogonalProjection s p := by
  ext
  rw [orthogonalProjection_eq_self_iff]
  exact orthogonalProjection_mem p

theorem eq_orthogonalProjection_of_eq_subspace {s s' : AffineSubspace 𝕜 P} [Nonempty s]
    [Nonempty s'] [s.direction.HasOrthogonalProjection] [s'.direction.HasOrthogonalProjection]
    (h : s = s') (p : P) : (orthogonalProjection s p : P) = (orthogonalProjection s' p : P) := by
  subst h
  rfl

@[simp] lemma orthogonalProjection_affineSpan_singleton (p₁ p₂ : P) :
    orthogonalProjection (affineSpan 𝕜 {p₁}) p₂ = p₁ := by
  have h := SetLike.coe_mem (orthogonalProjection (affineSpan 𝕜 {p₁}) p₂)
  rwa [mem_affineSpan_singleton] at h

/-- Subtracting `p` from its `orthogonalProjection` produces a result
in the orthogonal direction. -/
theorem orthogonalProjection_vsub_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    (orthogonalProjection s p : P) -ᵥ p ∈ s.directionᗮ := by
  rw [← mem_mk']
  apply orthogonalProjection_mem_orthogonal

/-- Subtracting the `orthogonalProjection` from `p` produces a result
in the orthogonal direction. -/
theorem vsub_orthogonalProjection_mem_direction_orthogonal (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : p -ᵥ orthogonalProjection s p ∈ s.directionᗮ :=
  direction_mk' p s.directionᗮ ▸
    vsub_mem_direction (self_mem_mk' _ _) (orthogonalProjection_mem_orthogonal s p)

/-- Subtracting the `orthogonalProjection` from `p` produces a result in the kernel of the linear
part of the orthogonal projection. -/
theorem orthogonalProjection_vsub_orthogonalProjection (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    s.direction.orthogonalProjection (p -ᵥ orthogonalProjection s p) = 0 := by
  apply Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero
  intro c hc
  rw [← neg_vsub_eq_vsub_rev, inner_neg_right,
    orthogonalProjection_vsub_mem_direction_orthogonal s p c hc, neg_zero]

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector was
in the orthogonal direction. -/
theorem orthogonalProjection_vadd_eq_self {s : AffineSubspace 𝕜 P} [Nonempty s]
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
theorem orthogonalProjection_vadd_smul_vsub_orthogonalProjection {s : AffineSubspace 𝕜 P}
    [Nonempty s] [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (r : 𝕜) (hp : p₁ ∈ s) :
    orthogonalProjection s (r • (p₂ -ᵥ orthogonalProjection s p₂ : V) +ᵥ p₁) = ⟨p₁, hp⟩ :=
  orthogonalProjection_vadd_eq_self hp
    (Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal s _))

/-- Reflection in an affine subspace, which is expected to be nonempty
and complete. The word "reflection" is sometimes understood to mean
specifically reflection in a codimension-one subspace, and sometimes
more generally to cover operations such as reflection in a point. The
definition here, of reflection in an affine subspace, is a more
general sense of the word that includes both those common cases. -/
def reflection (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection] :
    P ≃ᵃⁱ[𝕜] P :=
  letI x : P := Classical.arbitrary s
  AffineIsometryEquiv.vaddConst 𝕜 x
    |>.symm.trans s.direction.reflection.toAffineIsometryEquiv
    |>.trans <| AffineIsometryEquiv.vaddConst 𝕜 x

theorem reflection_apply (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection]
    (p : P) :
    reflection s p = s.direction.reflection (p -ᵥ Classical.arbitrary s)
      +ᵥ (Classical.arbitrary s : P) :=
  rfl

theorem reflection_apply_of_mem (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) {x} (hx : x ∈ s) :
    reflection s p = s.direction.reflection (p -ᵥ x) +ᵥ x := by
  rw [reflection_apply, vadd_eq_vadd_iff_sub_eq_vsub, ← map_sub,
    vsub_sub_vsub_cancel_left, s.direction.reflection_eq_self_iff]
  exact s.vsub_mem_direction (SetLike.coe_mem _) hx

theorem reflection_apply' (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) :
    reflection s p = (↑(orthogonalProjection s p) -ᵥ p) +ᵥ (orthogonalProjection s p : P) := by
  rw [reflection_apply, orthogonalProjection_apply', Submodule.coe_orthogonalProjection_apply]
  set x : P := ↑(Classical.arbitrary s)
  set v : V := s.direction.starProjection (p -ᵥ x)
  rw [Submodule.reflection_apply, two_smul, sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_assoc,
    add_comm v, add_vadd, vadd_vsub_assoc]

theorem eq_reflection_of_eq_subspace {s s' : AffineSubspace 𝕜 P} [Nonempty s] [Nonempty s']
    [s.direction.HasOrthogonalProjection] [s'.direction.HasOrthogonalProjection] (h : s = s')
    (p : P) : (reflection s p : P) = (reflection s' p : P) := by
  subst h
  rfl

/-- Reflecting twice in the same subspace. -/
@[simp]
theorem reflection_reflection (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : reflection s (reflection s p) = p := by
  simp [reflection, -AffineIsometryEquiv.map_vadd]

/-- Reflection is its own inverse. -/
@[simp]
theorem reflection_symm (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] : (reflection s).symm = reflection s := by
  ext
  rw [← (reflection s).injective.eq_iff]
  simp

/-- Reflection is involutive. -/
theorem reflection_involutive (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] : Function.Involutive (reflection s) :=
  reflection_reflection s

/-- A point is its own reflection if and only if it is in the subspace. -/
theorem reflection_eq_self_iff {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] (p : P) : reflection s p = p ↔ p ∈ s := by
  rw [reflection_apply, Eq.comm, eq_vadd_iff_vsub_eq, Eq.comm, s.direction.reflection_eq_self_iff,
    s.mem_direction_iff_eq_vsub_right (SetLike.coe_mem (Classical.arbitrary s))]
  simp

/-- Reflecting a point in two subspaces produces the same result if
and only if the point has the same orthogonal projection in each of
those subspaces. -/
theorem reflection_eq_iff_orthogonalProjection_eq (s₁ s₂ : AffineSubspace 𝕜 P) [Nonempty s₁]
    [Nonempty s₂] [s₁.direction.HasOrthogonalProjection] [s₂.direction.HasOrthogonalProjection]
    (p : P) :
    reflection s₁ p = reflection s₂ p ↔
      (orthogonalProjection s₁ p : P) = orthogonalProjection s₂ p := by
  rw [reflection_apply', reflection_apply']
  constructor
  · intro h
    rw [← @vsub_eq_zero_iff_eq V, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_comm, add_sub_assoc,
      vsub_sub_vsub_cancel_right, ←
      two_smul 𝕜 ((orthogonalProjection s₁ p : P) -ᵥ orthogonalProjection s₂ p), smul_eq_zero] at h
    norm_num at h
    exact h
  · intro h
    rw [h]

/-- The distance between `p₁` and the reflection of `p₂` equals that
between the reflection of `p₁` and `p₂`. -/
theorem dist_reflection (s : AffineSubspace 𝕜 P) [Nonempty s] [s.direction.HasOrthogonalProjection]
    (p₁ p₂ : P) : dist p₁ (reflection s p₂) = dist (reflection s p₁) p₂ := by
  conv_lhs => rw [← reflection_reflection s p₁]
  exact (reflection s).dist_map _ _

/-- A point in the subspace is equidistant from another point and its
reflection. -/
theorem dist_reflection_eq_of_mem (s : AffineSubspace 𝕜 P) [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (hp₁ : p₁ ∈ s) (p₂ : P) :
    dist p₁ (reflection s p₂) = dist p₁ p₂ := by
  rw [← reflection_eq_self_iff p₁] at hp₁
  convert (reflection s).dist_map p₁ p₂
  rw [hp₁]

/-- The reflection of a point in a subspace is contained in any larger
subspace containing both the point and the subspace reflected in. -/
theorem reflection_mem_of_le_of_mem {s₁ s₂ : AffineSubspace 𝕜 P} [Nonempty s₁]
    [s₁.direction.HasOrthogonalProjection] (hle : s₁ ≤ s₂) {p : P} (hp : p ∈ s₂) :
    reflection s₁ p ∈ s₂ := by
  rw [reflection_apply']
  have ho : ↑(orthogonalProjection s₁ p) ∈ s₂ := hle (orthogonalProjection_mem p)
  exact vadd_mem_of_mem_direction (vsub_mem_direction ho hp) ho

/-- Reflecting an orthogonal vector plus a point in the subspace
produces the negation of that vector plus the point. -/
theorem reflection_orthogonal_vadd {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} (hp : p ∈ s) {v : V} (hv : v ∈ s.directionᗮ) :
    reflection s (v +ᵥ p) = -v +ᵥ p := by
  rw [reflection_apply', orthogonalProjection_vadd_eq_self hp hv, vsub_vadd_eq_vsub_sub]
  simp

/-- Reflecting a vector plus a point in the subspace produces the
negation of that vector plus the point if the vector is a multiple of
the result of subtracting a point's orthogonal projection from that
point. -/
theorem reflection_vadd_smul_vsub_orthogonalProjection {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p₁ : P} (p₂ : P) (r : 𝕜) (hp₁ : p₁ ∈ s) :
    reflection s (r • (p₂ -ᵥ orthogonalProjection s p₂) +ᵥ p₁) =
      -(r • (p₂ -ᵥ orthogonalProjection s p₂)) +ᵥ p₁ :=
  reflection_orthogonal_vadd hp₁
    (Submodule.smul_mem _ _ (vsub_orthogonalProjection_mem_direction_orthogonal s _))

end PseudoMetricSpace

section MetricSpace

variable [MetricSpace P] [NormedAddTorsor V P]

/-- The distance to a point's orthogonal projection is 0 iff it lies in the subspace. -/
theorem dist_orthogonalProjection_eq_zero_iff {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} :
    dist p (orthogonalProjection s p) = 0 ↔ p ∈ s := by
  rw [dist_comm, dist_eq_zero, orthogonalProjection_eq_self_iff]

/-- The distance between a point and its orthogonal projection is
nonzero if it does not lie in the subspace. -/
theorem dist_orthogonalProjection_ne_zero_of_notMem {s : AffineSubspace 𝕜 P} [Nonempty s]
    [s.direction.HasOrthogonalProjection] {p : P} (hp : p ∉ s) :
    dist p (orthogonalProjection s p) ≠ 0 :=
  mt dist_orthogonalProjection_eq_zero_iff.mp hp

@[deprecated (since := "2025-05-23")]
alias dist_orthogonalProjection_ne_zero_of_not_mem := dist_orthogonalProjection_ne_zero_of_notMem

end MetricSpace

section Real

variable [InnerProductSpace ℝ V] [PseudoMetricSpace P] [NormedAddTorsor V P]

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

end Real

end EuclideanGeometry

namespace Affine

namespace Simplex

open EuclideanGeometry

variable {𝕜 : Type*} {V : Type*} {P : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [PseudoMetricSpace P]
variable [NormedAddTorsor V P]

/-- The orthogonal projection of a point `p` onto the hyperplane spanned by the simplex's points. -/
def orthogonalProjectionSpan {n : ℕ} (s : Simplex 𝕜 P n) :
    P →ᴬ[𝕜] affineSpan 𝕜 (Set.range s.points) :=
  orthogonalProjection (affineSpan 𝕜 (Set.range s.points))

/-- Adding a vector to a point in the given subspace, then taking the
orthogonal projection, produces the original point if the vector is a
multiple of the result of subtracting a point's orthogonal projection
from that point. -/
theorem orthogonalProjection_vadd_smul_vsub_orthogonalProjection {n : ℕ} (s : Simplex 𝕜 P n)
    {p₁ : P} (p₂ : P) (r : 𝕜) (hp : p₁ ∈ affineSpan 𝕜 (Set.range s.points)) :
    s.orthogonalProjectionSpan (r • (p₂ -ᵥ s.orthogonalProjectionSpan p₂ : V) +ᵥ p₁) = ⟨p₁, hp⟩ :=
  EuclideanGeometry.orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ _

theorem coe_orthogonalProjection_vadd_smul_vsub_orthogonalProjection {n : ℕ} {r₁ : 𝕜}
    (s : Simplex 𝕜 P n) {p p₁o : P} (hp₁o : p₁o ∈ affineSpan 𝕜 (Set.range s.points)) :
    ↑(s.orthogonalProjectionSpan (r₁ • (p -ᵥ ↑(s.orthogonalProjectionSpan p)) +ᵥ p₁o)) = p₁o :=
  congrArg ((↑) : _ → P) (orthogonalProjection_vadd_smul_vsub_orthogonalProjection _ _ _ hp₁o)

@[simp]
lemma orthogonalProjectionSpan_eq_point (s : Simplex 𝕜 P 0) (p : P) :
    s.orthogonalProjectionSpan p = s.points 0 := by
  rw [orthogonalProjectionSpan]
  convert orthogonalProjection_affineSpan_singleton _ _
  simp [Fin.fin_one_eq_zero]

lemma orthogonalProjectionSpan_faceOpposite_eq_point_rev (s : Simplex 𝕜 P 1) (i : Fin 2)
    (p : P) : (s.faceOpposite i).orthogonalProjectionSpan p = s.points i.rev := by
  simp [faceOpposite_point_eq_point_rev]

variable [InnerProductSpace ℝ V]

theorem dist_sq_eq_dist_orthogonalProjection_sq_add_dist_orthogonalProjection_sq {n : ℕ}
    (s : Simplex ℝ P n) {p₁ : P} (p₂ : P) (hp₁ : p₁ ∈ affineSpan ℝ (Set.range s.points)) :
    dist p₁ p₂ * dist p₁ p₂ =
      dist p₁ (s.orthogonalProjectionSpan p₂) * dist p₁ (s.orthogonalProjectionSpan p₂) +
        dist p₂ (s.orthogonalProjectionSpan p₂) * dist p₂ (s.orthogonalProjectionSpan p₂) := by
  rw [dist_comm p₂ _, dist_eq_norm_vsub V p₁ _, dist_eq_norm_vsub V p₁ _,
    dist_eq_norm_vsub V _ p₂, ← vsub_add_vsub_cancel p₁ (s.orthogonalProjectionSpan p₂) p₂,
    norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero]
  exact
    Submodule.inner_right_of_mem_orthogonal (vsub_orthogonalProjection_mem_direction p₂ hp₁)
      (orthogonalProjection_vsub_mem_direction_orthogonal _ p₂)

end Simplex

end Affine
