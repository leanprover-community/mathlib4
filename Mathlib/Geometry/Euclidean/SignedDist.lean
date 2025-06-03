/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.LinearAlgebra.AffineSpace.ContinuousAffineEquiv
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Topology.Algebra.AffineSubspace

/-!
# Signed distance to an affine subspace in a Euclidean space.

This file defines the signed distance between an affine subspace and a point, in the direction
of a given reference point.

## Main definitions

* `AffineSubspace.signedInfDist` is the signed distance between an affine subspace and a point.
* `Affine.Simplex.signedInfDist` is the signed distance between a face of a simplex and a point.
  In the case of a triangle, these distances are trilinear coordinates.

## References

* https://en.wikipedia.org/wiki/Trilinear_coordinates

-/


open EuclideanGeometry
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

namespace AffineSubspace

variable (s : AffineSubspace ℝ P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p : P)

/-- The signed distance between `s` and a point, in the direction of the reference point `p`.
This is expected to be used when `p` does not lie in `s` (in the degenerate case where `p` lies
in `s`, this yields 0) and when the point at which the distance is evaluated lies in the affine
span of `s` and `p` (any component of the distance orthogonal to that span is disregarded). -/
noncomputable def signedInfDist : P →ᴬ[ℝ] ℝ :=
  (innerSL ℝ (‖p -ᵥ orthogonalProjection s p‖⁻¹ •
      (p -ᵥ orthogonalProjection s p))).toContinuousAffineMap.comp
    ((ContinuousAffineEquiv.refl ℝ P).toContinuousAffineMap -ᵥ
      s.subtypeA.comp (orthogonalProjection s))

lemma signedInfDist_apply (x : P) :
    s.signedInfDist p x = ⟪‖p -ᵥ orthogonalProjection s p‖⁻¹ • (p -ᵥ orthogonalProjection s p),
      x -ᵥ orthogonalProjection s x⟫ :=
  rfl

lemma signedInfDist_linear : (s.signedInfDist p).linear =
    (innerₗ V (‖p -ᵥ orthogonalProjection s p‖⁻¹ • (p -ᵥ orthogonalProjection s p))).comp
      (LinearMap.id (R := ℝ) (M := V) -
        s.direction.subtype.comp s.direction.orthogonalProjection.toLinearMap) :=
  rfl

lemma signedInfDist_linear_apply (v : V) : (s.signedInfDist p).linear v =
    ⟪‖p -ᵥ orthogonalProjection s p‖⁻¹ • (p -ᵥ orthogonalProjection s p),
     v - s.direction.orthogonalProjection v⟫ :=
  rfl

@[simp] lemma signedInfDist_apply_self : s.signedInfDist p p = ‖p -ᵥ orthogonalProjection s p‖ := by
  simp [signedInfDist_apply, inner_smul_left, real_inner_self_eq_norm_sq, pow_two, ← mul_assoc]

variable {s} in
@[simp] lemma signedInfDist_apply_of_mem {x : P} (hx : x ∈ s) : s.signedInfDist p x = 0 := by
  simp [signedInfDist_apply, orthogonalProjection_eq_self_iff.2 hx]

variable {s p} in
@[simp] lemma signedInfDist_eq_const_of_mem (h : p ∈ s) :
    s.signedInfDist p = AffineMap.const ℝ P (0 : ℝ) := by
  ext x
  simp [signedInfDist_apply, orthogonalProjection_eq_self_iff.2 h]

variable {s p} in
lemma abs_signedInfDist_eq_dist_of_mem_affineSpan_insert {x : P}
    (h : x ∈ affineSpan ℝ (insert p s)) :
    |s.signedInfDist p x| = dist x (orthogonalProjection s x) := by
  rw [mem_affineSpan_insert_iff (orthogonalProjection s p).property] at h
  rcases h with ⟨r, p₀, hp₀, rfl⟩
  simp [hp₀, dist_eq_norm_vsub, vsub_vadd_eq_vsub_sub, orthogonalProjection_eq_self_iff.2 hp₀,
    orthogonalProjection_vsub_orthogonalProjection, norm_smul, abs_mul]

end AffineSubspace

namespace Affine

namespace Simplex

variable {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1))

/-- The signed distance between the face of `s` excluding point `i` of that simplex and a point,
in the direction of the reference point `i`. This is expected to be used when the point at which
the distance is evaluated lies in the affine span of the simplex (any component of the distance
orthogonal to that span is disregarded). In the case of a triangle, these distances are
trilinear coordinates; in a tetrahedron, they are quadriplanar coordinates. -/
noncomputable def signedInfDist : P →ᴬ[ℝ] ℝ :=
  AffineSubspace.signedInfDist (affineSpan ℝ (s.points '' {i}ᶜ)) (s.points i)

lemma signedInfDist_apply_self :
    s.signedInfDist i (s.points i) =
      ‖s.points i -ᵥ (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖ :=
  (AffineSubspace.signedInfDist_apply_self _ _).trans <| by simp [orthogonalProjectionSpan]

variable {i} in
lemma signedInfDist_apply_of_ne {j : Fin (n + 1)} (h : j ≠ i) :
    s.signedInfDist i (s.points j) = 0 :=
  AffineSubspace.signedInfDist_apply_of_mem _ (s.mem_affineSpan_image_iff.2 h)

lemma signedInfDist_affineCombination {w : Fin (n + 1) → ℝ} (h : ∑ i, w i = 1) :
    s.signedInfDist i (Finset.univ.affineCombination ℝ s.points w) = w i * ‖s.points i -ᵥ
      (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖ := by
  rw [← ContinuousAffineMap.coe_toAffineMap, Finset.map_affineCombination _ _ _ h,
    Finset.univ.affineCombination_apply_eq_lineMap_sum w
      ((s.signedInfDist i).toAffineMap ∘ s.points) 0
      ‖s.points i -ᵥ (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖
      {i} h]
  · simp [AffineMap.lineMap_apply]
  · simp [signedInfDist_apply_self]
  · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and,
      Function.comp_apply]
    intro j hj
    exact s.signedInfDist_apply_of_ne hj

variable {s} in
lemma abs_signedInfDist_eq_dist_of_mem_affineSpan_range {p : P}
    (h : p ∈ affineSpan ℝ (Set.range s.points)) :
    |s.signedInfDist i p| =
      dist p ((s.faceOpposite i).orthogonalProjectionSpan p) := by
  rw [signedInfDist, AffineSubspace.abs_signedInfDist_eq_dist_of_mem_affineSpan_insert,
    orthogonalProjectionSpan]
  · simp_rw [range_faceOpposite_points]
  rw [affineSpan_insert_affineSpan]
  convert h
  ext x
  by_cases hx : x = s.points i
  · simp [hx]
  · simp only [range_faceOpposite_points, ne_eq, Set.mem_insert_iff, hx, Set.mem_image,
      Set.mem_setOf_eq, false_or, Set.mem_range]
    refine ⟨?_, ?_⟩
    · rintro ⟨j, -, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j, fun hj ↦ hx (congr_arg _ hj), rfl⟩

end Simplex

end Affine
