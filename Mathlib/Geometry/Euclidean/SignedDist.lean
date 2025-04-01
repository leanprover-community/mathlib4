/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Signed distance to an affine subspace in a Euclidean space.

This file defines the signed distance between an affine subspace and a point, in the direction
of a given reference point.

## Main definitions

* `AffineSubspace.signedDist` is the signed distance between an affine subspace and a point.
* `Affine.Simplex.signedDist` is the signed distance between a face of a simplex and a point.
  In the case of a triangle, these distances are trilinear coordinates.

## References

* https://en.wikipedia.org/wiki/Trilinear_coordinates

-/


open EuclideanGeometry
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

namespace AffineSubspace

variable (s : AffineSubspace ℝ P) [Nonempty s] [HasOrthogonalProjection s.direction] (p : P)

/-- The signed distance between `s` and a point, in the direction of the reference point `p`.
This is expected to be used when `p` does not lie in `s` (in the degenerate case where `p` lies
in `s`, this yields 0) and when the point at which the distance is evaluated lies in the affine
span of `s` and `p` (any component of the distance orthogonal to that span is disregarded). -/
noncomputable def signedDist : P →ᵃ[ℝ] ℝ :=
  (innerₗ V (‖p -ᵥ orthogonalProjection s p‖⁻¹ • (p -ᵥ orthogonalProjection s p))).toAffineMap.comp
    (AffineMap.id ℝ P -ᵥ s.subtype.comp (orthogonalProjection s))

lemma signedDist_apply (x : P) :
    s.signedDist p x = ⟪‖p -ᵥ orthogonalProjection s p‖⁻¹ • (p -ᵥ orthogonalProjection s p),
      x -ᵥ orthogonalProjection s x⟫ :=
  rfl

lemma signedDist_linear : (s.signedDist p).linear =
    (innerₗ V (‖p -ᵥ orthogonalProjection s p‖⁻¹ • (p -ᵥ orthogonalProjection s p))).comp
      (LinearMap.id (R := ℝ) (M := V) -
        s.direction.subtype.comp (_root_.orthogonalProjection s.direction).toLinearMap) :=
  rfl

lemma signedDist_linear_apply (v : V) : (s.signedDist p).linear v =
    ⟪‖p -ᵥ orthogonalProjection s p‖⁻¹ • (p -ᵥ orthogonalProjection s p),
     v - _root_.orthogonalProjection s.direction v⟫ :=
  rfl

@[simp] lemma signedDist_apply_self : s.signedDist p p = ‖p -ᵥ orthogonalProjection s p‖ := by
  simp [signedDist_apply, inner_smul_left, real_inner_self_eq_norm_sq, pow_two, ← mul_assoc]

variable {s} in
@[simp] lemma signedDist_apply_of_mem {x : P} (hx : x ∈ s) : s.signedDist p x = 0 := by
  simp [signedDist_apply, orthogonalProjection_eq_self_iff.2 hx]

variable {s p} in
@[simp] lemma signedDist_eq_const_of_left_mem (h : p ∈ s) :
    s.signedDist p = AffineMap.const ℝ P (0 : ℝ) := by
  ext x
  simp [signedDist_apply, orthogonalProjection_eq_self_iff.2 h]

variable {s p} in
lemma abs_signedDist_eq_dist_of_mem_affineSpan_insert {x : P} (h : x ∈ affineSpan ℝ (insert p s)) :
    |s.signedDist p x| = dist x (orthogonalProjection s x) := by
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
noncomputable def signedDist : P →ᵃ[ℝ] ℝ :=
  AffineSubspace.signedDist (affineSpan ℝ (Set.range (s.faceOpposite i).points)) (s.points i)

lemma signedDist_apply_self : s.signedDist i (s.points i) = ‖s.points i -ᵥ
    orthogonalProjection (affineSpan ℝ (Set.range (s.faceOpposite i).points)) (s.points i)‖ :=
  AffineSubspace.signedDist_apply_self _ _

variable {i} in
lemma signedDist_apply_of_ne {j : Fin (n + 1)} (h : j ≠ i) : s.signedDist i (s.points j) = 0 :=
  AffineSubspace.signedDist_apply_of_mem _ (s.mem_affineSpan_range_faceOpposite_points_iff.2 h)

lemma signedDist_affineCombination {w : Fin (n + 1) → ℝ} (h : ∑ i, w i = 1) :
    s.signedDist i (Finset.univ.affineCombination ℝ s.points w) = w i * ‖s.points i -ᵥ
      orthogonalProjection (affineSpan ℝ (Set.range (s.faceOpposite i).points)) (s.points i)‖ := by
  rw [Finset.map_affineCombination _ _ _ h,
    Finset.univ.affineCombination_apply_eq_lineMap_sum w (s.signedDist i ∘ s.points) 0
      ‖s.points i -ᵥ
       orthogonalProjection (affineSpan ℝ (Set.range (s.faceOpposite i).points)) (s.points i)‖
      {i} h]
  · simp [AffineMap.lineMap_apply]
  · simp [signedDist_apply_self]
  · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and,
      Function.comp_apply]
    intro j hj
    exact s.signedDist_apply_of_ne hj

variable {s} in
lemma abs_signedDist_eq_dist_of_mem_affineSpan_range {p : P}
    (h : p ∈ affineSpan ℝ (Set.range s.points)) :
    |s.signedDist i p| =
      dist p (orthogonalProjection (affineSpan ℝ (Set.range (s.faceOpposite i).points)) p) := by
  apply AffineSubspace.abs_signedDist_eq_dist_of_mem_affineSpan_insert
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
