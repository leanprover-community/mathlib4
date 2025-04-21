/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Signed distance to an affine subspace in a Euclidean space.

This file defines the signed distance between two points, in the direction of a given a vector, and
the signed distance between an affine subspace and a point, in the direction of a given
reference point.

## Main definitions

* `signedDist` is the signed distance between two points
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

section signedDist

/-- Auxiliary definition for `signedDist`. It is the undelying linear map of `signedDist`. -/
private noncomputable def signedDistLinear (v : V) : V →ₗ[ℝ] P →ᵃ[ℝ] ℝ where
  toFun w := AffineMap.const ℝ P ⟪-(‖v‖⁻¹ • v), w⟫
  map_add' x y := by ext; simp [inner_add_right]
  map_smul' r x := by ext; simp [inner_smul_right]

private lemma signedDistLinear_apply (v w : V) :
    signedDistLinear v w = AffineMap.const ℝ P ⟪-(‖v‖⁻¹ • v), w⟫ := rfl

/-- The signed distance between two points `p` and `q`, in the direction of a reference vector `v`.
It is the size component of `q - p` in the direction of `v`. -/
noncomputable def signedDist (v : V) : P →ᵃ[ℝ] P →ᵃ[ℝ] ℝ where
  toFun p := (innerₗ V (‖v‖⁻¹ • v)).toAffineMap.comp (AffineMap.id ℝ P -ᵥ AffineMap.const ℝ P p)
  linear := signedDistLinear v
  map_vadd' p v' := by
    ext q
    rw [signedDistLinear_apply]
    generalize ‖v‖⁻¹ • v = x
    simp [vsub_vadd_eq_vsub_sub, inner_sub_right, ← sub_eq_neg_add]

variable (v w : V) (p q r : P)

-- Lemmas about the definition of `signedDist`

lemma signedDist_apply : signedDist v p =
    (innerₗ V (‖v‖⁻¹ • v)).toAffineMap.comp (AffineMap.id ℝ P -ᵥ AffineMap.const ℝ P p) :=
  rfl

lemma signedDist_apply_apply : signedDist v p q = ⟪‖v‖⁻¹ • v, q -ᵥ p⟫ :=
  rfl

lemma signedDist_linear_apply : (signedDist v).linear w = AffineMap.const ℝ P ⟪-(‖v‖⁻¹ • v), w⟫ :=
  rfl

lemma signedDist_linear_apply_apply : (signedDist v).linear w p = ⟪-(‖v‖⁻¹ • v), w⟫ :=
  rfl

lemma signedDist_apply_linear : (signedDist v p).linear = innerₗ V (‖v‖⁻¹ • v) := by
  change (innerₗ V (‖v‖⁻¹ • v)).comp (LinearMap.id - 0) = _
  simp

lemma signedDist_apply_linear_apply : (signedDist v p).linear w = ⟪‖v‖⁻¹ • v, w⟫ := by
  simp [signedDist_apply_linear, real_inner_smul_left]

-- Lemmas about the vector argument of `signedDist`

lemma signedDist_smul (r : ℝ) : signedDist (r • v) p q = SignType.sign r * signedDist v p q := by
  simp only [signedDist_apply_apply]
  rw [norm_smul, mul_inv_rev, smul_smul, mul_rotate, ← smul_smul, real_inner_smul_left]
  congr
  by_cases h : r = 0
  · simp [h]
  · rw [inv_mul_eq_iff_eq_mul₀ (by positivity)]
    simp only [Real.norm_eq_abs, abs_mul_sign]

@[simp] lemma signedDist_zero : signedDist 0 p q = 0 := by
  simpa using signedDist_smul 0 p q 0

@[simp] lemma signedDist_neg : signedDist (-v) p q = -signedDist v p q := by
  simpa using signedDist_smul v p q (-1)

-- Lemmas about permuting the point arguments of `signedDist`

@[simp] lemma signedDist_self : signedDist v p p = 0 := by
  simp [signedDist_apply_apply]

@[simp] lemma signedDist_swap : -signedDist v p q = signedDist v q p := by
  simp [signedDist_apply_apply, ← inner_neg_right]

@[simp]
lemma signedDist_triangle : signedDist v p q + signedDist v q r = signedDist v p r := by
  simp only [signedDist_apply_apply]
  rw [add_comm, ← inner_add_right, vsub_add_vsub_cancel]

@[simp]
lemma signedDist_triangle_left : signedDist v p q - signedDist v p r = signedDist v r q := by
  rw [sub_eq_iff_eq_add', signedDist_triangle]

@[simp]
lemma signedDist_triangle_right : signedDist v p r - signedDist v q r = signedDist v p q := by
  rw [sub_eq_iff_eq_add, signedDist_triangle]

-- Lemmas about offsetting the point arguments of `signedDist` with `+ᵥ`

lemma signedDist_vadd_left :
    signedDist v (w +ᵥ p) q = -inner (‖v‖⁻¹ • v) w + signedDist v p q := by
  simp [signedDist_linear_apply_apply]

lemma signedDist_vadd_right :
    signedDist v p (w +ᵥ q) = inner (‖v‖⁻¹ • v) w + signedDist v p q := by
  simp [signedDist_apply_linear_apply]

variable {v w} in
lemma signedDist_vadd_left_of_inner_eq_zero (h : inner v w = (0:ℝ)) :
    signedDist v (w +ᵥ p) q = signedDist v p q := by
  rw [signedDist_vadd_left]
  simp [real_inner_smul_left, h]

variable {v w} in
lemma signedDist_vadd_right_of_inner_eq_zero (h : inner v w = (0:ℝ)) :
    signedDist v p (w +ᵥ q) = signedDist v p q := by
  rw [signedDist_vadd_right]
  simp [real_inner_smul_left, h]

lemma signedDist_vadd_left_swap : signedDist v (w +ᵥ p) q = signedDist v p (-w +ᵥ q) := by
  rw [signedDist_vadd_left, signedDist_vadd_right, inner_neg_right]

lemma signedDist_vadd_right_swap : signedDist v p (w +ᵥ q) = signedDist v (-w +ᵥ p) q := by
  rw [signedDist_vadd_left_swap, neg_neg]

lemma signedDist_vadd_vadd : signedDist v (w +ᵥ p) (w +ᵥ q) = signedDist v p q := by
  rw [signedDist_vadd_left_swap, neg_vadd_vadd]

-- Lemmas relating `signedDist` to `dist`

lemma abs_signedDist_le_dist : |signedDist v p q| ≤ dist p q := by
  rw [signedDist_apply_apply]
  by_cases h : v = 0
  · simp [h]
  · convert abs_real_inner_le_norm (‖v‖⁻¹ • v) (q -ᵥ p)
    field_simp [norm_smul, dist_eq_norm_vsub']

lemma signedDist_le_dist : signedDist v p q ≤ dist p q :=
  le_trans (le_abs_self _) (abs_signedDist_le_dist _ _ _)


lemma abs_signedDist_eq_dist_iff_vsub_mem_span :
    |signedDist v p q| = dist p q ↔ q -ᵥ p ∈ ℝ ∙ v := by
  rw [Submodule.mem_span_singleton]
  rw [signedDist_apply_apply, dist_eq_norm_vsub', real_inner_smul_left, abs_mul, abs_inv, abs_norm]
  by_cases h : v = 0
  · simp [h, eq_comm (a := (0:ℝ)), eq_comm (a := (0:V))]
  rw [inv_mul_eq_iff_eq_mul₀ (by positivity)]
  have := (norm_inner_eq_norm_tfae ℝ v (q -ᵥ p)).out 0 2
  rw [Real.norm_eq_abs] at this
  rw [this]
  simp [h, eq_comm]

open NNReal in
lemma signedDist_eq_dist_iff_vsub_mem_span : signedDist v p q = dist p q ↔ q -ᵥ p ∈ ℝ≥0 ∙ v := by
  rw [Submodule.mem_span_singleton]
  rw [signedDist_apply_apply, dist_eq_norm_vsub', real_inner_smul_left]
  by_cases h : v = 0
  · simp [h, eq_comm (a := (0:ℝ)), eq_comm (a := (0:V))]
  rw [inv_mul_eq_iff_eq_mul₀ (by positivity)]
  rw [inner_eq_norm_mul_iff_real]
  simp only [smul_def]
  refine ⟨fun h => ?_, fun ⟨c, h⟩ => ?_⟩
  · simp only [NNReal.exists, coe_mk, exists_prop]
    use ‖v‖⁻¹ * ‖q -ᵥ p‖
    constructor
    · positivity
    · rw [← smul_smul, h, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
  · rw [← h, norm_smul, smul_smul, mul_comm]
    simp

end signedDist

namespace AffineSubspace

variable (s : AffineSubspace ℝ P) [Nonempty s] [HasOrthogonalProjection s.direction] (p : P)

/-- The signed distance between `s` and a point, in the direction of the reference point `p`.
This is expected to be used when `p` does not lie in `s` (in the degenerate case where `p` lies
in `s`, this yields 0) and when the point at which the distance is evaluated lies in the affine
span of `s` and `p` (any component of the distance orthogonal to that span is disregarded). -/
noncomputable def signedInfDist : P →ᵃ[ℝ] ℝ :=
  (innerₗ V (‖p -ᵥ orthogonalProjection s p‖⁻¹ • (p -ᵥ orthogonalProjection s p))).toAffineMap.comp
    (AffineMap.id ℝ P -ᵥ s.subtype.comp (orthogonalProjection s))

lemma signedInfDist_apply (x : P) :
    s.signedInfDist p x = ⟪‖p -ᵥ orthogonalProjection s p‖⁻¹ • (p -ᵥ orthogonalProjection s p),
      x -ᵥ orthogonalProjection s x⟫ :=
  rfl

lemma signedInfDist_linear : (s.signedInfDist p).linear =
    (innerₗ V (‖p -ᵥ orthogonalProjection s p‖⁻¹ • (p -ᵥ orthogonalProjection s p))).comp
      (LinearMap.id (R := ℝ) (M := V) -
        s.direction.subtype.comp (_root_.orthogonalProjection s.direction).toLinearMap) :=
  rfl

lemma signedInfDist_linear_apply (v : V) : (s.signedInfDist p).linear v =
    ⟪‖p -ᵥ orthogonalProjection s p‖⁻¹ • (p -ᵥ orthogonalProjection s p),
     v - _root_.orthogonalProjection s.direction v⟫ :=
  rfl

@[simp] lemma signedInfDist_apply_self : s.signedInfDist p p = ‖p -ᵥ orthogonalProjection s p‖ := by
  simp [signedInfDist_apply, real_inner_smul_left, real_inner_self_eq_norm_sq, pow_two, ← mul_assoc]

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
noncomputable def signedInfDist : P →ᵃ[ℝ] ℝ :=
  AffineSubspace.signedInfDist (affineSpan ℝ (Set.range (s.faceOpposite i).points)) (s.points i)

lemma signedInfDist_apply_self : s.signedInfDist i (s.points i) = ‖s.points i -ᵥ
    orthogonalProjection (affineSpan ℝ (Set.range (s.faceOpposite i).points)) (s.points i)‖ :=
  AffineSubspace.signedInfDist_apply_self _ _

variable {i} in
lemma signedInfDist_apply_of_ne {j : Fin (n + 1)} (h : j ≠ i) :
    s.signedInfDist i (s.points j) = 0 :=
  AffineSubspace.signedInfDist_apply_of_mem _ (s.mem_affineSpan_range_faceOpposite_points_iff.2 h)

lemma signedInfDist_affineCombination {w : Fin (n + 1) → ℝ} (h : ∑ i, w i = 1) :
    s.signedInfDist i (Finset.univ.affineCombination ℝ s.points w) = w i * ‖s.points i -ᵥ
      orthogonalProjection (affineSpan ℝ (Set.range (s.faceOpposite i).points)) (s.points i)‖ := by
  rw [Finset.map_affineCombination _ _ _ h,
    Finset.univ.affineCombination_apply_eq_lineMap_sum w (s.signedInfDist i ∘ s.points) 0
      ‖s.points i -ᵥ
       orthogonalProjection (affineSpan ℝ (Set.range (s.faceOpposite i).points)) (s.points i)‖
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
      dist p (orthogonalProjection (affineSpan ℝ (Set.range (s.faceOpposite i).points)) p) := by
  apply AffineSubspace.abs_signedInfDist_eq_dist_of_mem_affineSpan_insert
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
