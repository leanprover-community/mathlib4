/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Geometry.Euclidean.Projection
import Mathlib.Analysis.NormedSpace.Normalize

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


open EuclideanGeometry NormedSpace
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

section signedDist

/-- Auxiliary definition for `signedDist`. It is the underlying linear map of `signedDist`. -/
private noncomputable def signedDistLinear (v : V) : V →ₗ[ℝ] P →ᴬ[ℝ] ℝ where
  toFun w := .const ℝ P ⟪-normalize v, w⟫
  map_add' x y := by ext; simp [inner_add_right]
  map_smul' r x := by ext; simp [inner_smul_right]

private lemma signedDistLinear_apply (v w : V) :
    signedDistLinear v w = .const ℝ P ⟪-normalize v, w⟫ := rfl

/--
The signed distance between two points `p` and `q`, in the direction of a reference vector `v`.
It is the size of `q - p` in the direction of `v`.
In the degenerate case `v = 0`, it returns `0`.

TODO: once we have a topology on `P →ᴬ[ℝ] ℝ`, the type should be `P →ᴬ[ℝ] P →ᴬ[ℝ] ℝ`.
-/
noncomputable def signedDist (v : V) : P →ᵃ[ℝ] P →ᴬ[ℝ] ℝ where
  toFun p := (innerSL ℝ (normalize v)).toContinuousAffineMap.comp
    (ContinuousAffineMap.id ℝ P -ᵥ .const ℝ P p)
  linear := signedDistLinear v
  map_vadd' p v' := by
    ext q
    rw [signedDistLinear_apply]
    simp [vsub_vadd_eq_vsub_sub, inner_sub_right, ← sub_eq_neg_add]

variable (v w : V) (p q r : P)

-- Lemmas about the definition of `signedDist`

lemma signedDist_apply : signedDist v p = (innerSL ℝ (normalize v)).toContinuousAffineMap.comp
    (ContinuousAffineMap.id ℝ P -ᵥ .const ℝ P p) :=
  rfl

lemma signedDist_apply_apply : signedDist v p q = ⟪normalize v, q -ᵥ p⟫ :=
  rfl

lemma signedDist_apply_linear : (signedDist v p).linear = innerₗ V (normalize v) := by
  change (innerₗ V (normalize v)).comp (LinearMap.id - 0) = _
  simp

lemma signedDist_apply_linear_apply : (signedDist v p).linear w = ⟪normalize v, w⟫ := by
  simp [signedDist_apply_linear]

lemma signedDist_linear_apply : (signedDist v).linear w = .const ℝ P ⟪-normalize v, w⟫ :=
  rfl

lemma signedDist_linear_apply_apply : (signedDist v).linear w p = ⟪-normalize v, w⟫ :=
  rfl

-- Lemmas about the vector argument of `signedDist`

lemma signedDist_smul (r : ℝ) : signedDist (r • v) p q = SignType.sign r * signedDist v p q := by
  simp only [signedDist_apply_apply]
  rw [normalize_smul, real_inner_smul_left]

lemma signedDist_smul_of_pos {r : ℝ} (h : 0 < r) : signedDist (r • v) p q = signedDist v p q := by
  simp [signedDist_smul, h]

lemma signedDist_smul_of_neg {r : ℝ} (h : r < 0) : signedDist (r • v) p q = -signedDist v p q := by
  simp [signedDist_smul, h]

@[simp] lemma signedDist_zero : signedDist 0 p q = 0 := by
  simpa using signedDist_smul 0 p q 0

@[simp] lemma signedDist_neg : signedDist (-v) p q = -signedDist v p q := by
  simpa using signedDist_smul v p q (-1)

lemma signedDist_congr (h : ∃ r > (0 : ℝ), r • v = w) : signedDist (P := P) v = signedDist w := by
  obtain ⟨r, _, _⟩ := h
  ext p q
  simpa [*] using (signedDist_smul v p q r).symm

-- Lemmas about permuting the point arguments of `signedDist`, analogous to lemmas about `dist`

@[simp] lemma signedDist_self : signedDist v p p = 0 := by
  simp [signedDist_apply_apply]

@[simp] lemma signedDist_anticomm : -signedDist v p q = signedDist v q p := by
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

-- Lemmas about offsetting the point arguments of `signedDist` (with `+ᵥ` or `-ᵥ`)

lemma signedDist_vadd_left : signedDist v (w +ᵥ p) q = -⟪normalize v, w⟫ + signedDist v p q := by
  simp [signedDist_linear_apply_apply]

lemma signedDist_vadd_right : signedDist v p (w +ᵥ q) = ⟪normalize v, w⟫ + signedDist v p q := by
  simp [signedDist_apply_linear_apply]

-- TODO: find a better name for these 2 lemmas
lemma signedDist_vadd_left_swap : signedDist v (w +ᵥ p) q = signedDist v p (-w +ᵥ q) := by
  rw [signedDist_vadd_left, signedDist_vadd_right, inner_neg_right]

lemma signedDist_vadd_right_swap : signedDist v p (w +ᵥ q) = signedDist v (-w +ᵥ p) q := by
  rw [signedDist_vadd_left_swap, neg_neg]

lemma signedDist_vadd_vadd : signedDist v (w +ᵥ p) (w +ᵥ q) = signedDist v p q := by
  rw [signedDist_vadd_left_swap, neg_vadd_vadd]

variable {v p q} in
lemma signedDist_left_congr (h : ⟪v, p -ᵥ q⟫ = 0) : signedDist v p = signedDist v q := by
  ext r
  simpa [NormedSpace.normalize, real_inner_smul_left, h] using signedDist_vadd_left v (p -ᵥ q) q r

variable {v q r} in
lemma signedDist_right_congr (h : ⟪v, q -ᵥ r⟫ = 0) : signedDist v p q = signedDist v p r := by
  simpa [NormedSpace.normalize, real_inner_smul_left, h] using signedDist_vadd_right v (q -ᵥ r) p r

variable {v p q} in
lemma signedDist_eq_zero_of_orthogonal (h : ⟪v, q -ᵥ p⟫ = 0) : signedDist v p q = 0 := by
  simpa using signedDist_right_congr p h

-- Lemmas relating `signedDist` to `dist`

lemma abs_signedDist_le_dist : |signedDist v p q| ≤ dist p q := by
  rw [signedDist_apply_apply]
  by_cases h : v = 0
  · simp [h]
  · grw [abs_real_inner_le_norm]
    simp [norm_normalize h, dist_eq_norm_vsub']

lemma signedDist_le_dist : signedDist v p q ≤ dist p q :=
  le_trans (le_abs_self _) (abs_signedDist_le_dist _ _ _)

lemma abs_signedDist_eq_dist_iff_vsub_mem_span :
    |signedDist v p q| = dist p q ↔ q -ᵥ p ∈ ℝ ∙ v := by
  rw [Submodule.mem_span_singleton]
  rw [signedDist_apply_apply, dist_eq_norm_vsub', NormedSpace.normalize, real_inner_smul_left,
    abs_mul, abs_inv, abs_norm]
  by_cases h : v = 0
  · simp [h, eq_comm (a := (0 : ℝ)), eq_comm (a := (0 : V))]
  rw [inv_mul_eq_iff_eq_mul₀ (by positivity)]
  rw [← Real.norm_eq_abs, ((norm_inner_eq_norm_tfae ℝ v (q -ᵥ p)).out 0 2:)]
  simp [h, eq_comm]

open NNReal in
lemma signedDist_eq_dist_iff_vsub_mem_span : signedDist v p q = dist p q ↔ q -ᵥ p ∈ ℝ≥0 ∙ v := by
  rw [Submodule.mem_span_singleton]
  rw [signedDist_apply_apply, dist_eq_norm_vsub', NormedSpace.normalize, real_inner_smul_left]
  by_cases h : v = 0
  · simp [h, eq_comm (a := (0 : ℝ)), eq_comm (a := (0 : V))]
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

@[simp] lemma signedDist_vsub_self : signedDist (q -ᵥ p) p q = dist p q := by
  rw [signedDist_eq_dist_iff_vsub_mem_span]
  apply Submodule.mem_span_singleton_self

@[simp] lemma signedDist_vsub_self_rev : signedDist (p -ᵥ q) p q = -dist p q := by
  rw [← neg_eq_iff_eq_neg, ← signedDist_neg, neg_vsub_eq_vsub_rev]
  apply signedDist_vsub_self

end signedDist

namespace AffineSubspace

variable (s : AffineSubspace ℝ P) [Nonempty s] [s.direction.HasOrthogonalProjection] (p q : P)

/-- The signed distance between `s` and a point, in the direction of the reference point `p`.
This is expected to be used when `p` does not lie in `s` (in the degenerate case where `p` lies
in `s`, this yields 0) and when the point at which the distance is evaluated lies in the affine
span of `s` and `p` (any component of the distance orthogonal to that span is disregarded). -/
noncomputable def signedInfDist : P →ᴬ[ℝ] ℝ :=
  signedDist (p -ᵥ orthogonalProjection s p) (Classical.ofNonempty : s)

lemma signedInfDist_def :
    s.signedInfDist p = signedDist (p -ᵥ orthogonalProjection s p) ↑(Classical.ofNonempty : s) :=
  rfl

variable {s p q} in
lemma signedInfDist_eq_signedDist_of_mem (h : q ∈ s) :
    s.signedInfDist p = signedDist (p -ᵥ orthogonalProjection s p) q := by
  apply signedDist_left_congr
  apply s.direction.inner_left_of_mem_orthogonal
  · exact vsub_mem_direction (SetLike.coe_mem _) h
  · exact vsub_orthogonalProjection_mem_direction_orthogonal s p

lemma signedInfDist_eq_signedDist_orthogonalProjection {x : P} : s.signedInfDist p x =
    signedDist (p -ᵥ orthogonalProjection s p) ↑(orthogonalProjection s x) x := by
  rw [signedInfDist_eq_signedDist_of_mem (orthogonalProjection_mem x)]

@[simp] lemma signedInfDist_apply_self : s.signedInfDist p p = ‖p -ᵥ orthogonalProjection s p‖ := by
  rw [signedInfDist_eq_signedDist_orthogonalProjection, signedDist_vsub_self, dist_eq_norm_vsub']

variable {s} in
@[simp] lemma signedInfDist_apply_of_mem {x : P} (hx : x ∈ s) : s.signedInfDist p x = 0 := by
  simp [signedInfDist_eq_signedDist_orthogonalProjection, orthogonalProjection_eq_self_iff.2 hx]

variable {s p} in
@[simp] lemma signedInfDist_eq_const_of_mem (h : p ∈ s) :
    s.signedInfDist p = AffineMap.const ℝ P (0 : ℝ) := by
  ext x
  simp [signedInfDist_def, orthogonalProjection_eq_self_iff.2 h]

variable {s p} in
lemma abs_signedInfDist_eq_dist_of_mem_affineSpan_insert {x : P}
    (h : x ∈ affineSpan ℝ (insert p s)) :
    |s.signedInfDist p x| = dist x (orthogonalProjection s x) := by
  rw [mem_affineSpan_insert_iff (orthogonalProjection s p).property] at h
  rcases h with ⟨r, p₀, hp₀, rfl⟩
  simp [hp₀, dist_eq_norm_vsub, orthogonalProjection_eq_self_iff.2 hp₀,
    orthogonalProjection_vsub_orthogonalProjection, norm_smul, abs_mul]

lemma signedInfDist_singleton :
    (affineSpan ℝ ({q} : Set P)).signedInfDist p = signedDist (p -ᵥ q) q := by
  simpa using signedInfDist_eq_signedDist_of_mem (mem_affineSpan ℝ (Set.mem_singleton q))

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
  AffineSubspace.signedInfDist (affineSpan ℝ (s '' {i}ᶜ)) (s i)

lemma signedInfDist_apply_self :
    s.signedInfDist i (s i) =
      ‖s i -ᵥ (s.faceOpposite i).orthogonalProjectionSpan (s i)‖ :=
  (AffineSubspace.signedInfDist_apply_self _ _).trans <| by simp [orthogonalProjectionSpan]

variable {i} in
lemma signedInfDist_apply_of_ne {j : Fin (n + 1)} (h : j ≠ i) :
    s.signedInfDist i (s j) = 0 :=
  AffineSubspace.signedInfDist_apply_of_mem _ (s.mem_affineSpan_image_iff.2 h)

lemma signedInfDist_affineCombination {w : Fin (n + 1) → ℝ} (h : ∑ i, w i = 1) :
    s.signedInfDist i (Finset.univ.affineCombination ℝ s w) = w i * ‖s i -ᵥ
      (s.faceOpposite i).orthogonalProjectionSpan (s i)‖ := by
  rw [← ContinuousAffineMap.coe_toAffineMap, Finset.map_affineCombination _ _ _ h,
    Finset.univ.affineCombination_apply_eq_lineMap_sum w
      ((s.signedInfDist i).toAffineMap ∘ s) 0
      ‖s i -ᵥ (s.faceOpposite i).orthogonalProjectionSpan (s i)‖
      {i} h]
  · simp [AffineMap.lineMap_apply]
  · simp [signedInfDist_apply_self]
  · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and,
      Function.comp_apply]
    intro j hj
    exact s.signedInfDist_apply_of_ne hj

variable {s} in
lemma abs_signedInfDist_eq_dist_of_mem_affineSpan_range {p : P}
    (h : p ∈ affineSpan ℝ (Set.range s)) :
    |s.signedInfDist i p| =
      dist p ((s.faceOpposite i).orthogonalProjectionSpan p) := by
  rw [signedInfDist, AffineSubspace.abs_signedInfDist_eq_dist_of_mem_affineSpan_insert,
    orthogonalProjectionSpan]
  · simp_rw [range_faceOpposite_points]
  rw [affineSpan_insert_affineSpan]
  convert h
  exact Set.insert_image_compl_eq_range s i

end Simplex

end Affine
