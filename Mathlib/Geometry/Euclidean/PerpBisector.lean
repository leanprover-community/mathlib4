/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import Mathlib.Analysis.InnerProductSpace.Orthogonal
/-!
# Perpendicular bisector of a segment

In this file we prove that in a Euclidean affine space, `c` is equidistant from `p₁` and `p₁` if and
only if it belongs to the perpendicular bisector to the segment `[p₁, p₂]`. We give three equivalent
linear equations for the perpendicular bisector:

- `c -ᵥ midpoint R p₁ p₂` is orthogonal to `p₂ -ᵥ p₁`;
- `⟪c -ᵥ p₁, p₂ -ᵥ p₁⟫ = ⟪c -ᵥ p₂, p₁ -ᵥ p₂⟫`;
- `⟪c -ᵥ p₁, p₂ -ᵥ p₁⟫ = (dist p₂ p₁) ^ 2 / 2`.

## Keywords

euclidean geometry, perpendicular, perpendicular bisector, line segment bisector, equidistant
-/

open Set
open scoped BigOperators RealInnerProductSpace

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]

variable [NormedAddTorsor V P]

noncomputable section

namespace AffineSubspace

variable {c c₁ c₂ p₁ p₂ : P}

/-- Perpendicular bisector of a segment in a Euclidean affine space. -/
def perpBisector (p₁ p₂ : P) : AffineSubspace ℝ P :=
  .comap ((AffineEquiv.vaddConst ℝ (midpoint ℝ p₁ p₂)).symm : P →ᵃ[ℝ] V) <|
    (LinearMap.ker (innerₛₗ ℝ (p₂ -ᵥ p₁))).toAffineSubspace

/-- A point `c` belongs the perpendicular bisector of `[p₁, p₂] iff `p₂ -ᵥ p₁` is orthogonal to
`c -ᵥ midpoint ℝ p₁ p₂`. -/
theorem mem_perpBisector_iff_inner_eq_zero :
    c ∈ perpBisector p₁ p₂ ↔ ⟪p₂ -ᵥ p₁, c -ᵥ midpoint ℝ p₁ p₂⟫ = 0 :=
  Iff.rfl

theorem midpoint_mem_perpBisector (p₁ p₂ : P) :
    midpoint ℝ p₁ p₂ ∈ perpBisector p₁ p₂ := by
  simp [mem_perpBisector_iff_inner_eq_zero]

@[simp]
theorem direction_perpBisector (p₁ p₂ : P) :
    (perpBisector p₁ p₂).direction = (ℝ ∙ (p₂ -ᵥ p₁))ᗮ := by
  erw [perpBisector, comap_symm, map_direction, Submodule.map_id]
  

/-- A point `c` belongs the perpendicular bisector of `[p₁, p₂] iff `c -ᵥ midpoint ℝ p₁ p₂` is
orthogonal to `p₂ -ᵥ p₁`. -/
theorem mem_perpBisector_iff_inner_eq_zero' :
    c ∈ perpBisector p₁ p₂ ↔ ⟪c -ᵥ midpoint ℝ p₁ p₂, p₂ -ᵥ p₁⟫ = 0 :=
  inner_eq_zero_symm


@[simp]
theorem direction_perpBisector (p₁ p₂ : P) :
    (perpBisector p₁ p₂).direction = (ℝ ∙ (p₂ -ᵥ p₁))ᗮ := by


theorem mem_perpBisector_iff_dist_eq

end AffineSubspace


namespace EuclideanGeometry

/-- A point `c` is equidistant from `p₁` and `p₁` if and only if it belongs to the perpendicular
bisector. -/
theorem dist_eq_dist_iff_inner_vsub_midpoint_vsub_eq {c p₁ p₂ : P} :
    dist p₁ c = dist p₂ c ↔ ⟪c -ᵥ midpoint ℝ p₁ p₂, p₂ -ᵥ p₁⟫ = 0 := by
  rw [dist_eq_norm_vsub' V, dist_eq_norm_vsub' V, ← real_inner_add_sub_eq_zero_iff,
    vsub_sub_vsub_cancel_left, vsub_midpoint, invOf_eq_inv, ← smul_add, real_inner_smul_left]
  simp

/-- A point `c` is equidistant from `p₁` and `p₁` if and only if it belongs to the perpendicular
bisector. -/
theorem dist_eq_dist_iff_inner_vsub_vsub_eq_inner_vsub_vsub {c p₁ p₂ : P} :
    dist p₁ c = dist p₂ c ↔ ⟪c -ᵥ p₁, p₂ -ᵥ p₁⟫ = ⟪c -ᵥ p₂, p₁ -ᵥ p₂⟫ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← real_inner_add_sub_eq_zero_iff,
    vsub_sub_vsub_cancel_right, inner_add_left, add_eq_zero_iff_eq_neg,
    ← inner_neg_neg]
  simp only [neg_vsub_eq_vsub_rev, ← inner_neg_left]

/-- A point `c` is equidistant from `p₁` and `p₁` if and only if it belongs to the perpendicular
bisector. -/
theorem dist_eq_dist_iff_inner_vsub_vsub_eq_half_sq_dist {c p₁ p₂ : P} :
    dist p₁ c = dist p₂ c ↔ ⟪c -ᵥ p₁, p₂ -ᵥ p₁⟫ = (dist p₂ p₁) ^ 2 / 2 := by
  have : ⟪c -ᵥ p₁, p₂ -ᵥ p₁⟫ + ⟪c -ᵥ p₂, p₁ -ᵥ p₂⟫ = (dist p₂ p₁) ^ 2
  · rw [← inner_neg_neg, neg_vsub_eq_vsub_rev, neg_vsub_eq_vsub_rev, ← inner_add_left,
      vsub_add_vsub_cancel, real_inner_self_eq_norm_sq, dist_eq_norm_vsub' V]
  rw [dist_eq_dist_iff_inner_vsub_vsub_eq_inner_vsub_vsub, ← this,
    eq_div_iff_mul_eq two_ne_zero, mul_two, add_right_inj]

/-- Suppose that `c₁` is equidistant from `p₁` and `p₂`, and the same
applies to `c₂`. Then the vector between `c₁` and `c₂` is orthogonal
to that between `p₁` and `p₂`. (In two dimensions, this says that the
diagonals of a kite are orthogonal.) -/
theorem inner_vsub_vsub_of_dist_eq_of_dist_eq {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁)
    (hc₂ : dist p₁ c₂ = dist p₂ c₂) : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 := by
  rw [dist_eq_dist_iff_inner_vsub_midpoint_vsub_eq] at hc₁ hc₂
  simpa [← inner_sub_left] using congr_arg₂ (· - ·) hc₂ hc₁
#align euclidean_geometry.inner_vsub_vsub_of_dist_eq_of_dist_eq EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq

end EuclideanGeometry
