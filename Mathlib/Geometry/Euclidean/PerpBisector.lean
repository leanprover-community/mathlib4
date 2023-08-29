/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Joseph Myers
-/
import Mathlib.Analysis.InnerProductSpace.Orthogonal

#align_import geometry.euclidean.basic from "leanprover-community/mathlib"@"2de9c37fa71dde2f1c6feff19876dd6a7b1519f0"

/-!
# Perpendicular bisector of a segment

We define `AffineSubspace.perpBisector p₁ p₂` to be the perpendicular bisector of the segment
`[p₁, p₂]`, as a bundled affine subspace. We also prove that a point belongs to the perpendicular
bisector if and only if it is equidistant from `p₁` and `p₂`, as well as a few linear equations that
define this subspace.

## Keywords

euclidean geometry, perpendicular, perpendicular bisector, line segment bisector, equidistant
-/

set_option autoImplicit true

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
theorem mem_perpBisector_iff_inner_eq_zero' :
    c ∈ perpBisector p₁ p₂ ↔ ⟪p₂ -ᵥ p₁, c -ᵥ midpoint ℝ p₁ p₂⟫ = 0 :=
  Iff.rfl

/-- A point `c` belongs the perpendicular bisector of `[p₁, p₂] iff `c -ᵥ midpoint ℝ p₁ p₂` is
orthogonal to `p₂ -ᵥ p₁`. -/
theorem mem_perpBisector_iff_inner_eq_zero :
    c ∈ perpBisector p₁ p₂ ↔ ⟪c -ᵥ midpoint ℝ p₁ p₂, p₂ -ᵥ p₁⟫ = 0 :=
  inner_eq_zero_symm

theorem mem_perpBisector_iff_inner_pointReflection_vsub_eq_zero :
    c ∈ perpBisector p₁ p₂ ↔ ⟪Equiv.pointReflection c p₁ -ᵥ p₂, p₂ -ᵥ p₁⟫ = 0 := by
  rw [mem_perpBisector_iff_inner_eq_zero, Equiv.pointReflection_apply,
    vsub_midpoint, invOf_eq_inv, ← smul_add, real_inner_smul_left, vadd_vsub_assoc]
  simp
  -- 🎉 no goals

theorem mem_perpBisector_pointReflection_iff_inner_eq_zero :
    c ∈ perpBisector p₁ (Equiv.pointReflection p₂ p₁) ↔ ⟪c -ᵥ p₂, p₁ -ᵥ p₂⟫ = 0 := by
  rw [mem_perpBisector_iff_inner_eq_zero, midpoint_pointReflection_right,
    Equiv.pointReflection_apply, vadd_vsub_assoc, inner_add_right, add_self_eq_zero,
    ← neg_eq_zero, ← inner_neg_right, neg_vsub_eq_vsub_rev]

theorem midpoint_mem_perpBisector (p₁ p₂ : P) :
    midpoint ℝ p₁ p₂ ∈ perpBisector p₁ p₂ := by
  simp [mem_perpBisector_iff_inner_eq_zero]
  -- 🎉 no goals

theorem perpBisector_nonempty : (perpBisector p₁ p₂ : Set P).Nonempty :=
  ⟨_, midpoint_mem_perpBisector _ _⟩

@[simp]
theorem direction_perpBisector (p₁ p₂ : P) :
    (perpBisector p₁ p₂).direction = (ℝ ∙ (p₂ -ᵥ p₁))ᗮ := by
  erw [perpBisector, comap_symm, map_direction, Submodule.map_id,
    Submodule.toAffineSubspace_direction]
  ext x
  -- ⊢ x ∈ LinearMap.ker (↑(innerₛₗ ℝ) (p₂ -ᵥ p₁)) ↔ x ∈ (Submodule.span ℝ {p₂ -ᵥ p …
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.symm
  -- 🎉 no goals

theorem mem_perpBisector_iff_inner_eq_inner :
    c ∈ perpBisector p₁ p₂ ↔ ⟪c -ᵥ p₁, p₂ -ᵥ p₁⟫ = ⟪c -ᵥ p₂, p₁ -ᵥ p₂⟫ := by
  rw [Iff.comm, mem_perpBisector_iff_inner_eq_zero, ← add_neg_eq_zero, ← inner_neg_right,
    neg_vsub_eq_vsub_rev, ← inner_add_left, vsub_midpoint, invOf_eq_inv, ← smul_add,
    real_inner_smul_left]; simp
                           -- 🎉 no goals

theorem mem_perpBisector_iff_inner_eq :
    c ∈ perpBisector p₁ p₂ ↔ ⟪c -ᵥ p₁, p₂ -ᵥ p₁⟫ = (dist p₁ p₂) ^ 2 / 2 := by
  rw [mem_perpBisector_iff_inner_eq_zero, ← vsub_sub_vsub_cancel_right _ _ p₁, inner_sub_left,
    sub_eq_zero, midpoint_vsub_left, invOf_eq_inv, real_inner_smul_left, real_inner_self_eq_norm_sq,
    dist_eq_norm_vsub' V, div_eq_inv_mul]

theorem mem_perpBisector_iff_dist_eq : c ∈ perpBisector p₁ p₂ ↔ dist c p₁ = dist c p₂ := by
  rw [dist_eq_norm_vsub V, dist_eq_norm_vsub V, ← real_inner_add_sub_eq_zero_iff,
    vsub_sub_vsub_cancel_left, inner_add_left, add_eq_zero_iff_eq_neg, ← inner_neg_right,
    neg_vsub_eq_vsub_rev, mem_perpBisector_iff_inner_eq_inner]

theorem mem_perpBisector_iff_dist_eq' : c ∈ perpBisector p₁ p₂ ↔ dist p₁ c = dist p₂ c := by
  simp only [mem_perpBisector_iff_dist_eq, dist_comm]
  -- 🎉 no goals

theorem perpBisector_comm (p₁ p₂ : P) : perpBisector p₁ p₂ = perpBisector p₂ p₁ := by
  ext c; simp only [mem_perpBisector_iff_dist_eq, eq_comm]
  -- ⊢ c ∈ perpBisector p₁ p₂ ↔ c ∈ perpBisector p₂ p₁
         -- 🎉 no goals

@[simp] theorem right_mem_perpBisector : p₂ ∈ perpBisector p₁ p₂ ↔ p₁ = p₂ := by
  simpa [mem_perpBisector_iff_inner_eq_inner] using eq_comm
  -- 🎉 no goals

@[simp] theorem left_mem_perpBisector : p₁ ∈ perpBisector p₁ p₂ ↔ p₁ = p₂ := by
  rw [perpBisector_comm, right_mem_perpBisector, eq_comm]
  -- 🎉 no goals

@[simp] theorem perpBisector_self (p : P) : perpBisector p p = ⊤ :=
  top_unique <| fun _ ↦ by simp [mem_perpBisector_iff_inner_eq_inner]
                           -- 🎉 no goals

@[simp] theorem perpBisector_eq_top : perpBisector p₁ p₂ = ⊤ ↔ p₁ = p₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ perpBisector_self _⟩
  -- ⊢ p₁ = p₂
  rw [← left_mem_perpBisector, h]
  -- ⊢ p₁ ∈ ⊤
  trivial
  -- 🎉 no goals

@[simp] theorem perpBisector_ne_bot : perpBisector p₁ p₂ ≠ ⊥ := by
  rw [← nonempty_iff_ne_bot]; exact perpBisector_nonempty
  -- ⊢ Set.Nonempty ↑(perpBisector p₁ p₂)
                              -- 🎉 no goals

end AffineSubspace

open AffineSubspace

namespace EuclideanGeometry

/-- Suppose that `c₁` is equidistant from `p₁` and `p₂`, and the same applies to `c₂`. Then the
vector between `c₁` and `c₂` is orthogonal to that between `p₁` and `p₂`. (In two dimensions, this
says that the diagonals of a kite are orthogonal.) -/
theorem inner_vsub_vsub_of_dist_eq_of_dist_eq {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁)
    (hc₂ : dist p₁ c₂ = dist p₂ c₂) : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 := by
  rw [← Submodule.mem_orthogonal_singleton_iff_inner_left, ← direction_perpBisector]
  -- ⊢ c₂ -ᵥ c₁ ∈ direction (perpBisector p₁ p₂)
  apply vsub_mem_direction <;> rwa [mem_perpBisector_iff_dist_eq']
  -- ⊢ c₂ ∈ perpBisector p₁ p₂
                               -- 🎉 no goals
                               -- 🎉 no goals
#align euclidean_geometry.inner_vsub_vsub_of_dist_eq_of_dist_eq EuclideanGeometry.inner_vsub_vsub_of_dist_eq_of_dist_eq

end EuclideanGeometry

variable [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [MetricSpace P']
variable [NormedAddTorsor V' P']

theorem Isometry.preimage_perpBisector {f : P → P'} (h : Isometry f) (p₁ p₂ : P) :
    f ⁻¹' (perpBisector (f p₁) (f p₂)) = perpBisector p₁ p₂ := by
  ext x; simp [mem_perpBisector_iff_dist_eq, h.dist_eq]
  -- ⊢ x ∈ f ⁻¹' ↑(perpBisector (f p₁) (f p₂)) ↔ x ∈ ↑(perpBisector p₁ p₂)
         -- 🎉 no goals

theorem Isometry.mapsTo_perpBisector {f : P → P'} (h : Isometry f) (p₁ p₂ : P) :
    MapsTo f (perpBisector p₁ p₂) (perpBisector (f p₁) (f p₂)) :=
  (h.preimage_perpBisector p₁ p₂).ge
