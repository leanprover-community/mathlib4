/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Joseph Myers
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.Convex.Between

/-!
# Perpendicular bisector of a segment

We define `AffineSubspace.perpBisector p₁ p₂` to be the perpendicular bisector of the segment
`[p₁, p₂]`, as a bundled affine subspace. We also prove that a point belongs to the perpendicular
bisector if and only if it is equidistant from `p₁` and `p₂`, as well as a few linear equations that
define this subspace.

## Keywords

euclidean geometry, perpendicular, perpendicular bisector, line segment bisector, equidistant
-/

@[expose] public section

open Set
open scoped RealInnerProductSpace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
variable [NormedAddTorsor V P]

noncomputable section

namespace AffineSubspace

variable {c p₁ p₂ : P}

/-- Perpendicular bisector of a segment in a Euclidean affine space. -/
def perpBisector (p₁ p₂ : P) : AffineSubspace ℝ P :=
  mk' (midpoint ℝ p₁ p₂) (LinearMap.ker (innerₛₗ ℝ (p₂ -ᵥ p₁)))

/-- A point `c` belongs the perpendicular bisector of `[p₁, p₂]` iff `p₂ -ᵥ p₁` is orthogonal to
`c -ᵥ midpoint ℝ p₁ p₂`. -/
theorem mem_perpBisector_iff_inner_eq_zero' :
    c ∈ perpBisector p₁ p₂ ↔ ⟪p₂ -ᵥ p₁, c -ᵥ midpoint ℝ p₁ p₂⟫ = 0 :=
  Iff.rfl

/-- A point `c` belongs the perpendicular bisector of `[p₁, p₂]` iff `c -ᵥ midpoint ℝ p₁ p₂` is
orthogonal to `p₂ -ᵥ p₁`. -/
theorem mem_perpBisector_iff_inner_eq_zero :
    c ∈ perpBisector p₁ p₂ ↔ ⟪c -ᵥ midpoint ℝ p₁ p₂, p₂ -ᵥ p₁⟫ = 0 :=
  inner_eq_zero_symm

theorem mem_perpBisector_iff_inner_pointReflection_vsub_eq_zero :
    c ∈ perpBisector p₁ p₂ ↔ ⟪Equiv.pointReflection c p₁ -ᵥ p₂, p₂ -ᵥ p₁⟫ = 0 := by
  rw [mem_perpBisector_iff_inner_eq_zero, Equiv.pointReflection_apply,
    vsub_midpoint, invOf_eq_inv, ← smul_add, real_inner_smul_left, vadd_vsub_assoc]
  simp

theorem mem_perpBisector_pointReflection_iff_inner_eq_zero :
    c ∈ perpBisector p₁ (Equiv.pointReflection p₂ p₁) ↔ ⟪c -ᵥ p₂, p₁ -ᵥ p₂⟫ = 0 := by
  rw [mem_perpBisector_iff_inner_eq_zero, midpoint_pointReflection_right,
    Equiv.pointReflection_apply, vadd_vsub_assoc, inner_add_right, add_self_eq_zero,
    ← neg_eq_zero, ← inner_neg_right, neg_vsub_eq_vsub_rev]

theorem midpoint_mem_perpBisector (p₁ p₂ : P) :
    midpoint ℝ p₁ p₂ ∈ perpBisector p₁ p₂ := by
  simp [mem_perpBisector_iff_inner_eq_zero]

theorem perpBisector_nonempty : (perpBisector p₁ p₂ : Set P).Nonempty :=
  ⟨_, midpoint_mem_perpBisector _ _⟩

@[simp]
theorem direction_perpBisector (p₁ p₂ : P) :
    (perpBisector p₁ p₂).direction = (ℝ ∙ (p₂ -ᵥ p₁))ᗮ := by
  rw [perpBisector, direction_mk']
  ext x
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.symm

theorem mem_perpBisector_iff_inner_eq_inner :
    c ∈ perpBisector p₁ p₂ ↔ ⟪c -ᵥ p₁, p₂ -ᵥ p₁⟫ = ⟪c -ᵥ p₂, p₁ -ᵥ p₂⟫ := by
  rw [Iff.comm, mem_perpBisector_iff_inner_eq_zero, ← add_neg_eq_zero, ← inner_neg_right,
    neg_vsub_eq_vsub_rev, ← inner_add_left, vsub_midpoint, invOf_eq_inv, ← smul_add,
    real_inner_smul_left]; simp

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

theorem perpBisector_comm (p₁ p₂ : P) : perpBisector p₁ p₂ = perpBisector p₂ p₁ := by
  ext c; simp only [mem_perpBisector_iff_dist_eq, eq_comm]

@[simp] theorem right_mem_perpBisector : p₂ ∈ perpBisector p₁ p₂ ↔ p₁ = p₂ := by
  simpa [mem_perpBisector_iff_inner_eq_inner] using eq_comm

@[simp] theorem left_mem_perpBisector : p₁ ∈ perpBisector p₁ p₂ ↔ p₁ = p₂ := by
  rw [perpBisector_comm, right_mem_perpBisector, eq_comm]

@[simp] theorem perpBisector_self (p : P) : perpBisector p p = ⊤ :=
  top_unique fun _ ↦ by simp [mem_perpBisector_iff_inner_eq_inner]

@[simp] theorem perpBisector_eq_top : perpBisector p₁ p₂ = ⊤ ↔ p₁ = p₂ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ perpBisector_self _⟩
  rw [← left_mem_perpBisector, h]
  trivial

@[simp] theorem perpBisector_ne_bot : perpBisector p₁ p₂ ≠ ⊥ := by
  rw [← nonempty_iff_ne_bot]; exact perpBisector_nonempty

end AffineSubspace

open AffineSubspace

namespace EuclideanGeometry

/-- If `b` is strictly between `a` and `c`, and `p - a` is perpendicular to `b - a`,
then `p` is closer to `b` than to `c`. -/
theorem dist_lt_of_sbtw_of_inner_eq_zero {a b c p : P}
    (h_sbtw : Sbtw ℝ a b c)
    (h_inner : ⟪p -ᵥ a, b -ᵥ a⟫ = 0) :
    dist p b < dist p c := by
  obtain ⟨t, ⟨ht0, ht1⟩, hb_eq⟩ := h_sbtw.mem_image_Ioo
  set v := c -ᵥ a
  have hb : b -ᵥ a = t • v := by simp [← hb_eq, AffineMap.lineMap_apply, v]
  have hpc : ⟪p -ᵥ a, v⟫ = 0 := by simpa [ht0.ne', hb, inner_smul_right] using h_inner
  have hb_sq : dist p b ^ 2 = dist p a ^ 2 + t^2 * ‖v‖^2 := by
    rw [dist_eq_norm_vsub, dist_eq_norm_vsub,
        show p -ᵥ b = (p -ᵥ a) - t • v by rw [← hb, vsub_sub_vsub_cancel_right],
        ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
        inner_sub_right, inner_smul_right, inner_smul_left, inner_smul_left, inner_smul_right,
        real_inner_comm (p -ᵥ a) v, hpc]
    simp [real_inner_self_eq_norm_sq]
    ring
  have hc_sq : dist p c ^ 2 = dist p a ^ 2 + ‖c -ᵥ a‖^2 := by
    rw [dist_eq_norm_vsub, dist_eq_norm_vsub, ← real_inner_self_eq_norm_sq,
        ← real_inner_self_eq_norm_sq, ← vsub_sub_vsub_cancel_right, inner_sub_left, inner_sub_right,
        inner_sub_right, real_inner_comm (p -ᵥ a) (c -ᵥ a), hpc]
    simp only [sub_zero, zero_sub, sub_neg_eq_add, add_right_inj]
    exact real_inner_self_eq_norm_sq (c -ᵥ a)
  have ht_sq_lt : t^2 < 1 := by
    rw [sq_lt_one_iff₀ ht0.le]
    exact ht1
  have hv_pos : 0 < ‖v‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (vsub_ne_zero.mpr h_sbtw.left_ne_right.symm))
  have h_sq_ineq : dist p b ^ 2 < dist p c ^ 2 := by
    rw [hb_sq, hc_sq]
    have : t ^ 2 * ‖v‖ ^ 2 < ‖v‖ ^ 2 := mul_lt_of_lt_one_left hv_pos ht_sq_lt
    linarith
  simpa only [Real.sqrt_sq dist_nonneg] using Real.sqrt_lt_sqrt (sq_nonneg _) h_sq_ineq

/-- If `p` lies on the perpendicular bisector of `ab` and `b` is strictly between `a` and `c`,
then `p` is closer to `b` than to `c`. -/
theorem dist_lt_of_sbtw_of_mem_perpBisector {a b c p : P}
    (h_sbtw : Sbtw ℝ a b c)
    (hp : p ∈ AffineSubspace.perpBisector a b) :
    dist p b < dist p c :=
  dist_lt_of_sbtw_of_inner_eq_zero
    (h_sbtw.trans_left_right (sbtw_midpoint_of_ne ℝ h_sbtw.left_ne)) <| by
    rw [right_vsub_midpoint, inner_smul_right,
        mem_perpBisector_iff_inner_eq_zero.mp hp, invOf_eq_inv, mul_zero]

/-- Suppose that `c₁` is equidistant from `p₁` and `p₂`, and the same applies to `c₂`. Then the
vector between `c₁` and `c₂` is orthogonal to that between `p₁` and `p₂`. (In two dimensions, this
says that the diagonals of a kite are orthogonal.) -/
theorem inner_vsub_vsub_of_dist_eq_of_dist_eq {c₁ c₂ p₁ p₂ : P} (hc₁ : dist p₁ c₁ = dist p₂ c₁)
    (hc₂ : dist p₁ c₂ = dist p₂ c₂) : ⟪c₂ -ᵥ c₁, p₂ -ᵥ p₁⟫ = 0 := by
  rw [← Submodule.mem_orthogonal_singleton_iff_inner_left, ← direction_perpBisector]
  apply vsub_mem_direction <;> rwa [mem_perpBisector_iff_dist_eq']

end EuclideanGeometry

variable {V' P' : Type*} [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [MetricSpace P']
variable [NormedAddTorsor V' P']

theorem Isometry.preimage_perpBisector {f : P → P'} (h : Isometry f) (p₁ p₂ : P) :
    f ⁻¹' (perpBisector (f p₁) (f p₂)) = perpBisector p₁ p₂ := by
  ext x; simp [mem_perpBisector_iff_dist_eq, h.dist_eq]

theorem Isometry.mapsTo_perpBisector {f : P → P'} (h : Isometry f) (p₁ p₂ : P) :
    MapsTo f (perpBisector p₁ p₂) (perpBisector (f p₁) (f p₂)) :=
  (h.preimage_perpBisector p₁ p₂).ge
