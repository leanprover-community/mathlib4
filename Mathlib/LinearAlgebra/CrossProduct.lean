/-
Copyright (c) 2021 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Kyle Miller, Eric Wieser
-/
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# Cross products

This module defines the cross product of vectors in $R^3$ for $R$ a commutative ring,
as a bilinear map.

## Main definitions

* `crossProduct` is the cross product of pairs of vectors in $R^3$.

## Main results

* `triple_product_eq_det`
* `cross_dot_cross`
* `jacobi_cross`

## Notation

The locale `Matrix` gives the following notation:

* `×₃` for the cross product

## Tags

crossproduct
-/


open Matrix

variable {R : Type*} [CommRing R]

/-- The cross product of two vectors in $R^3$ for $R$ a commutative ring. -/
def crossProduct : (Fin 3 → R) →ₗ[R] (Fin 3 → R) →ₗ[R] Fin 3 → R := by
  apply LinearMap.mk₂ R fun a b : Fin 3 → R =>
      ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]
  · intros
    simp_rw [vec3_add, Pi.add_apply]
    apply vec3_eq <;> ring
  · intros
    simp_rw [smul_vec3, Pi.smul_apply, smul_sub, smul_mul_assoc]
  · intros
    simp_rw [vec3_add, Pi.add_apply]
    apply vec3_eq <;> ring
  · intros
    simp_rw [smul_vec3, Pi.smul_apply, smul_sub, mul_smul_comm]

@[inherit_doc] scoped[Matrix] infixl:74 " ×₃ " => crossProduct

theorem cross_apply (a b : Fin 3 → R) :
    a ×₃ b = ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0] := rfl

section ProductsProperties

@[simp]
theorem cross_anticomm (v w : Fin 3 → R) : -(v ×₃ w) = w ×₃ v := by
  simp [cross_apply, mul_comm]

alias neg_cross := cross_anticomm

@[simp]
theorem cross_anticomm' (v w : Fin 3 → R) : v ×₃ w + w ×₃ v = 0 := by
  rw [add_eq_zero_iff_eq_neg, cross_anticomm]

@[simp]
theorem cross_self (v : Fin 3 → R) : v ×₃ v = 0 := by
  simp [cross_apply, mul_comm]

/-- The cross product of two vectors is perpendicular to the first vector. -/
@[simp 1100] -- Porting note: increase priority so that the LHS doesn't simplify
theorem dot_self_cross (v w : Fin 3 → R) : v ⬝ᵥ v ×₃ w = 0 := by
  rw [cross_apply, vec3_dotProduct]
  norm_num
  ring

/-- The cross product of two vectors is perpendicular to the second vector. -/
@[simp 1100] -- Porting note: increase priority so that the LHS doesn't simplify
theorem dot_cross_self (v w : Fin 3 → R) : w ⬝ᵥ v ×₃ w = 0 := by
  rw [← cross_anticomm, dotProduct_neg, dot_self_cross, neg_zero]

/-- Cyclic permutations preserve the triple product. See also `triple_product_eq_det`. -/
theorem triple_product_permutation (u v w : Fin 3 → R) : u ⬝ᵥ v ×₃ w = v ⬝ᵥ w ×₃ u := by
  simp_rw [cross_apply, vec3_dotProduct]
  norm_num
  ring

/-- The triple product of `u`, `v`, and `w` is equal to the determinant of the matrix
    with those vectors as its rows. -/
theorem triple_product_eq_det (u v w : Fin 3 → R) : u ⬝ᵥ v ×₃ w = Matrix.det ![u, v, w] := by
  rw [vec3_dotProduct, cross_apply, det_fin_three]
  norm_num
  ring

/-- The scalar quadruple product identity, related to the Binet-Cauchy identity. -/
theorem cross_dot_cross (u v w x : Fin 3 → R) :
    u ×₃ v ⬝ᵥ w ×₃ x = u ⬝ᵥ w * v ⬝ᵥ x - u ⬝ᵥ x * v ⬝ᵥ w := by
  simp_rw [cross_apply, vec3_dotProduct]
  norm_num
  ring

end ProductsProperties

section LeibnizProperties

/-- The cross product satisfies the Leibniz lie property. -/
theorem leibniz_cross (u v w : Fin 3 → R) : u ×₃ (v ×₃ w) = u ×₃ v ×₃ w + v ×₃ (u ×₃ w) := by
  simp_rw [cross_apply, vec3_add]
  apply vec3_eq <;> norm_num <;> ring

/-- The three-dimensional vectors together with the operations + and ×₃ form a Lie ring.
    Note we do not make this an instance as a conflicting one already exists
    via `LieRing.ofAssociativeRing`. -/
def Cross.lieRing : LieRing (Fin 3 → R) :=
  { Pi.addCommGroup with
    bracket := fun u v => u ×₃ v
    add_lie := LinearMap.map_add₂ _
    lie_add := fun _ => LinearMap.map_add _
    lie_self := cross_self
    leibniz_lie := leibniz_cross }

attribute [local instance] Cross.lieRing

theorem cross_cross (u v w : Fin 3 → R) : u ×₃ v ×₃ w = u ×₃ (v ×₃ w) - v ×₃ (u ×₃ w) :=
  lie_lie u v w

/-- **Jacobi identity**: For a cross product of three vectors,
    their sum over the three even permutations is equal to the zero vector. -/
theorem jacobi_cross (u v w : Fin 3 → R) : u ×₃ (v ×₃ w) + v ×₃ (w ×₃ u) + w ×₃ (u ×₃ v) = 0 :=
  lie_jacobi u v w

end LeibnizProperties

-- this can also be proved via `dotProduct_eq_zero_iff` and `triple_product_eq_det`, but
-- that would require much heavier imports.
lemma crossProduct_ne_zero_iff_linearIndependent {F : Type*} [Field F] {v w : Fin 3 → F} :
    crossProduct v w ≠ 0 ↔ LinearIndependent F ![v, w] := by
  rw [not_iff_comm]
  by_cases hv : v = 0
  · rw [hv, map_zero, LinearMap.zero_apply, eq_self, iff_true]
    exact fun h ↦ h.ne_zero 0 rfl
  constructor
  · rw [LinearIndependent.pair_iff' hv, not_forall_not]
    rintro ⟨a, rfl⟩
    rw [LinearMap.map_smul, cross_self, smul_zero]
  have hv' : v = ![v 0, v 1, v 2] := by simp [← List.ofFn_inj]
  have hw' : w = ![w 0, w 1, w 2] := by simp [← List.ofFn_inj]
  intro h1 h2
  simp_rw [cross_apply, cons_eq_zero_iff, zero_empty, and_true, sub_eq_zero] at h1
  have h20 := LinearIndependent.pair_iff.mp h2 (- w 0) (v 0)
  have h21 := LinearIndependent.pair_iff.mp h2 (- w 1) (v 1)
  have h22 := LinearIndependent.pair_iff.mp h2 (- w 2) (v 2)
  rw [neg_smul, neg_add_eq_zero, hv', hw', smul_vec3, smul_vec3, ← hv', ← hw'] at h20 h21 h22
  simp only [smul_eq_mul, mul_comm (w 0), mul_comm (w 1), mul_comm (w 2), h1] at h20 h21 h22
  rw [hv', cons_eq_zero_iff, cons_eq_zero_iff, cons_eq_zero_iff, zero_empty] at hv
  exact hv ⟨(h20 trivial).2, (h21 trivial).2, (h22 trivial).2, rfl⟩


-- this is necessary to make sure the l2 norm is taken for members of `Fin 3 → ℝ`
-- instead of the sup norm
noncomputable def l2Norm (v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ‖v‖

-- The l2 norm of the cross of two real vectors equals the produce of their individual norms
-- times the sine of the angle between them.
theorem crossProduct_norm_eq_norm_mul_norm_mul_sin (a b : EuclideanSpace ℝ (Fin 3)) :
  l2Norm (a ×₃ b) = ‖a‖ * ‖b‖ * Real.sin (InnerProductGeometry.angle a b) :=
by
  let lhs := l2Norm (a ×₃ b)
  let rhs := ‖a‖ * ‖b‖ * Real.sin (InnerProductGeometry.angle a b)
  have h_lhs_pos : lhs ≥ 0 := norm_nonneg _
  have h_rhs_pos : rhs ≥ 0 := mul_nonneg
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (Real.sin_nonneg_of_mem_Icc
      (by simp [InnerProductGeometry.angle_nonneg, InnerProductGeometry.angle_le_pi]))
  suffices h_square_lhs_eq_square_rhs : lhs ^2 = rhs ^ 2 from by
    {rw [sq_eq_sq_iff_eq_or_eq_neg] at h_square_lhs_eq_square_rhs
     cases h_square_lhs_eq_square_rhs with
     | inl h_eq => exact h_eq
     | inr h_eq_neg =>
       unfold lhs at h_lhs_pos ; unfold lhs rhs at h_eq_neg
       rw [h_eq_neg] at h_lhs_pos
       have h_rhs_eq_0 : rhs = 0 := by
        unfold rhs
        exact le_antisymm (neg_le_neg_iff.mp (by simp [h_lhs_pos])) h_rhs_pos
       unfold rhs at h_rhs_eq_0
       simp [h_rhs_eq_0, h_eq_neg]}
  unfold lhs rhs
  have h_norm_sq_eq_inner (v : EuclideanSpace ℝ (Fin 3)): (‖v‖ ^ 2 = v ⬝ᵥ v) :=
    by rw [@norm_sq_eq_inner ℝ] ; exact rfl
  rw [l2Norm, h_norm_sq_eq_inner (a ×₃ b), cross_dot_cross,
      ←h_norm_sq_eq_inner, ←h_norm_sq_eq_inner, dotProduct_comm b a]
  have inner_eq_dotProduct (a b : EuclideanSpace ℝ (Fin 3)) :
    inner a b = a ⬝ᵥ b:= by exact rfl
  repeat rw [←inner_eq_dotProduct]
  rw [←(InnerProductGeometry.cos_angle_mul_norm_mul_norm a b)]
  calc
    _ = ‖a‖ ^ 2 * ‖b‖ ^ 2 * (1 - Real.cos (InnerProductGeometry.angle a b) ^ 2) := by ring
    _ = _ := by rw [←Real.sin_sq] ; ring
