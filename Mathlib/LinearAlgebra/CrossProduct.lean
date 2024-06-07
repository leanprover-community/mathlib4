/-
Copyright (c) 2021 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Kyle Miller, Eric Wieser
-/
import Mathlib.Data.Matrix.Notation
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Lie.Basic

#align_import linear_algebra.cross_product from "leanprover-community/mathlib"@"91288e351d51b3f0748f0a38faa7613fb0ae2ada"

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
#align cross_product crossProduct

scoped[Matrix] infixl:74 " ×₃ " => crossProduct

theorem cross_apply (a b : Fin 3 → R) :
    a ×₃ b = ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0] := rfl
#align cross_apply cross_apply

section ProductsProperties

-- Adaptation note: nightly-2024-04-01
-- The simpNF linter now times out on this lemma,
-- likely due to https://github.com/leanprover/lean4/pull/3807
@[simp, nolint simpNF]
theorem cross_anticomm (v w : Fin 3 → R) : -(v ×₃ w) = w ×₃ v := by
  simp [cross_apply, mul_comm]
#align cross_anticomm cross_anticomm

alias neg_cross := cross_anticomm
#align neg_cross neg_cross

-- Adaptation note: nightly-2024-04-01
-- The simpNF linter now times out on this lemma,
-- likely due to https://github.com/leanprover/lean4/pull/3807
@[simp, nolint simpNF]
theorem cross_anticomm' (v w : Fin 3 → R) : v ×₃ w + w ×₃ v = 0 := by
  rw [add_eq_zero_iff_eq_neg, cross_anticomm]
#align cross_anticomm' cross_anticomm'

-- Adaptation note: nightly-2024-04-01
-- The simpNF linter now times out on this lemma,
-- likely due to https://github.com/leanprover/lean4/pull/3807
@[simp, nolint simpNF]
theorem cross_self (v : Fin 3 → R) : v ×₃ v = 0 := by
  simp [cross_apply, mul_comm]
#align cross_self cross_self

/-- The cross product of two vectors is perpendicular to the first vector. -/
-- Adaptation note: nightly-2024-04-01
-- The simpNF linter now times out on this lemma,
-- likely due to https://github.com/leanprover/lean4/pull/3807
@[simp 1100, nolint simpNF] -- Porting note: increase priority so that the LHS doesn't simplify
theorem dot_self_cross (v w : Fin 3 → R) : v ⬝ᵥ v ×₃ w = 0 := by
  rw [cross_apply, vec3_dotProduct]
  set_option tactic.skipAssignedInstances false in norm_num
  ring
#align dot_self_cross dot_self_cross

/-- The cross product of two vectors is perpendicular to the second vector. -/
-- Adaptation note: nightly-2024-04-01
-- The simpNF linter now times out on this lemma,
-- likely due to https://github.com/leanprover/lean4/pull/3807
@[simp 1100, nolint simpNF] -- Porting note: increase priority so that the LHS doesn't simplify
theorem dot_cross_self (v w : Fin 3 → R) : w ⬝ᵥ v ×₃ w = 0 := by
  rw [← cross_anticomm, Matrix.dotProduct_neg, dot_self_cross, neg_zero]
#align dot_cross_self dot_cross_self

/-- Cyclic permutations preserve the triple product. See also `triple_product_eq_det`. -/
theorem triple_product_permutation (u v w : Fin 3 → R) : u ⬝ᵥ v ×₃ w = v ⬝ᵥ w ×₃ u := by
  simp_rw [cross_apply, vec3_dotProduct]
  norm_num
  ring
#align triple_product_permutation triple_product_permutation

/-- The triple product of `u`, `v`, and `w` is equal to the determinant of the matrix
    with those vectors as its rows. -/
theorem triple_product_eq_det (u v w : Fin 3 → R) : u ⬝ᵥ v ×₃ w = Matrix.det ![u, v, w] := by
  rw [vec3_dotProduct, cross_apply, det_fin_three]
  norm_num
  ring
#align triple_product_eq_det triple_product_eq_det

/-- The scalar quadruple product identity, related to the Binet-Cauchy identity. -/
theorem cross_dot_cross (u v w x : Fin 3 → R) :
    u ×₃ v ⬝ᵥ w ×₃ x = u ⬝ᵥ w * v ⬝ᵥ x - u ⬝ᵥ x * v ⬝ᵥ w := by
  simp_rw [cross_apply, vec3_dotProduct]
  norm_num
  ring
#align cross_dot_cross cross_dot_cross

end ProductsProperties

section LeibnizProperties

/-- The cross product satisfies the Leibniz lie property. -/
theorem leibniz_cross (u v w : Fin 3 → R) : u ×₃ (v ×₃ w) = u ×₃ v ×₃ w + v ×₃ (u ×₃ w) := by
  simp_rw [cross_apply, vec3_add]
  apply vec3_eq <;> norm_num <;> ring
#align leibniz_cross leibniz_cross

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
#align cross.lie_ring Cross.lieRing

attribute [local instance] Cross.lieRing

theorem cross_cross (u v w : Fin 3 → R) : u ×₃ v ×₃ w = u ×₃ (v ×₃ w) - v ×₃ (u ×₃ w) :=
  lie_lie u v w
#align cross_cross cross_cross

/-- **Jacobi identity**: For a cross product of three vectors,
    their sum over the three even permutations is equal to the zero vector. -/
theorem jacobi_cross (u v w : Fin 3 → R) : u ×₃ (v ×₃ w) + v ×₃ (w ×₃ u) + w ×₃ (u ×₃ v) = 0 :=
  lie_jacobi u v w
#align jacobi_cross jacobi_cross

end LeibnizProperties
