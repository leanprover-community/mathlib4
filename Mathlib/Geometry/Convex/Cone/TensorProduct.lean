/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
import Mathlib.Geometry.Convex.Cone.ConicalHull
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Tensor product of cones

The ordering of the tensor product of ordered modules
is not uniquely defined by the tensor product of modules.
Orderings can be expressed as (salient pointed) cones (representing the positive elements).
Therefore, equivalently to the above, the definition of the tensor product of convex cones
is not uniquely specified by the tensor product of modules.
"Sufficiently nice" candidates for tensor products of cones are
bounded by the minimal tensor product and the maximal tensor product.

We define the algebraic dual of a cone (which is independent of an inner product),
and define the minimal and maximal tensor products of two pointed cones:

'algebraicDual C': the algebraic dual of the pointed cone 'C'
'minTensorProduct C₁ C₂'
'maxTensorProduct C₁ C₂'

## Main results

- `minTensorProduct_le_maxTensorProduct`: the minimal tensor product
  is less than or equal to the maximal tensor product

## ToDo

The minimal and maximal tensor product are only equal when one or both cones are simplicies.

## Notation

- no special notation defined
- x, y, z are elements of the (original) cones
- φ, φ₁, φ₂ are elements of the dual cones

## References

[Aubrun et al. "Entangleability of cones"] Geom. Funct. Anal. Vol. 31 (2021) 181–205
available as https://arxiv.org/abs/1911.09663

-/

open Set Module Convex ConicalCombination TensorProduct LinearMap
open scoped TensorProduct

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {G : Type*} [AddCommGroup G] [Module K G]
variable {H : Type*} [AddCommGroup H] [Module K H]

namespace PointedCone

/-- The algebraic dual of a pointed cone C (as opposed to "the inner product dual")
are the elements of the dual module that are non-negative on all of C,
i.e., linear maps φ: C → K, such that 0 ≤ φ(x) for all x in C.
The algebraic dual is a pointed cone. -/
def algebraicDual (C : PointedCone K G) : PointedCone K (Dual K G) where
  carrier := {φ : Dual K G | ∀ x ∈ C, 0 ≤ φ x}
  zero_mem' := by
    intro x hx
    rw [zero_apply]
  smul_mem' := by
    intro c x hx g hg
    rw [← Nonneg.coe_smul, smul_apply]
    simp only [smul_eq_mul]
    rw [mul_nonneg_iff]
    left
    constructor
    · exact c.property
    · exact hx g hg
  add_mem' := by
    intro φ₁ φ₂ hφ₁ hφ₂ x hx
    rw [add_apply]
    exact add_nonneg (hφ₁ x hx) (hφ₂ x hx)

/-- The minimal tensor product of two cones is given by
all conical combinations of elementary tensor products x ⊗ₜ y
of cone elements. -/
noncomputable def minTensorProduct (C₁ : PointedCone K G) (C₂ : PointedCone K H)
    : PointedCone K (G ⊗[K] H) :=
  conicalHull K {z | ∃ x y, x ∈ C₁ ∧ y ∈ C₂ ∧ z = x ⊗ₜ[K] y}

/-- The maximal tensor product is given by the set of
all elements of the module tensor product space for which
all elementary tensor products of dual cone elements φ₁ ⊗ₜ φ₂
are positive. -/
noncomputable def maxTensorProduct (C₁ : PointedCone K G) (C₂ : PointedCone K H)
    : PointedCone K (G ⊗[K] H) where
  carrier :=
    {z : G ⊗[K] H | ∀ (φ₁ : Dual K G)(φ₂ : Dual K H),
      φ₁ ∈ (algebraicDual C₁) → φ₂ ∈ (algebraicDual C₂) →
      0 ≤ dualDistrib K G H (φ₁ ⊗ₜ[K] φ₂) z}
  zero_mem' := by
    intro m n hm hnm
    rw [map_zero]
  smul_mem' := by
    intro c z hz φ₁ φ₂ hφ₁ hφ₂
    simp only [map_smul_of_tower]
    simp only [mem_setOf_eq] at hz
    exact smul_nonneg (zero_le c) (hz φ₁ φ₂ hφ₁ hφ₂)
  add_mem' := by
    intro z₁ z₂ hz₁ hz₂ φ₁ φ₂ hφ₁ hφ₂
    rw [map_add]
    exact add_nonneg (hz₁ φ₁ φ₂ hφ₁ hφ₂) (hz₂ φ₁ φ₂ hφ₁ hφ₂)

/-- The minimal tensor product is less than or equal to the maximal tensor product. -/
theorem minTensorProduct_le_maxTensorProduct (C₁ : PointedCone K G) (C₂ : PointedCone K H)
    : (minTensorProduct C₁ C₂) ≤ (maxTensorProduct C₁ C₂)
    := by
  intro z h
  obtain ⟨n, c, v, hv, hc, hz⟩ := h
  intro φ₁ φ₂ hφ₁ hφ₂
  rw [hz, map_sum]
  apply Finset.sum_nonneg
  intro i _
  let T_mn := dualDistrib K G H (φ₁ ⊗ₜ[K] φ₂)
  rw [map_smul_of_tower T_mn (c i) (v i)]
  have hxy : ∃ x y, x ∈ C₁ ∧ y ∈ C₂ ∧ v i = x ⊗ₜ[K] y := hv i
  obtain ⟨x, y, hx, hy, hvi⟩ := hxy
  rw [hvi, dualDistrib_apply]
  exact mul_nonneg (hc i) (mul_nonneg (hφ₁ x hx) (hφ₂ y hy))

end PointedCone
