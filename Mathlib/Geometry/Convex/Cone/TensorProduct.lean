/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
import Mathlib.Geometry.Convex.Cone.ConicalHull
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Tensor product of cones

The ordering of the tensor product of ordered modules is not uniquely defined by the
tensor product of modules. Orderings can be expressed as (salient pointed) cones
(representing the positive elements). Therefore, equivalently to the above, the definition
of the tensor product of convex cones is not uniquely specified by the tensor product of
modules. "Sufficiently nice" candidates for tensor products of cones are bounded by
the minimal tensor product and the maximal tensor product. These are the analogues
of the injective and projective tensor products in the theory of operator algebras.

We define the minimal and maximal tensor products of two pointed cones:

'minTensorProduct C₁ C₂'
'maxTensorProduct C₁ C₂'

We use "algebraicDual" as a convenient abbreviation for the general
PointedCone.dual

## Main results

- `minTensorProduct_le_maxTensorProduct`: the minimal tensor product
  is less than or equal to the maximal tensor product

## ToDo

The minimal and maximal tensor product are only equal when one or both cones are simplices.

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

/-- The algebraic dual of a pointed cone C (as opposed to "the inner product dual") are the
elements of the dual module that are non-negative on all of C, i.e., linear maps φ: C → K,
such that 0 ≤ φ(x) for all x in C. The algebraic dual is a pointed cone. This abbreviation
is a concrete instance of the more general PointedCone.dual -/
abbrev algebraicDual (C : PointedCone K G) : PointedCone K (Dual K G) :=
      PointedCone.dual (Module.dualPairing K G).flip C.carrier

/-- The set of elementary tensor products from two cones: all tensors of the form x ⊗ₜ y
where x ∈ C₁ and y ∈ C₂. This forms the generating set for the minimal tensor product. -/
def elementaryTensors (C₁ : PointedCone K G) (C₂ : PointedCone K H) : Set (G ⊗[K] H) :=
  {z | ∃ x y, x ∈ C₁ ∧ y ∈ C₂ ∧ z = x ⊗ₜ[K] y}

/-- The minimal tensor product of two cones is given by all conical combinations of elementary
tensor products x ⊗ₜ y of cone elements. -/
noncomputable def minTensorProduct (C₁ : PointedCone K G) (C₂ : PointedCone K H)
    : PointedCone K (G ⊗[K] H) :=
  conicalHull K (elementaryTensors C₁ C₂)

/-- The maximal tensor product is the set of elements of the module tensor product
space for which all elementary tensor products of dual cone elements φ₁ ⊗ₜ φ₂ are non-negative. -/
noncomputable def maxTensorProduct (C₁ : PointedCone K G) (C₂ : PointedCone K H)
    : PointedCone K (G ⊗[K] H) where
  -- All elements z for which all (φ₁ ⊗ₜ φ₂) are non-negative
  carrier :=
    {z : G ⊗[K] H | ∀ (φ₁ : Dual K G)(φ₂ : Dual K H),
      φ₁ ∈ algebraicDual C₁ → φ₂ ∈ algebraicDual C₂ →
      0 ≤ dualDistrib K G H (φ₁ ⊗ₜ[K] φ₂) z}
  -- Follows direct from (φ₁ ⊗ₜ[K] φ₂) 0 = 0
  zero_mem' := by simp
  smul_mem' := fun c₁ x₁ hx₁ φ₁ φ₂ hφ₁ hφ₂ => by
    -- Both factors are nonnegative (make explicit and solve by mul_nonneg)
    have h_pos_c₁ : 0 ≤ (c₁ : K) := c₁.property
    have h_pos_dual : 0 ≤ dualDistrib K G H (φ₁ ⊗ₜ[K] φ₂) x₁ := hx₁ φ₁ φ₂ hφ₁ hφ₂
    simp only [map_smul_of_tower]
    exact mul_nonneg h_pos_c₁ h_pos_dual
  add_mem' := by
    intro z₁ z₂ hz₁ hz₂ φ₁ φ₂ hφ₁ hφ₂
    -- Both terms are nonnegative (make explicit and solve by positivity)
    have h_pos_z₁ : 0 ≤ dualDistrib K G H (φ₁ ⊗ₜ[K] φ₂) z₁ := hz₁ φ₁ φ₂ hφ₁ hφ₂
    have h_pos_z₂ : 0 ≤ dualDistrib K G H (φ₁ ⊗ₜ[K] φ₂) z₂ := hz₂ φ₁ φ₂ hφ₁ hφ₂
    simp [map_add]
    positivity

/-- Individual elementary tensors are in the maximal tensor product. -/
theorem tmul_mem_maxTensorProduct {x y} {C₁ : PointedCone K G} {C₂ : PointedCone K H} (hx : x ∈ C₁)
    (hy : y ∈ C₂) : x ⊗ₜ[K] y ∈ maxTensorProduct C₁ C₂ := by
  intro φ₁ φ₂ hφ₁ hφ₂
  simp only [dualDistrib_apply]
  -- Both factors are nonnegative (make explicit and solve by positivity)
  have h_pos_φ₁ : 0 ≤ φ₁ x := hφ₁ hx
  have h_pos_φ₂ : 0 ≤ φ₂ y := hφ₂ hy
  positivity

/-- The maximal tensor product contains the set of all elementary tensors. -/
theorem elementaryTensors_subset_maxTensorProduct (C₁ : PointedCone K G) (C₂ : PointedCone K H) :
    elementaryTensors C₁ C₂ ⊆ maxTensorProduct C₁ C₂ :=
  fun _ ⟨_, _, hx, hy, hw⟩ => hw ▸ tmul_mem_maxTensorProduct hx hy

/-- The minimal tensor product is less than or equal to the maximal tensor product. -/
theorem minTensorProduct_le_maxTensorProduct (C₁ : PointedCone K G) (C₂ : PointedCone K H)
    : minTensorProduct C₁ C₂ ≤ maxTensorProduct C₁ C₂ := by
  intro z hz
  obtain ⟨n, c, v, hv, hc, rfl⟩ := hz
  -- minTensorProduct = all conical combinations of elementary tensors
  -- maxTensorProduct contains all elementary tensors, hence it contains all conical combinations
  exact conical_comb_mem K (elementaryTensors C₁ C₂) c v hv hc (maxTensorProduct C₁ C₂)
    (elementaryTensors_subset_maxTensorProduct C₁ C₂)

end PointedCone
