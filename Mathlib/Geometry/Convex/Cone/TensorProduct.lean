/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
import Mathlib.Geometry.Convex.Cone.Dual
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Tensor product of cones

The ordering of the tensor product of ordered modules is not uniquely defined by the
tensor product of modules. Orderings can be expressed as (salient pointed) cones
(representing the nonnegative elements). Therefore, equivalently to the above, the definition
of the tensor product of convex cones is not uniquely specified by the tensor product of
modules. "Sufficiently nice" candidates for tensor products of cones are bounded by
the minimal tensor product and the maximal tensor product. These are the analogues
of the injective and projective tensor products in the theory of operator algebras.

We define the minimal and maximal tensor products of two pointed cones:

* `minTensorProduct C₁ C₂`: all conical combinations of elementary tensor products x ⊗ₜ y
  of cone elements x and y.
* `maxTensorProduct C₁ C₂`: the dual of the minimal tensor product of the dual cones.

## Main results

* `minTensorProduct_le_maxTensorProduct`: the minimal tensor product
  is less than or equal to the maximal tensor product

## Notation

* no special notation defined
* x, y, z are elements of the (original) cones
* φ, φ₁, φ₂ are elements of the dual cones

## References

* [Aubrun et al. *Entangleability of cones*][aubrunEntangleabilityCones2021]

-/

open Set Module Convex TensorProduct LinearMap
open scoped TensorProduct

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {G : Type*} [AddCommGroup G] [Module K G]
variable {H : Type*} [AddCommGroup H] [Module K H]

namespace PointedCone

/-- The minimal tensor product of two cones is given by all conical combinations of elementary
tensor products x ⊗ₜ y of cone elements x and y. -/
noncomputable def minTensorProduct (C₁ : PointedCone K G) (C₂ : PointedCone K H)
    : PointedCone K (G ⊗[K] H) :=
  .span K {z | ∃ x y, x ∈ C₁ ∧ y ∈ C₂ ∧ z = x ⊗ₜ[K] y}

/-- The maximal tensor product is the (algebraic) dual of the minimal tensor product
of the dual cones. -/
noncomputable def maxTensorProduct (C₁ : PointedCone K G) (C₂ : PointedCone K H)
    : PointedCone K (G ⊗[K] H) :=
  .dual
    (dualDistrib K G H)
    (minTensorProduct
      (.dual (Module.dualPairing K G).flip C₁.carrier)
      (.dual (Module.dualPairing K H).flip C₂.carrier)).carrier

/-- Characterization of the maximal tensor product: `z` lies in
`maxTensorProduct C₁ C₂` iff all pairings with elementary dual tensors are nonnegative. -/
theorem mem_maxTensorProduct_iff
    {C₁ : PointedCone K G} {C₂ : PointedCone K H} {z : G ⊗[K] H} :
    z ∈ maxTensorProduct (K:=K) C₁ C₂ ↔
      ∀ φ ∈ PointedCone.dual (Module.dualPairing K G).flip C₁.carrier,
      ∀ ψ ∈ PointedCone.dual (Module.dualPairing K H).flip C₂.carrier,
        0 ≤ (dualDistrib K G H (φ ⊗ₜ[K] ψ)) z := by
  constructor
  · intro hz φ hφ ψ hψ
    have h : ∀ x φ' (hφ' : φ' ∈ PointedCone.dual (Module.dualPairing K G).flip C₁.carrier) ψ'
        (hψ' : ψ' ∈ PointedCone.dual (Module.dualPairing K H).flip C₂.carrier),
        x = φ' ⊗ₜ ψ' → 0 ≤ (dualDistrib K G H x) z := by
      simpa [maxTensorProduct, minTensorProduct, PointedCone.mem_dual, PointedCone.dual_span]
        using hz
    exact h _ φ hφ ψ hψ rfl
  · intro h
    simpa [maxTensorProduct, minTensorProduct, PointedCone.mem_dual, PointedCone.dual_span] using
      fun x φ hφ ψ hψ (hx : x = φ ⊗ₜ ψ) => hx ▸ h φ hφ ψ hψ

/-- Individual elementary tensors are in the maximal tensor product. -/
theorem tmul_mem_maxTensorProduct {x y} {C₁ : PointedCone K G} {C₂ : PointedCone K H} (hx : x ∈ C₁)
    (hy : y ∈ C₂) : x ⊗ₜ[K] y ∈ maxTensorProduct C₁ C₂ := by
  rw [mem_maxTensorProduct_iff]
  intro φ hφ ψ hψ
  simp only [dualDistrib_apply]
  exact mul_nonneg (hφ hx) (hψ hy)

/-- Individual elementary tensors are in the minimal tensor product. -/
theorem tmul_mem_minTensorProduct {x y} {C₁ : PointedCone K G} {C₂ : PointedCone K H} (hx : x ∈ C₁)
    (hy : y ∈ C₂) : x ⊗ₜ[K] y ∈ minTensorProduct C₁ C₂ := by
  apply Submodule.subset_span
  exact ⟨x, y, hx, hy, rfl⟩

/-- The maximal tensor product contains the set of all elementary tensors. -/
theorem tmul_subset_maxTensorProduct (C₁ : PointedCone K G) (C₂ : PointedCone K H) :
    {z | ∃ x y, x ∈ C₁ ∧ y ∈ C₂ ∧ z = x ⊗ₜ[K] y} ⊆ maxTensorProduct C₁ C₂ :=
  fun _ ⟨_, _, hx, hy, hw⟩ => hw ▸ tmul_mem_maxTensorProduct hx hy

/-- The minimal tensor product is less than or equal to the maximal tensor product. -/
theorem minTensorProduct_le_maxTensorProduct (C₁ : PointedCone K G) (C₂ : PointedCone K H)
    : minTensorProduct C₁ C₂ ≤ maxTensorProduct C₁ C₂ := by
  exact Submodule.span_le.mpr (tmul_subset_maxTensorProduct C₁ C₂)

end PointedCone
