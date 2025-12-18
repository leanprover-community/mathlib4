/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Tensor products of cones

Given ordered modules `M` and `N`, there are in general several distinct possible
orderings of the tensor product module `M ⊗ N`. Since the ordering of an ordered module
can be represented by its cone of nonnegative elements, there are likewise multiple
ways to construct a cone in `M ⊗ N` from cones in `M` and `N`. Such constructions
are referred to as tensor products of cones.

"Sufficiently nice" candidates for tensor products of cones are bounded by the minimal
and maximal tensor products. These products are generally distinct but coincide in special cases.

We define the minimal and maximal tensor products of pointed cones:

* `minTensorProduct C₁ C₂`: all conical combinations of elementary tensor products
  `x ⊗ₜ y` with `x ∈ C₁` and `y ∈ C₂`.
* `maxTensorProduct C₁ C₂`: the dual cone of the minimal tensor product of the dual cones.

## Main results

* `minTensorProduct_le_maxTensorProduct`: the minimal tensor product
  is less than or equal to the maximal tensor product

## Notation

* no special notation defined
* x, y, z are elements of the (original) cones
* φ, ψ are elements of the dual cones

## References

* [Aubrun et al. *Entangleability of cones*][aubrunEntangleabilityCones2021]

-/

@[expose] public section

open TensorProduct Module

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {G : Type*} [AddCommGroup G] [Module R G]
variable {H : Type*} [AddCommGroup H] [Module R H]

namespace PointedCone

/-- The minimal tensor product of two cones is given by all conical combinations of elementary
tensor products `x ⊗ₜ y` with `x ∈ C₁` and `y ∈ C₂`. -/
noncomputable def minTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    PointedCone R (G ⊗[R] H) :=
  .span R (.image2 (· ⊗ₜ[R] ·) C₁ C₂)

/-- The maximal tensor product of two cones is the dual (pointed cone) of the minimal tensor product
of the dual cones. -/
noncomputable def maxTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    PointedCone R (G ⊗[R] H) :=
  .dual (dualDistrib R G H) (minTensorProduct (.dual (dualPairing R G).flip C₁)
    (.dual (dualPairing R H).flip C₂))

/-- Characterization of the maximal tensor product: `z` lies in `maxTensorProduct C₁ C₂` iff
all pairings with elementary dual tensors are nonnegative. -/
@[simp]
theorem mem_maxTensorProduct {C₁ : PointedCone R G} {C₂ : PointedCone R H} {z : G ⊗[R] H} :
    z ∈ maxTensorProduct (R := R) C₁ C₂ ↔
      ∀ φ ∈ PointedCone.dual (dualPairing R G).flip C₁,
      ∀ ψ ∈ PointedCone.dual (dualPairing R H).flip C₂,
      0 ≤ dualDistrib R G H (φ ⊗ₜ[R] ψ) z := by
  simp only [maxTensorProduct, minTensorProduct, dual_span, mem_dual, Set.forall_mem_image2,
    SetLike.mem_coe, mem_dual, LinearMap.flip_apply, dualPairing_apply]

/-- Elementary tensors are members of the maximal tensor product. -/
theorem tmul_mem_maxTensorProduct {x y} {C₁ : PointedCone R G} {C₂ : PointedCone R H} (hx : x ∈ C₁)
    (hy : y ∈ C₂) : x ⊗ₜ[R] y ∈ maxTensorProduct C₁ C₂ := by
  simp only [mem_maxTensorProduct, dualDistrib_apply]
  exact fun φ hφ ψ hψ => mul_nonneg (hφ hx) (hψ hy)

/-- Elementary tensors are members of the minimal tensor product. -/
theorem tmul_mem_minTensorProduct {x y} {C₁ : PointedCone R G} {C₂ : PointedCone R H} (hx : x ∈ C₁)
    (hy : y ∈ C₂) : x ⊗ₜ[R] y ∈ minTensorProduct C₁ C₂ :=
  Submodule.subset_span (Set.mem_image2_of_mem hx hy)

/-- The maximal tensor product contains the set of all elementary tensors. -/
theorem tmul_subset_maxTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    .image2 (· ⊗ₜ[R] ·) C₁ C₂ ⊆ (maxTensorProduct C₁ C₂ : Set (G ⊗[R] H)) :=
  fun _ ⟨_, hx, _, hy, hz⟩ => hz ▸ tmul_mem_maxTensorProduct hx hy

/-- The minimal tensor product contains the set of all elementary tensors. -/
theorem tmul_subset_minTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    .image2 (· ⊗ₜ[R] ·) C₁ C₂ ⊆ (minTensorProduct C₁ C₂ : Set (G ⊗[R] H)) :=
  fun _ ⟨_, hx, _, hy, hz⟩ => hz ▸ tmul_mem_minTensorProduct hx hy

/-- The minimal tensor product is less than or equal to the maximal tensor product. -/
theorem minTensorProduct_le_maxTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    minTensorProduct C₁ C₂ ≤ maxTensorProduct C₁ C₂ := by
  exact Submodule.span_le.mpr (tmul_subset_maxTensorProduct C₁ C₂)

variable {C₁ : PointedCone R G} {C₂ : PointedCone R H} {z : G ⊗[R] H}

/-- A finite sum of elementary tensors is in minTensorProduct if each component is. -/
theorem sum_tmul_mem_minTensorProduct {ι : Type*} [Fintype ι]
    {x : ι → G} {y : ι → H} (hx : ∀ i, x i ∈ C₁) (hy : ∀ i, y i ∈ C₂) :
    ∑ i, x i ⊗ₜ[R] y i ∈ minTensorProduct C₁ C₂ :=
  Submodule.sum_mem _ fun i _ => tmul_mem_minTensorProduct (hx i) (hy i)

/-- Evaluating the left factor of `z ∈ maxTensorProduct C₁ C₂` at `φ ∈ C₁*`
yields an element in the double dual of `C₂`. -/
theorem maxTensorProduct_lid_rTensor_mem_dual_dual (hz : z ∈ maxTensorProduct C₁ C₂)
    (φ : Module.Dual R G) (hφ : φ ∈ dual (dualPairing R G).flip C₁) :
    TensorProduct.lid R H (φ.rTensor H z) ∈ dual (dualPairing R H)
      (dual (dualPairing R H).flip C₂) := by
  intro ψ hψ
  have h_eq (z : G ⊗[R] H) :
      ψ (TensorProduct.lid R H (φ.rTensor H z)) = dualDistrib R G H (φ ⊗ₜ[R] ψ) z := by
    induction z <;> simp_all
  rw [dualPairing_apply, h_eq, mem_maxTensorProduct] at *
  exact hz φ hφ ψ hψ

/-- Evaluating the right factor of `z ∈ maxTensorProduct C₁ C₂` at `ψ ∈ C₂*`
yields an element in the double dual of `C₁`. -/
theorem maxTensorProduct_rid_lTensor_mem_dual_dual (hz : z ∈ maxTensorProduct C₁ C₂)
    (ψ : Module.Dual R H) (hψ : ψ ∈ dual (dualPairing R H).flip C₂) :
    TensorProduct.rid R G (ψ.lTensor G z) ∈ dual (dualPairing R G)
      (dual (dualPairing R G).flip C₁) := by
  intro φ hφ
  have h_eq (z : G ⊗[R] H) :
      φ (TensorProduct.rid R G (ψ.lTensor G z)) = dualDistrib R G H (φ ⊗ₜ[R] ψ) z := by
    induction z <;> simp_all [dualDistrib_apply, mul_comm, map_add]
  rw [dualPairing_apply, h_eq, mem_maxTensorProduct] at *
  exact hz φ hφ ψ hψ

/-- The minimal tensor product is commutative. -/
@[simp]
theorem minTensorProduct_comm :
    (minTensorProduct C₁ C₂).map (TensorProduct.comm R G H) = minTensorProduct C₂ C₁ := by
  simp only [minTensorProduct, map, span, Submodule.map_span, Set.image_image2,
    LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, TensorProduct.comm_tmul,
    Set.image2_swap (· ⊗ₜ[R] · : H → G → _)]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- Helper lemma: swapping order of duals and tensor product preserves evaluation. -/
private lemma dualDistrib_comm_swap {M N : Type*} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (φ : Dual R M) (ψ : Dual R N) (z : M ⊗[R] N) :
    dualDistrib R N M (ψ ⊗ₜ[R] φ) ((TensorProduct.comm R M N) z) =
      dualDistrib R M N (φ ⊗ₜ[R] ψ) z := by
  induction z <;> simp_all [mul_comm]

/-- The maximal tensor product is commutative. -/
@[simp]
theorem maxTensorProduct_comm :
    (maxTensorProduct C₁ C₂).map (TensorProduct.comm R G H) = maxTensorProduct C₂ C₁ := by
  ext z
  simp only [mem_map, mem_maxTensorProduct]
  constructor
  · rintro ⟨w, hw, rfl⟩ ψ hψ φ hφ
    simpa only [LinearEquiv.coe_coe, dualDistrib_comm_swap] using hw φ hφ ψ hψ
  · intro hz
    refine ⟨(TensorProduct.comm R H G) z, ?_, (TensorProduct.comm R H G).symm_apply_apply z⟩
    intro φ hφ ψ hψ
    simpa only [dualDistrib_comm_swap] using hz ψ hψ φ hφ

end PointedCone
