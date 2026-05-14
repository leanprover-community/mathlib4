/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Geometry.Convex.Cone.Dual
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.NAry
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

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
  .hull R (.image2 (· ⊗ₜ[R] ·) C₁ C₂)

/-- The maximal tensor product of two cones is the dual (pointed cone) of the minimal tensor product
of the dual cones. -/
noncomputable def maxTensorProduct (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    PointedCone R (G ⊗[R] H) :=
  .dual (dualDistrib R G H) (minTensorProduct (.dual (Dual.eval R G) C₁)
    (.dual (Dual.eval R H) C₂))

/-- Characterization of the maximal tensor product: `z` lies in `maxTensorProduct C₁ C₂` iff
all pairings with elementary dual tensors are nonnegative. -/
@[simp]
theorem mem_maxTensorProduct {C₁ : PointedCone R G} {C₂ : PointedCone R H} {z : G ⊗[R] H} :
    z ∈ maxTensorProduct (R := R) C₁ C₂ ↔
      ∀ φ ∈ PointedCone.dual (Dual.eval R G) C₁,
      ∀ ψ ∈ PointedCone.dual (Dual.eval R H) C₂,
      0 ≤ dualDistrib R G H (φ ⊗ₜ[R] ψ) z := by
  simp only [maxTensorProduct, minTensorProduct, dual_hull, mem_dual, Set.forall_mem_image2,
    SetLike.mem_coe, mem_dual]

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

variable {C₁ C₁' : PointedCone R G} {C₂ C₂' : PointedCone R H} {z : G ⊗[R] H}

/-- The minimal tensor product is commutative. -/
@[simp]
theorem minTensorProduct_comm :
    (minTensorProduct C₁ C₂).map (TensorProduct.comm R G H) = minTensorProduct C₂ C₁ := by
  simp [minTensorProduct, map, hull, Submodule.map_span, Set.image_image2,
    Set.image2_swap (· ⊗ₜ[R] · : H → G → _)]

/-- The maximal tensor product is commutative. -/
@[simp]
theorem maxTensorProduct_comm :
    (maxTensorProduct C₁ C₂).map (TensorProduct.comm R G H) = maxTensorProduct C₂ C₁ := by
  ext z
  simp only [mem_map, mem_maxTensorProduct]
  refine ⟨?_, fun hz ↦
    ⟨(TensorProduct.comm R H G) z, ?_, (TensorProduct.comm R H G).symm_apply_apply z⟩⟩
  · rintro ⟨w, hw, rfl⟩ ψ hψ φ hφ
    simpa [dualDistrib_apply_comm] using hw φ hφ ψ hψ
  · intro φ hφ ψ hψ
    simpa [dualDistrib_apply_comm] using hz ψ hψ φ hφ

/-- `minTensorProduct` is monotone. -/
@[gcongr]
theorem minTensorProduct_mono (h₁ : C₁ ≤ C₁') (h₂ : C₂ ≤ C₂') :
    minTensorProduct C₁ C₂ ≤ minTensorProduct C₁' C₂' :=
  Submodule.span_mono <| Set.image2_subset h₁ h₂

/-- `maxTensorProduct` is monotone. -/
theorem maxTensorProduct_mono (h₁ : C₁ ≤ C₁') (h₂ : C₂ ≤ C₂') :
    maxTensorProduct C₁ C₂ ≤ maxTensorProduct C₁' C₂' :=
  fun _ hz => mem_maxTensorProduct.mpr fun φ hφ ψ hψ =>
    mem_maxTensorProduct.mp hz φ (dual_le_dual h₁ hφ) ψ (dual_le_dual h₂ hψ)

variable {G' H' : Type*} [AddCommGroup G'] [Module R G'] [AddCommGroup H'] [Module R H']

/-- `minTensorProduct` is functorial: the image of a minimal tensor product under
`TensorProduct.map f g` is contained in the minimal tensor product of the images. -/
theorem minTensorProduct_map_le (f : G →ₗ[R] G') (g : H →ₗ[R] H')
    (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    (minTensorProduct C₁ C₂).map (TensorProduct.map f g) ≤
      minTensorProduct (C₁.map f) (C₂.map g) :=
  (Submodule.map_span_le _ _ _).mpr fun _ ⟨x, hx, y, hy, h⟩ ↦
    h ▸ map_tmul f g x y ▸ tmul_mem_minTensorProduct ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩

/-- `maxTensorProduct` is functorial: the image of a maximal tensor product under
`TensorProduct.map f g` is contained in the maximal tensor product of the images. -/
theorem maxTensorProduct_map_le (f : G →ₗ[R] G') (g : H →ₗ[R] H')
    (C₁ : PointedCone R G) (C₂ : PointedCone R H) :
    (maxTensorProduct C₁ C₂).map (TensorProduct.map f g) ≤
      maxTensorProduct (C₁.map f) (C₂.map g) := by
  rintro _ ⟨w, hw, rfl⟩
  simp only [SetLike.mem_coe, mem_maxTensorProduct] at hw ⊢
  intro φ hφ ψ hψ
  have h_eq : ((dualDistrib R G' H') (φ ⊗ₜ[R] ψ)).comp (TensorProduct.map f g) =
      ((dualDistrib R G H) ((φ.comp f) ⊗ₜ[R] (ψ.comp g))) :=
    TensorProduct.ext' fun x y ↦ by simp [map_tmul]
  convert hw (φ.comp f) (fun x hx ↦ hφ ⟨x, hx, rfl⟩) (ψ.comp g) (fun y hy ↦ hψ ⟨y, hy, rfl⟩)
  exact DFunLike.congr_fun h_eq w

end PointedCone
