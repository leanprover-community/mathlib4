/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Analysis.Convex.Cone.Basic
public import Mathlib.Geometry.Convex.Cone.Simplicial
public import Mathlib.Geometry.Convex.Cone.TensorProduct
public import Mathlib.Topology.Algebra.Module.LocallyConvex

import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Topology.Algebra.Module.TopDualPairing

/-!
# Tensor Products of Pointed Cones

For a simplicial cone in a real vector space and a closed cone (`ProperCone`) in a
finite-dimensional real topological vector space, this file proves that the minimal and maximal
tensor products are equal if and only if the simplicial cone is generating or the closed cone is
salient (`IsPointed`, i.e., contains no line).

The main theorem is an equivalence to a disjunction. This is to allow
non-generating simplicial cones. This requires that the closed cone be salient.

The generating condition concerns the ambient space rather than the cone: the minimal tensor
product does not depend on the ambient space of the simplicial cone, but the maximal one does. If
the simplicial cone is not generating and the closed cone contains a line, then the maximal tensor
product contains tensors `e ⊗ₜ l`, with `e` outside the span of the simplicial cone and `l ≠ 0` on
that line. Such tensors are not in the minimal tensor product.

Finite-dimensionality of the ambient space of the closed cone is by explicit declaration and is
required for the `topDualPairing_isContPerfPair` instance (in
`Topology.Algebra.Module.TopDualPairing`).

This file uses `topDualPairing` (the canonical pairing of a vector space and its topological dual)
to avoid explicit topology assumptions on `Module.Dual`.

The proof relies on the following result:

* **Bipolar theorem** (`ProperCone.dual_dual_flip`): The double dual of a closed cone is itself.

This requires:
- Local convexity and Hausdorff separation (for Hahn-Banach)
- A continuous perfect pairing between the module and its dual.

## Main results

* `PointedCone.minTensorProduct_eq_max_iff_of_simplicial_left` and `_right`: for a simplicial cone
  and a closed cone, the minimal and maximal tensor products are equal if and only if the
  simplicial cone is generating or the closed cone is salient.

* `PointedCone.minTensorProduct_eq_max_of_simplicial_generating_left` and `_right`: the minimal
  and maximal tensor products of a simplicial and generating cone and a closed cone are equal.

## References

* [Aubrun et al. *Entangleability of cones*][aubrunEntangleabilityCones2021]
-/

public section

/-! ### Equality of minimal and maximal tensor products -/

namespace PointedCone

section BasisCoordDual

variable {R M : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

open Module

/-- If a pointed cone `C` is contained in the conic hull of a basis `b`, then the coordinate
functionals of `b` lie in the dual cone of `C`. -/
lemma basis_coord_mem_dual {ι : Type*} (b : Basis ι R M) (C : PointedCone R M)
    (hC : (C : Set M) ⊆ (hull R (Set.range b) : Set M)) (i : ι) :
    b.coord i ∈ dual (Dual.eval R M) (C : Set M) := by
  classical
  refine dual_le_dual hC ?_
  simp [Finsupp.single_apply, ite_nonneg zero_le_one le_rfl]

end BasisCoordDual

section MainTheorems

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

variable [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F]
variable [FiniteDimensional ℝ F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]

open TensorProduct Module

/-- If `z` lies in the maximal tensor product of a cone `C₁` and a closed cone `C₂`, and the
functional `f` is nonnegative on `C₁`, then applying `f` to the left factor of `z` gives an
element of `C₂`. -/
lemma lid_rTensor_mem_of_mem_maxTensorProduct {C₁ : PointedCone ℝ E} {C₂ : ProperCone ℝ F}
    {z : E ⊗[ℝ] F} (hz : z ∈ maxTensorProduct C₁ C₂.toPointedCone) {f : Dual ℝ E}
    (hf : f ∈ dual (Dual.eval ℝ E) (C₁ : Set E)) :
    TensorProduct.lid ℝ F (f.rTensor F z) ∈ C₂ := by
  rw [← ProperCone.dual_dual_flip (topDualPairing ℝ F) C₂]
  intro g (hg : (g : F →ₗ[ℝ] ℝ) ∈ dual (Dual.eval ℝ F) (C₂ : Set F))
  have h := mem_maxTensorProduct.mp hz f hf g hg
  have h_eq : dualDistrib ℝ E F (f ⊗ₜ (g : F →ₗ[ℝ] ℝ)) =
      (g : F →ₗ[ℝ] ℝ) ∘ₗ (TensorProduct.lid ℝ F) ∘ₗ f.rTensor F := by
    ext; simp
  simpa only [h_eq, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap] using! h

/-- If `C₁` is a simplicial cone and `C₂` is a closed cone, then their minimal and maximal tensor
products are equal if and only if `C₁` is generating or `C₂` is salient. -/
theorem minTensorProduct_eq_max_iff_of_simplicial_left (C₁ : PointedCone ℝ E)
    (C₂ : ProperCone ℝ F) (h₁ : C₁.IsSimplicial) :
    minTensorProduct C₁ C₂.toPointedCone = maxTensorProduct C₁ C₂.toPointedCone ↔
      Submodule.span ℝ (C₁ : Set E) = ⊤ ∨ C₂.IsPointed := by
  classical
  obtain ⟨s, -, hs, rfl⟩ := h₁
  rw [Submodule.span_span_of_tower]
  -- Extend the generators of `C₁` to a basis `b`.
  let b := Basis.extend hs
  have hsb : s ⊆ Set.range b := by
    rw [Basis.range_extend]
    exact Basis.subset_extend hs
  -- If `b i` is not a generator of `C₁`, then `b.coord i` vanishes on the span of `C₁`.
  have hb : ∀ i, b i ∉ s → ∀ x ∈ Submodule.span ℝ s, b.coord i x = 0 := by
    intro i his x hx
    rw [← Set.image_preimage_eq_of_subset hsb] at hx
    exact Finsupp.notMem_support_iff.mp fun h ↦ his (b.repr_support_subset_of_mem_span _ hx h)
  refine ⟨fun h ↦ ?_, fun h ↦ le_antisymm (minTensorProduct_le_maxTensorProduct _ _) fun z hz ↦ ?_⟩
  · by_contra! hn
    obtain ⟨hgen, hsal⟩ := hn
    -- Some vector `b i` of the basis is not a generator of `C₁`.
    obtain ⟨i, his⟩ : ∃ i, b i ∉ s := by
      by_contra! hall
      exact hgen (eq_top_iff.mpr (b.span_eq ▸ Submodule.span_mono (Set.range_subset_iff.mpr hall)))
    -- Some nonzero `l` lies in `C₂` together with `-l`.
    obtain ⟨l, hl, hl', hl0⟩ : ∃ l, l ∈ C₂ ∧ -l ∈ C₂ ∧ l ≠ 0 := by
      by_contra! hcon
      exact hsal hcon
    -- The tensor `b i ⊗ₜ l` lies in the maximal tensor product.
    have hmax : b i ⊗ₜ l ∈ maxTensorProduct (hull ℝ s) C₂.toPointedCone := by
      refine mem_maxTensorProduct.mpr fun f _ g hg ↦ ?_
      have hgl : g l = 0 := le_antisymm (by simpa using hg hl') (hg hl)
      simp [hgl]
    -- The map `z ↦ (b.coord i ⊗ id) z` vanishes on the minimal tensor product, but not at
    -- `b i ⊗ₜ l`.
    let T : E ⊗[ℝ] F →ₗ[ℝ] F := (TensorProduct.lid ℝ F).toLinearMap ∘ₗ (b.coord i).rTensor F
    have hT : minTensorProduct (hull ℝ s) C₂.toPointedCone ≤
        (LinearMap.ker T).restrictScalars {c : ℝ // 0 ≤ c} := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨x, hx, y, -, rfl⟩
      simp [T, hb i his x (hull_le_span ℝ s hx)]
    have hTl : T (b i ⊗ₜ l) = 0 := hT (h ▸ hmax)
    exact hl0 (by simpa [T, LinearMap.rTensor_tmul] using hTl)
  · -- Write `z = ∑ i, b i ⊗ₜ y i`.
    rw [← (equivFinsuppOfBasisLeft b).symm_apply_apply z, equivFinsuppOfBasisLeft_symm_apply]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [equivFinsuppOfBasisLeft_apply]
    have hi : b.coord i ∈ dual (Dual.eval ℝ E) (hull ℝ s : Set E) :=
      basis_coord_mem_dual b _ (Submodule.span_mono hsb) i
    have hy := lid_rTensor_mem_of_mem_maxTensorProduct hz hi
    by_cases his : b i ∈ s
    · -- If `b i` is a generator of `C₁`, then `y i` lies in `C₂`.
      exact tmul_mem_minTensorProduct (subset_hull his) hy
    obtain hgen | hsal := h
    · -- Otherwise `b.coord i` vanishes on the span of `C₁`, which is impossible if `C₁` is
      -- generating.
      exact absurd (hb i his (b i) (hgen ▸ Submodule.mem_top)) (by simp)
    · -- If `C₂` is salient, then `y i = 0`, since `y i` and `-y i` lie in `C₂`.
      have hi' : -b.coord i ∈ dual (Dual.eval ℝ E) (hull ℝ s : Set E) :=
        fun x hx ↦ by simp [hb i his x (hull_le_span ℝ s hx)]
      have hy' := lid_rTensor_mem_of_mem_maxTensorProduct hz hi'
      rw [LinearMap.rTensor_neg, LinearMap.neg_apply, map_neg] at hy'
      simp [hsal _ hy hy']

/-- If `C₁` is a closed cone and `C₂` is a simplicial cone, then their minimal and maximal tensor
products are equal if and only if `C₂` is generating or `C₁` is salient. -/
theorem minTensorProduct_eq_max_iff_of_simplicial_right (C₁ : ProperCone ℝ F)
    (C₂ : PointedCone ℝ E) (h₂ : C₂.IsSimplicial) :
    minTensorProduct C₁.toPointedCone C₂ = maxTensorProduct C₁.toPointedCone C₂ ↔
      Submodule.span ℝ (C₂ : Set E) = ⊤ ∨ C₁.IsPointed := by
  rw [← minTensorProduct_eq_max_iff_of_simplicial_left C₂ C₁ h₂]
  constructor <;> intro h <;> rw [← minTensorProduct_comm, h, maxTensorProduct_comm]

/-- If `C₁` is a simplicial and generating cone and `C₂` is a closed cone, then their minimal
and maximal tensor products are equal. -/
theorem minTensorProduct_eq_max_of_simplicial_generating_left (C₁ : PointedCone ℝ E)
    (C₂ : ProperCone ℝ F) (h₁_simp : C₁.IsSimplicial) (h₁_gen : Submodule.span ℝ (C₁ : Set E) = ⊤) :
    minTensorProduct C₁ C₂.toPointedCone = maxTensorProduct C₁ C₂.toPointedCone :=
  (minTensorProduct_eq_max_iff_of_simplicial_left C₁ C₂ h₁_simp).mpr (.inl h₁_gen)

/-- If `C₁` is a closed cone and `C₂` is a simplicial and generating cone, then their minimal
and maximal tensor products are equal. -/
theorem minTensorProduct_eq_max_of_simplicial_generating_right (C₁ : ProperCone ℝ F)
    (C₂ : PointedCone ℝ E) (h₂_simp : C₂.IsSimplicial)
    (h₂_gen : Submodule.span ℝ (C₂ : Set E) = ⊤) :
    minTensorProduct C₁.toPointedCone C₂ = maxTensorProduct C₁.toPointedCone C₂ :=
  (minTensorProduct_eq_max_iff_of_simplicial_right C₁ C₂ h₂_simp).mpr (.inl h₂_gen)

end MainTheorems

end PointedCone
