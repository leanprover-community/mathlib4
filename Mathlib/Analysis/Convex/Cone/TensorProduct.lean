/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Geometry.Convex.Cone.Simplicial
public import Mathlib.Geometry.Convex.Cone.TensorProduct
public import Mathlib.Topology.Algebra.Module.TopDualPairing

/-!
# Tensor Products of Pointed Cones

This file proves that the minimal and maximal tensor products of pointed cones in
finite-dimensional real vector spaces are equal when one cone is simplicial and generating
and the other is proper (pointed and closed).

Finite-dimensionality of the proper cone ambient space is by explicit declaration and is required
for the `topDualPairing_isContPerfPair` instance (in `Topology.Algebra.Module.TopDualPairing`).
The simplicial and generating cone ambient space is implicitly finite dimensional by the
simplicial and generating assumption.

This file uses `topDualPairing` (the canonical pairing of a vector space and its topological dual)
to avoid explicit topology assumptions on `Module.Dual`.

The proof relies on the following result:

* **Bipolar theorem** (`ProperCone.dual_dual_flip`): The double dual of a proper cone is itself.

This requires:
- Local convexity and Hausdorff separation (for Hahn-Banach)
- A continuous perfect pairing between the module and its dual.

## Main results

* `PointedCone.minTensorProduct_eq_max_of_simplicial_generating_left`:
  If `C₁` is simplicial and generating and `C₂` is proper, then the minimal and
  maximal tensor products are equal.

* `PointedCone.minTensorProduct_eq_max_of_simplicial_generating_right`:
  If `C₁` is a proper cone and `C₂` is a simplicial and generating cone, then their minimal
  and maximal tensor products are equal.

## References

* [Aubrun et al. *Entangleability of cones*][aubrunEntangleabilityCones2021]
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

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
    b.coord i ∈ dual (dualPairing R M).flip (C : Set M) := by
  classical
  refine dual_le_dual hC ?_
  simp [Finsupp.single_apply, ite_nonneg zero_le_one le_rfl]

end BasisCoordDual

section MainTheorems

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

variable [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F]
variable [FiniteDimensional ℝ F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]

open TensorProduct Module

/-- If `C₁` is a simplicial and generating cone and `C₂` is a proper cone, then their minimal
and maximal tensor products are equal. -/
theorem minTensorProduct_eq_max_of_simplicial_generating_left (C₁ : PointedCone ℝ E)
    (C₂ : ProperCone ℝ F) (h₁_simp : C₁.IsSimplicial) (h₁_gen : Submodule.span ℝ (C₁ : Set E) = ⊤) :
    minTensorProduct C₁ C₂.toPointedCone = maxTensorProduct C₁ C₂.toPointedCone := by
  classical
  obtain ⟨s, hs_fin, hs_lin, hs_span⟩ := h₁_simp
  haveI : Fintype s := hs_fin.fintype
  -- The conic hull (R≥0-span) is contained in the linear span (ℝ-span)
  have hull_sub_span : (hull ℝ s : Set E) ⊆ Submodule.span ℝ s := by
    intro x hx
    rw [SetLike.mem_coe, PointedCone.mem_hull_set] at hx
    obtain ⟨c, hc_supp, _, hc_sum⟩ := hx
    exact hc_sum ▸ Submodule.sum_mem _ fun m hm =>
      Submodule.smul_mem _ _ (Submodule.subset_span (hc_supp hm))
  -- Extract basis from `C₁.IsSimplicial` + generating
  let b := Basis.mk hs_lin <| by
    simpa only [id_eq, Subtype.range_coe] using
      h₁_gen ▸ hs_span ▸ Submodule.span_le.mpr hull_sub_span
  -- Dual basis elements are in C₁*
  have h_coord_dual : ∀ i, b.coord i ∈ dual (dualPairing ℝ E).flip C₁ :=
    basis_coord_mem_dual _ _ (hs_span ▸ (Submodule.span_mono <| by simp [b]))
  -- Reduce to proving z ∈ max → z ∈ min
  apply le_antisymm (minTensorProduct_le_maxTensorProduct C₁ C₂.toPointedCone)
  intro z hz
  -- Express z using basis: z = ∑ b_i ⊗ y_i
  rw [← (equivFinsuppOfBasisLeft b).symm_apply_apply z,
    TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype _ _ (by simp)]
  -- Show z ∈ min by showing b_i ∈ C₁ and y_i ∈ C₂
  refine Submodule.sum_mem _ fun i _ => tmul_mem_minTensorProduct ?_ ?_
  · simpa only [b, Basis.coe_mk] using (hs_span ▸ subset_hull) i.prop
  · simp only [equivFinsuppOfBasisLeft_apply]
    rw [← ProperCone.dual_dual_flip (topDualPairing ℝ F) C₂]
    intro f (hf : (f : F →ₗ[ℝ] ℝ) ∈ dual (dualPairing ℝ F).flip (C₂ : Set F))
    simp only [mem_maxTensorProduct] at hz
    have h_nonneg := hz (b.coord i) (h_coord_dual i) (f : F →ₗ[ℝ] ℝ) hf
    have h_eq : dualDistrib ℝ E F ((b.coord i) ⊗ₜ[ℝ] (f : F →ₗ[ℝ] ℝ)) =
        (f : F →ₗ[ℝ] ℝ) ∘ₗ (TensorProduct.lid ℝ F) ∘ₗ (b.coord i).rTensor F := by
      ext; simp [mul_comm]
    simpa only [h_eq, LinearMap.comp_apply, LinearEquiv.coe_coe] using h_nonneg

/-- If `C₁` is a proper cone and `C₂` is a simplicial and generating cone, then their minimal
and maximal tensor products are equal. -/
theorem minTensorProduct_eq_max_of_simplicial_generating_right (C₁ : ProperCone ℝ F)
    (C₂ : PointedCone ℝ E) (h₂_simp : C₂.IsSimplicial)
    (h₂_gen : Submodule.span ℝ (C₂ : Set E) = ⊤) :
    minTensorProduct C₁.toPointedCone C₂ = maxTensorProduct C₁.toPointedCone C₂ := by
  rw [← minTensorProduct_comm, ← maxTensorProduct_comm,
    minTensorProduct_eq_max_of_simplicial_generating_left C₂ C₁ h₂_simp h₂_gen]

end MainTheorems

end PointedCone
