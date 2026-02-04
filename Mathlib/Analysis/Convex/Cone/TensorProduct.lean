/-
Copyright (c) 2025 Bjørn Solheim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Solheim
-/
module

public import Mathlib.Analysis.Convex.Cone.Dual
public import Mathlib.Geometry.Convex.Cone.Simplicial
public import Mathlib.Geometry.Convex.Cone.TensorProduct

/-!
# Tensor Products of Pointed Cones

This file proves that the minimal and maximal tensor products of pointed cones living in
finite-dimensional real vector spaces are equal when one of the cones is simplicial and generating.
We need to apply the bipolar theorem and therefore topological assumptions
are required on the factor which is not simplicial and generating.

We are using the following result:

* **Bipolar theorem** (`ProperCone.dual_dual_flip`): The double dual of a proper cone is itself.

This requires:
- Local convexity and Hausdorff separation (for Hahn-Banach)
- A continuous perfect pairing between the module and its dual.

## Main results

* All cones are pointed (i.e., closed under nonnegative scalars) unless otherwise noted.
* A proper cone is pointed and closed.
* The following results holds for cones in real finite dimensional vector spaces:

* `minTensorProduct_eq_max_of_simplicial_generating_left`:
  If C₁ is a simplicial and generating cone and C₂ is a proper cone,
  then their minimal and maximal tensor products are equal.

* `minTensorProduct_eq_max_of_simplicial_generating_right`:
  Symmetric version: If C₁ is a proper cone and C₂ is a simplicial and generating cone,
  then their minimal and maximal tensor products are equal.

## Implementation notes

Let `F` be the space containing the Proper (closed) cone. The topology on `Module.Dual ℝ F` is
provided by explicit type class assumptions rather than via custom instances. Since there is a
canonical choice of topology, this could alternatively be done via instances.

This would be either a set of local instance or a "load when required" namespace-protected
set of instances. This has been implemented as a test but we have assumed that this type of
design would be too experimental.

## References

* [Aubrun et al. *Entangleability of cones*][aubrunEntangleabilityCones2021]

-/

@[expose] public section

namespace PointedCone

section BasisCoordDual

variable {R M : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R]
variable [AddCommGroup M] [Module R M]

open Module

/- If a pointed cone `C` is contained in the conic span of a basis `b`, then the coordinate
functionals of `b` lie in the dual cone of `C`. -/
private lemma basis_coord_mem_dual {ι : Type*} (b : Basis ι R M) (C : PointedCone R M)
    (hC : (C : Set M) ⊆ (span R (Set.range b) : Set M)) (i : ι) :
    b.coord i ∈ dual (dualPairing R M).flip (C : Set M) := by
  classical
  refine dual_le_dual hC ?_
  simp [Finsupp.single_apply, ite_nonneg zero_le_one le_rfl]

end BasisCoordDual

section instIsContPerfPairDualPairing

open Module

-- We only require this instance for real vector spaces but we state it more generally
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
-- [CompleteSpace 𝕜] is required for `isModuleTopologyOfFiniteDimensional`
variable [CompleteSpace 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [FiniteDimensional 𝕜 E] [T2Space E]
variable [TopologicalSpace (Dual 𝕜 E)] [IsTopologicalAddGroup (Dual 𝕜 E)]
variable [ContinuousSMul 𝕜 (Dual 𝕜 E)] [T2Space (Dual 𝕜 E)]

/-- The dual pairing is a continuous perfect pairing for finite-dimensional Hausdorff spaces
over complete nontrivially normed fields. -/
private instance instIsContPerfPairDualPairing : (dualPairing 𝕜 E).IsContPerfPair where
  continuous_uncurry := by
    haveI : IsModuleTopology 𝕜 E := isModuleTopologyOfFiniteDimensional
    haveI : IsModuleTopology 𝕜 (Dual 𝕜 E) := isModuleTopologyOfFiniteDimensional
    exact IsModuleTopology.continuous_bilinear_of_finite_left (dualPairing 𝕜 E)
  bijective_left := LinearMap.toContinuousLinearMap.bijective
  bijective_right := LinearMap.toContinuousLinearMap.bijective.comp (evalEquiv 𝕜 E).bijective

end instIsContPerfPairDualPairing

/-! ### Equality of minimal and maximal tensor products of cones -/

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {F : Type*} [AddCommGroup F] [Module ℝ F]

variable [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F]
variable [FiniteDimensional ℝ F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]

-- Explicit topology on the dual space
variable [TopologicalSpace (Module.Dual ℝ F)] [IsTopologicalAddGroup (Module.Dual ℝ F)]
variable [ContinuousSMul ℝ (Module.Dual ℝ F)] [T2Space (Module.Dual ℝ F)]

open TensorProduct Module

/-- If C₁ is a simplicial and generating cone and C₂ is a proper cone,
then their minimal and maximal tensor products are equal. -/
theorem minTensorProduct_eq_max_of_simplicial_generating_left (C₁ : PointedCone ℝ E)
    (C₂ : ProperCone ℝ F) (h₁_simp : C₁.IsSimplicial)
    (h₁_gen : (C₁ : ConvexCone ℝ E).IsGenerating) :
    minTensorProduct C₁ C₂.toPointedCone = maxTensorProduct C₁ C₂.toPointedCone := by
  classical
  -- Extract basis from `C₁.IsSimplicial` + `C₁.IsGenerating`
  let b := h₁_simp.toBasis h₁_gen
  -- Dual basis elements are in C₁*
  have h_coord_dual : ∀ i, b.coord i ∈ dual (dualPairing ℝ E).flip C₁ := fun i => by
    apply basis_coord_mem_dual
    rw [show Set.range b = ↑h₁_simp.generators by ext; simp [b], h₁_simp.span_generators]
  -- Reduce to proving z ∈ max → z ∈ min
  apply le_antisymm (minTensorProduct_le_maxTensorProduct C₁ C₂.toPointedCone)
  intro z hz
  -- Express z using basis: z = ∑ b_i ⊗ y_i
  let y := equivFinsuppOfBasisLeft b z
  rw [← (equivFinsuppOfBasisLeft b).symm_apply_apply z,
    TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype _ _ (by simp)]
  -- Show z ∈ min by showing b_i ∈ C₁ and y_i ∈ C₂
  exact Submodule.sum_mem _ fun i _ => tmul_mem_minTensorProduct
    (h₁_simp.toBasis_apply h₁_gen i ▸ h₁_simp.generator_mem i)
    (by erw [TensorProduct.equivFinsuppOfBasisLeft_apply,
          ← ProperCone.dual_dual_flip (dualPairing ℝ F) C₂, ProperCone.mem_dual]
        intro ψ hψ
        simp only [dualPairing_apply, mem_maxTensorProduct] at hz ⊢
        convert hz (b.coord i) (h_coord_dual i) ψ hψ
        have h : TensorProduct.dualDistrib ℝ E F ((b.coord i) ⊗ₜ[ℝ] ψ) =
            ψ ∘ₗ (TensorProduct.lid ℝ F) ∘ₗ (b.coord i).rTensor F := by
          ext; simp [TensorProduct.dualDistrib_apply, mul_comm]
        simp [h])

/-- If C₁ is a proper cone and C₂ is a simplicial and generating cone,
then their minimal and maximal tensor products are equal. -/
theorem minTensorProduct_eq_max_of_simplicial_generating_right (C₁ : ProperCone ℝ F)
    (C₂ : PointedCone ℝ E) (h₂_simp : C₂.IsSimplicial)
    (h₂_gen : (C₂ : ConvexCone ℝ E).IsGenerating) :
    minTensorProduct C₁.toPointedCone C₂ = maxTensorProduct C₁.toPointedCone C₂ := by
  rw [← minTensorProduct_comm, ← maxTensorProduct_comm,
    minTensorProduct_eq_max_of_simplicial_generating_left C₂ C₁ h₂_simp h₂_gen]

end PointedCone
