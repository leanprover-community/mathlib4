/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Multilinear.DirectSum

/-!
# Tensor products of direct sums

This file shows that taking `PiTensorProduct`s commutes with taking `DirectSum`s in all arguments.

## Main results

* `PiTensorProduct.directSum`: the linear equivalence between a `PiTensorProduct` of `DirectSum`s
and the `DirectSum` of the `PiTensorProduct`s.
-/

suppress_compilation

namespace PiTensorProduct

open PiTensorProduct DirectSum LinearMap

open scoped TensorProduct

variable (R : Type*) [CommSemiring R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : ι → Type*} [(i : ι) → DecidableEq (κ i)]
variable (M : (i : ι) → κ i → Type*) (M' : Type*)
variable [Π i (j : κ i), AddCommMonoid (M i j)] [AddCommMonoid M']
variable [Π i (j : κ i), Module R (M i j)] [Module R M']
variable [Π i (j : κ i) (x : M i j),  Decidable (x ≠ 0)]

/-- The linear equivalence `⨂[R] i, (⨁ j : κ i, M i j) ≃ ⨁ p : (i : ι) → κ i, ⨂[R] i, M i (p i)`,
 i.e. "tensor product distributes over direct sum". -/
protected def directSum :
    (⨂[R] i, (⨁ j : κ i, M i j)) ≃ₗ[R] ⨁ p : Π i, κ i, ⨂[R] i, M i (p i) := by
  refine LinearEquiv.ofLinear (R := R) (R₂ := R) ?toFun ?invFun ?left ?right
  · exact lift (MultilinearMap.fromDirectSumEquiv R (M := M)
      (fun p ↦ (DirectSum.lof R _ _ p).compMultilinearMap (PiTensorProduct.tprod R)))
  · exact DirectSum.toModule R _ _ (fun p ↦ lift (LinearMap.compMultilinearMap
      (PiTensorProduct.map (fun i ↦ DirectSum.lof R _ _ (p i))) (tprod R)))
  · ext p x
    simp only [compMultilinearMap_apply, coe_comp, Function.comp_apply, toModule_lof, lift.tprod,
      map_tprod, MultilinearMap.fromDirectSumEquiv_apply, id_comp]
    rw [Finset.sum_subset (piFinset_support_lof_sub R κ p x)]
    · rw [Finset.sum_singleton]
      simp only [lof_apply]
    · simp only [Finset.mem_singleton, Fintype.mem_piFinset, DFinsupp.mem_support_toFun, ne_eq,
        not_forall, not_not, forall_exists_index, forall_eq, lof_apply]
      intro i hi
      rw [(tprod R).map_coord_zero i hi, LinearMap.map_zero]
  · ext x
    simp only [compMultilinearMap_apply, coe_comp, Function.comp_apply, lift.tprod,
      MultilinearMap.fromDirectSumEquiv_apply, map_sum, toModule_lof, map_tprod, id_coe, id_eq]
    change _ = tprod R (fun i ↦ x i)
    rw [funext (fun i ↦ Eq.symm (DirectSum.sum_support_of (fun j ↦ M i j) (x i)))]
    rw [MultilinearMap.map_sum_finset]
    rfl

end PiTensorProduct
