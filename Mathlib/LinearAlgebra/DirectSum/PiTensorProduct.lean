/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Eric Wieser
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Multilinear.DirectSum

/-!
# Tensor products of direct sums

This file shows that taking `PiTensorProduct`s commutes with taking `DirectSum`s in all arguments.

## Main results

* `PiTensorProduct.directSum`
-/

suppress_compilation

namespace PiTensorProduct

open PiTensorProduct

open DirectSum

open LinearMap

open scoped TensorProduct

attribute [local ext] TensorProduct.ext

variable (R : Type*) [CommSemiring R]

variable {ι : Type*} {κ : ι → Type*}

variable [Fintype ι]

variable [DecidableEq ι] [(i : ι) → DecidableEq (κ i)]

variable (M : (i : ι) → κ i → Type*) (M' : Type*)

variable [∀ i (j : κ i), AddCommMonoid (M i j)] [AddCommMonoid M']

variable [∀ i (j : κ i), Module R (M i j)] [Module R M']

variable [(i : ι) → (j : κ i) → (x : M i j) → Decidable (x ≠ 0)]

/-- The linear equivalence `⨂[R] i, (⨁ j : κ i, M i j) ≃ ⨁ p : (i : ι) → κ i, ⨂[R] i, M i (p i)`,
 i.e. "tensor product distributes over direct sum". -/
protected def directSum :
    (⨂[R] i, (⨁ j : κ i, M i j)) ≃ₗ[R] ⨁ p : (i : ι) → κ i, ⨂[R] i, M i (p i) := by
  refine LinearEquiv.ofLinear (R := R) (R₂ := R) ?toFun ?invFun ?left ?right
  · exact lift (MultilinearMap.fromDirectSumEquiv R (M := M)
      (fun p ↦ (DirectSum.lof R _ _ p).compMultilinearMap (PiTensorProduct.tprod R)))
  · refine DirectSum.toModule R _ _ (fun p ↦ lift (LinearMap.compMultilinearMap
      (PiTensorProduct.map (fun i ↦ DirectSum.lof R _ _ (p i))) (tprod R)))
  · ext p x
    simp only [compMultilinearMap_apply, coe_comp, Function.comp_apply, toModule_lof, lift.tprod,
      map_tprod, MultilinearMap.fromDirectSumEquiv_apply, id_comp]
    have hsub : (Fintype.piFinset fun i ↦ DFinsupp.support
        ((lof R (κ i) (fun j ↦ M i j) (p i)) (x i))) ⊆ {p} := by
      intro q
      simp only [Fintype.mem_piFinset, ne_eq, Finset.mem_singleton]
      simp_rw [DirectSum.lof_eq_of]
      exact fun hq ↦
          funext fun i ↦ Finset.mem_singleton.mp (DirectSum.support_of_subset _ (hq i))
    rw [Finset.sum_subset hsub]
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
-- We are doing stuff that we did in the construction of `MultilinearMap.fromDirectSumEquiv`,
-- so there must be a better way.

end PiTensorProduct
