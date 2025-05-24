/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Eric Wieser
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

/-- The n-ary tensor product distributes over m-ary direct sums. -/
protected def directSum :
    (⨂[R] i, (⨁ j : κ i, M i j)) ≃ₗ[R] ⨁ p : Π i, κ i, ⨂[R] i, M i (p i) :=
  LinearEquiv.ofLinear (R := R) (R₂ := R)
    (lift <| MultilinearMap.fromDirectSumEquiv R (κ := κ) (M := M)
      fun p ↦ (DirectSum.lof R _ _ p).compMultilinearMap (tprod R))
    (DirectSum.toModule R _ _ fun p ↦ lift <|
      (PiTensorProduct.map fun i ↦ DirectSum.lof R _ _ (p i)).compMultilinearMap (tprod R))
    (by ext p x; simp)
    (by ext x; simp)

@[simp]
theorem directSum_tprod_lof (p : Π i, κ i) (x : Π i, M i (p i)) :
    PiTensorProduct.directSum R M (⨂ₜ[R] i, DirectSum.lof R _ _ (p i) (x i)) =
      DirectSum.lof R _ _ p (⨂ₜ[R] i, x i) := by
  simp [PiTensorProduct.directSum]

@[simp]
theorem directSum_symm_lof_tprod (p : Π i, κ i) (x : Π i, M i (p i)) :
    (PiTensorProduct.directSum R M).symm (DirectSum.lof R _ _ p (tprod R x)) =
      (⨂ₜ[R] i, DirectSum.lof R _ _ (p i) (x i)) := by
  simp [PiTensorProduct.directSum]

@[simp]
theorem directSum_tprod_apply (x : Π i, ⨁ j, M i j) (p : Π i, κ i) :
    PiTensorProduct.directSum R M (tprod R x) p = ⨂ₜ[R] i, x i (p i) := by
  -- restate with bundled morphisms, to let `ext` fire
  let appLHS := DFinsupp.lapply (R := R) (M := fun p : Π i, κ i => ⨂[R] i, M i (p i)) p
  let appRHS (i : ι) : (⨁ j, M i j) →ₗ[R] M i (p i) := DFinsupp.lapply (R := R) (p i)
  suffices
      (appLHS ∘ₗ (PiTensorProduct.directSum R M).toLinearMap).compMultilinearMap (tprod R) =
      (tprod R).compLinearMap appRHS by
    exact congr($this x)
  ext p' x
  -- clean up
  simp only [MultilinearMap.compLinearMap_apply, compMultilinearMap_apply, coe_comp,
    Function.comp_apply, DFinsupp.lapply_apply, appLHS, appRHS]
  erw [directSum_tprod_lof R M _ x]
  simp only [DFinsupp.lapply, coe_mk, AddHom.coe_mk]
  obtain rfl | hp := eq_or_ne p' p
  · simp only [lof_apply]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hp
    erw [DFinsupp.single_eq_of_ne hp]
    refine (MultilinearMap.map_coord_zero _ i ?_).symm
    erw [DFinsupp.single_eq_of_ne hi]

end PiTensorProduct
