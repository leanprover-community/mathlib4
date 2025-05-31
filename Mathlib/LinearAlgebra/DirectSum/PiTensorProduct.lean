/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Eric Wieser
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.DFinsupp.PiTensorProduct
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
  PiTensorProduct.dfinsupp _ _

@[simp]
theorem directSum_tprod_lof (p : Π i, κ i) (x : Π i, M i (p i)) :
    PiTensorProduct.directSum R M (⨂ₜ[R] i, DirectSum.lof R _ _ (p i) (x i)) =
      DirectSum.lof R _ _ p (⨂ₜ[R] i, x i) :=
  PiTensorProduct.dfinsupp_tprod_single _ _ _ _

@[simp]
theorem directSum_symm_lof_tprod (p : Π i, κ i) (x : Π i, M i (p i)) :
    (PiTensorProduct.directSum R M).symm (DirectSum.lof R _ _ p (tprod R x)) =
      (⨂ₜ[R] i, DirectSum.lof R _ _ (p i) (x i)) :=
  PiTensorProduct.dfinsupp_symm_single_tprod _ _ _ _

@[simp]
theorem directSum_tprod_apply (x : Π i, ⨁ j, M i j) (p : Π i, κ i) :
    PiTensorProduct.directSum R M (tprod R x) p = ⨂ₜ[R] i, x i (p i) :=
  dfinsupp_tprod_apply _ _ _ _

end PiTensorProduct
