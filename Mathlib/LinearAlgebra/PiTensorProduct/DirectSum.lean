/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct
public import Mathlib.LinearAlgebra.PiTensorProduct.DFinsupp
public import Mathlib.Algebra.DirectSum.Module

/-!
# Tensor products of direct sums

This file shows that taking `PiTensorProduct`s commutes with taking `DirectSum`s in all arguments.

## Main results

* `ofDirectSumEquiv`: the linear equivalence between a `PiTensorProduct` of `DirectSum`s
  and the `DirectSum` of the `PiTensorProduct`s.
-/

@[expose] public section

namespace PiTensorProduct

open PiTensorProduct DirectSum TensorProduct

variable {R ι M' : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}
variable [CommSemiring R] [Fintype ι] [DecidableEq ι] [(i : ι) → DecidableEq (κ i)]
variable [Π i (j : κ i), AddCommMonoid (M i j)] [AddCommMonoid M']
variable [Π i (j : κ i), Module R (M i j)] [Module R M']

/-- The n-ary tensor product distributes over m-ary direct sums. -/
def ofDirectSumEquiv :
    (⨂[R] i, (⨁ j : κ i, M i j)) ≃ₗ[R] ⨁ p : Π i, κ i, ⨂[R] i, M i (p i) :=
  ofDFinsuppEquiv

@[simp]
theorem ofDirectSumEquiv_tprod_lof (p : Π i, κ i) (x : Π i, M i (p i)) :
    ofDirectSumEquiv (⨂ₜ[R] i, DirectSum.lof R _ _ (p i) (x i)) =
      DirectSum.lof R _ _ p (⨂ₜ[R] i, x i) :=
  ofDFinsuppEquiv_tprod_single _ _

@[simp]
theorem ofDirectSumEquiv_symm_lof_tprod (p : Π i, κ i) (x : Π i, M i (p i)) :
    ofDirectSumEquiv.symm (DirectSum.lof R _ _ p (tprod R x)) =
      (⨂ₜ[R] i, DirectSum.lof R _ _ (p i) (x i)) :=
  ofDFinsuppEquiv_symm_single_tprod _ _

@[simp]
theorem ofDirectSumEquiv_tprod_apply (x : Π i, ⨁ j, M i j) (p : Π i, κ i) :
    ofDirectSumEquiv (tprod R x) p = ⨂ₜ[R] i, x i (p i) :=
  ofDFinsuppEquiv_tprod_apply _ _

end PiTensorProduct
