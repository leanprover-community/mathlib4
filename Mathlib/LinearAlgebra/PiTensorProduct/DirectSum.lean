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

variable {R ι : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}
  [CommSemiring R] [Π i (j : κ i), AddCommMonoid (M i j)] [Π i (j : κ i), Module R (M i j)]

open scoped Classical in
/-- The n-ary tensor product distributes over m-ary direct sums. -/
noncomputable def ofDirectSumEquiv [Finite ι] :
    (⨂[R] i, (⨁ j : κ i, M i j)) ≃ₗ[R] ⨁ p : Π i, κ i, ⨂[R] i, M i (p i) :=
  have : Fintype ι := Fintype.ofFinite ι
  ofDFinsuppEquiv

@[simp]
theorem ofDirectSumEquiv_tprod_lof [Fintype ι] [(i : ι) → DecidableEq (κ i)]
    (p : Π i, κ i) (x : Π i, M i (p i)) :
    ofDirectSumEquiv (⨂ₜ[R] i, DirectSum.lof R _ _ (p i) (x i)) =
      DirectSum.lof R _ _ p (⨂ₜ[R] i, x i) := by
  classical
  rw [ofDirectSumEquiv]
  convert ofDFinsuppEquiv_tprod_single p x

@[simp]
theorem ofDirectSumEquiv_symm_lof_tprod [Fintype ι] [(i : ι) → DecidableEq (κ i)]
    (p : Π i, κ i) (x : Π i, M i (p i)) :
    ofDirectSumEquiv.symm (DirectSum.lof R _ _ p (tprod R x)) =
      (⨂ₜ[R] i, DirectSum.lof R _ _ (p i) (x i)) := by
  classical
  rw [ofDirectSumEquiv]
  convert ofDFinsuppEquiv_symm_single_tprod p x

@[simp]
theorem ofDirectSumEquiv_tprod_apply [Finite ι]
    (x : Π i, ⨁ j, M i j) (p : Π i, κ i) :
    ofDirectSumEquiv (tprod R x) p = ⨂ₜ[R] i, x i (p i) := by
  have : Fintype ι := Fintype.ofFinite ι
  convert ofDFinsuppEquiv_tprod_apply _ _

end PiTensorProduct
