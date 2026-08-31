/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Multilinear.DFinsupp

/-!
# Tensor products of finitely supported functions

This file shows that taking `PiTensorProduct`s commutes with taking `DFinsupp`s in all arguments.

## Main results

* `ofDFinsuppEquiv`: the linear equivalence between a `PiTensorProduct` of `DFinsupp`s
  and the `DFinsupp` of the `PiTensorProduct`s.
-/

@[expose] public section

namespace PiTensorProduct

open LinearMap TensorProduct

variable {R ι : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}
  [CommSemiring R] [Π i (j : κ i), AddCommMonoid (M i j)] [Π i (j : κ i), Module R (M i j)]
  [Fintype ι] [DecidableEq ι] [(i : ι) → DecidableEq (κ i)]

/-- The `ι`-ary tensor product distributes over `κ i`-ary finitely supported functions. -/
def ofDFinsuppEquiv :
    (⨂[R] i, (Π₀ j : κ i, M i j)) ≃ₗ[R] Π₀ p : Π i, κ i, ⨂[R] i, M i (p i) :=
  LinearEquiv.ofLinearMap
    (lift <| MultilinearMap.fromDFinsuppEquiv κ R
      fun p ↦ (DFinsupp.lsingle p).compMultilinearMap (tprod R))
    (DFinsupp.lsum R fun p ↦ lift <|
      ((PiTensorProduct.map fun i ↦ DFinsupp.lsingle (p i) :
          (⨂[R] i, M i (p i)) →ₗ[R] _)).compMultilinearMap (tprod R))
    (by ext p x; simp)
    (by
      classical
      ext x
      have hx : x = fun i ↦ ∑ j ∈ (x i).support, DFinsupp.single j ((x i) j) :=
        funext fun i ↦ ((x i).sum_single).symm
      conv_rhs =>
        rw [LinearMap.id_apply, hx,
          (tprod R).map_sum_finset (fun i j ↦ DFinsupp.single j ((x i) j))
            (fun i ↦ (x i).support)]
      simp [MultilinearMap.fromDFinsuppEquiv_apply])

@[simp]
theorem ofDFinsuppEquiv_tprod_single (p : Π i, κ i) (x : Π i, M i (p i)) :
    ofDFinsuppEquiv (⨂ₜ[R] i, DFinsupp.single (p i) (x i)) =
      DFinsupp.single p (⨂ₜ[R] i, x i) := by
  simp [ofDFinsuppEquiv]

@[simp]
theorem ofDFinsuppEquiv_symm_single_tprod (p : Π i, κ i) (x : Π i, M i (p i)) :
    ofDFinsuppEquiv.symm (DFinsupp.single p (tprod R x)) =
      (⨂ₜ[R] i, DFinsupp.single (p i) (x i)) := by
  simp [ofDFinsuppEquiv]

@[simp]
theorem ofDFinsuppEquiv_tprod_apply (x : Π i, Π₀ j, M i j) (p : Π i, κ i) :
    ofDFinsuppEquiv (tprod R x) p = ⨂ₜ[R] i, x i (p i) := by
  classical
  simpa [ofDFinsuppEquiv, MultilinearMap.fromDFinsuppEquiv_apply] using fun i hi ↦
    ((tprod R).map_coord_zero (m := fun i ↦ x i (p i)) i hi).symm

end PiTensorProduct
