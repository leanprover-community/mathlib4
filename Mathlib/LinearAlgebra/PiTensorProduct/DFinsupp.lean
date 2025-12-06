/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.PiTensorProduct
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

variable {R ι M' : Type*} {κ : ι → Type*} {M : (i : ι) → κ i → Type*}
variable [CommSemiring R] [Fintype ι] [DecidableEq ι] [(i : ι) → DecidableEq (κ i)]
variable [Π i (j : κ i), AddCommMonoid (M i j)] [AddCommMonoid M']
variable [Π i (j : κ i), Module R (M i j)] [Module R M']

/-- The `ι`-ary tensor product distributes over `κ i`-ary finitely supported functions. -/
def ofDFinsuppEquiv :
    (⨂[R] i, (Π₀ j : κ i, M i j)) ≃ₗ[R] Π₀ p : Π i, κ i, ⨂[R] i, M i (p i) :=
  LinearEquiv.ofLinear
    (lift <| MultilinearMap.fromDFinsuppEquiv κ R
      fun p ↦ (DFinsupp.lsingle p).compMultilinearMap (tprod R))
    (DFinsupp.lsum R fun p ↦ lift <|
      (PiTensorProduct.map fun i ↦ DFinsupp.lsingle (p i)).compMultilinearMap (tprod R))
    (by ext p x; simp)
    (by ext x; simp)

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
  haveI := fun i j => Classical.typeDecidableEq (M i j)
  simp only [ofDFinsuppEquiv, LinearEquiv.ofLinear_apply, lift.tprod,
    MultilinearMap.fromDFinsuppEquiv_apply, compMultilinearMap_apply, DFinsupp.lsingle_apply,
    DFinsupp.finset_sum_apply, DFinsupp.single_apply, ne_eq, Finset.sum_dite_eq',
    Fintype.mem_piFinset, DFinsupp.mem_support_toFun, ite_eq_left_iff, not_forall,
    Decidable.not_not, forall_exists_index]
  intro i hi
  rw [(tprod R).map_coord_zero i hi]

end PiTensorProduct
