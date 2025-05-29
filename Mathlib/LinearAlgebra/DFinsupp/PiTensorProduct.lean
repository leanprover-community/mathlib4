/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Eric Wieser
-/
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Multilinear.DFinsupp

/-!
# Tensor products of finitely supported functions

This file shows that taking `PiTensorProduct`s commutes with taking `DFinsupp`s in all arguments.

## Main results

* `PiTensorProduct.dfinsupp`: the linear equivalence between a `PiTensorProduct` of `DFinsupp`s
  and the `DFinsupp` of the `PiTensorProduct`s.
-/

suppress_compilation

namespace PiTensorProduct

open PiTensorProduct LinearMap

open scoped TensorProduct

variable (R : Type*) [CommSemiring R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : ι → Type*} [(i : ι) → DecidableEq (κ i)]
variable (M : (i : ι) → κ i → Type*) (M' : Type*)
variable [Π i (j : κ i), AddCommMonoid (M i j)] [AddCommMonoid M']
variable [Π i (j : κ i), Module R (M i j)] [Module R M']

/-- The `ι`-ary tensor product distributes over `κ i`-ary finitely supported functions. -/
protected def dfinsupp :
    (⨂[R] i, (Π₀ j : κ i, M i j)) ≃ₗ[R] Π₀ p : Π i, κ i, ⨂[R] i, M i (p i) :=
  LinearEquiv.ofLinear (R := R) (R₂ := R)
    (lift <| MultilinearMap.fromDFinsuppEquiv R (κ := κ) (M := M)
      fun p ↦ (DFinsupp.lsingle p).compMultilinearMap (tprod R))
    (DFinsupp.lsum R fun p ↦ lift <|
      (PiTensorProduct.map fun i ↦ DFinsupp.lsingle (p i)).compMultilinearMap (tprod R))
    (by ext p x; simp)
    (by ext x; simp)

@[simp]
theorem dfinsupp_tprod_single (p : Π i, κ i) (x : Π i, M i (p i)) :
    PiTensorProduct.dfinsupp R M (⨂ₜ[R] i, DFinsupp.single (p i) (x i)) =
      DFinsupp.single p (⨂ₜ[R] i, x i) := by
  simp [PiTensorProduct.dfinsupp]

@[simp]
theorem dfinsupp_symm_single_tprod (p : Π i, κ i) (x : Π i, M i (p i)) :
    (PiTensorProduct.dfinsupp R M).symm (DFinsupp.single p (tprod R x)) =
      (⨂ₜ[R] i, DFinsupp.single (p i) (x i)) := by
  simp [PiTensorProduct.dfinsupp]

@[simp]
theorem dfinsupp_tprod_apply (x : Π i, Π₀ j, M i j) (p : Π i, κ i) :
    PiTensorProduct.dfinsupp R M (tprod R x) p = ⨂ₜ[R] i, x i (p i) := by
  -- restate with bundled morphisms, to let `ext` fire
  let appLHS := DFinsupp.lapply (R := R) (M := fun p : Π i, κ i => ⨂[R] i, M i (p i)) p
  let appRHS (i : ι) : (Π₀ j, M i j) →ₗ[R] M i (p i) := DFinsupp.lapply (p i)
  suffices
      (appLHS ∘ₗ (PiTensorProduct.dfinsupp R M).toLinearMap).compMultilinearMap (tprod R) =
      (tprod R).compLinearMap appRHS by
    exact congr($this x)
  ext p' x
  -- clean up
  simp only [MultilinearMap.compLinearMap_apply, DFinsupp.lsingle_apply, compMultilinearMap_apply,
    coe_comp, LinearEquiv.coe_coe, Function.comp_apply, dfinsupp_tprod_single,
    DFinsupp.lapply_apply, appLHS, appRHS]
  obtain rfl | hp := eq_or_ne p' p
  · simp only [DFinsupp.single_eq_same]
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hp
    rw [DFinsupp.single_eq_of_ne hp, ((tprod R).map_coord_zero i ?_).symm]
    rw [DFinsupp.single_eq_of_ne hi]

end PiTensorProduct
