/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison, Sophie Morel
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Basic
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.PiTensorProduct.Finsupp

/-!
# Basis for `PiTensorProduct`

This file constructs a basis for `PiTensorProduct` given bases on the component spaces.
-/

@[expose] public section

section PiTensorProduct

attribute [local ext] PiTensorProduct.ext

open LinearMap PiTensorProduct Module TensorProduct

variable {ι R : Type*} [CommSemiring R] [DecidableEq R]
variable {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
variable {κ : ι → Type*}
variable [Fintype ι] [DecidableEq ι] [(i : ι) → DecidableEq (κ i)]

/-- Let `ι` be a `Fintype` and `M` be a family of modules indexed by `ι`. If `b i : κ i → M i`
is a basis for every `i` in `ι`, then `fun (p : Π i, κ i) ↦ ⨂ₜ[R] i, b i (p i)` is a basis
of `⨂[R] i, M i`.
-/
noncomputable def Basis.piTensorProduct (b : Π i, Basis (κ i) R (M i)) :
    Basis (Π i, κ i) R (⨂[R] i, M i) :=
  Finsupp.basisSingleOne.map
    ((PiTensorProduct.congr (fun i ↦ (b i).repr)).trans <|
      ofFinsuppEquiv.trans <|
      Finsupp.lcongr (Equiv.refl _) (constantBaseRingEquiv _ R).toLinearEquiv).symm

theorem Basis.piTensorProduct_apply (b : Π i, Basis (κ i) R (M i)) (p : Π i, κ i) :
    Basis.piTensorProduct b p = ⨂ₜ[R] i, (b i) (p i) := by
  simp only [piTensorProduct, LinearEquiv.trans_symm, Finsupp.lcongr_symm, Equiv.refl_symm,
    Basis.map_apply, Finsupp.coe_basisSingleOne, LinearEquiv.trans_apply, Finsupp.lcongr_single,
    Equiv.refl_apply, AlgEquiv.coe_symm_toLinearEquiv, map_one]
  apply LinearEquiv.injective (PiTensorProduct.congr (fun i ↦ (b i).repr))
  simp only [LinearEquiv.apply_symm_apply, congr_tprod, Basis.repr_self]
  apply LinearEquiv.injective ofFinsuppEquiv
  simp only [LinearEquiv.apply_symm_apply, ofFinsuppEquiv_tprod_single]
  rfl

end PiTensorProduct
