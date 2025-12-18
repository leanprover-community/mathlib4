/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison, Sophie Morel
-/
module

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

variable {ι R : Type*} {M : ι → Type*} {κ : ι → Type*} [CommSemiring R] [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)]

open Classical in
/-- Let `ι` be a `Finite` type and `M` be a family of modules indexed by `ι`. If `b i : κ i → M i`
is a basis for every `i` in `ι`, then `fun (p : Π i, κ i) ↦ ⨂ₜ[R] i, b i (p i)` is a basis
of `⨂[R] i, M i`.
-/
noncomputable def Basis.piTensorProduct [Finite ι] (b : Π i, Basis (κ i) R (M i)) :
    Basis (Π i, κ i) R (⨂[R] i, M i) :=
  haveI := Fintype.ofFinite ι
  Finsupp.basisSingleOne.map
    ((PiTensorProduct.congr (fun i ↦ (b i).repr)) ≪≫ₗ
      ofFinsuppEquiv ≪≫ₗ
      Finsupp.lcongr (Equiv.refl _) (constantBaseRingEquiv _ R).toLinearEquiv).symm

@[simp]
theorem Basis.piTensorProduct_repr_tprod_apply [Fintype ι] (b : Π i, Basis (κ i) R (M i))
    (x : Π i, M i) (p : Π i, κ i) :
    (Basis.piTensorProduct b).repr (tprod R x) p = ∏ i : ι, (b i).repr (x i) (p i) := by
  simp only [piTensorProduct, LinearEquiv.trans_symm, Finsupp.lcongr_symm, Equiv.refl_symm,
    Basis.map_repr, LinearEquiv.symm_symm, Finsupp.basisSingleOne_repr, LinearEquiv.trans_refl,
    LinearEquiv.trans_apply, congr_tprod, Finsupp.lcongr_apply_apply, Equiv.refl_apply,
    ofFinsuppEquiv_apply, AlgEquiv.toLinearEquiv_apply, constantBaseRingEquiv_tprod]
  convert rfl

@[simp]
theorem Basis.piTensorProduct_apply [Finite ι] (b : Π i, Basis (κ i) R (M i)) (p : Π i, κ i) :
    Basis.piTensorProduct b p = ⨂ₜ[R] i, (b i) (p i) := by
  haveI := Fintype.ofFinite ι
  classical
  refine (Basis.piTensorProduct b).ext_elem (fun q ↦ ?_)
  simp [Finsupp.single_apply, Fintype.prod_ite_zero, ← funext_iff]

end PiTensorProduct
