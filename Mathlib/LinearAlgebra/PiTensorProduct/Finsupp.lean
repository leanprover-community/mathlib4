/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.Algebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.PiTensorProduct.DirectSum
public import Mathlib.RingTheory.PiTensorProduct

/-!
# Results on finitely supported functions.

* `finsuppPiTensorProduct`, the tensor product of the family `κ i →₀ M i` indexed by `ι` is linearly
  equivalent to `∏ i, κ i →₀ ⨂[R] i, M i`.
-/

@[expose] public section

section PiTensorProduct

open PiTensorProduct BigOperators
open TensorProduct

attribute [local ext] TensorProduct.ext

variable (R : Type*) [CommSemiring R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (κ : ι → Type*) [(i : ι) → DecidableEq (κ i)]
variable (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-- If `ι` is a `Fintype`, `κ i` is a family of types indexed by `ι` and `M i` is a family
of modules indexed by `ι`, then the tensor product of the family `κ i →₀ M i` is linearly
equivalent to `∏ i, κ i →₀ ⨂[R] i, M i`.
-/
noncomputable def finsuppPiTensorProduct :
  (⨂[R] i, κ i →₀ M i) ≃ₗ[R] ((i : ι) → κ i) →₀ ⨂[R] i, M i :=
  PiTensorProduct.congr (fun i ↦ finsuppLEquivDirectSum R (M i) (κ i)) ≪≫ₗ
    (PiTensorProduct.directSum R (fun (i : ι) (_ : κ i) ↦ M i)) ≪≫ₗ
    (finsuppLEquivDirectSum R (⨂[R] i, M i) ((i : ι) → κ i)).symm

@[simp]
theorem finsuppPiTensorProduct_tprod_single (p : (i : ι) → κ i) (m : (i : ι) → M i) :
    finsuppPiTensorProduct R κ M (⨂ₜ[R] i, Finsupp.single (p i) (m i)) =
    Finsupp.single p (⨂ₜ[R] i, m i) := by
  simp [finsuppPiTensorProduct]

@[simp]
theorem finsuppPiTensorProduct_apply (f : (i : ι) → (κ i →₀ M i)) (p : (i : ι) → κ i) :
    finsuppPiTensorProduct R κ M (⨂ₜ[R] i, f i) p = ⨂ₜ[R] i, f i (p i) := by
  simp only [finsuppPiTensorProduct, finsuppLEquivDirectSum, LinearEquiv.trans_apply, congr_tprod]
  erw [directSum_tprod_apply R (M := fun i _ => M i) _ p]
  rfl

@[simp]
theorem finsuppPiTensorProduct_symm_single_tprod (p : (i : ι) → κ i) (m : (i : ι) → M i) :
    (finsuppPiTensorProduct R κ M).symm (Finsupp.single p (⨂ₜ[R] i, m i)) =
    ⨂ₜ[R] i, Finsupp.single (p i) (m i) :=
  (LinearEquiv.symm_apply_eq _).2 (finsuppPiTensorProduct_tprod_single _ _ _ _ _).symm

/-- A variant of `finsuppPiTensorProduct` where all modules `M i` are the ground ring. -/
noncomputable def finsuppPiTensorProduct' : (⨂[R] i, (κ i →₀ R)) ≃ₗ[R] ((i : ι) → κ i) →₀ R :=
  finsuppPiTensorProduct R κ (fun _ ↦ R) ≪≫ₗ
  Finsupp.lcongr (Equiv.refl ((i : ι) → κ i)) (constantBaseRingEquiv ι R).toLinearEquiv

@[simp]
theorem finsuppPiTensorProduct'_apply_apply (f : (i : ι) → κ i →₀ R) (p : (i : ι) → κ i) :
    finsuppPiTensorProduct' R κ (⨂ₜ[R] i, f i) p = ∏ i, f i (p i) := by
  simp only [finsuppPiTensorProduct', LinearEquiv.trans_apply, Finsupp.lcongr_apply_apply,
    Equiv.refl_symm, Equiv.refl_apply, finsuppPiTensorProduct_apply, AlgEquiv.toLinearEquiv_apply,
    constantBaseRingEquiv_tprod]

@[simp]
theorem finsuppPiTensorProduct'_tprod_single (p : (i : ι) → κ i) (r : ι → R) :
    finsuppPiTensorProduct' R κ (⨂ₜ[R] i, Finsupp.single (p i) (r i)) =
    Finsupp.single p (∏ i, r i) := by
  simp [finsuppPiTensorProduct']

end PiTensorProduct
