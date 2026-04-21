/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Algebra.DirectSum.Module
/-!
# Tensor products of direct sums

This file shows that taking `TensorProduct`s commutes with taking `DirectSum`s in both arguments.

## Main results

* `TensorProduct.directSum`
* `TensorProduct.directSumLeft`
* `TensorProduct.directSumRight`
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u v₁ v₂ w₁ w₁' w₂ w₂'

section Ring

namespace TensorProduct

open TensorProduct

open DirectSum

open LinearMap

attribute [local ext] TensorProduct.ext

variable (R : Type u) [CommSemiring R] (S) [Semiring S] [Algebra R S]
variable {ι₁ : Type v₁} {ι₂ : Type v₂}
variable [DecidableEq ι₁] [DecidableEq ι₂]
variable (M₁ : ι₁ → Type w₁) (M₁' : Type w₁') (M₂ : ι₂ → Type w₂) (M₂' : Type w₂')
variable [∀ i₁, AddCommMonoid (M₁ i₁)] [AddCommMonoid M₁']
variable [∀ i₂, AddCommMonoid (M₂ i₂)] [AddCommMonoid M₂']
variable [∀ i₁, Module R (M₁ i₁)] [Module R M₁'] [∀ i₂, Module R (M₂ i₂)] [Module R M₂']
variable [∀ i₁, Module S (M₁ i₁)] [∀ i₁, IsScalarTower R S (M₁ i₁)]
variable [Module S M₁'] [IsScalarTower R S M₁']

/-- The linear equivalence `(⨁ i₁, M₁ i₁) ⊗ (⨁ i₂, M₂ i₂) ≃ (⨁ i₁, ⨁ i₂, M₁ i₁ ⊗ M₂ i₂)`, i.e.
"tensor product distributes over direct sum". -/
protected def directSum :
    ((⨁ i₁, M₁ i₁) ⊗[R] ⨁ i₂, M₂ i₂) ≃ₗ[S] ⨁ i : ι₁ × ι₂, M₁ i.1 ⊗[R] M₂ i.2 := by
  refine LinearEquiv.ofLinear ?toFun ?invFun ?left ?right
  · exact AlgebraTensorModule.lift <|
      toModule S _ _ fun i₁ => flip <| toModule R _ _ fun i₂ => flip <| AlgebraTensorModule.curry <|
      DirectSum.lof S (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂)
  · exact toModule S _ _ fun i => AlgebraTensorModule.map (lof S _ M₁ i.1) (lof R _ M₂ i.2)
  · ext ⟨i₁, i₂⟩ x₁ x₂ : 4
    simp only [coe_comp, Function.comp_apply, toModule_lof, AlgebraTensorModule.map_tmul,
      AlgebraTensorModule.lift_apply, lift.tmul, coe_restrictScalars, flip_apply,
      AlgebraTensorModule.curry_apply, curry_apply, id_comp]
  · ext i₁ i₂ x₁ x₂ : 5
    simp only [coe_comp, Function.comp_apply, AlgebraTensorModule.curry_apply, curry_apply,
      coe_restrictScalars, AlgebraTensorModule.lift_apply, lift.tmul, toModule_lof, flip_apply,
      AlgebraTensorModule.map_tmul, id_coe, id_eq]

/-- Tensor products distribute over a direct sum on the left . -/
def directSumLeft : (⨁ i₁, M₁ i₁) ⊗[R] M₂' ≃ₗ[S] ⨁ i, M₁ i ⊗[R] M₂' :=
  TensorProduct.AlgebraTensorModule.congr 1 (DirectSum.lid _ _).symm ≪≫ₗ
  TensorProduct.directSum R S M₁ (fun _ : Unit ↦ M₂') ≪≫ₗ
  DirectSum.lequivCongrLeft S (Equiv.prodUnique _ _)

/-- Tensor products distribute over a direct sum on the right. -/
def directSumRight : (M₁' ⊗[R] ⨁ i, M₂ i) ≃ₗ[S] ⨁ i, M₁' ⊗[R] M₂ i :=
  TensorProduct.AlgebraTensorModule.congr (DirectSum.lid _ _).symm 1 ≪≫ₗ
  TensorProduct.directSum R S (fun _ : Unit ↦ M₁') M₂ ≪≫ₗ
  DirectSum.lequivCongrLeft S (Equiv.uniqueProd _ _)

@[deprecated (since := "2026-03-04")] alias directSumRight' := directSumRight

variable {M₁ M₁' M₂ M₂'}

@[simp]
theorem directSum_lof_tmul_lof (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) :
    TensorProduct.directSum R S M₁ M₂ (DirectSum.lof S ι₁ M₁ i₁ m₁ ⊗ₜ DirectSum.lof R ι₂ M₂ i₂ m₂) =
      DirectSum.lof S (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂) (m₁ ⊗ₜ m₂) := by
  simp [TensorProduct.directSum]

@[simp]
theorem directSum_symm_lof_tmul (i₁ : ι₁) (m₁ : M₁ i₁) (i₂ : ι₂) (m₂ : M₂ i₂) :
    (TensorProduct.directSum R S M₁ M₂).symm
      (DirectSum.lof S (ι₁ × ι₂) (fun i => M₁ i.1 ⊗[R] M₂ i.2) (i₁, i₂) (m₁ ⊗ₜ m₂)) =
      (DirectSum.lof S ι₁ M₁ i₁ m₁ ⊗ₜ DirectSum.lof R ι₂ M₂ i₂ m₂) := by
  rw [LinearEquiv.symm_apply_eq, directSum_lof_tmul_lof]

@[simp]
theorem directSumLeft_tmul_lof (i : ι₁) (x : M₁ i) (y : M₂') :
    directSumLeft R S M₁ M₂' (DirectSum.lof S _ _ i x ⊗ₜ[R] y) =
    DirectSum.lof S _ _ i (x ⊗ₜ[R] y) := by
  simpa [directSumLeft] using lequivCongrLeft_lof S (by simp) _ _ rfl

@[simp]
theorem directSumLeft_symm_lof_tmul (i : ι₁) (x : M₁ i) (y : M₂') :
    (directSumLeft R S M₁ M₂').symm (DirectSum.lof S _ _ i (x ⊗ₜ[R] y)) =
      DirectSum.lof S _ _ i x ⊗ₜ[R] y := by
  rw [LinearEquiv.symm_apply_eq, directSumLeft_tmul_lof]

@[simp]
lemma directSumLeft_tmul (m : ⨁ i, M₁ i) (n : M₂') (i : ι₁) :
    directSumLeft R S M₁ M₂' (m ⊗ₜ[R] n) i = (m i) ⊗ₜ[R] n := by
  suffices (DirectSum.component S ι₁ _ i) ∘ₗ (directSumLeft R S M₁ M₂').toLinearMap ∘ₗ
      ((AlgebraTensorModule.mk R S (⨁ i, M₁ i) M₂').flip n) =
        ((AlgebraTensorModule.mk R S (M₁ i) M₂').flip n) ∘ₗ (DirectSum.component S ι₁ M₁ i) by
    simpa using LinearMap.congr_fun this m
  ext j n
  by_cases hj : j = i
  · subst hj; simp
  · simp [DirectSum.component.of, hj]

@[simp]
theorem directSumRight_tmul_lof (x : M₁') (i : ι₂) (y : M₂ i) :
    directSumRight R S M₁' M₂ (x ⊗ₜ[R] DirectSum.lof R _ _ i y) =
    DirectSum.lof S _ _ i (x ⊗ₜ[R] y) := by
  simpa [directSumRight] using lequivCongrLeft_lof S (by simp) _ _ rfl

@[simp]
theorem directSumRight_symm_lof_tmul (x : M₁') (i : ι₂) (y : M₂ i) :
    (directSumRight R S M₁' M₂).symm (DirectSum.lof S _ _ i (x ⊗ₜ[R] y)) =
      x ⊗ₜ[R] DirectSum.lof R _ _ i y := by
  rw [LinearEquiv.symm_apply_eq, directSumRight_tmul_lof]

lemma directSumRight_comp_rTensor (f : M₁' →ₗ[R] M₂') :
    (directSumRight R R M₂' M₁).toLinearMap ∘ₗ f.rTensor _ =
      (lmap fun _ ↦ f.rTensor _) ∘ₗ directSumRight R R M₁' M₁ := by
  ext; simp

@[simp]
lemma directSumRight_tmul (m : M₁') (n : ⨁ i, M₂ i) (i : ι₂) :
    directSumRight R S M₁' M₂ (m ⊗ₜ[R] n) i = m ⊗ₜ[R] (n i) := by
  suffices (DirectSum.component S ι₂ _ i).restrictScalars R ∘ₗ
      (directSumRight R S M₁' M₂).toLinearMap.restrictScalars R ∘ₗ
        (TensorProduct.mk R M₁' (⨁ i, M₂ i) m) =
          (TensorProduct.mk R M₁' (M₂ i) m) ∘ₗ (DirectSum.component R ι₂ M₂ i) by
    simpa using LinearMap.congr_fun this n
  ext j n
  by_cases hj : j = i
  · subst hj; simp
  · simp [DirectSum.component.of, hj]

variable (S₀ : Type*) [CommSemiring S₀] [Algebra R S₀] [Algebra S₀ S]
  [Module S₀ M₁'] [IsScalarTower R S₀ M₁'] [IsScalarTower S₀ S M₁']

lemma restrictScalar_directSumRight :
    (directSumRight R S M₁' M₂).restrictScalars S₀ = directSumRight R S₀ M₁' M₂ :=
  LinearEquiv.restrictScalars_injective R <| LinearEquiv.toLinearMap_injective <| by ext; simp [lof]

@[deprecated (since := "2026-03-04")]
alias directSumRight'_restrict := restrictScalar_directSumRight

lemma coe_directSumRight :
    ⇑(directSumRight R S M₁' M₂) = directSumRight R R M₁' M₂ :=
  congr($(restrictScalar_directSumRight ..))

@[deprecated (since := "2026-03-04")] alias coe_directSumRight' := coe_directSumRight

end TensorProduct

end Ring
