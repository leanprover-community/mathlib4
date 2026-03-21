/-
Copyright (c) 2024 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.IsTensorProduct

/-!

# Lemmas about IsBaseChange under Exact Sequences

In this file, we show that cokernel preserves `IsBaseChange S`.
For kernel version (needs flat), see `Mathlib.RingTheory.Flat.IsBaseChange`.

# Main Results

For `S` an `R`-algebra, consider the following commutative diagram with exact rows,
`M₁` `M₂` `M₃` `R`-modules, `N₁` `N₂` `N₃` `S`-modules,
`R`-linear maps `f₁` `f₂` `i₁` `i₂` `i₃` and `S`-linear maps `g₁` `g₂`.

M₁ --f₁--> M₂ --f₂--> M₃
|          |          |
i₁         i₂         i₃
|          |          |
v          v          v
N₁ --g₁--> N₂ --g₂--> N₃

* `IsBaseChange.of_right_exact` : If `f₂` and `g₂` are surjective,
  `i₁` and `i₂` is base change by `S`, then `i₃` is base change by `S`.

-/

@[expose] public section

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]

variable {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [Module R N₁] [Module R N₂] [Module R N₃] [Module S N₁] [Module S N₂] [Module S N₃]
  [IsScalarTower R S N₁] [IsScalarTower R S N₂] [IsScalarTower R S N₃]
  (h₁ : M₁ →ₗ[R] N₁) (h₂ : M₂ →ₗ[R] N₂) (h₃ : M₃ →ₗ[R] N₃)
  {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} {f' : N₁ →ₗ[S] N₂} {g' : N₂ →ₗ[S] N₃}

lemma IsBaseChange.of_right_exact (comm1 : h₂.comp f = (f'.restrictScalars R).comp h₁)
    (comm2 : h₃.comp g = (g'.restrictScalars R).comp h₂)(isb1 : IsBaseChange S h₁)
    (isb2 : IsBaseChange S h₂) (exac1 : Function.Exact f g) (surj1 : Function.Surjective g)
    (exac2 : Function.Exact f' g') (surj2 : Function.Surjective g') : IsBaseChange S h₃ := by
  change Function.Bijective _ at isb1 isb2 ⊢
  refine LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    ((f.baseChange S).restrictScalars R) ((g.baseChange S).restrictScalars R)
    (f'.restrictScalars R) (g'.restrictScalars R) _ _ _ ?_ ?_ ?_ exac2 isb1.2 isb2 ?_ surj2
  · ext s m
    simpa using congr(s • ($comm1 m)).symm
  · ext s m
    simpa using congr(s • ($comm2 m)).symm
  · simpa [LinearMap.baseChange_eq_ltensor] using lTensor_exact S exac1 surj1
  · simpa [LinearMap.baseChange_eq_ltensor] using LinearMap.lTensor_surjective S surj1

lemma IsBaseChange.of_equiv_left (f : M₁ ≃ₗ[R] M₂) (f' : N₁ ≃ₗ[S] N₂)
    (comm1 : h₂.comp f.toLinearMap = (f'.restrictScalars R).comp h₁)
    (isb1 : IsBaseChange S h₁) : IsBaseChange S h₂ :=
  IsBaseChange.of_right_exact S (f := (0 : Unit →ₗ[R] M₁)) (f' := (0 : Unit →ₗ[S] N₁))
    (g := f) (g' := f') 0 h₁ h₂ (by simp) comm1 (show Function.Bijective _ from by simp) isb1
      (fun y ↦ (by simpa using eq_comm)) f.bijective.2 (fun y ↦ (by simpa using eq_comm))
        f'.bijective.2

lemma IsBaseChange.of_equiv_right (f : M₁ ≃ₗ[R] M₂) (f' : N₁ ≃ₗ[S] N₂)
    (comm1 : h₂.comp f.toLinearMap = (f'.restrictScalars R).comp h₁)
    (isb2 : IsBaseChange S h₂) : IsBaseChange S h₁ := by
  refine IsBaseChange.of_equiv_left S h₂ h₁ f.symm f'.symm (LinearMap.ext fun y ↦ ?_) isb2
  obtain ⟨y, rfl⟩ := f.surjective y
  exact f'.injective (by simpa using congr($comm1 y).symm)

lemma IsBaseChange.comp_equiv {M1 M2 N : Type*} [AddCommGroup M1] [AddCommGroup M2] [AddCommGroup N]
    [Module R M1] [Module R M2] [Module R N] [Module S N] [IsScalarTower R S N] (e : M1 ≃ₗ[R] M2)
    (f : M2 →ₗ[R] N) (isb : IsBaseChange S f) : IsBaseChange S (f.comp e.toLinearMap) :=
  IsBaseChange.of_equiv_right S (f.comp e.toLinearMap) f e 1 (LinearMap.ext fun y ↦ by simp) isb
