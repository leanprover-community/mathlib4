/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan
-/
module

public import Mathlib.Algebra.FiveLemma
public import Mathlib.RingTheory.Flat.Basic

/-!

# Lemmas about `IsBaseChange` under exact sequences

In this file, we show that if `S` is a flat `R`-algebra, taking kernels commutes with base change
of modules from `R` to `S`.

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

* `IsBaseChange.of_left_exact` : If `S` is flat over `R`, `f₁` and `g₁` are injective,
  `i₂` and `i₃` is base change by `S`, then `i₁` is base change by `S`.

-/

@[expose] public section

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]

variable {M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [Module R M₁] [Module R M₂] [Module R M₃]
  [Module R N₁] [Module R N₂] [Module R N₃] [Module S N₁] [Module S N₂] [Module S N₃]
  [IsScalarTower R S N₁] [IsScalarTower R S N₂] [IsScalarTower R S N₃]
  (h₁ : M₁ →ₗ[R] N₁) (h₂ : M₂ →ₗ[R] N₂) (h₃ : M₃ →ₗ[R] N₃)
  {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃} {f' : N₁ →ₗ[S] N₂} {g' : N₂ →ₗ[S] N₃}

lemma IsBaseChange.of_left_exact (comm₁ : h₂.comp f = (f'.restrictScalars R).comp h₁)
    (comm₂ : h₃.comp g = (g'.restrictScalars R).comp h₂) [Module.Flat R S]
    (isb₂ : IsBaseChange S h₂) (isb₃ : IsBaseChange S h₃)
    (exact₁ : Function.Exact f g) (inj₁ : Function.Injective f)
    (exact₂ : Function.Exact f' g') (inj₂ : Function.Injective f') : IsBaseChange S h₁ := by
  simp only [IsBaseChange, IsTensorProduct] at isb₂ isb₃ ⊢
  refine LinearMap.bijective_of_bijective_of_injective_of_left_exact
    ((f.baseChange S).restrictScalars R) ((g.baseChange S).restrictScalars R)
    (f'.restrictScalars R) (g'.restrictScalars R) _ _ _ ?_ ?_ ?_ exact₂ isb₂ isb₃.1 ?_ inj₂
  · ext s m
    simpa using congr(s • ($comm₁ m)).symm
  · ext s m
    simpa using congr(s • ($comm₂ m)).symm
  · exact Module.Flat.lTensor_exact S exact₁
  · exact Module.Flat.lTensor_preserves_injective_linearMap f inj₁
