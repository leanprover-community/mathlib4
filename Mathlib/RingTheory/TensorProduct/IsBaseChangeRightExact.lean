/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang, Nailin Guan
-/
module

public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.Algebra.Exact
import Mathlib.Algebra.FiveLemma
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!

# Lemmas about `IsBaseChange` under exact sequences

In this file, we show that for an `R`-algebra `S` taking cokernels commutes with base change
of modules from `R` to `S`.
If `S` is a flat `R`-algebra, the same holds for kernels,
see `Mathlib.RingTheory.Flat.IsBaseChange`.

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

lemma IsBaseChange.of_right_exact (comm₁ : h₂.comp f = (f'.restrictScalars R).comp h₁)
    (comm₂ : h₃.comp g = (g'.restrictScalars R).comp h₂) (isb₁ : IsBaseChange S h₁)
    (isb₂ : IsBaseChange S h₂) (exact₁ : Function.Exact f g) (surj₁ : Function.Surjective g)
    (exact₂ : Function.Exact f' g') (surj₂ : Function.Surjective g') : IsBaseChange S h₃ := by
  simp only [IsBaseChange, IsTensorProduct] at isb₁ isb₂ ⊢
  refine LinearMap.bijective_of_surjective_of_bijective_of_right_exact
    ((f.baseChange S).restrictScalars R) ((g.baseChange S).restrictScalars R)
    (f'.restrictScalars R) (g'.restrictScalars R) _ _ _ ?_ ?_ ?_ exact₂ isb₁.2 isb₂ ?_ surj₂
  · ext s m
    simpa using congr(s • ($comm₁ m)).symm
  · ext s m
    simpa using congr(s • ($comm₂ m)).symm
  · exact lTensor_exact S exact₁ surj₁
  · exact LinearMap.lTensor_surjective S surj₁
