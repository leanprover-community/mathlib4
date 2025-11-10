/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Jujian Zhang
-/
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Localization of modules is an exact functor

## Main definitions

- `LocalizedModule.map_exact`: Localization of modules is an exact functor.
- `IsLocalizedModule.map_exact`: A variant expressed in terms of `IsLocalizedModule`.

-/

section

open IsLocalizedModule Function Submonoid

variable {R : Type*} [CommSemiring R] (S : Submonoid R)
variable {M₀ M₀'} [AddCommMonoid M₀] [AddCommMonoid M₀'] [Module R M₀] [Module R M₀']
variable (f₀ : M₀ →ₗ[R] M₀') [IsLocalizedModule S f₀]
variable {M₁ M₁'} [AddCommMonoid M₁] [AddCommMonoid M₁'] [Module R M₁] [Module R M₁']
variable (f₁ : M₁ →ₗ[R] M₁') [IsLocalizedModule S f₁]
variable {M₂ M₂'} [AddCommMonoid M₂] [AddCommMonoid M₂'] [Module R M₂] [Module R M₂']
variable (f₂ : M₂ →ₗ[R] M₂') [IsLocalizedModule S f₂]

/-- Localization of modules is an exact functor, proven here for `LocalizedModule`.
See `IsLocalizedModule.map_exact` for the more general version. -/
lemma LocalizedModule.map_exact (g : M₀ →ₗ[R] M₁) (h : M₁ →ₗ[R] M₂) (ex : Exact g h) :
    Exact (map S (mkLinearMap S M₀) (mkLinearMap S M₁) g)
    (map S (mkLinearMap S M₁) (mkLinearMap S M₂) h) :=
  fun y ↦ Iff.intro
    (induction_on
      (fun m s hy ↦ by
        rw [map_LocalizedModules, ← zero_mk 1, mk_eq, one_smul, smul_zero] at hy
        obtain ⟨a, aS, ha⟩ := Subtype.exists.1 hy
        rw [smul_zero, mk_smul, ← LinearMap.map_smul, ex (a • m)] at ha
        rcases ha with ⟨x, hx⟩
        use mk x (⟨a, aS⟩ * s)
        rw [map_LocalizedModules, hx, ← mk_cancel_common_left ⟨a, aS⟩ s m, mk_smul])
      y)
    fun ⟨x, hx⟩ ↦ by
      revert hx
      refine induction_on (fun m s hx ↦ ?_) x
      rw [← hx, map_LocalizedModules, map_LocalizedModules, (ex (g m)).2 ⟨m, rfl⟩, zero_mk]

/-- Localization of modules is an exact functor. -/
theorem IsLocalizedModule.map_exact (g : M₀ →ₗ[R] M₁) (h : M₁ →ₗ[R] M₂) (ex : Function.Exact g h) :
    Function.Exact (map S f₀ f₁ g) (map S f₁ f₂ h) :=
  Function.Exact.of_ladder_linearEquiv_of_exact
    (map_iso_commute S f₀ f₁ g) (map_iso_commute S f₁ f₂ h) (LocalizedModule.map_exact S g h ex)

end
