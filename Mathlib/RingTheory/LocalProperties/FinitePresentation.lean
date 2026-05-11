/-
Copyright (c) 2026 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sihan Su, Yongle Hu, Yi Song
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# `Module.FinitePresentation` is a local property

In this file, we prove that `Module.FinitePresentation` is a local property.

## Main results
* `Module.FinitePresentation.of_localizationSpan` : If there exists a set `{ r }` of `R` that
  generates the unit ideal and such that `Mᵣ` is a finitely presented `Rᵣ`-module for each `r`,
  then `M` is a finitely presented `R`-module.
-/

public section

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] (s : Set R)

theorem Module.FinitePresentation.of_localizationSpan' (hs : Ideal.span s = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ (g : s), AddCommGroup (Mₚ g)] [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type*} [∀ (g : s), CommRing (Rₚ g)] [∀ (g : s), Algebra R (Rₚ g)]
    [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (ϕ : ∀ (g : s), M →ₗ[R] Mₚ g) [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (h : ∀ (g : s), Module.FinitePresentation (Rₚ g) (Mₚ g)) :
    Module.FinitePresentation R M := by
  have : Module.Finite R M :=
    Module.Finite.of_localizationSpan' (Rₚ := Rₚ) s hs ϕ (fun _ ↦ inferInstance)
  obtain ⟨n, f, fsurj⟩ := Module.Finite.exists_fin' R M
  rw [← Module.FinitePresentation.fg_ker_iff f fsurj]
  refine f.ker.of_localizationSpan' s hs (Rₚ := Rₚ)
    (fun g ↦ TensorProduct.mk R (Rₚ g) (Fin n → R) 1) (fun g ↦ ?_)
  rw [LinearMap.localized'_ker_eq_ker_localizedMap (Rₚ g) (Submonoid.powers g.1) _ (ϕ g) f]
  apply Module.FinitePresentation.fg_ker
  rw [← LinearMap.range_eq_top] at fsurj ⊢
  simp [← LinearMap.localized'_range_eq_range_localizedMap (Rₚ g) (Submonoid.powers g.1), fsurj]

/-- If there exists a set `{ r }` of `R` that generates the unit ideal and such that
  `Mᵣ` is a finitely presented `Rᵣ`-module for each `r`, then `M` is a finitely presented
  `R`-module. -/
theorem Module.FinitePresentation.of_localizationSpan (hs : Ideal.span s = ⊤)
    (h : ∀ g : s, Module.FinitePresentation (Localization.Away g.1) (LocalizedModule.Away g.1 M)) :
    Module.FinitePresentation R M :=
  of_localizationSpan' s hs (fun g ↦ LocalizedModule.mkLinearMap (Submonoid.powers g.1) M) h
