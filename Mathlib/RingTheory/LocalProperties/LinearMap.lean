/-
Copyright (c) 2024 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sihan Su, Yongle Hu, Yi Song
-/
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.Algebra.Exact
/-!
# Local properties about linear maps

In this file, we show that injective, surjective, bijective (of linear maps) are local properties.

-/
open Submodule LocalizedModule Ideal LinearMap

section localization_maximal

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N)

theorem injective_of_localization
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), Function.Injective (map J.primeCompl f)) :
    Function.Injective f :=
  ker_eq_bot.mp <| eq_bot_of_localization_maximal' <|
  fun J hJ ↦ (localized'_ker_eq_ker_localizedMap _ _ _ _ f).trans <| ker_eq_bot.mpr <| h J hJ

theorem surjective_of_localization
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), Function.Surjective (map J.primeCompl f)) :
    Function.Surjective f :=
  range_eq_top.mp <| eq_top_of_localization_maximal' <|
  fun J hJ ↦ (localized'_range_eq_range_localizedMap _ _ _ _ f).trans <| range_eq_top.mpr <| h J hJ

theorem bijective_of_localization
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), Function.Bijective (map J.primeCompl f)) :
    Function.Bijective f :=
  ⟨injective_of_localization _ fun J hJ => (h J hJ).1,
  surjective_of_localization _ fun J hJ => (h J hJ).2⟩

theorem exact_of_localization {R M₀ M₁ M₂ : Type*} [CommRing R] [AddCommGroup M₀] [Module R M₀]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
(h : ∀ (J : Ideal R) (_ : J.IsMaximal), Function.Exact (map J.primeCompl f) (map J.primeCompl g)) :
    Function.Exact f g := by
  simp only [LinearMap.exact_iff] at h ⊢
  apply eq_of_localization_maximal'
  intro J hJ
  unfold localized
  rw [LinearMap.localized'_range_eq_range_localizedMap _ _ (mkLinearMap J.primeCompl M₀) _,
    LinearMap.localized'_ker_eq_ker_localizedMap _ _ _ (mkLinearMap J.primeCompl M₂)]
  exact h J hJ

end localization_maximal

section localization_finitespan

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  (s : Finset R) (spn : span (s : Set R) = ⊤) (f : M →ₗ[R] M')
include spn

theorem injective_of_localization_finitespan (h : ∀ r : s, Function.Injective
    (map (Submonoid.powers r.1) f)) :
    Function.Injective f :=
  ker_eq_bot.mp <| eq_bot_of_localization_finitespan _ spn <|
  fun r ↦ (localized'_ker_eq_ker_localizedMap _ _ _ _ f).trans <| ker_eq_bot.mpr <| h r

theorem surjective_of_localization_finitespan (h : ∀ r : s, Function.Surjective
    (map (Submonoid.powers r.1) f)) :
    Function.Surjective f :=
  range_eq_top.mp <| eq_top_of_localization_finitespan _ spn <|
  fun r ↦ (localized'_range_eq_range_localizedMap _ _ _ _ f).trans <| range_eq_top.mpr <| h r

theorem bijective_of_localization_finitespan (h : ∀ r : s, Function.Bijective
    (map (Submonoid.powers r.1) f)) :
    Function.Bijective f :=
  ⟨injective_of_localization_finitespan _ spn _ fun r => (h r).1,
  surjective_of_localization_finitespan _ spn _ fun r => (h r).2⟩

lemma exact_of_localization_finitespan {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [Module R M₀]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] (f : M₀ →ₗ[R] M₁)
    (g : M₁ →ₗ[R] M₂) (h : ∀ r : s, Function.Exact ((map (Submonoid.powers r.1) f))
      ((map (Submonoid.powers r.1) g))) : Function.Exact f g := by
  simp only [LinearMap.exact_iff] at h ⊢
  apply Submodule.eq_of_localization_finitespan _ spn
  intro r
  unfold localized
  rw [LinearMap.localized'_range_eq_range_localizedMap _ _ (mkLinearMap (Submonoid.powers r.1) M₀),
    LinearMap.localized'_ker_eq_ker_localizedMap _ _ _ (mkLinearMap (Submonoid.powers r.1) M₂)]
  exact h r

end localization_finitespan
