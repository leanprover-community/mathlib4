/-
Copyright (c) 2024 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sihan Su, Yongle Hu, Yi Song
-/
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.Algebra.Exact
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Local properties about linear maps

In this file, we show that
injectivity, surjectivity, bijectivity and exactness of linear maps are local properties.
More precisely, we show that these can be checked at maximal ideals and on standard covers.

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

theorem exact_of_localization {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [Module R M₀] [AddCommGroup M₁]
    [Module R M₁] [AddCommGroup M₂] [Module R M₂] (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal),
    Function.Exact (map J.primeCompl f) (map J.primeCompl g)) :
    Function.Exact f g := by
  simp only [LinearMap.exact_iff] at h ⊢
  apply eq_of_localization_maximal'
  intro J hJ
  unfold localized
  rw [LinearMap.localized'_range_eq_range_localizedMap _ _ (mkLinearMap J.primeCompl M₀) _,
    LinearMap.localized'_ker_eq_ker_localizedMap _ _ _ (mkLinearMap J.primeCompl M₂)]
  exact h J hJ

end localization_maximal

section localization_maximal'

open IsLocalizedModule

variable {R A M N} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [AddCommGroup N] [Module R N] [Module A N]

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommRing (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [inst : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]
  (Nₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Nₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Nₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Nₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Nₚ P)]
  (g : ∀ (P : Ideal R) [P.IsMaximal], N →ₗ[R] Nₚ P)
  [inst : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (g P)]
  (k : M →ₗ[R] N)
include Rₚ

/-- A variant of `injective_of_localization` that accepts `IsLocalizedModule`.-/
theorem injective_of_localization'
    (H : ∀ (P : Ideal R) (_ : P.IsMaximal), Function.Injective (map P.primeCompl (f P) (g P) k)) :
    Function.Injective k :=
  ker_eq_bot.mp <| eq_bot_of_localization_maximal Rₚ Mₚ f _ <| fun P hP ↦
    (localized'_ker_eq_ker_localizedMap (Rₚ P) _ (f P) (g P) k).trans <| ker_eq_bot.mpr <| H P hP

/-- A variant of `surjective_of_localization` that accepts `IsLocalizedModule`.-/
theorem surjective_of_localization'
    (H : ∀ (P : Ideal R) (_ : P.IsMaximal), Function.Surjective (map P.primeCompl (f P) (g P) k)) :
    Function.Surjective k :=
  range_eq_top.mp <| eq_top_of_localization_maximal Rₚ Nₚ g _ <|
    fun P hP ↦ (localized'_range_eq_range_localizedMap (Rₚ P) _ (f P) (g P) k).trans <|
    range_eq_top.mpr <| H P hP

/-- A variant of `bijective_of_localization` that accepts `IsLocalizedModule`.-/
theorem bijective_of_localization'
    (H : ∀ (P : Ideal R) (_ : P.IsMaximal), Function.Bijective (map P.primeCompl (f P) (g P) k)) :
    Function.Bijective k :=
  ⟨injective_of_localization' Rₚ Mₚ f Nₚ g k fun J hJ => (H J hJ).1,
  surjective_of_localization' Rₚ Mₚ f Nₚ g k fun J hJ => (H J hJ).2⟩

variable {L : Type*} [AddCommGroup L] [Module R L] [Module A L]
variable (Lₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Lₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Lₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Lₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Lₚ P)]
  (h : ∀ (P : Ideal R) [P.IsMaximal], L →ₗ[R] Lₚ P)
  [inst : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (h P)]

/-- A variant of `exact_of_localization` that accepts `IsLocalizedModule`.-/
theorem exact_of_localization' (F : M →ₗ[R] N) (G : N →ₗ[R] L)
    (H : ∀ (J : Ideal R) (_ : J.IsMaximal),
    Function.Exact (map J.primeCompl (f J) (g J) F) (map J.primeCompl (g J) (h J) G)) :
    Function.Exact F G := by
  simp only [LinearMap.exact_iff] at H ⊢
  apply eq_of_localization_maximal Rₚ Nₚ g
  intro J hJ
  rw [LinearMap.localized'_range_eq_range_localizedMap (Rₚ J) _ (f J) (g J) F,
    LinearMap.localized'_ker_eq_ker_localizedMap (Rₚ J) J.primeCompl (g J) (h J) G]
  have := SetLike.ext_iff.mp <| H J hJ
  ext x
  simp only [mem_range, mem_ker, extendScalarsOfIsLocalization_apply'] at this ⊢
  exact this x

end localization_maximal'

section localization_span

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  (s : Set R) (spn : span s = ⊤) (f : M →ₗ[R] M')
include spn

theorem injective_of_localization_span (h : ∀ r : s, Function.Injective
    (map (Submonoid.powers r.1) f)) :
    Function.Injective f :=
  ker_eq_bot.mp <| eq_bot_of_localization_span _ spn <|
  fun r ↦ (localized'_ker_eq_ker_localizedMap _ _ _ _ f).trans <| ker_eq_bot.mpr <| h r

theorem surjective_of_localization_span (h : ∀ r : s, Function.Surjective
    (map (Submonoid.powers r.1) f)) :
    Function.Surjective f :=
  range_eq_top.mp <| eq_top_of_localization_span _ spn <|
  fun r ↦ (localized'_range_eq_range_localizedMap _ _ _ _ f).trans <| range_eq_top.mpr <| h r

theorem bijective_of_localization_span (h : ∀ r : s, Function.Bijective
    (map (Submonoid.powers r.1) f)) :
    Function.Bijective f :=
  ⟨injective_of_localization_span _ spn _ fun r => (h r).1,
  surjective_of_localization_span _ spn _ fun r => (h r).2⟩

lemma exact_of_localization_span {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [Module R M₀]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] (f : M₀ →ₗ[R] M₁)
    (g : M₁ →ₗ[R] M₂) (h : ∀ r : s, Function.Exact ((map (Submonoid.powers r.1) f))
      ((map (Submonoid.powers r.1) g))) : Function.Exact f g := by
  simp only [LinearMap.exact_iff] at h ⊢
  apply Submodule.eq_of_localization_span _ spn
  intro r
  unfold localized
  rw [LinearMap.localized'_range_eq_range_localizedMap _ _ (mkLinearMap (Submonoid.powers r.1) M₀),
    LinearMap.localized'_ker_eq_ker_localizedMap _ _ _ (mkLinearMap (Submonoid.powers r.1) M₂)]
  exact h r

end localization_span

section localization_span'

open IsLocalizedModule

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup N] [Module R N]
  [Module A N] [AddCommGroup M] [Module R M] [Module A M] (s : Set R) (spn : Ideal.span s = ⊤)
include spn

variable
  (Rₚ : ∀ _ : s, Type*)
  [∀ r : s, CommRing (Rₚ r)]
  [∀ r : s, Algebra R (Rₚ r)]
  [∀ r : s, IsLocalization.Away r.1 (Rₚ r)]
  (Mₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommGroup (Mₚ r)]
  [∀ r : s, Module R (Mₚ r)]
  [∀ r : s, Module (Rₚ r) (Mₚ r)]
  [∀ r : s, IsScalarTower R (Rₚ r) (Mₚ r)]
  (f : ∀ r : s, M →ₗ[R] Mₚ r)
  [inst : ∀ r : s, IsLocalizedModule (Submonoid.powers r.1) (f r)]
  (Nₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommGroup (Nₚ r)]
  [∀ r : s, Module R (Nₚ r)]
  [∀ r : s, Module (Rₚ r) (Nₚ r)]
  [∀ r : s, IsScalarTower R (Rₚ r) (Nₚ r)]
  (g : ∀ r : s, N →ₗ[R] Nₚ r)
  [inst : ∀ r : s, IsLocalizedModule (Submonoid.powers r.1) (g r)]
  (k : M →ₗ[R] N)
include Rₚ

/-- A variant of `injective_of_localization_span` that accepts `IsLocalizedModule`.-/
theorem injective_of_localization_span' (H : ∀ r : s, Function.Injective
    (map (Submonoid.powers r.1) (f r) (g r) k)) : Function.Injective k :=
  ker_eq_bot.mp <| eq_bot_of_localization_span' s spn Rₚ Mₚ f <|
  fun r ↦ (localized'_ker_eq_ker_localizedMap _ _ (f r) (g r) k).trans <| ker_eq_bot.mpr <| H r

/-- A variant of `surjective_of_localization_span` that accepts `IsLocalizedModule`.-/
theorem surjective_of_localization_span' (H : ∀ r : s, Function.Surjective
    (map (Submonoid.powers r.1) (f r) (g r) k)) : Function.Surjective k :=
  range_eq_top.mp <| eq_top_of_localization_span' s spn Rₚ Nₚ g <| fun r ↦
  (localized'_range_eq_range_localizedMap _ _ (f r) (g r) k).trans <| range_eq_top.mpr <| H r

/-- A variant of `bijective_of_localization_span` that accepts `IsLocalizedModule`.-/
theorem bijective_of_localization_span' (H : ∀ r : s, Function.Bijective
    (map (Submonoid.powers r.1) (f r) (g r) k)) : Function.Bijective k :=
  ⟨injective_of_localization_span' _ spn Rₚ Mₚ f Nₚ g k fun r => (H r).1,
  surjective_of_localization_span' _ spn Rₚ Mₚ f Nₚ g k fun r => (H r).2⟩

variable {L : Type*} [AddCommGroup L] [Module R L] [Module A L]
  (Lₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommGroup (Lₚ r)]
  [∀ r : s, Module R (Lₚ r)]
  [∀ r : s, Module (Rₚ r) (Lₚ r)]
  [∀ r : s, IsScalarTower R (Rₚ r) (Lₚ r)]
  (h : ∀ r : s, L →ₗ[R] Lₚ r)
  [inst : ∀ r : s, IsLocalizedModule (Submonoid.powers r.1) (h r)]
  (F : M →ₗ[R] N) (G : N →ₗ[R] L)

/-- A variant of `exact_of_localization_span` that accepts `IsLocalizedModule`.-/
lemma exact_of_localization_span' (H : ∀ r : s, Function.Exact
    (map (Submonoid.powers r.1) (f r) (g r) F)
      (map (Submonoid.powers r.1) (g r) (h r) G)) : Function.Exact F G := by
  simp only [LinearMap.exact_iff] at H ⊢
  apply Submodule.eq_of_localization_span' s spn Rₚ Nₚ g
  intro r
  rw [LinearMap.localized'_range_eq_range_localizedMap (Rₚ r) _ (f r) (g r) F]
  rw [LinearMap.localized'_ker_eq_ker_localizedMap (Rₚ r) (Submonoid.powers r.1) (g r) (h r) G]
  have := SetLike.ext_iff.mp <| H r
  ext x
  simp only [mem_range, mem_ker, extendScalarsOfIsLocalization_apply'] at this ⊢
  exact this x

end localization_span'
