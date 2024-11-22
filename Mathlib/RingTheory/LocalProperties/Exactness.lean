/-
Copyright (c) 2024 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sihan Su, Yongle Hu, Yi Song
-/
import Mathlib.Algebra.Exact
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Local properties about linear maps

In this file, we show that
injectivity, surjectivity, bijectivity and exactness of linear maps are local properties.
More precisely, we show that these can be checked at maximal ideals and on standard covers.

-/
open Submodule LocalizedModule Ideal LinearMap

section isLocalized_maximal

open IsLocalizedModule

variable {R A M N} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module A M] [AddCommGroup N] [Module R N] [Module A N]

variable
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]
  (Nₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Nₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Nₚ P)]
  (g : ∀ (P : Ideal R) [P.IsMaximal], N →ₗ[R] Nₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (g P)]
  (k : M →ₗ[R] N)

theorem injective_of_isLocalized_maximal
    (H : ∀ (P : Ideal R) (_ : P.IsMaximal), Function.Injective (map P.primeCompl (f P) (g P) k)) :
    Function.Injective k :=
  ker_eq_bot.mp <| eq_bot_of_localization₀_maximal Mₚ f _ <| fun P hP ↦
    (ker_localizedMap_eq_localized₀_ker _ (f P) (g P) k).symm.trans <| ker_eq_bot.mpr <| H P hP

theorem surjective_of_isLocalized_maximal
    (H : ∀ (P : Ideal R) (_ : P.IsMaximal), Function.Surjective (map P.primeCompl (f P) (g P) k)) :
    Function.Surjective k :=
  range_eq_top.mp <| eq_top_of_localization₀_maximal Nₚ g _ <|
    fun P hP ↦ (range_localizedMap_eq_localized₀_range _ (f P) (g P) k).symm.trans <|
    range_eq_top.mpr <| H P hP

theorem bijective_of_isLocalized_maximal
    (H : ∀ (P : Ideal R) (_ : P.IsMaximal), Function.Bijective (map P.primeCompl (f P) (g P) k)) :
    Function.Bijective k :=
  ⟨injective_of_isLocalized_maximal Mₚ f Nₚ g k fun J hJ ↦ (H J hJ).1,
  surjective_of_isLocalized_maximal Mₚ f Nₚ g k fun J hJ ↦ (H J hJ).2⟩

variable {L : Type*} [AddCommGroup L] [Module R L] [Module A L]
variable (Lₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Lₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Lₚ P)]
  (h : ∀ (P : Ideal R) [P.IsMaximal], L →ₗ[R] Lₚ P)
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (h P)]

theorem exact_of_isLocalized_maximal (F : M →ₗ[R] N) (G : N →ₗ[R] L)
    (H : ∀ (J : Ideal R) (_ : J.IsMaximal),
    Function.Exact (map J.primeCompl (f J) (g J) F) (map J.primeCompl (g J) (h J) G)) :
    Function.Exact F G := by
  simp only [LinearMap.exact_iff] at H ⊢
  apply eq_of_localization₀_maximal Nₚ g
  intro J hJ
  rw [← LinearMap.range_localizedMap_eq_localized₀_range _ (f J) (g J) F,
    ← LinearMap.ker_localizedMap_eq_localized₀_ker J.primeCompl (g J) (h J) G]
  have := SetLike.ext_iff.mp <| H J hJ
  ext x
  simp only [mem_range, mem_ker] at this ⊢
  exact this x

end isLocalized_maximal

section localized_maximal

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (f : M →ₗ[R] N)

theorem injective_of_localized_maximal
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), Function.Injective (map J.primeCompl f)) :
    Function.Injective f :=
  injective_of_isLocalized_maximal
    _ (fun P _ ↦ mkLinearMap P.primeCompl M)
    _ (fun P _ ↦ mkLinearMap P.primeCompl N) f h

theorem surjective_of_localized_maximal
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), Function.Surjective (map J.primeCompl f)) :
    Function.Surjective f :=
  surjective_of_isLocalized_maximal
    _ (fun P _ ↦ mkLinearMap P.primeCompl M)
    _ (fun P _ ↦ mkLinearMap P.primeCompl N) f h

theorem bijective_of_localized_maximal
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), Function.Bijective (map J.primeCompl f)) :
    Function.Bijective f :=
  ⟨injective_of_localized_maximal _ fun J hJ ↦ (h J hJ).1,
  surjective_of_localized_maximal _ fun J hJ ↦ (h J hJ).2⟩

theorem exact_of_localized_maximal {M N L : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup L] [Module R L] (f : M →ₗ[R] N) (g : N →ₗ[R] L)
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal),
    Function.Exact (map J.primeCompl f) (map J.primeCompl g)) :
    Function.Exact f g :=
  exact_of_isLocalized_maximal
    _ (fun P _ ↦ mkLinearMap P.primeCompl M)
    _ (fun P _ ↦ mkLinearMap P.primeCompl N)
    _ (fun P _ ↦ mkLinearMap P.primeCompl L) f g h

end localized_maximal

section isLocalized_span

open IsLocalizedModule

variable {R A M N : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup N] [Module R N]
  [Module A N] [AddCommGroup M] [Module R M] [Module A M] (s : Set R) (spn : Ideal.span s = ⊤)
include spn

variable
  (Mₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommGroup (Mₚ r)]
  [∀ r : s, Module R (Mₚ r)]
  (f : ∀ r : s, M →ₗ[R] Mₚ r)
  [∀ r : s, IsLocalizedModule (.powers r.1) (f r)]
  (Nₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommGroup (Nₚ r)]
  [∀ r : s, Module R (Nₚ r)]
  (g : ∀ r : s, N →ₗ[R] Nₚ r)
  [∀ r : s, IsLocalizedModule (.powers r.1) (g r)]
  (k : M →ₗ[R] N)

theorem injective_of_isLocalized_span
    (H : ∀ r : s, Function.Injective (map (.powers r.1) (f r) (g r) k)) :
    Function.Injective k :=
  ker_eq_bot.mp <| eq_bot_of_isLocalized₀_span s spn Mₚ f fun r ↦
    (ker_localizedMap_eq_localized₀_ker _ (f r) (g r) k).symm.trans <| ker_eq_bot.mpr <| H r

theorem surjective_of_isLocalized_span
    (H : ∀ r : s, Function.Surjective (map (.powers r.1) (f r) (g r) k)) :
    Function.Surjective k :=
  range_eq_top.mp <| eq_top_of_isLocalized₀_span s spn Nₚ g fun r ↦
    (range_localizedMap_eq_localized₀_range _ (f r) (g r) k).symm.trans <| range_eq_top.mpr <| H r

theorem bijective_of_isLocalized_span
    (H : ∀ r : s, Function.Bijective (map (.powers r.1) (f r) (g r) k)) :
    Function.Bijective k :=
  ⟨injective_of_isLocalized_span _ spn Mₚ f Nₚ g k fun r ↦ (H r).1,
  surjective_of_isLocalized_span _ spn Mₚ f Nₚ g k fun r ↦ (H r).2⟩

variable {L : Type*} [AddCommGroup L] [Module R L] [Module A L]
  (Lₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommGroup (Lₚ r)]
  [∀ r : s, Module R (Lₚ r)]
  (h : ∀ r : s, L →ₗ[R] Lₚ r)
  [∀ r : s, IsLocalizedModule (.powers r.1) (h r)]
  (F : M →ₗ[R] N) (G : N →ₗ[R] L)

lemma exact_of_isLocalized_span (H : ∀ r : s, Function.Exact
      (map (.powers r.1) (f r) (g r) F) (map (.powers r.1) (g r) (h r) G)) :
    Function.Exact F G := by
  simp only [LinearMap.exact_iff] at H ⊢
  apply Submodule.eq_of_isLocalized₀_span s spn Nₚ g
  intro r
  rw [← LinearMap.range_localizedMap_eq_localized₀_range _ (f r) (g r) F]
  rw [← LinearMap.ker_localizedMap_eq_localized₀_ker (.powers r.1) (g r) (h r) G]
  have := SetLike.ext_iff.mp <| H r
  ext x
  simp only [mem_range, mem_ker] at this ⊢
  exact this x

end isLocalized_span

section localized_span

variable {R M M' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  (s : Set R) (spn : span s = ⊤) (f : M →ₗ[R] M')
include spn

theorem injective_of_localization_span
    (h : ∀ r : s, Function.Injective (map (.powers r.1) f)) :
    Function.Injective f :=
  injective_of_isLocalized_span s spn
    _ (fun r ↦ mkLinearMap (.powers r.1) M)
    _ (fun r ↦ mkLinearMap (.powers r.1) M') f h

theorem surjective_of_localization_span
    (h : ∀ r : s, Function.Surjective (map (.powers r.1) f)) :
    Function.Surjective f :=
  surjective_of_isLocalized_span s spn
    _ (fun r ↦ mkLinearMap (.powers r.1) M)
    _ (fun r ↦ mkLinearMap (.powers r.1) M') f h

theorem bijective_of_localization_span
    (h : ∀ r : s, Function.Bijective (map (.powers r.1) f)) :
    Function.Bijective f :=
  ⟨injective_of_localization_span _ spn _ fun r ↦ (h r).1,
  surjective_of_localization_span _ spn _ fun r ↦ (h r).2⟩

lemma exact_of_localization_span {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [Module R M₀]
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (h : ∀ r : s, Function.Exact (map (.powers r.1) f) (map (.powers r.1) g)) :
    Function.Exact f g :=
  exact_of_isLocalized_span s spn
    _ (fun r ↦ mkLinearMap (.powers r.1) M₀)
    _ (fun r ↦ mkLinearMap (.powers r.1) M₁)
    _ (fun r ↦ mkLinearMap (.powers r.1) M₂) f g h

end localized_span
