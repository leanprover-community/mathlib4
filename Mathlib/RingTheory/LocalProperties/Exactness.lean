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

section isLocalized_maximal

open IsLocalizedModule

variable {R A M N} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [Module A M] [AddCommMonoid N] [Module R N] [Module A N]

variable
  (Rₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], CommSemiring (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Algebra R (Rₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsLocalization.AtPrime (Rₚ P) P]
  (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Mₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Mₚ P)]
  (f : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
  [inst : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (f P)]
  (Nₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Nₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Nₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Nₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Nₚ P)]
  (g : ∀ (P : Ideal R) [P.IsMaximal], N →ₗ[R] Nₚ P)
  [inst : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (g P)]
  (h : M →ₗ[R] N)

theorem injective_of_isLocalized_maximal
    (H : ∀ (P : Ideal R) (_ : P.IsMaximal), Function.Injective (map P.primeCompl (f P) (g P) h)) :
    Function.Injective h :=
  fun x y eq ↦ Module.eq_of_localization_maximal Mₚ f x y
    (fun P hP ↦ H P hP ((map_apply P.primeCompl (f P) (g P) h y) ▸
      (map_apply P.primeCompl (f P) (g P) h x) ▸ congr_arg (g P) eq))

theorem surjective_of_isLocalized_maximal
    (H : ∀ (P : Ideal R) (_ : P.IsMaximal), Function.Surjective (map P.primeCompl (f P) (g P) h)) :
    Function.Surjective h :=
  range_eq_top.mp <| eq_top_of_localization₀_maximal Nₚ g _ <|
    fun P hP ↦ (range_localizedMap_eq_localized₀_range _ (f P) (g P) h).symm.trans <|
    range_eq_top.mpr <| H P hP

theorem bijective_of_isLocalized_maximal
    (H : ∀ (P : Ideal R) (_ : P.IsMaximal), Function.Bijective (map P.primeCompl (f P) (g P) h)) :
    Function.Bijective h :=
  ⟨injective_of_isLocalized_maximal Mₚ f Nₚ g h fun J hJ => (H J hJ).1,
  surjective_of_isLocalized_maximal Mₚ f Nₚ g h fun J hJ => (H J hJ).2⟩

variable {L : Type*} [AddCommMonoid L] [Module R L] [Module A L]
variable (Lₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
  [∀ (P : Ideal R) [P.IsMaximal], AddCommMonoid (Lₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module R (Lₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], Module (Rₚ P) (Lₚ P)]
  [∀ (P : Ideal R) [P.IsMaximal], IsScalarTower R (Rₚ P) (Lₚ P)]
  (h : ∀ (P : Ideal R) [P.IsMaximal], L →ₗ[R] Lₚ P)
  [inst : ∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (h P)]

include Rₚ
theorem exact_of_isLocalized_maximal (F : M →ₗ[R] N) (G : N →ₗ[R] L)
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

end isLocalized_maximal

section localized_maximal

variable {R M N : Type*} [CommSemiring R]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N)

theorem injective_of_localized_maximal
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), Function.Injective (map J.primeCompl f)) :
    Function.Injective f := injective_of_isLocalized_maximal
      (fun P _ ↦ LocalizedModule P.primeCompl M) (fun P _ ↦ mkLinearMap P.primeCompl M)
      (fun P _ ↦ LocalizedModule P.primeCompl N) (fun P _ ↦ mkLinearMap P.primeCompl N)
      f h

theorem surjective_of_localized_maximal
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), Function.Surjective (map J.primeCompl f)) :
    Function.Surjective f := surjective_of_isLocalized_maximal
      (fun P _ ↦ LocalizedModule P.primeCompl M) (fun P _ ↦ mkLinearMap P.primeCompl M)
      (fun P _ ↦ LocalizedModule P.primeCompl N) (fun P _ ↦ mkLinearMap P.primeCompl N)
      f h

theorem bijective_of_localized_maximal
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal), Function.Bijective (map J.primeCompl f)) :
    Function.Bijective f := ⟨injective_of_localized_maximal _ fun J hJ => (h J hJ).1,
  surjective_of_localized_maximal _ fun J hJ => (h J hJ).2⟩

theorem exact_of_localized_maximal {M N L : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N]
    [Module R N] [AddCommMonoid L] [Module R L] (f : M →ₗ[R] N) (g : N →ₗ[R] L)
    (h : ∀ (J : Ideal R) (_ : J.IsMaximal),
    Function.Exact (map J.primeCompl f) (map J.primeCompl g)) :
    Function.Exact f g := exact_of_isLocalized_maximal (fun P _ ↦ Localization.AtPrime P)
      (fun P _ ↦ LocalizedModule P.primeCompl M) (fun P _ ↦ mkLinearMap P.primeCompl M)
      (fun P _ ↦ LocalizedModule P.primeCompl N) (fun P _ ↦ mkLinearMap P.primeCompl N)
      (fun P _ ↦ LocalizedModule P.primeCompl L) (fun P _ ↦ mkLinearMap P.primeCompl L)
      f g h

end localized_maximal

section isLocalized_span

open IsLocalizedModule

variable {R A M N : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid N] [Module R N] [Module A N] [AddCommMonoid M] [Module R M] [Module A M]
  (s : Set R) (spn : Ideal.span s = ⊤)
include spn

variable
  (Rₚ : ∀ _ : s, Type*)
  [∀ r : s, CommSemiring (Rₚ r)]
  [∀ r : s, Algebra R (Rₚ r)]
  [∀ r : s, IsLocalization.Away r.1 (Rₚ r)]
  (Mₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommMonoid (Mₚ r)]
  [∀ r : s, Module R (Mₚ r)]
  [∀ r : s, Module (Rₚ r) (Mₚ r)]
  [∀ r : s, IsScalarTower R (Rₚ r) (Mₚ r)]
  (f : ∀ r : s, M →ₗ[R] Mₚ r)
  [inst : ∀ r : s, IsLocalizedModule (Submonoid.powers r.1) (f r)]
  (Nₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommMonoid (Nₚ r)]
  [∀ r : s, Module R (Nₚ r)]
  [∀ r : s, Module (Rₚ r) (Nₚ r)]
  [∀ r : s, IsScalarTower R (Rₚ r) (Nₚ r)]
  (g : ∀ r : s, N →ₗ[R] Nₚ r)
  [inst : ∀ r : s, IsLocalizedModule (Submonoid.powers r.1) (g r)]
  (h : M →ₗ[R] N)

theorem injective_of_isLocalized_span (H : ∀ r : s, Function.Injective
    (map (Submonoid.powers r.1) (f r) (g r) h)) : Function.Injective h :=
  fun x y eq ↦ eq_of_isLocalized_span s spn Mₚ f x y
    (fun r ↦ H r ((map_apply (Submonoid.powers r.1) (f r) (g r) h y) ▸
      (map_apply (Submonoid.powers r.1) (f r) (g r) h x) ▸ congr_arg (g r) eq))

theorem surjective_of_isLocalized_span (H : ∀ r : s, Function.Surjective
    (map (Submonoid.powers r.1) (f r) (g r) h)) : Function.Surjective h :=
  range_eq_top.mp <| eq_top_of_isLocalized₀_span s spn Nₚ g <| fun r ↦
  (range_localizedMap_eq_localized₀_range _ (f r) (g r) h).symm.trans <| range_eq_top.mpr <| H r

theorem bijective_of_isLocalized_span (H : ∀ r : s, Function.Bijective
    (map (Submonoid.powers r.1) (f r) (g r) h)) : Function.Bijective h :=
  ⟨injective_of_isLocalized_span _ spn Mₚ f Nₚ g h fun r => (H r).1,
  surjective_of_isLocalized_span _ spn Mₚ f Nₚ g h fun r => (H r).2⟩

variable {L : Type*} [AddCommMonoid L] [Module R L] [Module A L]
  (Lₚ : ∀ _ : s, Type*)
  [∀ r : s, AddCommMonoid (Lₚ r)]
  [∀ r : s, Module R (Lₚ r)]
  [∀ r : s, Module (Rₚ r) (Lₚ r)]
  [∀ r : s, IsScalarTower R (Rₚ r) (Lₚ r)]
  (h : ∀ r : s, L →ₗ[R] Lₚ r)
  [inst : ∀ r : s, IsLocalizedModule (Submonoid.powers r.1) (h r)]
  (F : M →ₗ[R] N) (G : N →ₗ[R] L)

include Rₚ
lemma exact_of_isLocalized_span (H : ∀ r : s, Function.Exact
    (map (Submonoid.powers r.1) (f r) (g r) F)
      (map (Submonoid.powers r.1) (g r) (h r) G)) : Function.Exact F G := by
  simp only [LinearMap.exact_iff] at H ⊢
  apply Submodule.eq_of_isLocalized'_span s spn Rₚ Nₚ g
  intro r
  rw [LinearMap.localized'_range_eq_range_localizedMap (Rₚ r) _ (f r) (g r) F]
  rw [LinearMap.localized'_ker_eq_ker_localizedMap (Rₚ r) (Submonoid.powers r.1) (g r) (h r) G]
  have := SetLike.ext_iff.mp <| H r
  ext x
  simp only [mem_range, mem_ker, extendScalarsOfIsLocalization_apply'] at this ⊢
  exact this x

end isLocalized_span

section localized_span

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] (s : Set R) (spn : span s = ⊤) (f : M →ₗ[R] N)
include spn

theorem injective_of_localization_span (h : ∀ r : s, Function.Injective
    (map (Submonoid.powers r.1) f)) :
    Function.Injective f := injective_of_isLocalized_span s spn
      (fun r ↦ LocalizedModule (Submonoid.powers r.1) M)
      (fun r ↦ mkLinearMap (Submonoid.powers r.1) M)
      (fun r ↦ LocalizedModule (Submonoid.powers r.1) N)
      (fun r ↦ mkLinearMap (Submonoid.powers r.1) N) f h

theorem surjective_of_localization_span (h : ∀ r : s, Function.Surjective
    (map (Submonoid.powers r.1) f)) :
    Function.Surjective f := surjective_of_isLocalized_span s spn
      (fun r ↦ LocalizedModule (Submonoid.powers r.1) M)
      (fun r ↦ mkLinearMap (Submonoid.powers r.1) M)
      (fun r ↦ LocalizedModule (Submonoid.powers r.1) N)
      (fun r ↦ mkLinearMap (Submonoid.powers r.1) N) f h

theorem bijective_of_localization_span (h : ∀ r : s, Function.Bijective
    (map (Submonoid.powers r.1) f)) :
    Function.Bijective f :=
  ⟨injective_of_localization_span _ spn _ fun r => (h r).1,
  surjective_of_localization_span _ spn _ fun r => (h r).2⟩

lemma exact_of_localization_span {M N L : Type*} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] [AddCommMonoid L] [Module R L] (f : M →ₗ[R] N)
    (g : N →ₗ[R] L) (h : ∀ r : s, Function.Exact ((map (Submonoid.powers r.1) f))
      ((map (Submonoid.powers r.1) g))) : Function.Exact f g := exact_of_isLocalized_span s spn
      (fun r ↦ Localization.Away r.1) (fun r ↦ LocalizedModule (Submonoid.powers r.1) M)
      (fun r ↦ mkLinearMap (Submonoid.powers r.1) M)
      (fun r ↦ LocalizedModule (Submonoid.powers r.1) N)
      (fun r ↦ mkLinearMap (Submonoid.powers r.1) N)
      (fun r ↦ LocalizedModule (Submonoid.powers r.1) L)
      (fun r ↦ mkLinearMap (Submonoid.powers r.1) L) f g h

end localized_span
