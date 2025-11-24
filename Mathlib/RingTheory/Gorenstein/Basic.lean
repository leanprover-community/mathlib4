/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.RingTheory.Gorenstein.Defs
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.LocalProperties.InjectiveDimension

/-!

# Basic Properties of Gorenstein Local Ring

-/

@[expose] public section

universe v u

variable (R : Type u) [CommRing R]

open CategoryTheory

section

variable {R} in
lemma isGoresteinLocalRing_localization [IsGorensteinLocalRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] : IsGorensteinLocalRing (Localization.AtPrime p) := by
  rw [isGorensteinLocalRing_def]
  let le := injectiveDimension_le_injectiveDimension_of_isLocalizedModule p.primeCompl
    (ModuleCat.of R R)
  have : injectiveDimension ((ModuleCat.of R R).localizedModule p.primeCompl) ≠ ⊤ :=
    ne_top_of_le_ne_top ((isGorensteinLocalRing_def R).mp ‹_›) le
  let e' : LocalizedModule p.primeCompl R ≃ₗ[R] Localization.AtPrime p :=
    IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl R) (Algebra.linearMap R (Localization.AtPrime p))
  let e : ((ModuleCat.of R R).localizedModule p.primeCompl) ≅
    (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p)) :=
    ((Shrink.linearEquiv.{u} (Localization.AtPrime p) _).trans
    (e'.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p))).toModuleIso
  simpa [← injectiveDimension_eq_of_iso e] using this

variable {R} in
lemma isGoresteinLocalRing_of_isLocalizationAtPrime [IsGorensteinLocalRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (Rₚ : Type*) [CommRing Rₚ] [Algebra R Rₚ]
    [IsLocalization.AtPrime Rₚ p] : IsGorensteinLocalRing Rₚ :=
  let _ := isGoresteinLocalRing_localization p
  IsGorensteinLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) Rₚ).toRingEquiv

end

section

lemma isGorensteinRing_iff [IsNoetherianRing R] : IsGorensteinRing R ↔
    ∀ m : Ideal R, ∀ (_ : m.IsMaximal), IsGorensteinLocalRing (Localization.AtPrime m) := by
  refine ⟨fun ⟨h⟩ ↦ fun m hm ↦ h m (Ideal.IsMaximal.isPrime hm), fun h ↦ ⟨fun p hp ↦  ?_⟩⟩
  rcases Ideal.exists_le_maximal p (Ideal.IsPrime.ne_top hp) with ⟨m, hm, le⟩
  have := h m hm
  let Rₘ := Localization.AtPrime m
  let Rₚ := Localization.AtPrime p
  have disj := (Set.disjoint_compl_left_iff_subset.mpr le)
  have : (p.map (algebraMap R Rₘ)).IsPrime := by
    simpa [IsLocalization.isPrime_iff_isPrime_disjoint m.primeCompl Rₘ, hp,
      IsLocalization.comap_map_of_isPrime_disjoint m.primeCompl Rₘ p hp disj] using disj
  have le' : m.primeCompl ≤ p.primeCompl := by simpa [Ideal.primeCompl] using le
  let : Algebra Rₘ Rₚ := IsLocalization.localizationAlgebraOfSubmonoidLe Rₘ Rₚ _ _ le'
  have := IsLocalization.localization_isScalarTower_of_submonoid_le Rₘ Rₚ _ _ le'
  have : IsLocalization.AtPrime (Localization.AtPrime (Ideal.map (algebraMap R Rₘ) p)) p := by
    convert IsLocalization.isLocalization_atPrime_localization_atPrime m.primeCompl
      (p.map (algebraMap R Rₘ))
    rw [IsLocalization.comap_map_of_isPrime_disjoint m.primeCompl Rₘ p hp disj]
  let e' := (IsLocalization.algEquiv p.primeCompl Rₚ
      (Localization.AtPrime (Ideal.map (algebraMap R Rₘ) p)))
  let e : Rₚ ≃ₐ[Rₘ] Localization.AtPrime (Ideal.map (algebraMap R Rₘ) p) :=
    AlgEquiv.ofLinearEquiv (LinearEquiv.extendScalarsOfIsLocalization m.primeCompl Rₘ e')
      (map_one e') (map_mul e')
  have : IsLocalization.AtPrime Rₚ (p.map (algebraMap R Rₘ)) :=
    IsLocalization.isLocalization_of_algEquiv (Ideal.map (algebraMap R Rₘ) p).primeCompl e.symm
  exact isGoresteinLocalRing_of_isLocalizationAtPrime (p.map (algebraMap R Rₘ)) Rₚ

open IsLocalRing

lemma IsGorensteinRing.of_isGorensteinLocalRing [IsGorensteinLocalRing R]
    [IsNoetherianRing R] : IsGorensteinRing R := by
  apply (isGorensteinRing_iff R).mpr (fun m hm ↦ ?_)
  let _ := IsLocalization.at_units m.primeCompl (fun x hx ↦ by simpa [eq_maximalIdeal hm] using hx)
  let e := (IsLocalization.algEquiv m.primeCompl R (Localization.AtPrime m)).toRingEquiv
  exact IsGorensteinLocalRing.of_ringEquiv e

lemma IsGorensteinLocalRing.of_isLocalRing_of_isGorensteinRing [IsLocalRing R]
    [IsNoetherianRing R] [IsGorensteinRing R] : IsGorensteinLocalRing R := by
  let _ := IsLocalization.at_units (maximalIdeal R).primeCompl (fun x hx ↦ by simpa using hx)
  let _ := (isGorensteinRing_def R).mp ‹_› (maximalIdeal R) inferInstance
  let e := (IsLocalization.algEquiv (maximalIdeal R).primeCompl R
    (Localization.AtPrime (maximalIdeal R))).toRingEquiv
  exact IsGorensteinLocalRing.of_ringEquiv e.symm

end
