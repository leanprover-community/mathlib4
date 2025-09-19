/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
import Mathlib.RingTheory.RegularLocalRing.Localization
import Mathlib.RingTheory.RegularLocalRing.RegularRing.GlobalDimension
/-!

# Localization of Regular Ring is Regular

In this file, we establish the full version of Auslander-Buchsbaum-Serre criterion and its corollary
that localization of regular local ring is regular.

-/

universe u v

variable (R : Type u) [CommRing R]

lemma isRegularRing_of_globalDimension_lt_top [IsNoetherianRing R] [Small.{v} R]
    (h : globalDimension.{v} R < ⊤) :  IsRegularRing R := by
  apply (isRegularRing_iff R).mpr (fun p hp ↦ ?_)
  have : globalDimension.{v} (Localization.AtPrime p) ≤ globalDimension.{v} R := by
    rw [globalDimension_eq_iSup_loclization_prime R]
    apply le_iSup (fun (q : PrimeSpectrum R) ↦ globalDimension.{v} (Localization.AtPrime q.1))
      ⟨p, hp⟩
  let _ : Small.{v, u} (Localization.AtPrime p) := small_of_surjective Localization.mkHom_surjective
  exact IsRegularLocalRing.of_globalDimension_lt_top.{u, v} (lt_of_le_of_lt this h)

lemma isRegularRing_of_isRegularLocalRing [IsRegularLocalRing R] : IsRegularRing R := by
  apply isRegularRing_of_globalDimension_lt_top.{u, u}
  rw [IsRegularLocalRing.globalDimension_eq_ringKrullDim]
  exact ringKrullDim_lt_top

lemma isRegularRing_of_localization_maximal_isRegularLocalRing
    (h : ∀ m : Ideal R, ∀ (_ : m.IsMaximal), IsRegularLocalRing (Localization.AtPrime m)) :
    IsRegularRing R := by
  apply (isRegularRing_iff R).mpr (fun p hp ↦ ?_)
  rcases Ideal.exists_le_maximal p (Ideal.IsPrime.ne_top hp) with ⟨m, hm, le⟩
  let Rₘ := Localization.AtPrime m
  let _ : IsRegularLocalRing Rₘ := h m hm
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
  have : IsLocalization.AtPrime Rₚ (Ideal.map (algebraMap R Rₘ) p) :=
    IsLocalization.isLocalization_of_algEquiv (Ideal.map (algebraMap R Rₘ) p).primeCompl e.symm
  exact IsRegularLocalRing.of_isLocalization Rₘ (Ideal.map (algebraMap R Rₘ) p) Rₚ
