/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.DiscreteValuationRing.TFAE

#align_import ring_theory.dedekind_domain.dvr from "leanprover-community/mathlib"@"f0c8bf9245297a541f468be517f1bde6195105e9"

/-!
# Dedekind domains

This file defines an equivalent notion of a Dedekind domain (or Dedekind ring),
namely a Noetherian integral domain where the localization at all nonzero prime ideals is a DVR
(TODO: and shows that implies the main definition).

## Main definitions

 - `IsDedekindDomainDvr` alternatively defines a Dedekind domain as an integral domain that
   is Noetherian, and the localization at every nonzero prime ideal is a DVR.

## Main results
 - `IsLocalization.AtPrime.discreteValuationRing_of_dedekind_domain` shows that
   `IsDedekindDomain` implies the localization at each nonzero prime ideal is a DVR.
 - `IsDedekindDomain.isDedekindDomainDvr` is one direction of the equivalence of definitions
   of a Dedekind domain

## Implementation notes

The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. The `..._iff` lemmas express this independence.

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/


variable (R A K : Type*) [CommRing R] [CommRing A] [IsDomain A] [Field K]

open scoped nonZeroDivisors Polynomial

/-- A Dedekind domain is an integral domain that is Noetherian, and the
localization at every nonzero prime is a discrete valuation ring.

This is equivalent to `IsDedekindDomain`.
TODO: prove the equivalence.
-/
structure IsDedekindDomainDvr : Prop where
  isNoetherianRing : IsNoetherianRing A
  is_dvr_at_nonzero_prime :
    ∀ (P) (_ : P ≠ (⊥ : Ideal A)) (_ : P.IsPrime), DiscreteValuationRing (Localization.AtPrime P)
#align is_dedekind_domain_dvr IsDedekindDomainDvr

/-- Localizing a domain of Krull dimension `≤ 1` gives another ring of Krull dimension `≤ 1`.

Note that the same proof can/should be generalized to preserving any Krull dimension,
once we have a suitable definition.
-/
theorem Ring.DimensionLEOne.localization {R : Type*} (Rₘ : Type*) [CommRing R] [IsDomain R]
    [CommRing Rₘ] [Algebra R Rₘ] {M : Submonoid R} [IsLocalization M Rₘ] (hM : M ≤ R⁰)
    [h : Ring.DimensionLEOne R] : Ring.DimensionLEOne Rₘ := ⟨by
  intro p hp0 hpp
  -- ⊢ Ideal.IsMaximal p
  refine' Ideal.isMaximal_def.mpr ⟨hpp.ne_top, Ideal.maximal_of_no_maximal fun P hpP hPm => _⟩
  -- ⊢ False
  have hpP' : (⟨p, hpp⟩ : { p : Ideal Rₘ // p.IsPrime }) < ⟨P, hPm.isPrime⟩ := hpP
  -- ⊢ False
  rw [← (IsLocalization.orderIsoOfPrime M Rₘ).lt_iff_lt] at hpP'
  -- ⊢ False
  haveI : Ideal.IsPrime (Ideal.comap (algebraMap R Rₘ) p) :=
    ((IsLocalization.orderIsoOfPrime M Rₘ) ⟨p, hpp⟩).2.1
  haveI : Ideal.IsPrime (Ideal.comap (algebraMap R Rₘ) P) :=
    ((IsLocalization.orderIsoOfPrime M Rₘ) ⟨P, hPm.isPrime⟩).2.1
  have _ : Ideal.comap (algebraMap R Rₘ) p < Ideal.comap (algebraMap R Rₘ) P := hpP'
  -- ⊢ False
  refine' h.not_lt_lt ⊥ (Ideal.comap _ _) (Ideal.comap _ _) ⟨_, hpP'⟩
  -- ⊢ ⊥ < Ideal.comap (algebraMap R Rₘ) ↑{ val := p, property := hpp }
  exact IsLocalization.bot_lt_comap_prime _ _ hM _ hp0⟩
  -- 🎉 no goals
#align ring.dimension_le_one.localization Ring.DimensionLEOne.localization

/-- The localization of a Dedekind domain is a Dedekind domain. -/
theorem IsLocalization.isDedekindDomain [IsDedekindDomain A] {M : Submonoid A} (hM : M ≤ A⁰)
    (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocalization M Aₘ] :
    IsDedekindDomain Aₘ := by
  have h : ∀ y : M, IsUnit (algebraMap A (FractionRing A) y) := by
    rintro ⟨y, hy⟩
    exact IsUnit.mk0 _ (mt IsFractionRing.to_map_eq_zero_iff.mp (nonZeroDivisors.ne_zero (hM hy)))
  letI : Algebra Aₘ (FractionRing A) := RingHom.toAlgebra (IsLocalization.lift h)
  -- ⊢ IsDedekindDomain Aₘ
  haveI : IsScalarTower A Aₘ (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq h x).symm
  haveI : IsFractionRing Aₘ (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M _ _
  refine' (isDedekindDomain_iff _ (FractionRing A)).mpr ⟨_, _, _, _⟩
  · infer_instance
    -- 🎉 no goals
  · exact IsLocalization.isNoetherianRing M _ (by infer_instance)
    -- 🎉 no goals
  · exact Ring.DimensionLEOne.localization Aₘ hM
    -- 🎉 no goals
  · intro x hx
    -- ⊢ ∃ y, ↑(algebraMap Aₘ (FractionRing A)) y = x
    obtain ⟨⟨y, y_mem⟩, hy⟩ := hx.exists_multiple_integral_of_isLocalization M _
    -- ⊢ ∃ y, ↑(algebraMap Aₘ (FractionRing A)) y = x
    obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff _).mp IsDedekindDomain.toIsIntegrallyClosed hy
    -- ⊢ ∃ y, ↑(algebraMap Aₘ (FractionRing A)) y = x
    refine' ⟨IsLocalization.mk' Aₘ z ⟨y, y_mem⟩, (IsLocalization.lift_mk'_spec _ _ _ _).mpr _⟩
    -- ⊢ ↑(algebraMap A (FractionRing A)) z = ↑(algebraMap A (FractionRing A)) ↑{ val …
    rw [hz, ← Algebra.smul_def]
    -- ⊢ { val := y, property := y_mem } • x = ↑{ val := y, property := y_mem } • x
    rfl
    -- 🎉 no goals
#align is_localization.is_dedekind_domain IsLocalization.isDedekindDomain

/-- The localization of a Dedekind domain at every nonzero prime ideal is a Dedekind domain. -/
theorem IsLocalization.AtPrime.isDedekindDomain [IsDedekindDomain A] (P : Ideal A) [P.IsPrime]
    (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] :
    IsDedekindDomain Aₘ :=
  IsLocalization.isDedekindDomain A P.primeCompl_le_nonZeroDivisors Aₘ
#align is_localization.at_prime.is_dedekind_domain IsLocalization.AtPrime.isDedekindDomain

theorem IsLocalization.AtPrime.not_isField {P : Ideal A} (hP : P ≠ ⊥) [pP : P.IsPrime] (Aₘ : Type*)
    [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] : ¬IsField Aₘ := by
  intro h
  -- ⊢ False
  letI := h.toField
  -- ⊢ False
  obtain ⟨x, x_mem, x_ne⟩ := P.ne_bot_iff.mp hP
  -- ⊢ False
  exact
    (LocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff Aₘ P _).mpr x_mem)
        (isUnit_iff_ne_zero.mpr
          ((map_ne_zero_iff (algebraMap A Aₘ)
                (IsLocalization.injective Aₘ P.primeCompl_le_nonZeroDivisors)).mpr
            x_ne)))
#align is_localization.at_prime.not_is_field IsLocalization.AtPrime.not_isField

/-- In a Dedekind domain, the localization at every nonzero prime ideal is a DVR. -/
theorem IsLocalization.AtPrime.discreteValuationRing_of_dedekind_domain [IsDedekindDomain A]
    {P : Ideal A} (hP : P ≠ ⊥) [pP : P.IsPrime] (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ]
    [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] : DiscreteValuationRing Aₘ := by
  classical
  letI : IsNoetherianRing Aₘ :=
    IsLocalization.isNoetherianRing P.primeCompl _ IsDedekindDomain.toIsNoetherian
  letI : LocalRing Aₘ := IsLocalization.AtPrime.localRing Aₘ P
  have hnf := IsLocalization.AtPrime.not_isField A hP Aₘ
  exact
    ((DiscreteValuationRing.TFAE Aₘ hnf).out 0 2).mpr
      (IsLocalization.AtPrime.isDedekindDomain A P _)
#align is_localization.at_prime.discrete_valuation_ring_of_dedekind_domain IsLocalization.AtPrime.discreteValuationRing_of_dedekind_domain

/-- Dedekind domains, in the sense of Noetherian integrally closed domains of Krull dimension ≤ 1,
are also Dedekind domains in the sense of Noetherian domains where the localization at every
nonzero prime ideal is a DVR. -/
theorem IsDedekindDomain.isDedekindDomainDvr [IsDedekindDomain A] : IsDedekindDomainDvr A :=
  { isNoetherianRing := IsDedekindDomain.toIsNoetherian
    is_dvr_at_nonzero_prime := fun _ hP _ =>
      IsLocalization.AtPrime.discreteValuationRing_of_dedekind_domain A hP _ }
#align is_dedekind_domain.is_dedekind_domain_dvr IsDedekindDomain.isDedekindDomainDvr
