/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio, Yongle Hu
-/
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Dedekind domains

This file defines an equivalent notion of a Dedekind domain (or Dedekind ring),
namely a Noetherian integral domain where the localization at every nonzero prime ideal is a DVR.

## Main definitions

- `IsDedekindDomainDvr` alternatively defines a Dedekind domain as an integral domain that
  is Noetherian, and the localization at every nonzero prime ideal is a DVR.

## Main results
- `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` shows that
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
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/


variable (A : Type*) [CommRing A] [IsDomain A]

open scoped nonZeroDivisors Polynomial

/-- A Dedekind domain is an integral domain that is Noetherian, and the
localization at every nonzero prime is a discrete valuation ring.

This is equivalent to `IsDedekindDomain`.
-/
class IsDedekindDomainDvr : Prop extends IsNoetherian A A where
  is_dvr_at_nonzero_prime : ∀ P ≠ (⊥ : Ideal A), ∀ _ : P.IsPrime,
    IsDiscreteValuationRing (Localization.AtPrime P)

/-- Localizing a domain of Krull dimension `≤ 1` gives another ring of Krull dimension `≤ 1`.

Note that the same proof can/should be generalized to preserving any Krull dimension,
once we have a suitable definition.
-/
theorem Ring.DimensionLEOne.localization {R : Type*} (Rₘ : Type*) [CommRing R] [IsDomain R]
    [CommRing Rₘ] [Algebra R Rₘ] {M : Submonoid R} [IsLocalization M Rₘ] (hM : M ≤ R⁰)
    [h : Ring.DimensionLEOne R] : Ring.DimensionLEOne Rₘ := ⟨by
  intro p hp0 hpp
  refine Ideal.isMaximal_def.mpr ⟨hpp.ne_top, Ideal.maximal_of_no_maximal fun P hpP hPm => ?_⟩
  have hpP' : (⟨p, hpp⟩ : { p : Ideal Rₘ // p.IsPrime }) < ⟨P, hPm.isPrime⟩ := hpP
  rw [← (IsLocalization.orderIsoOfPrime M Rₘ).lt_iff_lt] at hpP'
  haveI : Ideal.IsPrime (Ideal.comap (algebraMap R Rₘ) p) :=
    ((IsLocalization.orderIsoOfPrime M Rₘ) ⟨p, hpp⟩).2.1
  haveI : Ideal.IsPrime (Ideal.comap (algebraMap R Rₘ) P) :=
    ((IsLocalization.orderIsoOfPrime M Rₘ) ⟨P, hPm.isPrime⟩).2.1
  have hlt : Ideal.comap (algebraMap R Rₘ) p < Ideal.comap (algebraMap R Rₘ) P := hpP'
  refine h.not_lt_lt ⊥ (Ideal.comap _ _) (Ideal.comap _ _) ⟨?_, hlt⟩
  exact IsLocalization.bot_lt_comap_prime _ _ hM _ hp0⟩

/-- The localization of a Dedekind domain is a Dedekind domain. -/
theorem IsLocalization.isDedekindDomain [IsDedekindDomain A] {M : Submonoid A} (hM : M ≤ A⁰)
    (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocalization M Aₘ] :
    IsDedekindDomain Aₘ := by
  have h : ∀ y : M, IsUnit (algebraMap A (FractionRing A) y) := by
    rintro ⟨y, hy⟩
    exact IsUnit.mk0 _ (mt IsFractionRing.to_map_eq_zero_iff.mp (nonZeroDivisors.ne_zero (hM hy)))
  letI : Algebra Aₘ (FractionRing A) := RingHom.toAlgebra (IsLocalization.lift h)
  haveI : IsScalarTower A Aₘ (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq h x).symm
  haveI : IsFractionRing Aₘ (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M _ _
  refine (isDedekindDomain_iff _ (FractionRing A)).mpr ⟨?_, ?_, ?_, ?_⟩
  · infer_instance
  · exact IsLocalization.isNoetherianRing M _ inferInstance
  · exact Ring.DimensionLEOne.localization Aₘ hM
  · intro x hx
    obtain ⟨⟨y, y_mem⟩, hy⟩ := hx.exists_multiple_integral_of_isLocalization M _
    obtain ⟨z, hz⟩ := (isIntegrallyClosed_iff _).mp IsDedekindRing.toIsIntegralClosure hy
    refine ⟨IsLocalization.mk' Aₘ z ⟨y, y_mem⟩, (IsLocalization.lift_mk'_spec _ _ _ _).mpr ?_⟩
    rw [hz, ← Algebra.smul_def]
    rfl

/-- The localization of a Dedekind domain at every nonzero prime ideal is a Dedekind domain. -/
theorem IsLocalization.AtPrime.isDedekindDomain [IsDedekindDomain A] (P : Ideal A) [P.IsPrime]
    (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] :
    IsDedekindDomain Aₘ :=
  IsLocalization.isDedekindDomain A P.primeCompl_le_nonZeroDivisors Aₘ

instance Localization.AtPrime.isDedekindDomain [IsDedekindDomain A] (P : Ideal A) [P.IsPrime] :
    IsDedekindDomain (Localization.AtPrime P) :=
  IsLocalization.AtPrime.isDedekindDomain A P _

theorem IsLocalization.AtPrime.not_isField {P : Ideal A} (hP : P ≠ ⊥) [pP : P.IsPrime] (Aₘ : Type*)
    [CommRing Aₘ] [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] : ¬ IsField Aₘ := by
  intro h
  letI := h.toField
  obtain ⟨x, x_mem, x_ne⟩ := P.ne_bot_iff.mp hP
  exact
    (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      (Ideal.eq_top_of_isUnit_mem _
        ((IsLocalization.AtPrime.to_map_mem_maximal_iff Aₘ P _).mpr x_mem)
        (isUnit_iff_ne_zero.mpr
          ((map_ne_zero_iff (algebraMap A Aₘ)
                (IsLocalization.injective Aₘ P.primeCompl_le_nonZeroDivisors)).mpr
            x_ne)))

/-- In a Dedekind domain, the localization at every nonzero prime ideal is a DVR. -/
theorem IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain [IsDedekindDomain A]
    {P : Ideal A} (hP : P ≠ ⊥) [pP : P.IsPrime] (Aₘ : Type*) [CommRing Aₘ] [IsDomain Aₘ]
    [Algebra A Aₘ] [IsLocalization.AtPrime Aₘ P] : IsDiscreteValuationRing Aₘ := by
  classical
  letI : IsNoetherianRing Aₘ :=
    IsLocalization.isNoetherianRing P.primeCompl _ IsDedekindRing.toIsNoetherian
  letI : IsLocalRing Aₘ := IsLocalization.AtPrime.isLocalRing Aₘ P
  have hnf := IsLocalization.AtPrime.not_isField A hP Aₘ
  exact
    ((IsDiscreteValuationRing.TFAE Aₘ hnf).out 0 2).mpr
      (IsLocalization.AtPrime.isDedekindDomain A P _)

/-- Dedekind domains, in the sense of Noetherian integrally closed domains of Krull dimension ≤ 1,
are also Dedekind domains in the sense of Noetherian domains where the localization at every
nonzero prime ideal is a DVR. -/
instance IsDedekindDomain.isDedekindDomainDvr [IsDedekindDomain A] : IsDedekindDomainDvr A where
  is_dvr_at_nonzero_prime := fun _ hP _ =>
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP _

instance IsDedekindDomainDvr.ring_dimensionLEOne [h : IsDedekindDomainDvr A] :
    Ring.DimensionLEOne A where
  maximalOfPrime := by
    intro p hp hpp
    rcases p.exists_le_maximal (Ideal.IsPrime.ne_top hpp) with ⟨q, hq, hpq⟩
    let f := (IsLocalization.orderIsoOfPrime q.primeCompl (Localization.AtPrime q)).symm
    let P := f ⟨p, hpp, hpq.disjoint_compl_left⟩
    let Q := f ⟨q, hq.isPrime, Set.disjoint_left.mpr fun _ a => a⟩
    have hinj : Function.Injective (algebraMap A (Localization.AtPrime q)) :=
      IsLocalization.injective (Localization.AtPrime q) q.primeCompl_le_nonZeroDivisors
    have hp1 : P.1 ≠ ⊥ := fun x => hp ((p.map_eq_bot_iff_of_injective hinj).mp x)
    have hq1 : Q.1 ≠ ⊥ :=
      fun x => (ne_bot_of_le_ne_bot hp hpq) ((q.map_eq_bot_iff_of_injective hinj).mp x)
    rcases (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime (Localization.AtPrime q)).mp
      (h.is_dvr_at_nonzero_prime q (ne_bot_of_le_ne_bot hp hpq) hq.isPrime) with ⟨_, huq⟩
    rw [show p = q from Subtype.val_inj.mpr <| f.injective <|
      Subtype.val_inj.mp (huq.unique ⟨hp1, P.2⟩ ⟨hq1, Q.2⟩)]
    exact hq

instance IsDedekindDomainDvr.isIntegrallyClosed [h : IsDedekindDomainDvr A] :
    IsIntegrallyClosed A :=
  IsIntegrallyClosed.of_localization_maximal <| fun p hp0 hpm ↦
    let ⟨_, _⟩ := (IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime
      (Localization.AtPrime p)).mp (h.is_dvr_at_nonzero_prime p hp0 hpm.isPrime)
    inferInstance

/-- If an integral domain is Noetherian, and the localization at every nonzero prime is
a discrete valuation ring, then it is a Dedekind domain. -/
instance IsDedekindDomainDvr.isDedekindDomain [IsDedekindDomainDvr A] : IsDedekindDomain A where
