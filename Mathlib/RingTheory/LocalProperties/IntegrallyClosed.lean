/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Localization

/-!
# `IsIntegrallyClosed` is a local property

In this file, we prove that `IsIntegrallyClosed` is a local property.

## Main results

* `IsIntegrallyClosed.of_localization_maximal` : An integral domain `R` is integral closed
  if `Rₘ` is integral closed for any maximal ideal `m` of `R`.
-/

open scoped nonZeroDivisors

open Localization Ideal IsLocalization

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]

theorem IsIntegrallyClosed.iInf {ι : Type*} (S : ι → Subalgebra R K)
    (h : ∀ i, IsIntegrallyClosed (S i)) :
    IsIntegrallyClosed (⨅ i, S i : Subalgebra R K) := by
  refine (isIntegrallyClosed_iff K).mpr (fun {x} hx ↦ CanLift.prf x (Algebra.mem_iInf.mpr ?_))
  intro i
  have le : (⨅ i : ι, S i : Subalgebra R K) ≤ S i := iInf_le S i
  algebraize [(Subalgebra.inclusion le).toRingHom]
  have : IsScalarTower ↥(⨅ i, S i) (S i) K := Subalgebra.inclusion.isScalarTower_right le K
  rcases (isIntegrallyClosed_iff K).mp (h i) hx.tower_top with ⟨⟨_, hin⟩, hy⟩
  rwa [← hy]

theorem IsIntegrallyClosed.of_iInf_eq_bot {ι : Type*} (S : ι → Subalgebra R K)
    (h : ∀ i : ι, IsIntegrallyClosed (S i)) (hs : ⨅ i : ι, S i = ⊥) : IsIntegrallyClosed R :=
  have f : (⊥ : Subalgebra R K) ≃ₐ[R] R :=
    Algebra.botEquivOfInjective (FaithfulSMul.algebraMap_injective R K)
  (IsIntegrallyClosed.iInf S h).of_equiv (hs ▸ f).toRingEquiv

theorem IsIntegrallyClosed.of_localization_submonoid [IsDomain R] {ι : Type*} (S : ι → Submonoid R)
    (h : ∀ i : ι, S i ≤ R⁰) (hi : ∀ i : ι, IsIntegrallyClosed (Localization (S i)))
    (hs : ⨅ i : ι, Localization.subalgebra (FractionRing R) (S i) (h i) = ⊥) :
    IsIntegrallyClosed R :=
  IsIntegrallyClosed.of_iInf_eq_bot (fun i ↦ Localization.subalgebra (FractionRing R) (S i) (h i))
    (fun i ↦ (hi i).of_equiv (IsLocalization.algEquiv (S i) (Localization (S i)) _).toRingEquiv) hs

/-- An integral domain $R$ is integrally closed if there exists a set of prime ideals $S$ such that
  $\bigcap_{\mathfrak{p} \in S} R_{\mathfrak{p}} = R$ and for every $\mathfrak{p} \in S$,
  $R_{\mathfrak{p}}$ is integrally closed. -/
theorem IsIntegrallyClosed.of_localization [IsDomain R] (S : Set (PrimeSpectrum R))
    (h : ∀ p ∈ S, IsIntegrallyClosed (Localization.AtPrime p.1))
    (hs : ⨅ p ∈ S, (Localization.subalgebra (FractionRing R) p.1.primeCompl
      p.1.primeCompl_le_nonZeroDivisors) = ⊥) : IsIntegrallyClosed R := by
  apply IsIntegrallyClosed.of_localization_submonoid (fun p : S ↦ p.1.1.primeCompl)
    (fun p ↦ p.1.1.primeCompl_le_nonZeroDivisors) (fun p ↦ h p.1 p.2)
  ext x
  simp only [← hs, Algebra.mem_iInf, Subtype.forall]

/-- An integral domain `R` is integral closed if `Rₘ` is integral closed
  for any maximal ideal `m` of `R`. -/
theorem IsIntegrallyClosed.of_localization_maximal [IsDomain R]
    (h : ∀ p : Ideal R, p ≠ ⊥ → [p.IsMaximal] → IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed R := by
  by_cases hf : IsField R
  · exact hf.toField.instIsIntegrallyClosed
  refine of_localization (.range MaximalSpectrum.toPrimeSpectrum) (fun _ ↦ ?_) ?_
  · rintro ⟨p, rfl⟩
    exact h p.asIdeal (Ring.ne_bot_of_isMaximal_of_not_isField p.isMaximal hf)
  · rw [iInf_range]
    convert MaximalSpectrum.iInf_localization_eq_bot R (FractionRing R)
    rw [subalgebra.ofField_eq, MaximalSpectrum.toPrimeSpectrum]

theorem isIntegrallyClosed_ofLocalizationMaximal :
    OfLocalizationMaximal fun R _ => ([IsDomain R] → IsIntegrallyClosed R) :=
  fun _ _ h _ ↦ IsIntegrallyClosed.of_localization_maximal fun p _ hpm ↦ h p hpm
