/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# `IsIntegrallyClosed` is a local property

In this file, we prove that `IsIntegrallyClosed` is a local property.

## Main results

* `IsIntegrallyClosed.of_localization_maximal` : An integral domain `R` is integral closed
  if `Rₘ` is integral closed for any maximal ideal `m` of `R`.

## TODO

Prove that `IsIntegrallyClosed` is preserved by localization

-/

open scoped nonZeroDivisors

open Localization Ideal IsLocalization

/-- An integral domain `R` is integral closed if `Rₘ` is integral closed
  for any maximal ideal `m` of `R`. -/
theorem IsIntegrallyClosed.of_localization_maximal {R : Type*} [CommRing R] [IsDomain R]
    (h : ∀ p : Ideal R, p ≠ ⊥ → [p.IsMaximal] → IsIntegrallyClosed (Localization.AtPrime p)) :
    IsIntegrallyClosed R := by
  by_cases hf : IsField R
  · exact hf.toField.instIsIntegrallyClosed
  apply (isIntegrallyClosed_iff (FractionRing R)).mpr
  rintro ⟨x⟩ hx
  let I : Ideal R := span {x.2.1} / span {x.1}
  have h1 : 1 ∈ I := by
    apply I.eq_top_iff_one.mp
    by_contra hn
    rcases I.exists_le_maximal hn with ⟨p, hpm, hpi⟩
    have hic := h p (Ring.ne_bot_of_isMaximal_of_not_isField hpm hf)
    have hxp : IsIntegral (Localization.AtPrime p) (mk x.1 x.2) := hx.tower_top
    /- `x.1 / x.2.1 ∈ Rₚ` since it is integral over `Rₚ` and `Rₚ` is integrally closed.
      More precisely, `x.1 / x.2.1 = y.1 / y.2.1` where `y.1, y.2.1 ∈ R` and `y.2.1 ∉ p`. -/
    rcases (isIntegrallyClosed_iff (FractionRing R)).mp hic hxp with ⟨⟨y⟩, hy⟩
    /- `y.2.1 ∈ I` since for all `a ∈ Ideal.span {x.1}`, say `a = b * x.1`,
      we have `y.2 * a = b * x.1 * y.2 = b * y.1 * x.2.1 ∈ Ideal.span {x.2.1}`. -/
    have hyi : y.2.1 ∈ I := by
      intro a ha
      rcases mem_span_singleton'.mp ha with ⟨b, hb⟩
      apply mem_span_singleton'.mpr ⟨b * y.1, _⟩
      rw [← hb, ← mul_assoc, mul_comm y.2.1 b, mul_assoc, mul_assoc]
      exact congrArg (HMul.hMul b) <| (mul_comm y.1 x.2.1).trans <|
        FaithfulSMul.algebraMap_injective R (Localization R⁰) <| mk'_eq_iff_eq.mp <|
          (mk'_eq_algebraMap_mk'_of_submonoid_le _ _ p.primeCompl_le_nonZeroDivisors y.1 y.2).trans
            <| show algebraMap (Localization.AtPrime p) _ (mk' _ y.1 y.2) = mk' _ x.1 x.2
              by simpa only [← mk_eq_mk', ← hy] using by rfl
    -- `y.2.1 ∈ I` implies `y.2.1 ∈ p` since `I ⊆ p`, which contradicts to the choice of `y`.
    exact y.2.2 (hpi hyi)
  rcases mem_span_singleton'.mp (h1 x.1 (mem_span_singleton_self x.1)) with ⟨y, hy⟩
  exact ⟨y, (eq_mk'_of_mul_eq (hy.trans (one_mul x.1))).trans (mk_eq_mk'_apply x.1 x.2).symm⟩

theorem isIntegrallyClosed_ofLocalizationMaximal :
    OfLocalizationMaximal fun R _ => ([IsDomain R] → IsIntegrallyClosed R) :=
  fun _ _ h _ ↦ IsIntegrallyClosed.of_localization_maximal fun p _ hpm ↦ h p hpm

theorem IsIntegrallyClosed.of_equiv {R S : Type*} [CommRing R] [CommRing S] (f : R ≃+* S)
    [h : IsIntegrallyClosed R] : IsIntegrallyClosed S := by
  let _ : Algebra S R := f.symm.toRingHom.toAlgebra
  let f : S ≃ₐ[S] R := AlgEquiv.ofRingEquiv fun _ ↦ rfl
  let g : FractionRing S ≃ₐ[S] FractionRing R := IsFractionRing.algEquivOfAlgEquiv f
  refine (isIntegrallyClosed_iff (FractionRing S)).mpr (fun hx ↦ ?_)
  rcases (isIntegrallyClosed_iff (FractionRing R)).mp h <|
    IsIntegral.tower_top ((isIntegral_algEquiv g).mpr hx) with ⟨z, hz⟩
  exact ⟨f.symm z, (IsFractionRing.algEquivOfAlgEquiv_algebraMap f.symm z).symm.trans <|
    (AlgEquiv.symm_apply_eq g).mpr hz⟩

theorem IsIntegrallyClosed.of_localization {R : Type*} [CommRing R] [IsDomain R]
    (S : Set (PrimeSpectrum R)) (h : ∀ p ∈ S, IsIntegrallyClosed (Localization.AtPrime p.1))
    (hs : ⨅ p ∈ S, (Localization.subalgebra (FractionRing R) p.1.primeCompl
    p.1.primeCompl_le_nonZeroDivisors) = ⊥) : IsIntegrallyClosed R := by
  by_cases hf : IsField R
  · exact hf.toField.instIsIntegrallyClosed
  apply (isIntegrallyClosed_iff (FractionRing R)).mpr
  intro x hx
  show x ∈ (⊥ : Subalgebra R (FractionRing R))
  rw [← hs]
  refine Algebra.mem_iInf.mpr ?_
  intro p
  refine Algebra.mem_iInf.mpr ?_
  intro hp
  have := h p hp
  let B := Localization.subalgebra (FractionRing R) p.1.primeCompl p.1.primeCompl_le_nonZeroDivisors
  have : IsIntegrallyClosed B := sorry
  have : IsIntegral B x := sorry
  sorry
/- letI : Algebra R (FractionRing S) := ((algebraMap S (FractionRing S)).comp f.toRingHom).toAlgebra
  have : IsFractionRing R (FractionRing S) := sorry
  apply (isIntegrallyClosed_iff (FractionRing S)).mpr
  intro x hx
  let g : FractionRing S ≃+* FractionRing R := IsFractionRing.ringEquivOfRingEquiv f.symm
  have := g x
  have : IsIntegral R (g x) := by
    sorry
  have : ∃ z, (algebraMap R (FractionRing R)) z = (g x) := IsIntegralClosure.isIntegral_iff.mp this -/
