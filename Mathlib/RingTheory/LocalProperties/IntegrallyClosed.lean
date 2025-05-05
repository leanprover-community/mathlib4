/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Localization.AsSubring

/-!
# `IsIntegrallyClosed` is a local property

In this file, we prove that `IsIntegrallyClosed` is a local property.

## Main results

* `IsIntegrallyClosed.of_localization_maximal` : An integral domain `R` is integral closed
  if `Rₘ` is integral closed for any maximal ideal `m` of `R`.
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

/-- An integral domain $R$ is integrally closed if there exists a set of prime ideals $S$ such that
  $\bigcap_{\mathrm{p} \in S} R_{\mathrm{p}} = R$ and for every $\mathrm{p} \in S$, $R_{\mathrm{p}}$
  is integrally closed. -/
theorem IsIntegrallyClosed.of_localization {R : Type*} [CommRing R] [NoZeroDivisors R]
    (S : Set (PrimeSpectrum R)) (h : ∀ p ∈ S, IsIntegrallyClosed (Localization.AtPrime p.1))
    (hs : ⨅ p ∈ S, (Localization.subalgebra (FractionRing R) p.1.primeCompl
      p.1.primeCompl_le_nonZeroDivisors) = ⊥) : IsIntegrallyClosed R := by
  apply (isIntegrallyClosed_iff (FractionRing R)).mpr
  intro x hx
  show x ∈ (⊥ : Subalgebra R (FractionRing R))
  rw [← hs]
  refine Algebra.mem_iInf.mpr (fun p ↦ (Algebra.mem_iInf.mpr (fun hp ↦ ?_)))
  let B := Localization.subalgebra (FractionRing R) p.1.primeCompl p.1.primeCompl_le_nonZeroDivisors
  have hb : IsIntegrallyClosed B := of_equiv (h := h p hp)
    (IsLocalization.algEquiv p.1.primeCompl (Localization.AtPrime p.1) B).toRingEquiv
  rcases ((isIntegrallyClosed_iff (FractionRing R)).mp hb) hx.tower_top with ⟨⟨_, hin⟩, hy⟩
  rw [← hy]
  exact hin
