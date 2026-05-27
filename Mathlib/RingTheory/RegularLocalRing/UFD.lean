/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.FiniteFreeResolution.HasProjectiveDimensionLE
public import Mathlib.Algebra.Module.FiniteFreeResolution.Localization
public import Mathlib.Algebra.Module.StablyFree.FreeOfInvertible
public import Mathlib.Algebra.Module.StablyFree.HasFiniteFreeResolution
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.LocalProperties.Invertible
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Mathlib.RingTheory.RegularLocalRing.Localization

/-!
# Any regular local ring is a UFD
-/

public section

universe u

variable {R : Type u} [CommRing R]

open Module

namespace IsRegularLocalRing

private lemma ufd_localization_away_of_prime_of_nonmaximal_localizations_ufd [IsRegularLocalRing R]
    {x : R} (hxmem : x ∈ IsLocalRing.maximalIdeal R) (hxp : Prime x)
    (hP : ∀ (P : Ideal R) [P.IsPrime] (_ : P < IsLocalRing.maximalIdeal R),
      UniqueFactorizationMonoid (Localization.AtPrime P)) :
    UniqueFactorizationMonoid (Localization.Away x) := by
  let M : Submonoid R := Submonoid.powers x
  have : IsDomain (Localization.Away x) := Localization.Away.isDomain hxp.ne_zero
  rw [UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one]
  intro Q hQ hQheight
  have : Module.Invertible (Localization.Away x) Q := by
    refine Module.Invertible.of_localized_maximal (fun P _ ↦ ?_)
    let Q' : Ideal (Localization.AtPrime P) := Ideal.map (algebraMap (Localization.Away x) _) Q
    let eIdeal : LocalizedModule P.primeCompl Q ≃ₗ[Localization.AtPrime P] Q' :=
      LinearEquiv.extendScalarsOfIsLocalization P.primeCompl (Localization.AtPrime P) <|
        IsLocalizedModule.linearEquiv P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl Q)
          (Algebra.idealMap (Localization.AtPrime P) Q)
    by_cases hQP : Q ≤ P
    · let p : Ideal R := Ideal.comap (algebraMap R (Localization.Away x)) P
      have hx_not_mem_p : x ∉ p := Set.disjoint_left.mp
        ((IsLocalization.isPrime_iff_isPrime_disjoint M (Localization.Away x) P).1 inferInstance).2
          (Submonoid.mem_powers x)
      have hp_lt_max : p < IsLocalRing.maximalIdeal R :=
        lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime p) (fun h ↦ hx_not_mem_p (h ▸ hxmem))
      have : UniqueFactorizationMonoid (Localization.AtPrime P) :=
        IsLocalization.localizationLocalizationAtPrimeIsoLocalization M P
          |>.toMulEquiv.uniqueFactorizationMonoid (hP p hp_lt_max)
      have : Q'.IsPrime := Ideal.isPrime_map_of_isLocalizationAtPrime P hQP
      have hd : Disjoint (P.primeCompl : Set (Localization.Away x)) Q := by
        simp [Ideal.primeCompl, ← le_compl_iff_disjoint_left, hQP]
      have hQh : Q'.height = 1 := by
        simp [Q', IsLocalization.under_map_of_isPrime_disjoint P.primeCompl (Localization.AtPrime P)
          inferInstance hd, hQheight, ← IsLocalization.height_under P.primeCompl Q']
      have := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hQh
      exact Module.Invertible.congr <| Q'.isoBaseOfIsPrincipal
        (Ideal.height_eq_zero_iff_eq_bot.not.mp (by simp [hQh])) ≪≫ₗ eIdeal.symm
    · exact Module.Invertible.congr <| LinearEquiv.symm <| eIdeal.trans <| LinearEquiv.ofTop Q' <|
        IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime P) hQP
  let q : Ideal R := Q.under R
  have : HasFiniteFreeResolution R (R ⧸ q) := HasFiniteFreeResolution.of_projectiveDimension_ne_top
      (projectiveDimension_ne_top_of_isRegularLocalRing (ModuleCat.of R (R ⧸ q)))
  have := HasFiniteFreeResolution.of_linearEquiv <| (localizedQuotientEquiv M q).symm.trans
      (Submodule.quotEquivOfEq _ _ (q.localized'_eq_map (Localization.Away x) M))
  have : HasFiniteFreeResolution (Localization.Away x) (Localization.Away x ⧸ Q) :=
    HasFiniteFreeResolution.of_linearEquiv <| AlgEquiv.toLinearEquiv <|
      Ideal.quotientEquivAlgOfEq (Localization.Away x) (IsLocalization.map_under M _ Q)
  have : Free (Localization.Away x) Q := by
    have := HasFiniteFreeResolution.of_shortExact_of_middle_of_right _ _
      (Submodule.subtype_injective Q) (Submodule.mkQ_surjective Q) (LinearMap.exact_subtype_mkQ Q)
    exact free_of_isStablyFree_of_invertible (Localization.Away x) Q
  exact Q.isPrincipal_of_free

variable (R) in
/-- Any regular local ring is a unique factorization domain. -/
instance (priority := low) uniqueFactorizationMonoid [IsRegularLocalRing R] :
    UniqueFactorizationMonoid R := by
  have hmain (n : ℕ) : ∀ {S : Type u} [CommRing S] [IsRegularLocalRing S],
      ringKrullDim S = n → UniqueFactorizationMonoid S := by
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro S _ _ h
      cases n with
      | zero =>
          have := (isField_of_isRegularLocalRing_of_dimension_zero h).isPrincipalIdealRing
          infer_instance
      | succ n =>
          have hsd : ringKrullDim S ≠ 0 := by
            rw [h]
            norm_cast
          obtain ⟨x, hxm, hxnm⟩ :=
            Set.exists_of_ssubset (IsLocalRing.maximalIdeal_sq_lt_of_ringKrullDim_ne_zero hsd)
          have hx_ne_zero : x ≠ 0 := fun hx0 ↦ hxnm (by simp [hx0])
          have : IsRegularLocalRing (S ⧸ Ideal.span {x}) := (quotient_span_singleton S hxm hxnm).1
          have hxp : Prime x := by
            rw [← Ideal.span_singleton_prime hx_ne_zero, ← Ideal.Quotient.isDomain_iff_prime]
            infer_instance
          have hP (P : Ideal S) [P.IsPrime] (hP_lt_max : P < IsLocalRing.maximalIdeal S) :
              UniqueFactorizationMonoid (Localization.AtPrime P) := by
            have : IsRegularLocalRing _ := isRegularLocalRing_localization S P
            obtain ⟨k, hk⟩ := FiniteRingKrullDim.ringKrullDim_eq_nat (Localization.AtPrime P)
            exact ih k (ENat.coe_lt_coe.mp <| WithBot.coe_lt_coe.mp <| hk.symm.trans_lt <|
              (IsLocalization.AtPrime.ringKrullDim_lt_of_lt_maximalIdeal hP_lt_max).trans_eq h) hk
          have := ufd_localization_away_of_prime_of_nonmaximal_localizations_ufd hxm hxp hP
          rwa [UniqueFactorizationMonoid.iff_localization_away_of_prime hxp]
  obtain ⟨n, hn⟩ := FiniteRingKrullDim.ringKrullDim_eq_nat R
  exact hmain n hn

end IsRegularLocalRing
