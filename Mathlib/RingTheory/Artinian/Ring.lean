/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu, Jujian Zhang
-/
module

public import Mathlib.Algebra.Field.Equiv
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Artinian rings

A ring is said to be left (or right) Artinian if it is Artinian as a left (or right) module over
itself, or simply Artinian if it is both left and right Artinian.

## Main definitions

* `IsArtinianRing R` is the proposition that `R` is a left Artinian ring.

## Main results

* `IsArtinianRing.localization_surjective`: the canonical homomorphism from a commutative Artinian
  ring to any localization of itself is surjective.

* `IsArtinianRing.isNilpotent_jacobson_bot`: the Jacobson radical of a commutative Artinian ring
  is a nilpotent ideal.

## Implementation Details

The predicate `IsArtinianRing` is defined in `Mathlib/RingTheory/Artinian/Ring.lean` instead,
so that we can apply basic API on Artinian modules to division rings without a heavy import.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1967]

## Tags

Artinian, artinian, Artinian ring, artinian ring

-/

@[expose] public section

open Set Submodule IsArtinian

namespace IsArtinianRing

@[stacks 00J8]
theorem isNilpotent_jacobson_bot {R} [Ring R] [IsArtinianRing R] :
    IsNilpotent (Ideal.jacobson (⊥ : Ideal R)) :=
  Ideal.jacobson_bot (R := R) ▸ IsSemiprimaryRing.isNilpotent

variable {R : Type*} [CommRing R] [IsArtinianRing R]

lemma jacobson_eq_radical (I : Ideal R) : I.jacobson = I.radical := by
  simp_rw [Ideal.jacobson, Ideal.radical_eq_sInf, IsArtinianRing.isPrime_iff_isMaximal]

theorem isNilpotent_nilradical : IsNilpotent (nilradical R) := by
  rw [nilradical, ← jacobson_eq_radical]
  exact isNilpotent_jacobson_bot

variable (R) in
/-- A version of `IsArtinianRing.equivPiLocalization` with worse definitional equality. -/
noncomputable def equivPiLocalizationAux :
    R ≃ₐ[R] ∀ I : MaximalSpectrum R, Localization.AtPrime I.1 :=
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite (MaximalSpectrum R)
  letI n : ℕ := Classical.choose (isNilpotent_nilradical (R := R))
  letI hn : nilradical R ^ n = ⊥ := Classical.choose_spec isNilpotent_nilradical
  haveI hn : nilradical R ^ (n + 1) = ⊥ := by rw [pow_succ, hn, bot_mul]
  haveI (I : MaximalSpectrum R) : IsLocalization I.1.primeCompl (R ⧸ I.asIdeal ^ (n + 1)) := by
    classical
    rw [isLocalization_iff]
    refine ⟨fun x ↦ ?_, fun x ↦ ?_, fun h ↦ ?_⟩
    · exact (Ideal.Quotient.isUnit_mk_pow_iff_notMem I.1 n.succ_ne_zero).mpr x.2
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨⟨y, 1⟩, by simp⟩
    · have key : IsCoprime ((∏ J ≠ I, J.1) ^ (n + 1)) (I.1 ^ (n + 1)) := by
        rw [IsCoprime.pow_iff n.succ_pos n.succ_pos, IsCoprime.prod_left_iff]
        intro J hJ
        rw [Ideal.isCoprime_iff_sup_eq]
        exact J.2.coprime_of_ne I.2 <| mt MaximalSpectrum.ext <| Finset.ne_of_mem_erase hJ
      obtain ⟨a, ha, b, hb, hab⟩ := key.exists
      refine ⟨⟨a, ?_⟩, ?_⟩
      · simpa [← hab, I.1.add_mem_iff_left, I.1.pow_le_self _ hb] using I.1.one_notMem
      · rw [← sub_eq_zero, ← mul_sub, ← Ideal.mem_bot, ← hn, nilradical_pow_eq_iInf,
          iInf_split_single _ I, mul_comm]
        refine Ideal.mul_le_inf (Ideal.mul_mem_mul (Ideal.Quotient.eq.mp h) ?_)
        simp only [mem_iInf]
        refine fun J h ↦ Ideal.pow_right_mono ?_ (n + 1) ha
        refine Ideal.prod_le_inf.trans (Finset.inf_le ?_)
        exact Finset.mem_erase_of_ne_of_mem h (Finset.mem_univ J)
  .symm <| .trans (AlgEquiv.piCongrRight fun I ↦ IsLocalization.algEquiv I.1.primeCompl _ _) <|
    .trans (quotNilradicalPowEquivPi R (n + 1)).symm <|
      .trans (Ideal.quotientEquivAlgOfEq R hn) (.quotientBot R R)

variable (R) in
/-- An Artinian local ring is isomorphic to the product of its localizations. -/
noncomputable def equivPiLocalizationMaximal :
    R ≃ₐ[R] ∀ I : MaximalSpectrum R, Localization.AtPrime I.1 :=
  letI ψ := equivPiLocalizationAux R
  AlgEquiv.ofBijective (Algebra.ofId _ _)
    ⟨Localization.injective_algebraMap_pi_localization_maximalSpectrum R,
      fun x ↦ ⟨ψ.symm x, (ψ.commutes (ψ.symm x)).symm.trans (ψ.apply_symm_apply x)⟩⟩

@[simp]
theorem equivPiLocalizationMaximal_apply (x : R) :
    equivPiLocalizationMaximal R x = algebraMap R _ x :=
  rfl

@[simp]
theorem equivPiLocalizationMaximal_apply_apply (x : R) (I : MaximalSpectrum R) :
    equivPiLocalizationMaximal R x I = algebraMap R _ x :=
  rfl

variable (R) in
/-- An Artinian local ring is isomorphic to the product of its localizations. -/
noncomputable def equivPiLocalizationPrime :
    R ≃ₐ[R] ∀ I : PrimeSpectrum R, Localization.AtPrime I.1 :=
  (equivPiLocalizationMaximal R).trans (AlgEquiv.piCongrLeft R (fun I ↦ Localization.AtPrime I.1)
    primeSpectrumEquivMaximalSpectrum.symm)

@[simp]
theorem equivPiLocalizationPrime_apply (x : R) :
    equivPiLocalizationPrime R x = algebraMap R _ x :=
  rfl

@[simp]
theorem equivPiLocalizationPrime_apply_apply (x : R) (I : PrimeSpectrum R) :
    equivPiLocalizationPrime R x I = algebraMap R _ x :=
  rfl

variable (R) in
/-- Commutative Artinian reduced local ring is a field. -/
theorem isField_of_isReduced_of_isLocalRing [IsReduced R] [IsLocalRing R] : IsField R :=
  (IsArtinianRing.equivPi R).toRingEquiv.trans (RingEquiv.piUnique _) |>.toMulEquiv.isField
    (Ideal.Quotient.field _).toIsField

section Localization

variable (S : Submonoid R) (L : Type*) [CommSemiring L] [Algebra R L] [IsLocalization S L]
include S

/-- Localizing an Artinian ring can only reduce the amount of elements. -/
theorem localization_surjective : Function.Surjective (algebraMap R L) := by
  intro r'
  obtain ⟨r₁, s, rfl⟩ := IsLocalization.exists_mk'_eq S r'
  rsuffices ⟨r₂, h⟩ : ∃ r : R, IsLocalization.mk' L 1 s = algebraMap R L r
  · exact ⟨r₁ * r₂, by rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, h]⟩
  obtain ⟨n, r, hr⟩ := IsArtinian.exists_pow_succ_smul_dvd (s : R) (1 : R)
  use r
  rw [smul_eq_mul, smul_eq_mul, pow_succ, mul_assoc] at hr
  apply_fun algebraMap R L at hr
  simp only [map_mul] at hr
  rw [← IsLocalization.mk'_one (M := S) L, IsLocalization.mk'_eq_iff_eq, mul_one,
    Submonoid.coe_one, ← (IsLocalization.map_units L (s ^ n)).mul_left_cancel hr, map_mul]

theorem localization_artinian : IsArtinianRing L :=
  (localization_surjective S L).isArtinianRing

/-- `IsArtinianRing.localization_artinian` can't be made an instance, as it would make `S` + `R`
into metavariables. However, this is safe. -/
instance : IsArtinianRing (Localization S) :=
  localization_artinian S _

end Localization

end IsArtinianRing
