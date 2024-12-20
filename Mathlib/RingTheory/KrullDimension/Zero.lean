/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Ideal.MinimalPrime

/-!

# Zero-dimensional rings

## Main definition
- `RingKrullDimZero`: The class of commutative (semi)rings with krull dimension 0 (or `⊥`).
- `Ideal.isMaximal_iff_isPrime`: maximal <=> prime in zero dimensional rings.
- `ringKrullDimZero_iff_ringKrullDim_eq_zero`: `RingKrullDimZero R ↔ ringKrullDim R = 0`.
- `ringKrullDimZero_and_isLocalRing_tfae`: Equivalent conditions for zero-dimensional local rings.

-/

/-- The class of commutative rings with krull dimension 0 (or `⊥`).
See `ringKrullDimZero_iff_ringKrullDim_le_zero` and `ringKrullDimZero_iff_ringKrullDim_eq_zero` -/
@[mk_iff]
class RingKrullDimZero (R : Type*) [CommSemiring R] : Prop where
  isMaximal_of_isPrime : ∀ (I : Ideal R) [I.IsPrime], I.IsMaximal

alias Ideal.isMaximal_of_isPrime := RingKrullDimZero.isMaximal_of_isPrime

attribute [instance 900] Ideal.isMaximal_of_isPrime

section CommSemiring

variable {R : Type*} [CommSemiring R] [RingKrullDimZero R] (I : Ideal R)

variable {I} in
lemma Ideal.IsPrime.isMaximal (hI : I.IsPrime) : I.IsMaximal :=
  I.isMaximal_of_isPrime

variable {I} in
lemma Ideal.isMaximal_iff_isPrime : I.IsMaximal ↔ I.IsPrime :=
  ⟨fun h ↦ h.isPrime, fun h ↦ h.isMaximal⟩

lemma RingKrullDimZero.mem_minimalPrimes_iff {I J : Ideal R} :
    I ∈ J.minimalPrimes ↔ I.IsPrime ∧ J ≤ I :=
  ⟨fun H ↦ H.1, fun H ↦ ⟨H, fun _ h e ↦ (h.1.isMaximal.eq_of_le H.1.ne_top e).ge⟩⟩

lemma RingKrullDimZero.mem_minimalPrimes_iff_le {I J : Ideal R} [I.IsPrime] :
    I ∈ J.minimalPrimes ↔ J ≤ I := by
  rwa [mem_minimalPrimes_iff, and_iff_right]

variable (R) in
lemma RingKrullDimZero.minimalPrimes_eq_setOf_isPrime :
    minimalPrimes R = { I | I.IsPrime } := by
  ext; simp [minimalPrimes, mem_minimalPrimes_iff]

variable (R) in
lemma RingKrullDimZero.minimalPrimes_eq_setOf_isMaximal :
    minimalPrimes R = { I | I.IsMaximal } := by
  ext; simp [minimalPrimes_eq_setOf_isPrime, Ideal.isMaximal_iff_isPrime]

/-- Note that the `ringKrullDim` of the trivial ring is `⊥` and not `0`. -/
instance (priority := 100) [Subsingleton R] : RingKrullDimZero R :=
  ⟨fun _ hI ↦ (hI.ne_top (Subsingleton.elim _ _)).elim⟩

attribute [local instance] Ideal.bot_prime in
lemma RingKrullDimZero.isField_of_isDomain [IsDomain R] : IsField R := by
  by_contra h
  obtain ⟨p, hp, h⟩ := Ring.not_isField_iff_exists_prime.mp h
  exact hp.symm ((inferInstanceAs ((⊥ : Ideal R).IsMaximal)).eq_of_le h.ne_top bot_le)

section IsLocalRing

omit [RingKrullDimZero R] in
variable (R) in
lemma ringKrullDimZero_and_isLocalRing_tfae :
    List.TFAE
    [ RingKrullDimZero R ∧ IsLocalRing R,
      ∃! I : Ideal R, I.IsPrime,
      ∀ x : R, IsNilpotent x ↔ ¬ IsUnit x,
      (nilradical R).IsMaximal ] := by
  tfae_have 1 → 3 := by
    intro ⟨h₁, h₂⟩ x
    show x ∈ nilradical R ↔ x ∈ IsLocalRing.maximalIdeal R
    rw [nilradical, Ideal.radical_eq_sInf]
    simp [← Ideal.isMaximal_iff_isPrime, IsLocalRing.isMaximal_iff]
  tfae_have 3 → 4 := by
    intro H
    refine ⟨?_, ?_⟩
    · intro e
      obtain ⟨n, hn⟩ := (Ideal.eq_top_iff_one _).mp e
      exact (H 0).mp .zero ((show (1 : R) = 0 by simpa using hn) ▸ isUnit_one)
    · intro I hI
      obtain ⟨x, hx, hx'⟩ := (SetLike.lt_iff_le_and_exists.mp hI).2
      exact Ideal.eq_top_of_isUnit_mem _ hx (not_not.mp ((H x).not.mp hx'))
  tfae_have 4 → 2 := by
    intro H
    exact ⟨_, H.isPrime, fun p (hp : p.IsPrime) ↦
      (H.eq_of_le hp.ne_top (nilradical_le_prime p)).symm⟩
  tfae_have 2 → 1 := by
    rintro ⟨P, hP₁, hP₂⟩
    obtain ⟨P, hP₃, -⟩ := P.exists_le_maximal hP₁.ne_top
    obtain rfl := hP₂ P hP₃.isPrime
    exact ⟨⟨fun P' h ↦ hP₂ P' h ▸ hP₃⟩, .of_unique_max_ideal ⟨P, hP₃, fun P' h ↦ hP₂ P' h.isPrime⟩⟩
  tfae_finish

@[simp]
lemma RingKrullDimZero.le_isUnit_iff_zero_not_mem [IsLocalRing R]
    {M : Submonoid R} : M ≤ IsUnit.submonoid R ↔ 0 ∉ M := by
  have := ((ringKrullDimZero_and_isLocalRing_tfae R).out 0 2).mp
    (by exact ⟨inferInstance, inferInstance⟩)
  exact ⟨fun h₁ h₂ ↦ not_isUnit_zero (h₁ h₂),
    fun H x hx ↦ (this x).not_left.mp fun ⟨n, hn⟩ ↦ H (hn ▸ pow_mem hx n)⟩

variable (R) in
theorem RingKrullDimZero.existsUnique_isPrime [IsLocalRing R] :
    ∃! I : Ideal R, I.IsPrime :=
  ((ringKrullDimZero_and_isLocalRing_tfae R).out 0 1).mp
    (by exact ⟨inferInstance, inferInstance⟩)

theorem RingKrullDimZero.unique_isPrime [IsLocalRing R] (J : Ideal R) [J.IsPrime] :
    J = IsLocalRing.maximalIdeal R :=
  have : ∃! I : Ideal R, I.IsPrime := ((ringKrullDimZero_and_isLocalRing_tfae R).out 0 1).mp
    (by exact ⟨inferInstance, inferInstance⟩)
  this.unique inferInstance inferInstance

theorem RingKrullDimZero.isNilpotent_iff_mem_maximalIdeal [IsLocalRing R] {x} :
    IsNilpotent x ↔ x ∈ IsLocalRing.maximalIdeal R :=
  (ringKrullDimZero_and_isLocalRing_tfae R _
    (List.mem_of_get? (n := 0) rfl) _ (List.mem_of_get? (n := 2) rfl)).mp
      ⟨inferInstance, inferInstance⟩ x

theorem RingKrullDimZero.isNilpotent_iff_mem_nonunits [IsLocalRing R] {x} :
    IsNilpotent x ↔ x ∈ nonunits R :=
  isNilpotent_iff_mem_maximalIdeal

variable (R) in
theorem RingKrullDimZero.nilradical_eq_maximalIdeal [IsLocalRing R] :
    nilradical R = IsLocalRing.maximalIdeal R :=
  Ideal.ext fun _ ↦ isNilpotent_iff_mem_maximalIdeal


omit [RingKrullDimZero R] in
variable (R) in
theorem IsLocalRing.of_nilradical_isMaximal [(nilradical R).IsMaximal] :
    IsLocalRing R :=
  ((ringKrullDimZero_and_isLocalRing_tfae R _
    (List.mem_of_get? (n := 3) rfl) _ (List.mem_of_get? (n := 0) rfl)).mp
    inferInstance).2

omit [RingKrullDimZero R] in
variable (R) in
theorem RingKrullDimZero.of_nilradical_isMaximal [(nilradical R).IsMaximal] :
    RingKrullDimZero R :=
  ((ringKrullDimZero_and_isLocalRing_tfae R _
    (List.mem_of_get? (n := 3) rfl) _ (List.mem_of_get? (n := 0) rfl)).mp
    inferInstance).1

omit [RingKrullDimZero R] in
lemma RingKrullDimZero.of_isLocalization (p : Ideal R) (hp : p ∈ minimalPrimes R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization.AtPrime S p (hp := hp.1.1)] :
    RingKrullDimZero S := by
  have := hp.1.1
  have := IsLocalization.AtPrime.isLocalRing S p
  haveI : Subsingleton {i : Ideal R // i.IsPrime ∧ i ≤ p} := ⟨fun i₁ i₂ ↦ Subtype.ext <| by
    rw [minimalPrimes_eq_minimals, Set.mem_setOf] at hp
    rw [hp.eq_of_le i₁.2.1 i₁.2.2, hp.eq_of_le i₂.2.1 i₂.2.2]⟩
  have := ((ringKrullDimZero_and_isLocalRing_tfae S).out 0 1).mpr
  refine (this ⟨IsLocalRing.maximalIdeal S, inferInstance, fun q hq ↦ ?_⟩).1
  exact Subtype.ext_iff.mp <| (IsLocalization.AtPrime.orderIsoOfPrime S p).injective
    (a₁ := ⟨q, hq⟩) (a₂ := ⟨IsLocalRing.maximalIdeal S, inferInstance⟩) (Subsingleton.elim _ _)

lemma RingKrullDimZero.isField_of_isReduced [IsReduced R] [IsLocalRing R] : IsField R := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← nilradical_eq_maximalIdeal,
    nilradical_eq_zero, Ideal.zero_eq_bot]

end IsLocalRing

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] [RingKrullDimZero R] (I : Ideal R)

lemma Ideal.jacobson_eq_radical : I.jacobson = I.radical := by
  simp [jacobson, radical_eq_sInf, Ideal.isMaximal_iff_isPrime]

instance (priority := 100) [RingKrullDimZero R] : IsJacobsonRing R :=
  ⟨fun I hI ↦ by rw [I.jacobson_eq_radical, hI.radical]⟩

omit [RingKrullDimZero R] in
lemma ringKrullDimZero_iff_ringKrullDim_eq_zero [Nontrivial R] :
    RingKrullDimZero R ↔ ringKrullDim R = 0 := by
  rw [ringKrullDimZero_iff, ringKrullDim, Order.krullDim_eq_iSup_coheight_of_nonempty]
  simp only [WithBot.coe_eq_zero, ENat.iSup_eq_zero, Order.coheight_eq_zero,
    (PrimeSpectrum.equivSubtype R).forall_congr_left, Subtype.forall, PrimeSpectrum.isMax_iff]
  rfl

omit [RingKrullDimZero R] in
lemma ringKrullDimZero_iff_ringKrullDim_le_zero :
    RingKrullDimZero R ↔ ringKrullDim R ≤ 0 := by
  cases subsingleton_or_nontrivial R
  · simp only [ringKrullDim_eq_bot_of_subsingleton, bot_le, iff_true]
    infer_instance
  · simp [ringKrullDimZero_iff_ringKrullDim_eq_zero, le_antisymm_iff,
      ringKrullDim_nonneg_of_nontrivial]

end CommRing

section Deprecated

namespace Localization.AtPrime

variable {R : Type*} [CommSemiring R] {I : Ideal R} [hI : I.IsPrime] (hMin : I ∈ minimalPrimes R)
include hMin

@[deprecated RingKrullDimZero.existsUnique_isPrime (since := "2024-12-20")]
lemma _root_.IsLocalization.AtPrime.prime_unique_of_minimal {S} [CommSemiring S] [Algebra R S]
    [IsLocalization.AtPrime S I] {J K : Ideal S} [J.IsPrime] [K.IsPrime] : J = K :=
  haveI := RingKrullDimZero.of_isLocalization I hMin S
  haveI := IsLocalization.AtPrime.isLocalRing S I
  (RingKrullDimZero.existsUnique_isPrime _).unique inferInstance inferInstance

@[deprecated (since := "2024-12-20")]
alias prime_unique_of_minimal := RingKrullDimZero.unique_isPrime

@[deprecated (since := "2024-12-20")]
alias nilpotent_iff_mem_maximal_of_minimal := RingKrullDimZero.isNilpotent_iff_mem_maximalIdeal

@[deprecated (since := "2024-12-20")]
alias nilpotent_iff_not_unit_of_minimal := RingKrullDimZero.isNilpotent_iff_mem_nonunits

end Localization.AtPrime

section Nilrad_max_localization

open Ideal

@[deprecated (since := "2024-11-09")]
alias LocalRing.of_nilradical_isMaximal := IsLocalRing.of_nilradical_isMaximal

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] [Algebra R S] {M : Submonoid R}

attribute [local instance]
  IsLocalRing.of_nilradical_isMaximal RingKrullDimZero.of_nilradical_isMaximal in
/--
Let `S` be the localization of a commutative semiring `R` at a submonoid `M` that does not
contain 0. If the nilradical of `R` is maximal then there is a `R`-algebra isomorphism between
`R` and `S`. -/
@[deprecated IsLocalization.atUnits (since := "2024-12-20")]
noncomputable def localizationEquivSelfOfNilradicalIsMaximal [h : (nilradical R).IsMaximal]
    (h' : (0 : R) ∉ M) [IsLocalization M S] : R ≃ₐ[R] S :=
  IsLocalization.atUnits _ _ (by simpa)

end Nilrad_max_localization

end Deprecated
