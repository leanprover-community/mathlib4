/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!

# Zero-dimensional rings

We provide basic API for zero-dimensional rings.

-/

section CommSemiring

variable {R : Type*} [CommSemiring R] [Ring.KrullDimLE 0 R] (I : Ideal R)

variable {I} in
/-- Also see `Ideal.IsPrime.isMaximal` for the analogous statement for dedekind domains. -/
lemma Ideal.IsPrime.isMaximal' (hI : I.IsPrime) : I.IsMaximal :=
  I.isMaximal_of_isPrime

lemma Ring.KrullDimLE.mem_minimalPrimes_iff {I J : Ideal R} :
    I ∈ J.minimalPrimes ↔ I.IsPrime ∧ J ≤ I :=
  ⟨fun H ↦ H.1, fun H ↦ ⟨H, fun _ h e ↦ (h.1.isMaximal'.eq_of_le H.1.ne_top e).ge⟩⟩

lemma Ring.KrullDimLE.mem_minimalPrimes_iff_le {I J : Ideal R} [I.IsPrime] :
    I ∈ J.minimalPrimes ↔ J ≤ I := by
  rwa [mem_minimalPrimes_iff, and_iff_right]

variable (R) in
lemma Ring.KrullDimLE.minimalPrimes_eq_setOf_isPrime :
    minimalPrimes R = { I | I.IsPrime } := by
  ext; simp [minimalPrimes, mem_minimalPrimes_iff]

variable (R) in
lemma Ring.KrullDimLE.minimalPrimes_eq_setOf_isMaximal :
    minimalPrimes R = { I | I.IsMaximal } := by
  ext; simp [minimalPrimes_eq_setOf_isPrime, Ideal.isMaximal_iff_isPrime]

/-- Note that the `ringKrullDim` of the trivial ring is `⊥` and not `0`. -/
instance (priority := 100) [Subsingleton R] : Ring.KrullDimLE 0 R :=
  ⟨show ringKrullDim R ≤ 0 by rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le⟩

lemma Ring.KrullDimLE.isField_of_isDomain [IsDomain R] : IsField R := by
  by_contra h
  obtain ⟨p, hp, h⟩ := Ring.not_isField_iff_exists_prime.mp h
  exact hp.symm (Ideal.bot_prime.isMaximal'.eq_of_le h.ne_top bot_le)

section IsLocalRing

omit [Ring.KrullDimLE 0 R] in
variable (R) in
lemma Ring.krullDimLE_zero_and_isLocalRing_tfae :
    List.TFAE
    [ Ring.KrullDimLE 0 R ∧ IsLocalRing R,
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
    exact ⟨.mk₀ fun Q h ↦ hP₂ Q h ▸ hP₃, .of_unique_max_ideal ⟨P, hP₃, fun Q h ↦ hP₂ Q h.isPrime⟩⟩
  tfae_finish

@[simp]
lemma le_isUnit_iff_zero_not_mem [IsLocalRing R]
    {M : Submonoid R} : M ≤ IsUnit.submonoid R ↔ 0 ∉ M := by
  have := ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 2).mp
    (by exact ⟨inferInstance, inferInstance⟩)
  exact ⟨fun h₁ h₂ ↦ not_isUnit_zero (h₁ h₂),
    fun H x hx ↦ (this x).not_left.mp fun ⟨n, hn⟩ ↦ H (hn ▸ pow_mem hx n)⟩

variable (R) in
theorem Ring.KrullDimLE.existsUnique_isPrime [IsLocalRing R] :
    ∃! I : Ideal R, I.IsPrime :=
  ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 1).mp
    (by exact ⟨inferInstance, inferInstance⟩)

theorem Ring.KrullDimLE.unique_isPrime [IsLocalRing R] (J : Ideal R) [J.IsPrime] :
    J = IsLocalRing.maximalIdeal R :=
  have : ∃! I : Ideal R, I.IsPrime := ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 1).mp
    (by exact ⟨inferInstance, inferInstance⟩)
  this.unique inferInstance inferInstance

theorem Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal [IsLocalRing R] {x} :
    IsNilpotent x ↔ x ∈ IsLocalRing.maximalIdeal R :=
  (Ring.krullDimLE_zero_and_isLocalRing_tfae R _
    (List.mem_of_getElem? (i := 0) rfl) _ (List.mem_of_getElem? (i := 2) rfl)).mp
      ⟨inferInstance, inferInstance⟩ x

theorem Ring.KrullDimLE.isNilpotent_iff_mem_nonunits [IsLocalRing R] {x} :
    IsNilpotent x ↔ x ∈ nonunits R :=
  isNilpotent_iff_mem_maximalIdeal

variable (R) in
theorem Ring.KrullDimLE.nilradical_eq_maximalIdeal [IsLocalRing R] :
    nilradical R = IsLocalRing.maximalIdeal R :=
  Ideal.ext fun _ ↦ isNilpotent_iff_mem_maximalIdeal

omit [Ring.KrullDimLE 0 R] in
variable (R) in
theorem IsLocalRing.of_isMaximal_nilradical [(nilradical R).IsMaximal] :
    IsLocalRing R :=
  ((Ring.krullDimLE_zero_and_isLocalRing_tfae R _
    (List.mem_of_getElem? (i := 3) rfl) _ (List.mem_of_getElem? (i := 0) rfl)).mp
    inferInstance).2

omit [Ring.KrullDimLE 0 R] in
variable (R) in
theorem Ring.KrullDimLE.of_isMaximal_nilradical [(nilradical R).IsMaximal] :
    Ring.KrullDimLE 0 R :=
  ((Ring.krullDimLE_zero_and_isLocalRing_tfae R _
    (List.mem_of_getElem? (i := 3) rfl) _ (List.mem_of_getElem? (i := 0) rfl)).mp
    inferInstance).1

omit [Ring.KrullDimLE 0 R] in
lemma Ring.KrullDimLE.of_isLocalization (p : Ideal R) (hp : p ∈ minimalPrimes R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization.AtPrime S p (hp := hp.1.1)] :
    Ring.KrullDimLE 0 S := by
  have := hp.1.1
  have := IsLocalization.AtPrime.isLocalRing S p
  haveI : Subsingleton {i : Ideal R // i.IsPrime ∧ i ≤ p} := ⟨fun i₁ i₂ ↦ Subtype.ext <| by
    rw [minimalPrimes_eq_minimals, Set.mem_setOf] at hp
    rw [hp.eq_of_le i₁.2.1 i₁.2.2, hp.eq_of_le i₂.2.1 i₂.2.2]⟩
  have := ((Ring.krullDimLE_zero_and_isLocalRing_tfae S).out 0 1).mpr
  refine (this ⟨IsLocalRing.maximalIdeal S, inferInstance, fun q hq ↦ ?_⟩).1
  exact Subtype.ext_iff.mp <| (IsLocalization.AtPrime.orderIsoOfPrime S p).injective
    (a₁ := ⟨q, hq⟩) (a₂ := ⟨IsLocalRing.maximalIdeal S, inferInstance⟩) (Subsingleton.elim _ _)

lemma Ring.KrullDimLE.isField_of_isReduced [IsReduced R] [IsLocalRing R] : IsField R := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← nilradical_eq_maximalIdeal,
    nilradical_eq_zero, Ideal.zero_eq_bot]

instance PrimeSpectrum.unique_of_ringKrullDimLE_zero [IsLocalRing R] : Unique (PrimeSpectrum R) :=
  ⟨⟨IsLocalRing.closedPoint _⟩, fun _ ↦ PrimeSpectrum.ext (Ring.KrullDimLE.unique_isPrime _)⟩

end IsLocalRing

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (I : Ideal R)

lemma Ideal.jacobson_eq_radical [Ring.KrullDimLE 0 R] : I.jacobson = I.radical := by
  simp [jacobson, radical_eq_sInf, Ideal.isMaximal_iff_isPrime]

instance (priority := 100) [Ring.KrullDimLE 0 R] : IsJacobsonRing R :=
  ⟨fun I hI ↦ by rw [I.jacobson_eq_radical, hI.radical]⟩

lemma ringKrullDimZero_iff_ringKrullDim_eq_zero [Nontrivial R] :
    Ring.KrullDimLE 0 R ↔ ringKrullDim R = 0 := by
  rw [Ring.KrullDimLE, Order.krullDimLE_iff, le_antisymm_iff, ← ringKrullDim, Nat.cast_zero,
    iff_self_and]
  exact fun _ ↦ ringKrullDim_nonneg_of_nontrivial

end CommRing

section Deprecated

namespace Localization.AtPrime

variable {R : Type*} [CommSemiring R] {I : Ideal R} [hI : I.IsPrime] (hMin : I ∈ minimalPrimes R)
include hMin

@[deprecated Ring.KrullDimLE.existsUnique_isPrime (since := "2024-12-20")]
lemma _root_.IsLocalization.AtPrime.prime_unique_of_minimal {S} [CommSemiring S] [Algebra R S]
    [IsLocalization.AtPrime S I] {J K : Ideal S} [J.IsPrime] [K.IsPrime] : J = K :=
  haveI := Ring.KrullDimLE.of_isLocalization I hMin S
  haveI := IsLocalization.AtPrime.isLocalRing S I
  (Ring.KrullDimLE.existsUnique_isPrime _).unique inferInstance inferInstance

@[deprecated (since := "2024-12-20")]
alias prime_unique_of_minimal := Ring.KrullDimLE.unique_isPrime

@[deprecated (since := "2024-12-20")]
alias nilpotent_iff_mem_maximal_of_minimal := Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal

@[deprecated (since := "2024-12-20")]
alias nilpotent_iff_not_unit_of_minimal := Ring.KrullDimLE.isNilpotent_iff_mem_nonunits

end Localization.AtPrime

@[deprecated "Use `PrimeSpectrum.unique_of_ringKrullDimZero` with `Ring.KrullDimLE.of_isLocalization`" (since := "2024-12-20")]
alias PrimeSpectrum.primeSpectrum_unique_of_localization_at_minimal :=
  PrimeSpectrum.unique_of_ringKrullDimZero

section Nilrad_max_localization

open Ideal

@[deprecated (since := "2024-11-09")]
alias LocalRing.of_nilradical_isMaximal := IsLocalRing.of_isMaximal_nilradical

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S] [Algebra R S] {M : Submonoid R}

attribute [local instance]
  IsLocalRing.of_isMaximal_nilradical Ring.KrullDimLE.of_isMaximal_nilradical in
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
