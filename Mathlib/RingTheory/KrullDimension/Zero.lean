/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!

# Zero-dimensional rings

We provide further API for zero-dimensional rings.
Basic definitions and lemmas are provided in `Mathlib/RingTheory/KrullDimension/Basic.lean`.

-/

section CommSemiring

variable {R : Type*} [CommSemiring R] [Ring.KrullDimLE 0 R] (I : Ideal R)

lemma Ring.KrullDimLE.mem_minimalPrimes_iff {I J : Ideal R} :
    I ∈ J.minimalPrimes ↔ I.IsPrime ∧ J ≤ I :=
  ⟨fun H ↦ H.1, fun H ↦ ⟨H, fun _ h e ↦ (h.1.isMaximal'.eq_of_le H.1.ne_top e).ge⟩⟩

lemma Ring.KrullDimLE.mem_minimalPrimes_iff_le_of_isPrime {I J : Ideal R} [I.IsPrime] :
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
example [Subsingleton R] : Ring.KrullDimLE 0 R := inferInstance

lemma Ring.KrullDimLE.isField_of_isDomain [IsDomain R] : IsField R := by
  by_contra h
  obtain ⟨p, hp, h⟩ := Ring.not_isField_iff_exists_prime.mp h
  exact hp.symm (Ideal.bot_prime.isMaximal'.eq_of_le h.ne_top bot_le)

omit [Ring.KrullDimLE 0 R] in
lemma ringKrullDimZero_iff_ringKrullDim_eq_zero [Nontrivial R] :
    Ring.KrullDimLE 0 R ↔ ringKrullDim R = 0 := by
  rw [Ring.KrullDimLE, Order.krullDimLE_iff, le_antisymm_iff, ← ringKrullDim, Nat.cast_zero,
    iff_self_and]
  exact fun _ ↦ ringKrullDim_nonneg_of_nontrivial

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
    change x ∈ nilradical R ↔ x ∈ IsLocalRing.maximalIdeal R
    rw [nilradical, Ideal.radical_eq_sInf]
    simp [← Ideal.isMaximal_iff_isPrime, IsLocalRing.isMaximal_iff]
  tfae_have 3 → 4 := by
    refine fun H ↦ ⟨fun e ↦ ?_, fun I hI ↦ ?_⟩
    · obtain ⟨n, hn⟩ := (Ideal.eq_top_iff_one _).mp e
      exact (H 0).mp .zero ((show (1 : R) = 0 by simpa using hn) ▸ isUnit_one)
    · obtain ⟨x, hx, hx'⟩ := (SetLike.lt_iff_le_and_exists.mp hI).2
      exact Ideal.eq_top_of_isUnit_mem _ hx (not_not.mp ((H x).not.mp hx'))
  tfae_have 4 → 2 := fun H ↦ ⟨_, H.isPrime, fun p (hp : p.IsPrime) ↦
      (H.eq_of_le hp.ne_top (nilradical_le_prime p)).symm⟩
  tfae_have 2 → 1 := by
    rintro ⟨P, hP₁, hP₂⟩
    obtain ⟨P, hP₃, -⟩ := P.exists_le_maximal hP₁.ne_top
    obtain rfl := hP₂ P hP₃.isPrime
    exact ⟨.mk₀ fun Q h ↦ hP₂ Q h ▸ hP₃, .of_unique_max_ideal ⟨P, hP₃, fun Q h ↦ hP₂ Q h.isPrime⟩⟩
  tfae_finish

@[simp]
lemma le_isUnit_iff_zero_notMem [IsLocalRing R]
    {M : Submonoid R} : M ≤ IsUnit.submonoid R ↔ 0 ∉ M := by
  have := ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 2 rfl rfl).mp ⟨‹_›, ‹_›⟩
  exact ⟨fun h₁ h₂ ↦ not_isUnit_zero (h₁ h₂),
    fun H x hx ↦ (this x).not_left.mp fun ⟨n, hn⟩ ↦ H (hn ▸ pow_mem hx n)⟩

@[deprecated (since := "2025-05-23")] alias le_isUnit_iff_zero_not_mem := le_isUnit_iff_zero_notMem

variable (R) in
theorem Ring.KrullDimLE.existsUnique_isPrime [IsLocalRing R] :
    ∃! I : Ideal R, I.IsPrime :=
  ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 1 rfl rfl).mp ⟨‹_›, ‹_›⟩

theorem Ring.KrullDimLE.eq_maximalIdeal_of_isPrime [IsLocalRing R] (J : Ideal R) [J.IsPrime] :
    J = IsLocalRing.maximalIdeal R :=
  (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 1 rfl rfl).mp ⟨‹_›, ‹_›⟩).unique
    ‹_› inferInstance

lemma Ring.KrullDimLE.radical_eq_maximalIdeal [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) :
    I.radical = IsLocalRing.maximalIdeal R := by
  rw [Ideal.radical_eq_sInf]
  refine (sInf_le ?_).antisymm (le_sInf ?_)
  · exact ⟨IsLocalRing.le_maximalIdeal hI, inferInstance⟩
  · rintro J ⟨h₁, h₂⟩
    exact (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime J).ge

variable (R) in
theorem Ring.KrullDimLE.subsingleton_primeSpectrum [IsLocalRing R] :
    Subsingleton (PrimeSpectrum R) :=
  ⟨fun x y ↦ PrimeSpectrum.ext <|
    (eq_maximalIdeal_of_isPrime x.1).trans (eq_maximalIdeal_of_isPrime y.1).symm⟩

theorem Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal [IsLocalRing R] {x} :
    IsNilpotent x ↔ x ∈ IsLocalRing.maximalIdeal R :=
  ((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 0 2 rfl rfl).mp ⟨‹_›, ‹_›⟩ x

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
  (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 3 0 rfl rfl).mp ‹_›).2

omit [Ring.KrullDimLE 0 R] in
variable (R) in
theorem Ring.KrullDimLE.of_isMaximal_nilradical [(nilradical R).IsMaximal] :
    Ring.KrullDimLE 0 R :=
  (((Ring.krullDimLE_zero_and_isLocalRing_tfae R).out 3 0 rfl rfl).mp ‹_›).1

omit [Ring.KrullDimLE 0 R] in
lemma Ring.KrullDimLE.of_isLocalization (p : Ideal R) (hp : p ∈ minimalPrimes R)
    (S : Type*) [CommSemiring S] [Algebra R S] [IsLocalization.AtPrime S p (hp := hp.1.1)] :
    Ring.KrullDimLE 0 S :=
  have := IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes p hp S
  ⟨Order.krullDim_nonpos_of_subsingleton⟩

lemma Ring.KrullDimLE.isField_of_isReduced [IsReduced R] [IsLocalRing R] : IsField R := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← nilradical_eq_maximalIdeal,
    nilradical_eq_zero, Ideal.zero_eq_bot]

instance PrimeSpectrum.unique_of_ringKrullDimLE_zero [IsLocalRing R] : Unique (PrimeSpectrum R) :=
  ⟨⟨IsLocalRing.closedPoint _⟩,
    fun _ ↦ PrimeSpectrum.ext (Ring.KrullDimLE.eq_maximalIdeal_of_isPrime _)⟩

end IsLocalRing

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (I : Ideal R)

lemma Ideal.jacobson_eq_radical [Ring.KrullDimLE 0 R] : I.jacobson = I.radical := by
  simp [jacobson, radical_eq_sInf, Ideal.isMaximal_iff_isPrime]

instance (priority := 100) [Ring.KrullDimLE 0 R] : IsJacobsonRing R :=
  ⟨fun I hI ↦ by rw [I.jacobson_eq_radical, hI.radical]⟩

end CommRing
