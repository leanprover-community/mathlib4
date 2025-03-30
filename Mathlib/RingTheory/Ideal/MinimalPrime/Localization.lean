/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.Nilpotent.Lemmas

/-!

# Minimal primes and localization

We provide various results concerning the minimal primes above an ideal that needs the theory
of localizations

## Main results
- `Ideal.exists_minimalPrimes_comap_eq` If `p` is a minimal prime over `f ⁻¹ I`, then it is the
  preimage of some minimal prime over `I`.
- `Ideal.minimalPrimes_eq_comap`: The minimal primes over `I` are precisely the preimages of
  minimal primes of `R ⧸ I`.
- `IsLocalization.minimalPrimes_comap`: If `A` is a localization of `R` with respect to the
  submonoid `S`, `J` is an ideal of `A`, then the minimal primes over the preimage of `J`
  (under `R →+* A`) are exactly the preimages of the minimal primes over `J`.
- `IsLocalization.minimalPrimes_map`: If `A` is a localization of `R` with respect to the
  submonoid `S`, `J` is an ideal of `R`, then the minimal primes over the span of the image of `J`
  (under `R →+* A`) are exactly the ideals of `A` such that the preimage of which is a minimal prime
  over `J`.
- `Localization.AtPrime.prime_unique_of_minimal`: When localizing at a minimal prime ideal `I`,
  the resulting ring only has a single prime ideal.
-/


section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] {I J : Ideal R}

theorem Ideal.iUnion_minimalPrimes :
    ⋃ p ∈ I.minimalPrimes, p = { x | ∃ y ∉ I.radical, x * y ∈ I.radical } := by
  classical
  ext x
  simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop, Set.mem_setOf_eq]
  constructor
  · rintro ⟨p, ⟨⟨hp₁, hp₂⟩, hp₃⟩, hxp⟩
    have : p.map (algebraMap R (Localization.AtPrime p)) ≤ (I.map (algebraMap _ _)).radical := by
      rw [Ideal.radical_eq_sInf, le_sInf_iff]
      rintro q ⟨hq', hq⟩
      obtain ⟨h₁, h₂⟩ := ((IsLocalization.AtPrime.orderIsoOfPrime _ p) ⟨q, hq⟩).2
      rw [Ideal.map_le_iff_le_comap] at hq' ⊢
      exact hp₃ ⟨h₁, hq'⟩ h₂
    obtain ⟨n, hn⟩ := this (Ideal.mem_map_of_mem _ hxp)
    rw [IsLocalization.mem_map_algebraMap_iff (M := p.primeCompl)] at hn
    obtain ⟨⟨a, b⟩, hn⟩ := hn
    rw [← map_pow, ← map_mul, IsLocalization.eq_iff_exists p.primeCompl] at hn
    obtain ⟨t, ht⟩ := hn
    refine ⟨t * b, fun h ↦ (t * b).2 (hp₁.radical_le_iff.mpr hp₂ h), n + 1, ?_⟩
    simp only at ht
    have : (x * (t.1 * b.1)) ^ (n + 1) = (t.1 ^ n * b.1 ^ n * x * t.1) * a := by
      rw [mul_assoc, ← ht]; ring
    rw [this]
    exact I.mul_mem_left _ a.2
  · rintro ⟨y, hy, hx⟩
    obtain ⟨p, hp, hyp⟩ : ∃ p ∈ I.minimalPrimes, y ∉ p := by
      simpa [← Ideal.sInf_minimalPrimes] using hy
    refine ⟨p, hp, (hp.1.1.mem_or_mem ?_).resolve_right hyp⟩
    exact hp.1.1.radical_le_iff.mpr hp.1.2 hx

theorem Ideal.exists_mul_mem_of_mem_minimalPrimes
    {p : Ideal R} (hp : p ∈ I.minimalPrimes) {x : R} (hx : x ∈ p) :
    ∃ y ∉ I, x * y ∈ I := by
  classical
  obtain ⟨y, hy, n, hx⟩ := Ideal.iUnion_minimalPrimes.subset (Set.mem_biUnion hp hx)
  have H : ∃ m, x ^ m * y ^ n ∈ I := ⟨n, mul_pow x y n ▸ hx⟩
  have : Nat.find H ≠ 0 :=
    fun h ↦ hy ⟨n, by simpa only [h, pow_zero, one_mul] using Nat.find_spec H⟩
  refine ⟨x ^ (Nat.find H - 1) * y ^ n, Nat.find_min H (Nat.sub_one_lt this), ?_⟩
  rw [← mul_assoc, ← pow_succ', tsub_add_cancel_of_le (Nat.one_le_iff_ne_zero.mpr this)]
  exact Nat.find_spec H

/-- minimal primes are contained in zero divisors. -/
lemma Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes {p : Ideal R} (hp : p ∈ minimalPrimes R) :
    Disjoint (p : Set R) (nonZeroDivisors R) := by
  classical
  rw [← Set.subset_compl_iff_disjoint_right, Set.subset_def]
  simp only [SetLike.mem_coe, Set.mem_compl_iff, mem_nonZeroDivisors_iff, not_forall,
    Classical.not_imp]
  intro x hxp
  simp_rw [exists_prop, @and_comm (_ * _ = _), ← mul_comm x]
  exact Ideal.exists_mul_mem_of_mem_minimalPrimes hp hxp

theorem Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective {f : R →+* S}
    (hf : Function.Injective f) (p) (H : p ∈ minimalPrimes R) :
    ∃ p' : Ideal S, p'.IsPrime ∧ p'.comap f = p := by
  have := H.1.1
  have : Nontrivial (Localization (Submonoid.map f p.primeCompl)) := by
    refine ⟨⟨1, 0, ?_⟩⟩
    convert (IsLocalization.map_injective_of_injective p.primeCompl (Localization.AtPrime p)
        (Localization <| p.primeCompl.map f) hf).ne one_ne_zero
    · rw [map_one]
    · rw [map_zero]
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Localization (Submonoid.map f p.primeCompl))
  refine ⟨M.comap (algebraMap S <| Localization (Submonoid.map f p.primeCompl)), inferInstance, ?_⟩
  rw [Ideal.comap_comap, ← @IsLocalization.map_comp _ _ _ _ _ _ _ _ Localization.isLocalization
      _ _ _ _ _ Localization.isLocalization p.primeCompl.le_comap_map,
    ← Ideal.comap_comap]
  suffices _ ≤ p by exact this.antisymm (H.2 ⟨inferInstance, bot_le⟩ this)
  intro x hx
  by_contra h
  apply hM.ne_top
  apply M.eq_top_of_isUnit_mem hx
  apply IsUnit.map
  apply IsLocalization.map_units _ (show p.primeCompl from ⟨x, h⟩)

end

section

variable {R S : Type*} [CommRing R] [CommRing S] {I J : Ideal R}

theorem Ideal.exists_comap_eq_of_mem_minimalPrimes {I : Ideal S} (f : R →+* S) (p)
    (H : p ∈ (I.comap f).minimalPrimes) : ∃ p' : Ideal S, p'.IsPrime ∧ I ≤ p' ∧ p'.comap f = p := by
  have := H.1.1
  let f' := (Ideal.Quotient.mk I).comp f
  have e : RingHom.ker f' = I.comap f := by
    ext1
    exact Submodule.Quotient.mk_eq_zero _
  have : RingHom.ker (Ideal.Quotient.mk <| RingHom.ker f') ≤ p := by
    rw [Ideal.mk_ker, e]
    exact H.1.2
  suffices _ by
    have ⟨p', hp₁, hp₂⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective
      (RingHom.kerLift_injective f') (p.map <| Ideal.Quotient.mk <| RingHom.ker f') this
    refine ⟨p'.comap <| Ideal.Quotient.mk I, Ideal.IsPrime.comap _, ?_, ?_⟩
    · exact Ideal.mk_ker.symm.trans_le (Ideal.comap_mono bot_le)
    · convert congr_arg (Ideal.comap <| Ideal.Quotient.mk <| RingHom.ker f') hp₂
      rwa [Ideal.comap_map_of_surjective (Ideal.Quotient.mk <| RingHom.ker f')
        Ideal.Quotient.mk_surjective, eq_comm, sup_eq_left]
  refine ⟨⟨?_, bot_le⟩, ?_⟩
  · apply Ideal.map_isPrime_of_surjective _ this
    exact Ideal.Quotient.mk_surjective
  · rintro q ⟨hq, -⟩ hq'
    rw [← Ideal.map_comap_of_surjective
        (Ideal.Quotient.mk (RingHom.ker ((Ideal.Quotient.mk I).comp f)))
        Ideal.Quotient.mk_surjective q]
    apply Ideal.map_mono
    apply H.2
    · refine ⟨inferInstance, (Ideal.mk_ker.trans e).symm.trans_le (Ideal.comap_mono bot_le)⟩
    · refine (Ideal.comap_mono hq').trans ?_
      rw [Ideal.comap_map_of_surjective]
      exacts [sup_le rfl.le this, Ideal.Quotient.mk_surjective]

theorem Ideal.exists_minimalPrimes_comap_eq {I : Ideal S} (f : R →+* S) (p)
    (H : p ∈ (I.comap f).minimalPrimes) : ∃ p' ∈ I.minimalPrimes, Ideal.comap f p' = p := by
  obtain ⟨p', h₁, h₂, h₃⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes f p H
  obtain ⟨q, hq, hq'⟩ := Ideal.exists_minimalPrimes_le h₂
  refine ⟨q, hq, Eq.symm ?_⟩
  have := hq.1.1
  have := (Ideal.comap_mono hq').trans_eq h₃
  exact (H.2 ⟨inferInstance, Ideal.comap_mono hq.1.2⟩ this).antisymm this

theorem Ideal.minimalPrimes_comap_subset {A : Type*} [CommRing A] (f : R →+* A) (J : Ideal A) :
    (J.comap f).minimalPrimes ⊆ Ideal.comap f '' J.minimalPrimes :=
  fun p hp ↦ Ideal.exists_minimalPrimes_comap_eq f p hp

theorem Ideal.minimal_primes_comap_of_surjective {f : R →+* S} (hf : Function.Surjective f)
    {I J : Ideal S} (h : J ∈ I.minimalPrimes) : J.comap f ∈ (I.comap f).minimalPrimes := by
  have := h.1.1
  refine ⟨⟨inferInstance, Ideal.comap_mono h.1.2⟩, ?_⟩
  rintro K ⟨hK, e₁⟩ e₂
  have : RingHom.ker f ≤ K := (Ideal.comap_mono bot_le).trans e₁
  rw [← sup_eq_left.mpr this, RingHom.ker_eq_comap_bot, ← Ideal.comap_map_of_surjective f hf]
  apply Ideal.comap_mono _
  apply h.2 _ _
  · exact ⟨Ideal.map_isPrime_of_surjective hf this, Ideal.le_map_of_comap_le_of_surjective f hf e₁⟩
  · exact Ideal.map_le_of_le_comap e₂

theorem Ideal.comap_minimalPrimes_eq_of_surjective {f : R →+* S} (hf : Function.Surjective f)
    (I : Ideal S) : (I.comap f).minimalPrimes = Ideal.comap f '' I.minimalPrimes := by
  ext J
  constructor
  · intro H
    obtain ⟨p, h, rfl⟩ := Ideal.exists_minimalPrimes_comap_eq f J H
    exact ⟨p, h, rfl⟩
  · rintro ⟨J, hJ, rfl⟩
    exact Ideal.minimal_primes_comap_of_surjective hf hJ

theorem Ideal.minimalPrimes_eq_comap :
    I.minimalPrimes = Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (R ⧸ I) := by
  rw [minimalPrimes, ← Ideal.comap_minimalPrimes_eq_of_surjective Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

end

section

variable {R : Type*} [CommRing R] (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]

theorem IsLocalization.minimalPrimes_map [IsLocalization S A] (J : Ideal R) :
    (J.map (algebraMap R A)).minimalPrimes = Ideal.comap (algebraMap R A) ⁻¹' J.minimalPrimes := by
  ext p
  constructor
  · intro hp
    haveI := hp.1.1
    refine ⟨⟨Ideal.IsPrime.comap _, Ideal.map_le_iff_le_comap.mp hp.1.2⟩, ?_⟩
    rintro I hI e
    have hI' : Disjoint (S : Set R) I := Set.disjoint_of_subset_right e
      ((IsLocalization.isPrime_iff_isPrime_disjoint S A _).mp hp.1.1).2
    refine (Ideal.comap_mono <|
      hp.2 ⟨?_, Ideal.map_mono hI.2⟩ (Ideal.map_le_iff_le_comap.mpr e)).trans_eq ?_
    · exact IsLocalization.isPrime_of_isPrime_disjoint S A I hI.1 hI'
    · exact IsLocalization.comap_map_of_isPrime_disjoint S A _ hI.1 hI'
  · intro hp
    refine ⟨⟨?_, Ideal.map_le_iff_le_comap.mpr hp.1.2⟩, ?_⟩
    · rw [IsLocalization.isPrime_iff_isPrime_disjoint S A,
        IsLocalization.disjoint_comap_iff S]
      refine ⟨hp.1.1, ?_⟩
      rintro rfl
      exact hp.1.1.ne_top rfl
    · intro I hI e
      rw [← IsLocalization.map_comap S A I, ← IsLocalization.map_comap S A p]
      haveI := hI.1
      exact Ideal.map_mono (hp.2 ⟨Ideal.IsPrime.comap _, Ideal.map_le_iff_le_comap.mp hI.2⟩
        (Ideal.comap_mono e))

theorem IsLocalization.minimalPrimes_comap [IsLocalization S A] (J : Ideal A) :
    (J.comap (algebraMap R A)).minimalPrimes = Ideal.comap (algebraMap R A) '' J.minimalPrimes := by
  conv_rhs => rw [← map_comap S A J, minimalPrimes_map S]
  refine (Set.image_preimage_eq_iff.mpr ?_).symm
  exact subset_trans (Ideal.minimalPrimes_comap_subset (algebraMap R A) J) (by simp)

end

namespace Localization.AtPrime

variable {R : Type*} [CommSemiring R] {I : Ideal R} [hI : I.IsPrime] (hMin : I ∈ minimalPrimes R)
include hMin

theorem _root_.IsLocalization.AtPrime.prime_unique_of_minimal {S} [CommSemiring S] [Algebra R S]
    [IsLocalization.AtPrime S I] {J K : Ideal S} [J.IsPrime] [K.IsPrime] : J = K :=
  haveI : Subsingleton {i : Ideal R // i.IsPrime ∧ i ≤ I} := ⟨fun i₁ i₂ ↦ Subtype.ext <| by
    rw [minimalPrimes_eq_minimals, Set.mem_setOf] at hMin
    rw [hMin.eq_of_le i₁.2.1 i₁.2.2, hMin.eq_of_le i₂.2.1 i₂.2.2]⟩
  Subtype.ext_iff.mp <| (IsLocalization.AtPrime.orderIsoOfPrime S I).injective
    (a₁ := ⟨J, ‹_›⟩) (a₂ := ⟨K, ‹_›⟩) (Subsingleton.elim _ _)

theorem prime_unique_of_minimal (J : Ideal (Localization I.primeCompl)) [J.IsPrime] :
    J = IsLocalRing.maximalIdeal (Localization I.primeCompl) :=
  IsLocalization.AtPrime.prime_unique_of_minimal hMin

theorem nilpotent_iff_mem_maximal_of_minimal {x : _} :
    IsNilpotent x ↔ x ∈ IsLocalRing.maximalIdeal (Localization I.primeCompl) := by
  rw [nilpotent_iff_mem_prime]
  exact ⟨(· (IsLocalRing.maximalIdeal _) (Ideal.IsMaximal.isPrime' _)), fun _ J _ =>
    by simpa [prime_unique_of_minimal hMin J]⟩

theorem nilpotent_iff_not_unit_of_minimal {x : Localization I.primeCompl} :
    IsNilpotent x ↔ x ∈ nonunits _ := by
  simpa only [← IsLocalRing.mem_maximalIdeal] using nilpotent_iff_mem_maximal_of_minimal hMin

end Localization.AtPrime
