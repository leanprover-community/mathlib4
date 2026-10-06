/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.LocalProperties.Basic

/-!
# `IsReduced` is a local property

In this file, we prove that `IsReduced` is a local property.

## Main results

Let `R` be a commutative ring, `M` be a submonoid of `R`.

* `isReduced_localizationPreserves` :  `M⁻¹R` is reduced if `R` is reduced.
* `isReduced_ofLocalizationMaximal` : `R` is reduced if `Rₘ` is reduced for all maximal ideal `m`.

-/

public section

/-- `M⁻¹R` is reduced if `R` is reduced. -/
theorem isReduced_localizationPreserves : LocalizationPreserves fun R _ => IsReduced R := by
  introv R _ _
  constructor
  rintro x ⟨_ | n, e⟩
  · simpa using congr($e * x)
  obtain ⟨⟨y, m⟩, hx⟩ := IsLocalization.surj M x
  dsimp only at hx
  let hx' := congr($hx ^ n.succ)
  simp only [mul_pow, e, zero_mul, ← map_pow] at hx'
  rw [← (algebraMap R S).map_zero] at hx'
  obtain ⟨m', hm'⟩ := (IsLocalization.eq_iff_exists M S).mp hx'
  apply_fun (· * (m' : R) ^ n) at hm'
  simp only [mul_assoc, zero_mul, mul_zero] at hm'
  rw [← mul_left_comm, ← pow_succ', ← mul_pow] at hm'
  replace hm' := IsNilpotent.eq_zero ⟨_, hm'.symm⟩
  rw [← (IsLocalization.map_units S m).mul_left_inj, hx, zero_mul,
    IsLocalization.map_eq_zero_iff M]
  exact ⟨m', by rw [← hm', mul_comm]⟩

instance {R : Type*} [CommRing R] (M : Submonoid R) [IsReduced R] : IsReduced (Localization M) :=
  isReduced_localizationPreserves M _ inferInstance

/-- `R` is reduced if `Rₘ` is reduced for all maximal ideal `m`. -/
theorem isReduced_ofLocalizationMaximal : OfLocalizationMaximal fun R _ => IsReduced R := by
  introv R h
  constructor
  intro x hx
  apply eq_zero_of_localization
  intro J hJ
  specialize h J hJ
  exact (hx.map <| algebraMap R <| Localization.AtPrime J).eq_zero

lemma Localization.AtPrime.isField_of_mem_minimalPrimes {S : Type*} [CommRing S] [IsReduced S]
    (p : Ideal S) (min : p ∈ minimalPrimes S) :
    letI := min.isPrime
    IsField (Localization.AtPrime p) := by
  let := min.isPrime
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
  intro x hx
  apply IsReduced.eq_zero x (nilpotent_iff_mem_prime.mpr (fun q hq ↦ ?_))
  convert hx
  have : Ideal.comap (algebraMap S (Localization.AtPrime p)) q ≤ p := by
    apply le_of_le_of_eq _ (IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p)
    exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal_of_isPrime q)
  rw [← Localization.AtPrime.eq_maximalIdeal_iff_under_eq]
  exact le_antisymm this (min.2 ⟨q.comap_isPrime _, bot_le⟩ this)

/-- The map of a ring to product of its localizations at minimal primes.

When `S` is reduced and has finitely many minimal primes, the target is actually the
total fraction ring of `S`. -/
@[expose]
def MinimalPrimes.piLocalizationMap (S : Type*) [CommRing S] :=
  (RingHom.pi (fun (p : minimalPrimes S) ↦
    letI := p.2.isPrime
    algebraMap S (Localization.AtPrime p.1)))

/-- The map of a reduced ring to product of its localizations at minimal primes is injective. -/
@[stacks 00EW "(2)"]
lemma IsReduced.piLocalizationMap_injective (S : Type*) [CommRing S] [IsReduced S] :
    Function.Injective (MinimalPrimes.piLocalizationMap S) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  apply IsReduced.eq_zero x (nilpotent_iff_mem_prime.mpr (fun q hq ↦ ?_))
  rcases Ideal.exists_minimalPrimes_le (bot_le (a := q)) with ⟨p, min, hp⟩
  let := min.isPrime
  apply hp
  rw [← IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p) p, Ideal.mem_comap]
  have : (MinimalPrimes.piLocalizationMap S) x ⟨p, min⟩ = 0 := by
    rw [hx, Pi.zero_apply]
  simp only [MinimalPrimes.piLocalizationMap, RingHom.pi_apply] at this
  simp [this]
