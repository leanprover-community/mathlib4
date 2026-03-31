/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

/-!
# UFD criteria via height `1` prime ideals and localization

## Main results
* `Ideal.ufd_iff_height_one_primes_principal` : Let `R` be a Noetherian domain. Then `R` is a UFD
  if and only if every height `1` prime ideal is principal.

* `ufd_of_ufd_localization_away_of_prime` : Let `R` be a Noetherian domain, `x ∈ R` be a prime
  element. If `Rₓ` is a UFD, then `R` is also a UFD.
-/

public section

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Let `R` be a Noetherian domain. Then `R` is a UFD if and only if every height `1` prime ideal is
  principal. -/
@[stacks 0AFT]
theorem Ideal.ufd_iff_height_one_primes_principal [IsNoetherianRing R] :
    UniqueFactorizationMonoid R ↔
    ∀ (p : Ideal R) [p.IsPrime], p.primeHeight = 1 → p.IsPrincipal := by
  apply UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.trans
  constructor
  · intro h p hp h1
    have hpn : p ≠ ⊥ := p.primeHeight_eq_zero_iff_eq_bot.not.1 (ne_zero_of_eq_one h1)
    rcases h p hpn hp with ⟨x, hxmem, hxp⟩
    exact ⟨x, p.eq_span_singleton_of_primeHeight_eq_one h1 hxmem hxp⟩
  · intro h I hIn _
    rcases I.ne_bot_iff.1 hIn with ⟨x, hxI, hx0⟩
    rcases Ideal.exists_minimalPrimes_le (I.span_singleton_le_iff_mem.2 hxI) with ⟨p, hpmin, hpl⟩
    have : p.IsPrime := Ideal.minimalPrimes_isPrime hpmin
    have hpn : p ≠ ⊥ := fun hp_bot ↦
      hx0 <| Ideal.span_singleton_eq_bot.1 <| le_antisymm (hp_bot ▸ hpmin.1.2) bot_le
    have hpp : p.IsPrincipal := h p <| by
      refine le_antisymm ?_ (ENat.one_le_iff_ne_zero.2 (p.primeHeight_eq_zero_iff_eq_bot.not.2 hpn))
      exact p.height_eq_primeHeight.symm.trans_le <|
        Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) p hpmin
    exact ⟨hpp.generator p, hpl (hpp.generator_mem p), hpp.prime_generator_of_isPrime p hpn⟩

theorem Ideal.isPrincipal_of_isPrincipal_localization_away_of_prime
    [WfDvdMonoid R] {x : R} (hx : Prime x) {p : Ideal R} [p.IsPrime] (hxp : x ∉ p)
    (hp : (map (algebraMap R (Localization.Away x)) p).IsPrincipal) : p.IsPrincipal := by
  let M : Submonoid R := Submonoid.powers x
  have hM : M ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero
  have hd := (Ideal.disjoint_powers_iff_notMem x (IsPrime.isRadical ‹_›)).mpr hxp
  have : IsDomain (Localization.Away x) := Localization.Away.isDomain hx.ne_zero
  by_cases hpbot : p = ⊥
  · simpa [hpbot] using bot_isPrincipal
  · have hpb : map (algebraMap R (Localization.Away x)) p ≠ ⊥ := by
      simpa [Ideal.map_eq_bot_iff_of_injective (IsLocalization.injective _ hM)] using hpbot
    obtain ⟨g, hg⟩ := hp
    have hg0 : g ≠ 0 := fun hg0 ↦ hpb <| by simpa [hg0] using hg
    obtain ⟨a, n, hxa, hag⟩ := exists_reduced_fraction' x (Localization.Away x) hg0 hx.irreducible
    have hu : IsUnit (selfZPow x (Localization.Away x) n) :=
      IsUnit.of_mul_eq_one (selfZPow x _ (- n)) (selfZPow_mul_neg x _ n)
    have : algebraMap R (Localization.Away x) a ∈ map (algebraMap R (Localization.Away x)) p := by
      rw [← Ideal.unit_mul_mem_iff_mem (map (algebraMap R (Localization.Away x)) p) hu, hag, hg]
      exact Ideal.mem_span_singleton_self g
    have haeq : map (algebraMap R (Localization.Away x)) p = map (algebraMap R _) (span {a}) := by
      simpa [hg, map_span, hag] using span_singleton_mul_left_unit hu (algebraMap R _ a)
    refine ⟨a, le_antisymm (fun z hz ↦ ?_) (p.span_singleton_le_iff_mem.2 <| by
      rwa [← IsLocalization.comap_map_of_isPrime_disjoint M (Localization.Away x) ‹_› hd])⟩
    have hzmap := mem_map_of_mem (algebraMap R (Localization.Away x)) hz
    rw [haeq, IsLocalization.algebraMap_mem_map_algebraMap_iff M] at hzmap
    rcases hzmap with ⟨s, hs, hsz⟩
    rcases (Submonoid.mem_powers_iff s x).1 hs with ⟨n, rfl⟩
    rcases mem_span_singleton.mp hsz with ⟨a, ha⟩
    rcases hx.pow_dvd_of_dvd_mul_right n hxa ⟨z, by rw [mul_comm, ← ha]⟩ with ⟨b, hb⟩
    exact mem_span_singleton.2 ⟨b, mul_left_cancel₀ (pow_ne_zero n hx.ne_zero) <| by
      simp [ha, hb, mul_assoc, mul_comm]⟩

/-- Let `R` be a Noetherian domain, `x ∈ R` be a prime element. If `Rₓ` is a UFD,
  then `R` is also a UFD. -/
theorem ufd_of_ufd_localization_away_of_prime [IsNoetherianRing R] {x : R} (hx : Prime x)
    [UniqueFactorizationMonoid (Localization.Away x)] : UniqueFactorizationMonoid R := by
  let M : Submonoid R := Submonoid.powers x
  have : IsDomain (Localization.Away x) := Localization.Away.isDomain hx.ne_zero
  rw [Ideal.ufd_iff_height_one_primes_principal]
  intro p hp h1
  by_cases hxp : x ∈ p
  · exact ⟨x, p.eq_span_singleton_of_primeHeight_eq_one h1 hxp hx⟩
  · have hd := (Ideal.disjoint_powers_iff_notMem x (Ideal.IsPrime.isRadical hp)).mpr hxp
    have := IsLocalization.isPrime_of_isPrime_disjoint M (Localization.Away x) p hp hd
    exact p.isPrincipal_of_isPrincipal_localization_away_of_prime hx hxp <|
      Ideal.ufd_iff_height_one_primes_principal.1 ‹_› _ <| by
        rw [← IsLocalization.primeHeight_comap M (Ideal.map (algebraMap R (Localization.Away x)) p)]
        simp_rw [IsLocalization.comap_map_of_isPrime_disjoint M (Localization.Away x) hp hd, h1]
