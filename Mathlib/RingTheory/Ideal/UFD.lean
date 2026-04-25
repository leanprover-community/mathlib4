/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.UniqueFactorizationDomain.Localization

/-!
# UFD criteria via height `1` prime ideals and localization

## Main results
* `ufd_iff_height_one_primes_principal` : Let `R` be a Noetherian domain. Then `R` is a UFD
  if and only if every height `1` prime ideal is principal.

* `ufd_iff_ufd_localization_away_of_prime` : Let `R` be a Noetherian domain, `x ∈ R` be a prime
  element. Then `R` is a UFD if and only if `Rₓ` is a UFD.
-/

public section

variable {R : Type*} [CommRing R] [IsDomain R]

theorem Ideal.height_one_primes_principal_of_ufd [UniqueFactorizationMonoid R]
    {p : Ideal R} [p.IsPrime] (hph : p.height = 1) : p.IsPrincipal := by
  have hpn : p ≠ ⊥ := p.height_eq_zero_iff_eq_bot.not.1 (ne_zero_of_eq_one hph)
  obtain ⟨x, hxmem, hxp⟩ := IsPrime.exists_mem_prime_of_ne_bot ‹_› hpn
  exact ⟨x, p.eq_span_singleton_of_height_eq_one hph hxmem hxp⟩

theorem ufd_of_ideal_height_one_primes_principal [IsNoetherianRing R]
    (h : ∀ (p : Ideal R) [p.IsPrime] (_ : p.height = 1), p.IsPrincipal) :
    UniqueFactorizationMonoid R := by
  rw [UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime]
  intro I hIn _
  rcases I.ne_bot_iff.1 hIn with ⟨x, hxI, hx0⟩
  rcases Ideal.exists_minimalPrimes_le (I.span_singleton_le_iff_mem.2 hxI) with ⟨p, hpmin, hpl⟩
  have : p.IsPrime := Ideal.minimalPrimes_isPrime hpmin
  have hpn : p ≠ ⊥ := fun hpb ↦ hx0 <|
    Ideal.span_singleton_eq_bot.1 <| bot_unique (hpmin.1.2.trans_eq hpb)
  have hpp : p.IsPrincipal := h p <| le_antisymm
    ((Ideal.span {x}).height_le_one_of_isPrincipal_of_mem_minimalPrimes p hpmin)
      (ENat.one_le_iff_ne_zero.2 (p.height_eq_zero_iff_eq_bot.not.2 hpn))
  exact ⟨hpp.generator p, hpl (hpp.generator_mem p), hpp.prime_generator_of_isPrime p hpn⟩

/-- Let `R` be a Noetherian domain. Then `R` is a UFD if and only if every height `1` prime ideal is
  principal. -/
@[stacks 0AFT]
theorem ufd_iff_height_one_primes_principal [IsNoetherianRing R] :
    UniqueFactorizationMonoid R ↔
    ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → p.IsPrincipal :=
  ⟨fun _ p _ ↦ p.height_one_primes_principal_of_ufd, ufd_of_ideal_height_one_primes_principal⟩

theorem Ideal.isPrincipal_of_isPrincipal_isLocalization_away_of_prime
    [WfDvdMonoid R] {x : R} (hx : Prime x) {p : Ideal R} [p.IsPrime] (hxp : x ∉ p)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away x S]
    (hp : (map (algebraMap R S) p).IsPrincipal) : p.IsPrincipal := by
  let M : Submonoid R := Submonoid.powers x
  have hM : M ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero
  have hd : Disjoint (Submonoid.powers x : Set R) p := by
    rwa [← Ideal.disjoint_powers_iff_notMem_of_isPrime x] at hxp
  have : IsDomain S := IsLocalization.Away.isDomain S hx.ne_zero
  by_cases hpbot : p = ⊥
  · simpa [hpbot] using bot_isPrincipal
  · have hpb : map (algebraMap R S) p ≠ ⊥ := by
      simpa [Ideal.map_eq_bot_iff_of_injective (IsLocalization.injective S hM)] using hpbot
    obtain ⟨g, hg⟩ := hp
    have hg0 : g ≠ 0 := fun hg0 ↦ hpb <| by simpa [hg0] using hg
    obtain ⟨a, n, hxa, hag⟩ := exists_reduced_fraction' x S hg0 hx.irreducible
    have hu : IsUnit (selfZPow x S n) :=
      IsUnit.of_mul_eq_one (selfZPow x _ (- n)) (selfZPow_mul_neg x _ n)
    have : algebraMap R S a ∈ map (algebraMap R S) p := by
      rw [← Ideal.unit_mul_mem_iff_mem (map (algebraMap R S) p) hu, hag, hg]
      exact Ideal.mem_span_singleton_self g
    have haeq : map (algebraMap R S) p = map (algebraMap R _) (span {a}) := by
      simpa [hg, map_span, hag] using span_singleton_mul_left_unit hu (algebraMap R _ a)
    refine ⟨a, le_antisymm (fun z hz ↦ ?_) (p.span_singleton_le_iff_mem.2 <| by
      rwa [← IsLocalization.comap_map_of_isPrime_disjoint M S ‹_› hd])⟩
    have hzmap := mem_map_of_mem (algebraMap R S) hz
    rw [haeq, IsLocalization.algebraMap_mem_map_algebraMap_iff M] at hzmap
    rcases hzmap with ⟨s, hs, hsz⟩
    rcases (Submonoid.mem_powers_iff s x).1 hs with ⟨n, rfl⟩
    rcases mem_span_singleton.mp hsz with ⟨a, ha⟩
    rcases hx.pow_dvd_of_dvd_mul_right n hxa ⟨z, by rw [mul_comm, ← ha]⟩ with ⟨b, hb⟩
    exact mem_span_singleton.2 ⟨b, mul_left_cancel₀ (pow_ne_zero n hx.ne_zero) <| by
      simp [ha, hb, mul_assoc, mul_comm]⟩

theorem Ideal.isPrincipal_of_isPrincipal_localization_away_of_prime
    [WfDvdMonoid R] {x : R} (hx : Prime x) {p : Ideal R} [p.IsPrime] (hxp : x ∉ p)
    (hp : (map (algebraMap R (Localization.Away x)) p).IsPrincipal) : p.IsPrincipal :=
  p.isPrincipal_of_isPrincipal_isLocalization_away_of_prime hx hxp (Localization.Away x) hp

theorem ufd_iff_ufd_isLocalization_away_of_prime [IsNoetherianRing R] {x : R} (hx : Prime x)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away x S] :
    UniqueFactorizationMonoid R ↔ UniqueFactorizationMonoid S := by
  let M : Submonoid R := Submonoid.powers x
  have : IsDomain S := IsLocalization.Away.isDomain S hx.ne_zero
  have hM : M ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero
  refine ⟨fun _ ↦ isLocalization_ufd hM S, fun _ ↦ ?_⟩
  have : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers x) S inferInstance
  rw [ufd_iff_height_one_primes_principal]
  intro p hp h1
  by_cases hxp : x ∈ p
  · exact ⟨x, p.eq_span_singleton_of_height_eq_one h1 hxp hx⟩
  · have hd := by rwa [← Ideal.disjoint_powers_iff_notMem_of_isPrime x] at hxp
    have := IsLocalization.isPrime_of_isPrime_disjoint M S p hp hd
    exact p.isPrincipal_of_isPrincipal_isLocalization_away_of_prime hx hxp S <|
      ufd_iff_height_one_primes_principal.1 ‹_› _ <| by
        rw [← IsLocalization.height_comap M (Ideal.map (algebraMap R S) p)]
        simp_rw [IsLocalization.comap_map_of_isPrime_disjoint M S hp hd, h1]

/-- Let `R` be a Noetherian domain, `x ∈ R` be a prime element. Then `R` is a UFD if and only if
  `Rₓ` is a UFD. -/
theorem ufd_iff_ufd_localization_away_of_prime [IsNoetherianRing R] {x : R} (hx : Prime x) :
    UniqueFactorizationMonoid R ↔ UniqueFactorizationMonoid (Localization.Away x) :=
  ufd_iff_ufd_isLocalization_away_of_prime hx (Localization.Away x)
