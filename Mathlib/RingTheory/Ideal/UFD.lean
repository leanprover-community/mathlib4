/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky

/-!
# UFD criteria via height `1` prime ideals and localization

## Main results
* `UniqueFactorizationMonoid.iff_forall_isPrincipal_of_height_eq_one` : Let `R` be a
  Noetherian domain. Then `R` is a UFD if and only if every height `1` prime ideal is principal.

* `UniqueFactorizationMonoid.iff_localizationAway_of_prime` : Let `R` be a Noetherian domain,
  `x ∈ R` be a prime element. Then `R` is a UFD if and only if `Rₓ` is a UFD.
-/

public section

variable {R : Type*} [CommRing R] [IsDomain R]

namespace Ideal

variable [WfDvdMonoid R] {x : R} (hx : Prime x) {p : Ideal R} [p.IsPrime] (hxp : x ∉ p)

include hx hxp

theorem isPrincipal_of_isPrincipal_isLocalizationAway_of_prime
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away x S]
    (hp : (map (algebraMap R S) p).IsPrincipal) : p.IsPrincipal := by
  have := (disjoint_powers_iff_notMem_of_isPrime x).mpr hxp
  by_cases hpbot : p = ⊥
  · simp [hpbot, bot_isPrincipal]
  · have hi := IsLocalization.injective S (powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero)
    have hpb : map (algebraMap R S) p ≠ ⊥ := by simp [Ideal.map_eq_bot_iff_of_injective hi, hpbot]
    obtain ⟨g, hg⟩ := hp
    have hg0 : g ≠ 0 := fun hg0 ↦ hpb <| by simp [hg0, hg]
    obtain ⟨a, n, hxa, hag⟩ := exists_reduced_fraction' x S hg0 hx.irreducible
    have hu : IsUnit (selfZPow x S n) :=
      IsUnit.of_mul_eq_one (selfZPow x S (- n)) (selfZPow_mul_neg x S n)
    refine ⟨a, Ideal.eq_of_map_algebraMap_le S x ?_ (by simp [IsPrime.mul_mem_left_iff hxp]) ?_⟩
    · simp [hg, map_span, ← span_singleton_mul_left_unit hu (algebraMap R S a), hag]
    · intro y hy
      rw [mem_span_singleton] at hy ⊢
      exact (hx.left_dvd_or_dvd_right_of_dvd_mul hy).resolve_left hxa

theorem isPrincipal_of_isPrincipal_localizationAway_of_prime
    (hp : (map (algebraMap R (Localization.Away x)) p).IsPrincipal) : p.IsPrincipal :=
  p.isPrincipal_of_isPrincipal_isLocalizationAway_of_prime hx hxp (Localization.Away x) hp

end Ideal

namespace UniqueFactorizationMonoid

theorem isPrincipal_of_height_eq_one [UniqueFactorizationMonoid R]
    {p : Ideal R} [p.IsPrime] (hph : p.height = 1) : p.IsPrincipal := by
  have hpn : p ≠ ⊥ := p.ne_bot_of_height_eq_one hph
  obtain ⟨x, hxmem, hxp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹_› hpn
  exact ⟨x, p.eq_span_singleton_of_height_eq_one hph hxmem hxp⟩

variable [IsNoetherianRing R]

theorem of_forall_isPrincipal_of_height_eq_one
    (h : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → p.IsPrincipal) :
    UniqueFactorizationMonoid R := by
  rw [iff_exists_prime_mem_of_isPrime]
  intro I hIn _
  rcases I.ne_bot_iff.mp hIn with ⟨x, hxI, hx0⟩
  rcases Ideal.exists_minimalPrimes_le (I.span_singleton_le_iff_mem.mpr hxI) with ⟨p, hpmin, hpl⟩
  have : p.IsPrime := hpmin.isPrime
  have hpn : p ≠ ⊥ := fun hpb ↦ hx0 <|
    Ideal.span_singleton_eq_bot.mp <| bot_unique (hpmin.le.trans_eq hpb)
  have hpp : p.IsPrincipal := h p <| le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hpmin)
      (by simpa [Order.one_le_iff_ne_zero])
  exact ⟨hpp.generator p, hpl (hpp.generator_mem p), hpp.prime_generator_of_isPrime p hpn⟩

/-- Let `R` be a Noetherian domain. Then `R` is a UFD if and only if every height `1` prime ideal is
  principal. -/
@[stacks 0AFT]
theorem iff_forall_isPrincipal_of_height_eq_one :
    UniqueFactorizationMonoid R ↔ ∀ (p : Ideal R) [p.IsPrime], p.height = 1 → p.IsPrincipal :=
  ⟨fun _ _ _ ↦ isPrincipal_of_height_eq_one, of_forall_isPrincipal_of_height_eq_one⟩

theorem iff_of_isLocalizationAway_of_prime {x : R} (hx : Prime x)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away x S] :
    UniqueFactorizationMonoid R ↔ UniqueFactorizationMonoid S := by
  have : IsDomain S := IsLocalization.Away.isDomain S hx.ne_zero
  refine ⟨fun _ ↦ of_isLocalization (Submonoid.powers x) S, fun _ ↦ ?_⟩
  rw [iff_forall_isPrincipal_of_height_eq_one]
  intro p hp h1
  by_cases hxp : x ∈ p
  · exact ⟨x, p.eq_span_singleton_of_height_eq_one h1 hxp hx⟩
  · have hd := by rwa [← Ideal.disjoint_powers_iff_notMem_of_isPrime x] at hxp
    have := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x) S p hp hd
    refine p.isPrincipal_of_isPrincipal_isLocalizationAway_of_prime hx hxp S
      (isPrincipal_of_height_eq_one ?_)
    rw [← IsLocalization.height_under (Submonoid.powers x),
      IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers x) S hp hd, h1]

/-- Let `R` be a Noetherian domain, `x ∈ R` be a prime element. Then `R` is a UFD if and only if
  `Rₓ` is a UFD. -/
theorem iff_localizationAway_of_prime {x : R} (hx : Prime x) :
    UniqueFactorizationMonoid R ↔ UniqueFactorizationMonoid (Localization.Away x) :=
  iff_of_isLocalizationAway_of_prime hx (Localization.Away x)

end UniqueFactorizationMonoid
