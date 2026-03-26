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

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsDomain R]

/-- Let `R` be a Noetherian domain. Then `R` is a UFD if and only if every height `1` prime ideal is
  principal. -/
@[stacks 0AFT]
theorem Ideal.ufd_iff_height_one_primes_principal :
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
      hx0 (Ideal.span_singleton_eq_bot.1 (le_antisymm (hp_bot ▸ hpmin.1.2) bot_le))
    have hpp : p.IsPrincipal := h p <| by
      refine le_antisymm ?_ <| ENat.one_le_iff_ne_zero.2 <|
        p.primeHeight_eq_zero_iff_eq_bot.not.2 hpn
      exact p.height_eq_primeHeight.symm.trans_le <|
        Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) p hpmin
    exact ⟨hpp.generator p, hpl (hpp.generator_mem p), hpp.prime_generator_of_isPrime p hpn⟩

theorem Ideal.isPrincipal_of_isPrincipal_localization_away_of_prime
    {x : R} (hx : Prime x) {p : Ideal R} [p.IsPrime] (hxp : x ∉ p)
    (hp : (map (algebraMap R (Localization.Away x)) p).IsPrincipal) : p.IsPrincipal := by
  let M : Submonoid R := Submonoid.powers x
  have hM : M ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero
  have hd := (Ideal.disjoint_powers_iff_notMem x (IsPrime.isRadical ‹_›)).mpr hxp
  have : IsDomain (Localization.Away x) := Localization.Away.isDomain hx.ne_zero
  by_cases hpbot : p = ⊥
  · simpa [hpbot] using bot_isPrincipal
  let S : Set (Ideal R) := {I | ∃ y : R, span {y} ≤ p ∧ I = span {y} ∧
    map (algebraMap R (Localization.Away x)) (span {y}) = map (algebraMap R _) p}
  obtain ⟨I, ⟨y, hyp, rfl, hy⟩, hImax⟩ : ∃ I ∈ S, ∀ J ∈ S, ¬ I < J := by
    refine IsWellFounded.wf.has_min S ?_
    obtain ⟨g, hg⟩ := hp
    obtain ⟨a, s, hgs⟩ := IsLocalization.exists_mk'_eq M g
    refine ⟨span {a}, a, ?_, rfl, ?_⟩
    · rw [← IsLocalization.comap_map_of_isPrime_disjoint M (Localization.Away x) ‹_› hd]
      rw [span_singleton_le_iff_mem, mem_comap, ← IsLocalization.mk'_spec _ a s, hgs]
      exact Ideal.mul_mem_right _ _ (by simp [hg, mem_span_singleton_self])
    · rw [hg, submodule_span_eq, map_span, Set.image_singleton, span_singleton_eq_span_singleton]
      rw [← hgs, ← IsLocalization.mk'_spec (Localization.Away x) a s]
      exact associated_mul_unit_left _ _ (IsLocalization.map_units (Localization.Away x) s)
  have hpb : map (algebraMap R (Localization.Away x)) p ≠ ⊥ := by
    simpa [Ideal.map_eq_bot_iff_of_injective (IsLocalization.injective _ hM)] using hpbot
  have hyb : span {y} ≠ ⊥ := fun hbot ↦ hpb <| by rw [← hy, hbot, map_bot]
  have hy0 : y ≠ 0 := fun hy0 ↦ by simp [hy0] at hyb
  have hxy : ¬ x ∣ y := by
    rintro ⟨b, rfl⟩
    have hsp : span {b} ∈ S := by
      refine ⟨b, p.span_singleton_le_iff_mem.2 <|
        (IsPrime.mem_or_mem ‹_› (by simpa using hyp)).resolve_left hxp, rfl, ?_⟩
      rw [map_span, Set.image_singleton, ← span_singleton_eq_span_singleton.2]
      · rw [← hy, map_span, Set.image_singleton]
      · rw [map_mul]
        exact associated_unit_mul_left _ _ (IsLocalization.Away.algebraMap_isUnit x)
    have hxb : span {x * b} ≤ span {b} := span_singleton_le_span_singleton.2 ⟨x, mul_comm x b⟩
    have hb0 : b ≠ 0 := fun hb0 ↦ hy0 <| by simp [hb0]
    exact hImax (span {b}) hsp <| lt_of_le_of_ne hxb <| by
      intro hEq
      have hb : b ∈ span {x * b} := by simpa only [hEq] using subset_span (by simp)
      rcases mem_span_singleton.mp hb with ⟨c, hc⟩
      exact hx.not_unit <| IsUnit.of_mul_eq_one c <| mul_right_cancel₀ hb0
        (by simpa [mul_assoc, mul_left_comm, mul_comm] using hc.symm)
  refine ⟨y, le_antisymm (fun z hz ↦ ?_) hyp⟩
  have hzmap := mem_map_of_mem (algebraMap R (Localization.Away x)) hz
  rw [← hy, IsLocalization.algebraMap_mem_map_algebraMap_iff M] at hzmap
  rcases hzmap with ⟨s, hs, hsz⟩
  rcases (Submonoid.mem_powers_iff s x).1 hs with ⟨n, rfl⟩
  clear hs
  induction n with
  | zero => simpa using hsz
  | succ n ih =>
      have hxn : x * (x ^ n * z) ∈ span {y} := by simpa [pow_succ', mul_assoc] using hsz
      rcases mem_span_singleton.mp hxn with ⟨a, ha⟩
      rcases (hx.2.2 y a ⟨x ^ n * z, ha.symm⟩).resolve_left hxy with ⟨b, hb⟩
      exact ih <| by simpa only [mem_span_singleton] using ⟨b, mul_left_cancel₀ hx.ne_zero <| by
        simpa [hb, mul_assoc, mul_left_comm, mul_comm] using ha⟩

/-- Let `R` be a Noetherian domain, `x ∈ R` be a prime element. If `Rₓ` is a UFD,
  then `R` is also a UFD. -/
theorem ufd_of_ufd_localization_away_of_prime {x : R} (hx : Prime x)
    [UniqueFactorizationMonoid (Localization.Away x)] : UniqueFactorizationMonoid R := by
  let M : Submonoid R := Submonoid.powers x
  have : IsDomain (Localization.Away x) := Localization.Away.isDomain hx.ne_zero
  rw [Ideal.ufd_iff_height_one_primes_principal]
  intro p hp h1
  by_cases hxp : x ∈ p
  · exact ⟨x, p.eq_span_singleton_of_primeHeight_eq_one h1 hxp hx⟩
  · have hd := (Ideal.disjoint_powers_iff_notMem x (Ideal.IsPrime.isRadical hp)).mpr hxp
    have : (Ideal.map (algebraMap R (Localization.Away x)) p).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M (Localization.Away x) p ‹_› hd
    exact p.isPrincipal_of_isPrincipal_localization_away_of_prime hx hxp <|
      Ideal.ufd_iff_height_one_primes_principal.1 ‹_› _ <| by
        rw [← IsLocalization.primeHeight_comap M (Ideal.map (algebraMap R (Localization.Away x)) p)]
        simp_rw [IsLocalization.comap_map_of_isPrime_disjoint M (Localization.Away x) ‹_› hd, h1]
