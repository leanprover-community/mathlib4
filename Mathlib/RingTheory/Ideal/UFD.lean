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
  apply (UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime).trans
  constructor
  · intro hufd p hp h1
    have hp_ne_bot : p ≠ ⊥ := by
      intro hp
      simp_rw [hp] at h1
      exact zero_ne_one ((Order.height_bot (PrimeSpectrum R)).symm.trans h1)
    rcases hufd p hp_ne_bot hp with ⟨x, hxmem, hxprime⟩
    have hx0 : x ≠ 0 := hxprime.ne_zero
    have hspan_prime : (Ideal.span {x}).IsPrime := (Ideal.span_singleton_prime hx0).2 hxprime
    have hspan_eq : Ideal.span {x} = p := by
      by_contra hne
      have hp_height_le : p.height ≤ 1 := by rw [Ideal.height_eq_primeHeight p, h1]
      have hspan_height_lt : (Ideal.span {x}).height < 1 :=
        (Ideal.height_le_iff.mp hp_height_le) _ hspan_prime <|
          lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem p).2 hxmem) hne
      have hspan_min : Ideal.span {x} ∈ minimalPrimes R :=
        Ideal.primeHeight_eq_zero_iff.1 <| by
          simpa [Ideal.height_eq_primeHeight (Ideal.span {x})] using
            ENat.lt_one_iff_eq_zero.mp hspan_height_lt
      rw [IsDomain.minimalPrimes_eq_singleton_bot R] at hspan_min
      have hspan_bot : Ideal.span {x} = ⊥ := Set.mem_singleton_iff.mp hspan_min
      exact hx0 ((Ideal.span_singleton_eq_bot).1 hspan_bot)
    rw [← hspan_eq]
    infer_instance
  · intro hprincipal I hI_ne_bot hI_prime
    rcases (Submodule.ne_bot_iff I).1 hI_ne_bot with ⟨x, hxI, hx0⟩
    rcases Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem I).2 hxI) with
      ⟨p, hpmin, hp_le_I⟩
    have : p.IsPrime := Ideal.minimalPrimes_isPrime hpmin
    have hp_ne_bot : p ≠ ⊥ := by
      intro hp_bot
      exact hx0 (Ideal.span_singleton_eq_bot.1 (le_antisymm (hp_bot ▸ hpmin.1.2) bot_le))
    have hp_primeHeight_le : p.primeHeight ≤ 1 := by
      simpa [Ideal.height_eq_primeHeight p] using
        Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) p hpmin
    have hp_primeHeight_ne_zero : p.primeHeight ≠ 0 := by
      intro hp_zero
      have hp_min : p ∈ minimalPrimes R := Ideal.primeHeight_eq_zero_iff.1 hp_zero
      rw [IsDomain.minimalPrimes_eq_singleton_bot R] at hp_min
      exact hp_ne_bot (Set.mem_singleton_iff.mp hp_min)
    have : p.IsPrincipal := hprincipal p <|
      le_antisymm hp_primeHeight_le (ENat.one_le_iff_ne_zero.2 hp_primeHeight_ne_zero)
    exact ⟨Submodule.IsPrincipal.generator p, hp_le_I (Submodule.IsPrincipal.generator_mem p),
      Submodule.IsPrincipal.prime_generator_of_isPrime p hp_ne_bot⟩

theorem Ideal.isPrincipal_of_isPrincipal_localization_away_of_prime
    {x : R} (hx : Prime x) {p : Ideal R} [p.IsPrime] (hxp : x ∉ p)
    (hp : (map (algebraMap R (Localization.Away x)) p).IsPrincipal) : p.IsPrincipal := by
  let M : Submonoid R := Submonoid.powers x
  have hM : M ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero
  have hd : Disjoint (M : Set R) (p : Set R) :=
    (Ideal.disjoint_powers_iff_notMem x (IsPrime.isRadical ‹_›)).mpr hxp
  have hcomap :
      comap (algebraMap R (Localization.Away x)) (map (algebraMap R (Localization.Away x)) p) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint M (Localization.Away x) ‹_› hd
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
    · rw [← hcomap, span_singleton_le_iff_mem, mem_comap]
      rw [← IsLocalization.mk'_spec (Localization.Away x) a s, hgs]
      exact Ideal.mul_mem_right _ _ (by simp [hg, mem_span_singleton_self])
    · rw [hg, submodule_span_eq, map_span, Set.image_singleton, span_singleton_eq_span_singleton]
      rw [← hgs, ← IsLocalization.mk'_spec (Localization.Away x) a s]
      exact associated_mul_unit_left _ _ (IsLocalization.map_units (Localization.Away x) s)
  have hpb : map (algebraMap R (Localization.Away x)) p ≠ ⊥ := by
    intro h
    rw [h, comap_bot_of_injective _ (IsLocalization.injective (Localization.Away x) hM)] at hcomap
    exact hpbot hcomap.symm
  have hyb : span {y} ≠ ⊥ := fun hbot ↦ hpb <| by rw [← hy, hbot, map_bot]
  have hy0 : y ≠ 0 := fun hy0 ↦ by simp [hy0] at hyb
  have hxy : ¬ x ∣ y := by
    intro hxy
    rcases hxy with ⟨b, rfl⟩
    have hsp : span {b} ∈ S := by
      refine ⟨b, p.span_singleton_le_iff_mem.2 <|
        (IsPrime.mem_or_mem ‹_› (by simpa using hyp)).resolve_left hxp, rfl, ?_⟩
      rw [map_span, Set.image_singleton, ← span_singleton_eq_span_singleton.2]
      · rw [← hy, map_span, Set.image_singleton]
      · rw [map_mul]
        exact associated_unit_mul_left _ _ (IsLocalization.Away.algebraMap_isUnit x)
    have hxb : span {x * b} ≤ span {b} :=
      span_singleton_le_span_singleton.2 ⟨x, mul_comm x b⟩
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
  · have : (Ideal.span {x}).IsPrime := (Ideal.span_singleton_prime hx.ne_zero).2 hx
    rcases lt_or_eq_of_le (p.span_singleton_le_iff_mem.mpr hxp) with lt | eq
    · absurd Ideal.primeHeight_strict_mono lt
      have htmp : (⊥ : Ideal R).primeHeight + 1 ≤ (Ideal.span {x}).primeHeight :=
        Ideal.primeHeight_add_one_le_of_lt <| by
          simpa [bot_lt_iff_ne_bot, Ideal.span_singleton_eq_bot] using hx.ne_zero
      simpa [h1, ← Ideal.height_eq_primeHeight, Ideal.height_bot] using htmp
    · exact ⟨x, eq.symm⟩
  · have hd : Disjoint (M : Set R) (p : Set R) :=
      (Ideal.disjoint_powers_iff_notMem x (Ideal.IsPrime.isRadical ‹_›)).mpr hxp
    have : (Ideal.map (algebraMap R (Localization.Away x)) p).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M (Localization.Away x) p ‹_› hd
    exact p.isPrincipal_of_isPrincipal_localization_away_of_prime hx hxp <|
      Ideal.ufd_iff_height_one_primes_principal.1 ‹_› _ <| by
        simpa [IsLocalization.comap_map_of_isPrime_disjoint M _ ‹_› hd, h1] using
          (IsLocalization.primeHeight_comap M (p.map (algebraMap R (Localization.Away x)))).symm
