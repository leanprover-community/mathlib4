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
    {x : R} (hx : Prime x) {p : Ideal R} [p.IsPrime] (hpx : x ∉ p)
    (hprincipal : (map (algebraMap R (Localization.Away x)) p).IsPrincipal) : p.IsPrincipal := by
  let M : Submonoid R := Submonoid.powers x
  have hM : Submonoid.powers x ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero
  have : IsDomain (Localization.Away x) := by
    simpa using IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away x) hM
  by_cases hpbot : p = ⊥
  · simpa [hpbot] using (inferInstance : (⊥ : Ideal R).IsPrincipal)
  let S : Set (Ideal R) := {I | I ≤ p ∧ I.IsPrincipal ∧
    map (algebraMap R (Localization.Away x)) I = map (algebraMap R (Localization.Away x)) p}
  have hSnonempty : S.Nonempty := by
    have hex : ∃ y : R, y ∈ p ∧ map (algebraMap R (Localization.Away x)) p =
        span {algebraMap R (Localization.Away x) y} := by
      let J : Ideal (Localization.Away x) := map (algebraMap R (Localization.Away x)) p
      let g : Localization.Away x := Submodule.IsPrincipal.generator J
      obtain ⟨a, s, hgs⟩ := IsLocalization.exists_mk'_eq M g
      have hgJ : g ∈ J := Submodule.IsPrincipal.generator_mem J
      rw [← hgs, IsLocalization.mk'_mem_map_algebraMap_iff M] at hgJ
      rcases hgJ with ⟨t, ht, hat⟩
      refine ⟨t * a, hat, show J = span {algebraMap R (Localization.Away x) (t * a)} from ?_⟩
      rw [← span_singleton_generator J]
      have hg_eq :
          g * (algebraMap R (Localization.Away x) s) = algebraMap R (Localization.Away x) a := by
        simpa [hgs] using (IsLocalization.mk'_spec (Localization.Away x) a s)
      have hy_eq : algebraMap R (Localization.Away x) (t * a) = Submodule.IsPrincipal.generator J *
          ((algebraMap R (Localization.Away x) t) * (algebraMap R (Localization.Away x) s)) := by
        rw [map_mul]
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          congrArg ((algebraMap R (Localization.Away x) t) * ·) hg_eq.symm
      refine span_singleton_eq_span_singleton.2 <| associated_of_dvd_dvd
        ⟨(algebraMap R (Localization.Away x) t) * (algebraMap R (Localization.Away x) s), hy_eq⟩ ?_
      rcases (IsLocalization.map_units (Localization.Away x) ⟨t, ht⟩).mul
        (IsLocalization.map_units (Localization.Away x) s) with ⟨u, hu⟩
      exact ⟨u⁻¹.1, by simp [hy_eq, ← hu, mul_assoc]⟩
    rcases hex with ⟨y, hyp, hy⟩
    refine ⟨span {y}, ⟨(span_singleton_le_iff_mem p).2 hyp, inferInstance, ?_⟩⟩
    rw [map_span, Set.image_singleton, hy]
  obtain ⟨I, hIS, hImax⟩ : ∃ I ∈ S, ∀ J ∈ S, ¬ I < J := IsWellFounded.wf.has_min S hSnonempty
  have hIprincipal : I.IsPrincipal := hIS.2.1
  let y : R := Submodule.IsPrincipal.generator I
  have hy_mem_p : y ∈ p := hIS.1 (Submodule.IsPrincipal.generator_mem I)
  have hIspan : span {y} = I := span_singleton_generator I
  have hcomap :
      comap (algebraMap R (Localization.Away x)) (map (algebraMap R (Localization.Away x)) p) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint M (Localization.Away x) inferInstance <| by
      rw [Set.disjoint_left]
      intro s hs hs'
      rcases (Submonoid.mem_powers_iff s x).1 hs with ⟨n, rfl⟩
      exact hpx (IsPrime.mem_of_pow_mem inferInstance n hs')
  have hJ_ne_bot : map (algebraMap R (Localization.Away x)) p ≠ ⊥ :=
    have hcbot : comap (algebraMap R (Localization.Away x)) ⊥ = ⊥ := by
      ext a
      change ((algebraMap R (Localization.Away x)) a = 0) ↔ a = 0
      constructor
      · exact (injective_iff_map_eq_zero (algebraMap R (Localization.Away x))).1
          (IsLocalization.injective (Localization.Away x) hM) a
      · intro ha
        simp [ha]
    fun hbot => hpbot (by simpa [hbot, hcbot] using hcomap.symm)
  have hI_ne_bot : I ≠ ⊥ := fun hbot => hJ_ne_bot <| by rw [← hIS.2.2, hbot, map_bot]
  have hy_ne_zero : y ≠ 0 :=
    fun hy0 => hI_ne_bot <| (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero I).2 hy0
  have hy_not_dvd : ¬ x ∣ y := by
    intro hxy
    rcases hxy with ⟨b, hb⟩
    have hspanb_mem : span {b} ∈ S := by
      refine ⟨(span_singleton_le_iff_mem p).2 <| IsPrime.mem_or_mem inferInstance
        (by simpa [hb] using hy_mem_p) |>.resolve_left hpx, inferInstance, ?_⟩
      have hassoc : Associated (algebraMap R (Localization.Away x) (x * b))
          (algebraMap R (Localization.Away x) b) := by
        apply associated_of_dvd_dvd
        · rcases IsLocalization.map_units (Localization.Away x)
            ⟨x, by exact (Submonoid.mem_powers_iff x x).2 ⟨1, by simp⟩⟩ with ⟨u, hu⟩
          exact ⟨u⁻¹.1, by simp [← hu, mul_left_comm, mul_comm]⟩
        · exact ⟨algebraMap R (Localization.Away x) x, by rw [map_mul, mul_comm]⟩
      rw [map_span, Set.image_singleton, ← span_singleton_eq_span_singleton.2 hassoc]
      rw [← hIS.2.2, ← hIspan, hb, map_span, Set.image_singleton]
    have hI_le_spanb : I ≤ span {b} := by
      simpa [← hIspan, hb] using (span_singleton_le_span_singleton).2 ⟨x, by rw [mul_comm]⟩
    have hb_ne_zero : b ≠ 0 := fun hb0 => hy_ne_zero <| by simp [hb, hb0]
    have hI_ne_spanb : I ≠ span {b} := by
      intro hEq
      have hb_mem_I : b ∈ I := by
        rw [hEq]
        exact subset_span (by simp)
      rw [← hIspan, mem_span_singleton] at hb_mem_I
      rcases hb_mem_I with ⟨c, hc⟩
      have hc' : (x * b) * c = b := by simpa [hb, mul_assoc] using hc.symm
      exact hx.not_unit <| IsUnit.of_mul_eq_one c <| mul_right_cancel₀ hb_ne_zero
        (by simpa [one_mul, mul_assoc, mul_left_comm, mul_comm] using hc')
    exact hImax (span {b}) hspanb_mem (lt_of_le_of_ne hI_le_spanb hI_ne_spanb)
  refine ⟨y, ?_⟩
  change p = span _
  rw [hIspan]
  apply le_antisymm
  · intro z hz
    have hzmap :
        algebraMap R (Localization.Away x) z ∈ map (algebraMap R (Localization.Away x)) I := by
      rw [hIS.2.2]
      exact mem_map_of_mem _ hz
    rw [IsLocalization.algebraMap_mem_map_algebraMap_iff M] at hzmap
    rcases hzmap with ⟨s, hs, hsz⟩
    rcases (Submonoid.mem_powers_iff s x).1 hs with ⟨n, rfl⟩
    clear hs
    induction n with
    | zero =>
        simpa using hsz
    | succ n ih =>
        have hxz_mem : x * (x ^ n * z) ∈ I := by simpa [pow_succ', mul_assoc] using hsz
        rw [← hIspan, mem_span_singleton] at hxz_mem
        rcases hxz_mem with ⟨a, ha⟩
        rcases (hx.2.2 y a ⟨x ^ n * z, ha.symm⟩).resolve_left hy_not_dvd with ⟨b, hb⟩
        apply ih
        rw [← hIspan, mem_span_singleton]
        exact ⟨b, mul_left_cancel₀ hx.ne_zero <| by
          simpa [hb, mul_assoc, mul_left_comm, mul_comm] using ha⟩
  · exact hIS.1

/-- Let `R` be a Noetherian domain, `x ∈ R` be a prime element. If `Rₓ` is a UFD,
  then `R` is also a UFD. -/
theorem ufd_of_ufd_localization_away_of_prime {x : R} (hx : Prime x)
    [UniqueFactorizationMonoid (Localization.Away x)] : UniqueFactorizationMonoid R := by
  let M : Submonoid R := Submonoid.powers x
  have hM : M ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hx.ne_zero
  have : IsDomain (Localization.Away x) := by
    simpa [M] using IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away x) hM
  rw [Ideal.ufd_iff_height_one_primes_principal]
  intro p hp h1
  by_cases hxp : x ∈ p
  · let q : Ideal R := Ideal.span {x}
    have hqprime : q.IsPrime := (Ideal.span_singleton_prime hx.ne_zero).2 hx
    by_cases hqp : q = p
    · rw [← hqp]
      infer_instance
    · have hq_ge_one : (1 : ℕ∞) ≤ q.primeHeight := by
        have htmp : (⊥ : Ideal R).primeHeight + 1 ≤ q.primeHeight :=
          Ideal.primeHeight_add_one_le_of_lt <| bot_lt_iff_ne_bot.mpr <| by
            simpa [q, Ideal.span_singleton_eq_bot] using hx.ne_zero
        rwa [← Ideal.height_eq_primeHeight, Ideal.height_bot] at htmp
      have htwo : (2 : ℕ∞) ≤ p.primeHeight := by
        calc _ = (1 : ℕ∞) + 1 := by norm_num
          _ ≤ q.primeHeight + 1 := by simpa [add_comm] using add_le_add_right hq_ge_one 1
          _ ≤ p.primeHeight := Ideal.primeHeight_add_one_le_of_lt
            (lt_of_le_of_ne ((Ideal.span_singleton_le_iff_mem p).2 hxp) hqp)
      have htwo : (2 : WithTop ℕ) ≤ 1 := by rwa [h1] at htwo
      exfalso
      norm_num at htwo
  · have hd : Disjoint (M : Set R) (p : Set R) := by
      rw [Set.disjoint_left]
      intro s hs hs'
      rcases (Submonoid.mem_powers_iff s x).1 hs with ⟨n, rfl⟩
      exact hxp (Ideal.IsPrime.mem_of_pow_mem inferInstance n hs')
    have : (Ideal.map (algebraMap R (Localization.Away x)) p).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint M (Localization.Away x) p inferInstance hd
    exact p.isPrincipal_of_isPrincipal_localization_away_of_prime hx hxp <|
      Ideal.ufd_iff_height_one_primes_principal.1 inferInstance
        (p.map (algebraMap R (Localization.Away x))) <| by
          simpa [IsLocalization.comap_map_of_isPrime_disjoint M (Localization.Away x)
            inferInstance hd, h1] using
              (IsLocalization.primeHeight_comap M (p.map (algebraMap R (Localization.Away x)))).symm
