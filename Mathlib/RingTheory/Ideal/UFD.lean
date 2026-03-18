/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

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
  constructor
  · intro h p hp h1
    have hpb : p ≠ ⊥ := by
      intro hp
      simp_rw [hp] at h1
      have h : Order.height (⊥ : PrimeSpectrum R) = 1 := h1
      simp at h
    rcases (Submodule.ne_bot_iff p).mp hpb with ⟨x, hxp, hx⟩
    rcases UniqueFactorizationMonoid.exists_prime_factors x hx with ⟨s, hps, hxs⟩
    have hsprod_mem : s.prod ∈ p := by
      rcases Associated.dvd hxs.symm with ⟨b, hb⟩
      rw [hb]
      exact mul_mem_right b p hxp
    obtain ⟨a, ha, hap⟩ : ∃ a ∈ s, a ∈ p :=
      (IsPrime.multiset_prod_mem_iff_exists_mem hp s).1 hsprod_mem
    have hsap : (span {a}).IsPrime :=
      (span_singleton_prime (Prime.ne_zero (hps a ha))).mpr (hps a ha)
    by_cases hpa : p = span {a}
    · simpa [hpa] using ⟨a, rfl⟩
    let l1 : LTSeries (PrimeSpectrum R) := by
      refine (RelSeries.singleton _ (⊥ : PrimeSpectrum R)).append
        (RelSeries.singleton _ ⟨span {a}, hsap⟩) ?_
      simp only [RelSeries.last_singleton, RelSeries.head_singleton, Set.mem_setOf_eq]
      refine (PrimeSpectrum.asIdeal_lt_asIdeal ⊥ ⟨span {a}, hsap⟩).mp ?_
      simpa [bot_lt_iff_ne_bot] using Prime.ne_zero (hps a ha)
    let l : LTSeries (PrimeSpectrum R) := by
      refine l1.append (RelSeries.singleton _ ⟨p, hp⟩) ?_
      simpa using (PrimeSpectrum.asIdeal_lt_asIdeal ⟨span {a}, hsap⟩ ⟨p, hp⟩).mp <|
        lt_of_le_of_ne ((span_singleton_le_iff_mem p).mpr hap) fun eq => hpa eq.symm
    have h2 : 2 ≤ p.primeHeight := by simpa using by exact le_sSup ⟨l, by simp [l, l1]⟩
    rw [h1] at h2
    exfalso
    have h2' : (2 : WithTop ℕ) ≤ 1 := h2
    norm_num at h2'
  · intro hPrincipal
    refine UniqueFactorizationMonoid.mk ?_
    intro q
    constructor
    · intro hqirr
      have hq0 : q ≠ 0 := Irreducible.ne_zero hqirr
      have hspan_ne_top : (span {q}) ≠ ⊤ :=
        fun htop => hqirr.not_isUnit ((span_singleton_eq_top).1 htop)
      rcases exists_le_maximal (span {q}) hspan_ne_top with ⟨M, _, hspan_le_M⟩
      rcases exists_minimalPrimes_le hspan_le_M with ⟨p, hpmin, _⟩
      have hpp : p.IsPrime := minimalPrimes_isPrime hpmin
      have hq_mem_p : q ∈ p := hpmin.1.2 (subset_span (by simp))
      have hp_ne_bot : p ≠ ⊥ := fun hpbot => hq0 (by simpa [hpbot] using hq_mem_p)
      have hp_not_min : p ∉ minimalPrimes R := by
        intro hpminR
        rw [IsDomain.minimalPrimes_eq_singleton_bot R] at hpminR
        exact hp_ne_bot (by simpa using hpminR)
      have hp_height_ne_zero : p.primeHeight ≠ 0 :=
        fun hp0 => hp_not_min (p.primeHeight_eq_zero_iff.1 hp0)
      have hp_height_le_one : p.primeHeight ≤ 1 := by
        simpa [p.height_eq_primeHeight] using
          height_le_one_of_isPrincipal_of_mem_minimalPrimes (span {q}) p hpmin
      have hp_height_eq_one : p.primeHeight = 1 := by
        rcases ENat.ne_top_iff_exists.mp (primeHeight_ne_top p) with ⟨n, hn⟩
        rw [← hn] at hp_height_le_one hp_height_ne_zero ⊢
        have hn_le : n ≤ 1 := by
          simpa using (show (n : WithTop ℕ) ≤ 1 from hp_height_le_one)
        interval_cases n <;> simp at *
      have : p.IsPrincipal := hPrincipal p hp_height_eq_one
      let g : R := Submodule.IsPrincipal.generator p
      have hp_span : span {g} = p := by simp [g]
      have hq_mem_span_g : q ∈ span {g} := by simpa [g] using hq_mem_p
      rcases (mem_span_singleton.mp hq_mem_span_g) with ⟨a, hqa⟩
      have hg_ne_zero : g ≠ 0 := fun hg0 => hp_ne_bot <| by simpa [← hp_span, span_singleton_eq_bot]
      have hg_irr : Irreducible g := Prime.irreducible <|
        (span_singleton_prime hg_ne_zero).1 (by simpa [g] using hpp)
      have hassoc : Associated g q := Irreducible.associated_of_dvd hg_irr hqirr ⟨a, hqa⟩
      exact (span_singleton_prime hq0).1 <| by
        simpa [(span_singleton_eq_span_singleton).2 hassoc |>.symm.trans hp_span] using hpp
    · exact Prime.irreducible

theorem Ideal.isPrincipal_of_isPrincipal_localization_away_of_prime
    {x : R} (hx : Prime x) {p : Ideal R} [p.IsPrime] (hpx : x ∉ p)
    (hprincipal : (map (algebraMap R (Localization.Away x)) p).IsPrincipal) :
    p.IsPrincipal := by
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
  have hM : M ≤ nonZeroDivisors R := by
    refine Submonoid.powers_le.2 ?_
    rw [mem_nonZeroDivisors_iff]
    constructor <;> intro a ha
    · exact mul_eq_zero.mp ha |>.resolve_left hx.ne_zero
    · exact mul_eq_zero.mp ha |>.resolve_right hx.ne_zero
  have : IsDomain (Localization.Away x) := by
    simpa [M] using IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away x) hM
  rw [Ideal.ufd_iff_height_one_primes_principal]
  intro p hp hheight
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
      have htwo : (2 : WithTop ℕ) ≤ 1 := by rwa [hheight] at htwo
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
            inferInstance hd, hheight] using
              (IsLocalization.primeHeight_comap M (p.map (algebraMap R (Localization.Away x)))).symm
