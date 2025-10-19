/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Order.Filter.Cofinite

/-!
# Factorization of ideals and fractional ideals of Dedekind domains
Every nonzero ideal `I` of a Dedekind domain `R` can be factored as a product `∏_v v^{n_v}` over the
maximal ideals of `R`, where the exponents `n_v` are natural numbers.

Similarly, every nonzero fractional ideal `I` of a Dedekind domain `R` can be factored as a product
`∏_v v^{n_v}` over the maximal ideals of `R`, where the exponents `n_v` are integers. We define
`FractionalIdeal.count K v I` (abbreviated as `val_v(I)` in the documentation) to be `n_v`, and we
prove some of its properties. If `I = 0`, we define `val_v(I) = 0`.

## Main definitions
- `FractionalIdeal.count` : If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of
  `R` such that `I = a⁻¹J`, then we define `val_v(I)` as `(val_v(J) - val_v(a))`. If `I = 0`, we
  set `val_v(I) = 0`.

## Main results
- `Ideal.finite_factors` : Only finitely many maximal ideals of `R` divide a given nonzero ideal.
- `Ideal.finprod_heightOneSpectrum_factorization` : The ideal `I` equals the finprod
  `∏_v v^(val_v(I))`, where `val_v(I)` denotes the multiplicity of `v` in the factorization of `I`
  and `v` runs over the maximal ideals of `R`.
- `FractionalIdeal.finprod_heightOneSpectrum_factorization` : If `I` is a nonzero fractional ideal,
  `a ∈ R`, and `J` is an ideal of `R` such that `I = a⁻¹J`, then `I` is equal to the product
  `∏_v v^(val_v(J) - val_v(a))`.
  - `FractionalIdeal.finprod_heightOneSpectrum_factorization'` : If `I` is a nonzero fractional
  ideal, then `I` is equal to the product `∏_v v^(val_v(I))`.
- `FractionalIdeal.finprod_heightOneSpectrum_factorization_principal` : For a nonzero `k = r/s ∈ K`,
  the fractional ideal `(k)` is equal to the product `∏_v v^(val_v(r) - val_v(s))`.
- `FractionalIdeal.finite_factors` : If `I ≠ 0`, then `val_v(I) = 0` for all but finitely many
  maximal ideals of `R`.
- `IsDedekindDomain.exists_sup_span_eq`: For every ideals `0 < I ≤ J`,
  there exists `a` such that `J = I + ⟨a⟩`.
- `Ideal.map_algebraMap_eq_finset_prod_pow`: if `p` is a maximal ideal, then the lift of `p`
  in an extension is the product of the primes over `p` to the power the ramification index.

## Implementation notes
Since we are only interested in the factorization of nonzero fractional ideals, we define
`val_v(0) = 0` so that every `val_v` is in `ℤ` and we can avoid having to use `WithTop ℤ`.

## Tags
dedekind domain, fractional ideal, ideal, factorization
-/

noncomputable section

open scoped nonZeroDivisors

open Set Function UniqueFactorizationMonoid IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Factorization of ideals of Dedekind domains -/

variable [IsDedekindDomain R] (v : HeightOneSpectrum R)

open scoped Classical in
/-- Given a maximal ideal `v` and an ideal `I` of `R`, `maxPowDividing` returns the maximal
  power of `v` dividing `I`. -/
def IsDedekindDomain.HeightOneSpectrum.maxPowDividing (I : Ideal R) : Ideal R :=
  v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors

open Associates in
theorem IsDedekindDomain.HeightOneSpectrum.maxPowDividing_eq_pow_multiset_count
    [DecidableEq (Ideal R)] {I : Ideal R} (hI : I ≠ 0) :
    maxPowDividing v I =
      v.asIdeal ^ Multiset.count v.asIdeal (normalizedFactors I) := by
  classical
  rw [maxPowDividing, factors_mk _ hI, count_some (irreducible_mk.mpr v.irreducible),
    ← Multiset.count_map_eq_count' _ _ Subtype.val_injective, map_subtype_coe_factors',
    factors_eq_normalizedFactors, ← Multiset.count_map_eq_count' _ _ (mk_injective (M := Ideal R))]

/-- Only finitely many maximal ideals of `R` divide a given nonzero ideal. -/
theorem Ideal.finite_factors {I : Ideal R} (hI : I ≠ 0) :
    {v : HeightOneSpectrum R | v.asIdeal ∣ I}.Finite := by
  rw [← Set.finite_coe_iff, Set.coe_setOf]
  haveI h_fin := fintypeSubtypeDvd I hI
  refine
    Finite.of_injective (fun v => (⟨(v : HeightOneSpectrum R).asIdeal, v.2⟩ : { x // x ∣ I })) ?_
  intro v w hvw
  exact Subtype.coe_injective (HeightOneSpectrum.ext (by simpa using hvw))

open scoped Classical in
/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that the
  multiplicity of `v` in the factorization of `I`, denoted `val_v(I)`, is nonzero. -/
theorem Associates.finite_factors {I : Ideal R} (hI : I ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ) = 0 := by
  have h_supp : {v : HeightOneSpectrum R | ¬((Associates.mk v.asIdeal).count
      (Associates.mk I).factors : ℤ) = 0} = {v : HeightOneSpectrum R | v.asIdeal ∣ I} := by
    ext v
    simp_rw [Int.natCast_eq_zero]
    exact Associates.count_ne_zero_iff_dvd hI v.irreducible
  rw [Filter.eventually_cofinite, h_supp]
  exact Ideal.finite_factors hI

namespace Ideal

open scoped Classical in
/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
  `v^(val_v(I))` is not the unit ideal. -/
theorem finite_mulSupport {I : Ideal R} (hI : I ≠ 0) :
    (mulSupport fun v : HeightOneSpectrum R => v.maxPowDividing I).Finite :=
  haveI h_subset : {v : HeightOneSpectrum R | v.maxPowDividing I ≠ 1} ⊆
      {v : HeightOneSpectrum R |
        ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ) ≠ 0} := by
    intro v hv h_zero
    have hv' : v.maxPowDividing I = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, Int.natCast_eq_zero.mp h_zero,
        pow_zero _]
    exact hv hv'
  Finite.subset (Filter.eventually_cofinite.mp (Associates.finite_factors hI)) h_subset

open scoped Classical in
/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^(val_v(I))`, regarded as a fractional ideal, is not `(1)`. -/
theorem finite_mulSupport_coe {I : Ideal R} (hI : I ≠ 0) :
    (mulSupport fun v : HeightOneSpectrum R => (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ)).Finite := by
  rw [mulSupport]
  simp_rw [Ne, zpow_natCast, ← FractionalIdeal.coeIdeal_pow, FractionalIdeal.coeIdeal_eq_one]
  exact finite_mulSupport hI

open scoped Classical in
/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^-(val_v(I))` is not the unit ideal. -/
theorem finite_mulSupport_inv {I : Ideal R} (hI : I ≠ 0) :
    (mulSupport fun v : HeightOneSpectrum R => (v.asIdeal : FractionalIdeal R⁰ K) ^
      (-((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ))).Finite := by
  rw [mulSupport]
  simp_rw [zpow_neg, Ne, inv_eq_one]
  exact finite_mulSupport_coe hI

open scoped Classical in
/-- For every nonzero ideal `I` of `v`, `v^(val_v(I) + 1)` does not divide `∏_v v^(val_v(I))`. -/
theorem finprod_not_dvd (I : Ideal R) (hI : I ≠ 0) :
    ¬v.asIdeal ^ ((Associates.mk v.asIdeal).count (Associates.mk I).factors + 1) ∣
        ∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I := by
  have hf := finite_mulSupport hI
  have h_ne_zero : v.maxPowDividing I ≠ 0 := pow_ne_zero _ v.ne_bot
  rw [← mul_finprod_cond_ne v hf, pow_add, pow_one, finprod_cond_ne _ _ hf]
  intro h_contr
  have hv_prime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime
  obtain ⟨w, hw, hvw'⟩ :=
    Prime.exists_mem_finset_dvd hv_prime ((mul_dvd_mul_iff_left h_ne_zero).mp h_contr)
  have hw_prime : Prime w.asIdeal := Ideal.prime_of_isPrime w.ne_bot w.isPrime
  have hvw := Prime.dvd_of_dvd_pow hv_prime hvw'
  rw [Prime.dvd_prime_iff_associated hv_prime hw_prime, associated_iff_eq] at hvw
  exact (Finset.mem_erase.mp hw).1 (HeightOneSpectrum.ext hvw.symm)

end Ideal

theorem Associates.finprod_ne_zero (I : Ideal R) :
    Associates.mk (∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I) ≠ 0 := by
  classical
  rw [Associates.mk_ne_zero, finprod_def]
  split_ifs
  · rw [Finset.prod_ne_zero_iff]
    intro v _
    apply pow_ne_zero _ v.ne_bot
  · exact one_ne_zero

namespace Ideal

open scoped Classical in
/-- The multiplicity of `v` in `∏_v v^(val_v(I))` equals `val_v(I)`. -/
theorem finprod_count (I : Ideal R) (hI : I ≠ 0) : (Associates.mk v.asIdeal).count
    (Associates.mk (∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I)).factors =
    (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  have h_ne_zero := Associates.finprod_ne_zero I
  have hv : Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  have h_dvd := finprod_mem_dvd v (Ideal.finite_mulSupport hI)
  have h_not_dvd := Ideal.finprod_not_dvd v I hI
  simp only [IsDedekindDomain.HeightOneSpectrum.maxPowDividing] at h_dvd h_ne_zero h_not_dvd
  rw [← Associates.mk_dvd_mk] at h_dvd h_not_dvd
  simp only [Associates.dvd_eq_le] at h_dvd h_not_dvd
  rw [Associates.mk_pow, Associates.prime_pow_dvd_iff_le h_ne_zero hv] at h_dvd h_not_dvd
  rw [not_le] at h_not_dvd
  apply Nat.eq_of_le_of_lt_succ h_dvd h_not_dvd

/-- The ideal `I` equals the finprod `∏_v v^(val_v(I))`. -/
theorem finprod_heightOneSpectrum_factorization {I : Ideal R} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I = I := by
  rw [← associated_iff_eq, ← Associates.mk_eq_mk_iff_associated]
  classical
  apply Associates.eq_of_eq_counts
  · apply Associates.finprod_ne_zero I
  · apply Associates.mk_ne_zero.mpr hI
  intro v hv
  obtain ⟨J, hJv⟩ := Associates.exists_rep v
  rw [← hJv, Associates.irreducible_mk] at hv
  rw [← hJv]
  apply Ideal.finprod_count
    ⟨J, Ideal.isPrime_of_prime (irreducible_iff_prime.mp hv), Irreducible.ne_zero hv⟩ I hI

variable (K)

open scoped Classical in
/-- The ideal `I` equals the finprod `∏_v v^(val_v(I))`, when both sides are regarded as fractional
ideals of `R`. -/
theorem finprod_heightOneSpectrum_factorization_coe {I : Ideal R} (hI : I ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ)) = I := by
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  rw [FractionalIdeal.coeIdeal_finprod R⁰ K (le_refl _)]
  simp_rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, FractionalIdeal.coeIdeal_pow,
    zpow_natCast]

end Ideal

/-! ### Factorization of fractional ideals of Dedekind domains -/

namespace FractionalIdeal

open Int IsLocalization

open scoped Classical in
/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that
`I = a⁻¹J`, then `I` is equal to the product `∏_v v^(val_v(J) - val_v(a))`. -/
theorem finprod_heightOneSpectrum_factorization {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) {a : R}
    {J : Ideal R} (haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ) = I := by
  have hJ_ne_zero : J ≠ 0 := ideal_factor_ne_zero hI haJ
  have hJ := Ideal.finprod_heightOneSpectrum_factorization_coe K hJ_ne_zero
  have ha_ne_zero : Ideal.span {a} ≠ 0 := constant_factor_ne_zero hI haJ
  have ha := Ideal.finprod_heightOneSpectrum_factorization_coe K ha_ne_zero
  rw [haJ, ← div_spanSingleton, div_eq_mul_inv, ← coeIdeal_span_singleton, ← hJ, ← ha,
    ← finprod_inv_distrib]
  simp_rw [← zpow_neg]
  rw [← finprod_mul_distrib (Ideal.finite_mulSupport_coe hJ_ne_zero)
    (Ideal.finite_mulSupport_inv ha_ne_zero)]
  apply finprod_congr
  intro v
  rw [← zpow_add₀ ((@coeIdeal_ne_zero R _ K _ _ _ _).mpr v.ne_bot), sub_eq_add_neg]

open scoped Classical in
/-- For a nonzero `k = r/s ∈ K`, the fractional ideal `(k)` is equal to the product
`∏_v v^(val_v(r) - val_v(s))`. -/
theorem finprod_heightOneSpectrum_factorization_principal_fraction {n : R} (hn : n ≠ 0) (d : ↥R⁰) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {n} : Ideal R)).factors -
        (Associates.mk v.asIdeal).count (Associates.mk ((Ideal.span {(↑d : R)}) :
        Ideal R)).factors : ℤ) = spanSingleton R⁰ (mk' K n d) := by
  have hd_ne_zero : (algebraMap R K) (d : R) ≠ 0 :=
    map_ne_zero_of_mem_nonZeroDivisors _ (IsFractionRing.injective R K) d.property
  have h0 : spanSingleton R⁰ (mk' K n d) ≠ 0 := by
    rw [spanSingleton_ne_zero_iff, IsFractionRing.mk'_eq_div, ne_eq, div_eq_zero_iff, not_or]
    exact ⟨(map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).mpr hn, hd_ne_zero⟩
  have hI : spanSingleton R⁰ (mk' K n d) =
      spanSingleton R⁰ ((algebraMap R K) d)⁻¹ * ↑(Ideal.span {n} : Ideal R) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton]
    apply congr_arg
    rw [IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  exact finprod_heightOneSpectrum_factorization h0 hI

open Classical in
/-- For a nonzero `k = r/s ∈ K`, the fractional ideal `(k)` is equal to the product
`∏_v v^(val_v(r) - val_v(s))`. -/
theorem finprod_heightOneSpectrum_factorization_principal {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (k : K) (hk : I = spanSingleton R⁰ k) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {choose
          (mk'_surjective R⁰ k)} : Ideal R)).factors -
        (Associates.mk v.asIdeal).count (Associates.mk ((Ideal.span {(↑(choose
          (choose_spec (mk'_surjective R⁰ k)) : ↥R⁰) : R)}) : Ideal R)).factors : ℤ) = I := by
  set n : R := choose (mk'_surjective R⁰ k)
  set d : ↥R⁰ := choose (choose_spec (mk'_surjective R⁰ k))
  have hnd : mk' K n d = k := choose_spec (choose_spec (mk'_surjective R⁰ k))
  have hn0 : n ≠ 0 := by
    by_contra h
    rw [← hnd, h, IsFractionRing.mk'_eq_div, map_zero, zero_div, spanSingleton_zero] at hk
    exact hI hk
  rw [finprod_heightOneSpectrum_factorization_principal_fraction hn0 d, hk, hnd]

variable (K)

open Classical in
/-- If `I` is a nonzero fractional ideal, `a ∈ R`, and `J` is an ideal of `R` such that `I = a⁻¹J`,
then we define `val_v(I)` as `(val_v(J) - val_v(a))`. If `I = 0`, we set `val_v(I) = 0`. -/
def count (I : FractionalIdeal R⁰ K) : ℤ :=
  dite (I = 0) (fun _ : I = 0 => 0) fun _ : ¬I = 0 =>
    let a := choose (exists_eq_spanSingleton_mul I)
    let J := choose (choose_spec (exists_eq_spanSingleton_mul I))
    ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ)

/-- val_v(0) = 0. -/
lemma count_zero : count K v (0 : FractionalIdeal R⁰ K) = 0 := by simp only [count, dif_pos]

open Classical in
lemma count_ne_zero {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    count K v I = ((Associates.mk v.asIdeal).count (Associates.mk
      (choose (choose_spec (exists_eq_spanSingleton_mul I)))).factors -
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {choose (exists_eq_spanSingleton_mul I)})).factors : ℤ) := by
  simp only [count, dif_neg hI]

open Classical in
/-- `val_v(I)` does not depend on the choice of `a` and `J` used to represent `I`. -/
theorem count_well_defined {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) {a : R}
    {J : Ideal R} (h_aJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) :
    count K v I = ((Associates.mk v.asIdeal).count (Associates.mk J).factors -
      (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ) := by
  set a₁ := choose (exists_eq_spanSingleton_mul I)
  set J₁ := choose (choose_spec (exists_eq_spanSingleton_mul I))
  have h_a₁J₁ : I = spanSingleton R⁰ ((algebraMap R K) a₁)⁻¹ * ↑J₁ :=
    (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
  have h_a₁_ne_zero : a₁ ≠ 0 := (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).1
  have h_J₁_ne_zero : J₁ ≠ 0 := ideal_factor_ne_zero hI h_a₁J₁
  have h_a_ne_zero : Ideal.span {a} ≠ 0 := constant_factor_ne_zero hI h_aJ
  have h_J_ne_zero : J ≠ 0 := ideal_factor_ne_zero hI h_aJ
  have h_a₁' : spanSingleton R⁰ ((algebraMap R K) a₁) ≠ 0 := by
    rw [ne_eq, spanSingleton_eq_zero_iff, ← (algebraMap R K).map_zero,
      Injective.eq_iff (IsLocalization.injective K (le_refl R⁰))]
    exact h_a₁_ne_zero
  have h_a' : spanSingleton R⁰ ((algebraMap R K) a) ≠ 0 := by
    rw [ne_eq, spanSingleton_eq_zero_iff, ← (algebraMap R K).map_zero,
      Injective.eq_iff (IsLocalization.injective K (le_refl R⁰))]
    rw [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at h_a_ne_zero
    exact h_a_ne_zero
  have hv : Irreducible (Associates.mk v.asIdeal) := by
    exact Associates.irreducible_mk.mpr v.irreducible
  rw [h_a₁J₁, ← div_spanSingleton, ← div_spanSingleton, div_eq_div_iff h_a₁' h_a',
    ← coeIdeal_span_singleton, ← coeIdeal_span_singleton, ← coeIdeal_mul, ← coeIdeal_mul] at h_aJ
  rw [count, dif_neg hI, sub_eq_sub_iff_add_eq_add, ← natCast_add, ← natCast_add, natCast_inj,
    ← Associates.count_mul _ _ hv, ← Associates.count_mul _ _ hv, Associates.mk_mul_mk,
    Associates.mk_mul_mk, coeIdeal_injective h_aJ]
  · rw [ne_eq, Associates.mk_eq_zero]; exact h_J_ne_zero
  · rw [ne_eq, Associates.mk_eq_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact h_a₁_ne_zero
  · rw [ne_eq, Associates.mk_eq_zero]; exact h_J₁_ne_zero
  · rw [ne_eq, Associates.mk_eq_zero]; exact h_a_ne_zero

/-- For nonzero `I, I'`, `val_v(I*I') = val_v(I) + val_v(I')`. -/
theorem count_mul {I I' : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hI' : I' ≠ 0) :
    count K v (I * I') = count K v I + count K v I' := by
  classical
  have hv : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  obtain ⟨a, J, ha, haJ⟩ := exists_eq_spanSingleton_mul I
  have ha_ne_zero : Associates.mk (Ideal.span {a} : Ideal R) ≠ 0 := by
    rw [ne_eq, Associates.mk_eq_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha
  have hJ_ne_zero : Associates.mk J ≠ 0 := Associates.mk_ne_zero.mpr (ideal_factor_ne_zero hI haJ)
  obtain ⟨a', J', ha', haJ'⟩ := exists_eq_spanSingleton_mul I'
  have ha'_ne_zero : Associates.mk (Ideal.span {a'} : Ideal R) ≠ 0 := by
    rw [ne_eq, Associates.mk_eq_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact ha'
  have hJ'_ne_zero : Associates.mk J' ≠ 0 :=
    Associates.mk_ne_zero.mpr (ideal_factor_ne_zero hI' haJ')
  have h_prod : I * I' = spanSingleton R⁰ ((algebraMap R K) (a * a'))⁻¹ * ↑(J * J') := by
    rw [haJ, haJ', mul_assoc, mul_comm (J : FractionalIdeal R⁰ K), mul_assoc, ← mul_assoc,
      spanSingleton_mul_spanSingleton, coeIdeal_mul, RingHom.map_mul, mul_inv,
      mul_comm (J : FractionalIdeal R⁰ K)]
  rw [count_well_defined K v hI haJ, count_well_defined K v hI' haJ',
    count_well_defined K v (mul_ne_zero hI hI') h_prod, ← Associates.mk_mul_mk,
    Associates.count_mul hJ_ne_zero hJ'_ne_zero hv, ← Ideal.span_singleton_mul_span_singleton,
    ← Associates.mk_mul_mk, Associates.count_mul ha_ne_zero ha'_ne_zero hv]
  push_cast
  ring

/-- For nonzero `I, I'`, `val_v(I*I') = val_v(I) + val_v(I')`. If `I` or `I'` is zero, then
`val_v(I*I') = 0`. -/
theorem count_mul' (I I' : FractionalIdeal R⁰ K) [Decidable (I ≠ 0 ∧ I' ≠ 0)] :
    count K v (I * I') = if I ≠ 0 ∧ I' ≠ 0 then count K v I + count K v I' else 0 := by
  split_ifs with h
  · exact count_mul K v h.1 h.2
  · rw [← mul_ne_zero_iff, not_ne_iff] at h
    rw [h, count_zero]

/-- val_v(1) = 0. -/
theorem count_one : count K v (1 : FractionalIdeal R⁰ K) = 0 := by
  have h1 : (1 : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑(1 : Ideal R) := by
    rw [(algebraMap R K).map_one, Ideal.one_eq_top, coeIdeal_top, mul_one, inv_one,
      spanSingleton_one]
  rw [count_well_defined K v one_ne_zero h1, Ideal.span_singleton_one, Ideal.one_eq_top, sub_self]

theorem count_prod {ι} (s : Finset ι) (I : ι → FractionalIdeal R⁰ K) (hS : ∀ i ∈ s, I i ≠ 0) :
    count K v (∏ i ∈ s, I i) = ∑ i ∈ s, count K v (I i) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, count_one]
  | insert i s hi hrec =>
    have hS' : ∀ i ∈ s, I i ≠ 0 := fun j hj => hS j (Finset.mem_insert_of_mem hj)
    have hS0 : ∏ i ∈ s, I i ≠ 0 := Finset.prod_ne_zero_iff.mpr hS'
    have hi0 : I i ≠ 0 := hS i (Finset.mem_insert_self i s)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, count_mul K v hi0 hS0, hrec hS']

/-- For every `n ∈ ℕ` and every ideal `I`, `val_v(I^n) = n*val_v(I)`. -/
theorem count_pow (n : ℕ) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ n) = n * count K v I := by
  induction n with
  | zero => rw [pow_zero, ofNat_zero, zero_mul, count_one]
  | succ n h =>
    classical rw [pow_succ, count_mul']
    by_cases hI : I = 0
    · have h_neg : ¬(I ^ n ≠ 0 ∧ I ≠ 0) := by
        rw [not_and', not_not, ne_eq]
        intro h
        exact absurd hI h
      rw [if_neg h_neg, hI, count_zero, mul_zero]
    · rw [if_pos (And.intro (pow_ne_zero n hI) hI), h, Nat.cast_add,
        Nat.cast_one]
      ring

/-- `val_v(v) = 1`, when `v` is regarded as a fractional ideal. -/
theorem count_self : count K v (v.asIdeal : FractionalIdeal R⁰ K) = 1 := by
  have hv : (v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 := coeIdeal_ne_zero.mpr v.ne_bot
  have h_self : (v.asIdeal : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑v.asIdeal := by
    rw [(algebraMap R K).map_one, inv_one, spanSingleton_one, one_mul]
  have hv_irred : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  classical rw [count_well_defined K v hv h_self, Associates.count_self hv_irred,
    Ideal.span_singleton_one, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one,
    Associates.count_zero hv_irred, ofNat_zero, sub_zero, ofNat_one]

/-- `val_v(v^n) = n` for every `n ∈ ℕ`. -/
theorem count_pow_self (n : ℕ) :
    count K v ((v.asIdeal : FractionalIdeal R⁰ K) ^ n) = n := by
  rw [count_pow, count_self, mul_one]

/-- `val_v(I⁻ⁿ) = -val_v(Iⁿ)` for every `n ∈ ℤ`. -/
theorem count_neg_zpow (n : ℤ) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ (-n)) = -count K v (I ^ n) := by
  by_cases hI : I = 0
  · by_cases hn : n = 0
    · rw [hn, neg_zero, zpow_zero, count_one, neg_zero]
    · rw [hI, zero_zpow n hn, zero_zpow (-n) (neg_ne_zero.mpr hn), count_zero, neg_zero]
  · rw [eq_neg_iff_add_eq_zero, ← count_mul K v (zpow_ne_zero _ hI) (zpow_ne_zero _ hI),
      ← zpow_add₀ hI, neg_add_cancel, zpow_zero]
    exact count_one K v

theorem count_inv (I : FractionalIdeal R⁰ K) :
    count K v (I⁻¹) = -count K v I := by
  rw [← zpow_neg_one, count_neg_zpow K v (1 : ℤ) I, zpow_one]

/-- `val_v(Iⁿ) = n*val_v(I)` for every `n ∈ ℤ`. -/
theorem count_zpow (n : ℤ) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ n) = n * count K v I := by
  obtain n | n := n
  · rw [ofNat_eq_coe, zpow_natCast]
    exact count_pow K v n I
  · rw [negSucc_eq, count_neg_zpow, ← Int.natCast_succ, zpow_natCast, count_pow]
    ring

/-- `val_v(v^n) = n` for every `n ∈ ℤ`. -/
theorem count_zpow_self (n : ℤ) :
    count K v ((v.asIdeal : FractionalIdeal R⁰ K) ^ n) = n := by
  rw [count_zpow, count_self, mul_one]

/-- If `v ≠ w` are two maximal ideals of `R`, then `val_v(w) = 0`. -/
theorem count_maximal_coprime {w : HeightOneSpectrum R} (hw : w ≠ v) :
    count K v (w.asIdeal : FractionalIdeal R⁰ K) = 0 := by
  have hw_fact : (w.asIdeal : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑w.asIdeal := by
    rw [(algebraMap R K).map_one, inv_one, spanSingleton_one, one_mul]
  have hw_ne_zero : (w.asIdeal : FractionalIdeal R⁰ K) ≠ 0 :=
    coeIdeal_ne_zero.mpr w.ne_bot
  have hv : Irreducible (Associates.mk v.asIdeal) := by apply v.associates_irreducible
  have hw' : Irreducible (Associates.mk w.asIdeal) := by apply w.associates_irreducible
  classical
  rw [count_well_defined K v hw_ne_zero hw_fact, Ideal.span_singleton_one, ← Ideal.one_eq_top,
    Associates.mk_one, Associates.factors_one, Associates.count_zero hv, ofNat_zero, sub_zero,
    natCast_eq_zero, ← pow_one (Associates.mk w.asIdeal), Associates.factors_prime_pow hw',
    Associates.count_some hv, Multiset.replicate_one, Multiset.count_eq_zero,
    Multiset.mem_singleton]
  simp only [Subtype.mk.injEq]
  rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq, ← HeightOneSpectrum.ext_iff]
  exact Ne.symm hw

theorem count_maximal (w : HeightOneSpectrum R) [Decidable (w = v)] :
    count K v (w.asIdeal : FractionalIdeal R⁰ K) = if w = v then 1 else 0 := by
  split_ifs with h
  · rw [h, count_self]
  · exact count_maximal_coprime K v h

/-- `val_v(∏_{w ≠ v} w^{exps w}) = 0`. -/
theorem count_finprod_coprime (exps : HeightOneSpectrum R → ℤ) :
    count K v (∏ᶠ (w : HeightOneSpectrum R) (_ : w ≠ v),
      (w.asIdeal : (FractionalIdeal R⁰ K)) ^ exps w) = 0 := by
  apply finprod_mem_induction fun I => count K v I = 0
  · exact count_one K v
  · intro I I' hI hI'
    classical
    by_cases h : I ≠ 0 ∧ I' ≠ 0
    · rw [count_mul' K v, if_pos h, hI, hI', add_zero]
    · rw [count_mul' K v, if_neg h]
  · intro w hw
    rw [count_zpow, count_maximal_coprime K v hw, mul_zero]

theorem count_finsuppProd (exps : HeightOneSpectrum R →₀ ℤ) :
    count K v (exps.prod (HeightOneSpectrum.asIdeal · ^ ·)) = exps v := by
  rw [Finsupp.prod, count_prod]
  · classical simp only [count_zpow, count_maximal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      exps.mem_support_iff, ne_eq, ite_not, ite_eq_right_iff, @eq_comm ℤ 0, imp_self]
  · exact fun v hv ↦ zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

@[deprecated (since := "2025-04-06")] alias count_finsupp_prod := count_finsuppProd

/-- If `exps` is finitely supported, then `val_v(∏_w w^{exps w}) = exps v`. -/
theorem count_finprod (exps : HeightOneSpectrum R → ℤ)
    (h_exps : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, exps v = 0) :
    count K v (∏ᶠ v : HeightOneSpectrum R,
      (v.asIdeal : FractionalIdeal R⁰ K) ^ exps v) = exps v := by
  convert count_finsuppProd K v (Finsupp.mk h_exps.toFinset exps (fun _ ↦ h_exps.mem_toFinset))
  rw [finprod_eq_finset_prod_of_mulSupport_subset (s := h_exps.toFinset), Finsupp.prod]
  · rfl
  · rw [Finite.coe_toFinset]
    intro v hv h
    rw [mem_mulSupport, h, zpow_zero] at hv
    exact hv (Eq.refl 1)

open scoped Classical in
theorem count_coe {J : Ideal R} (hJ : J ≠ 0) :
    count K v J = (Associates.mk v.asIdeal).count (Associates.mk J).factors := by
  rw [count_well_defined K (J := J) (a := 1), Ideal.span_singleton_one, sub_eq_self,
    Nat.cast_eq_zero, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one,
    Associates.count_zero v.associates_irreducible]
  · simpa only [ne_eq, coeIdeal_eq_zero]
  · simp only [map_one, inv_one, spanSingleton_one, one_mul]

theorem count_coe_nonneg (J : Ideal R) : 0 ≤ count K v J := by
  by_cases hJ : J = 0
  · simp only [hJ, Submodule.zero_eq_bot, coeIdeal_bot, count_zero, le_refl]
  · classical simp only [count_coe K v hJ, Nat.cast_nonneg]

theorem count_mono {I J} (hI : I ≠ 0) (h : I ≤ J) : count K v J ≤ count K v I := by
  by_cases hJ : J = 0
  · exact (hI (FractionalIdeal.le_zero_iff.mp (h.trans hJ.le))).elim
  have := mul_le_mul_left' h J⁻¹
  rw [inv_mul_cancel₀ hJ, FractionalIdeal.le_one_iff_exists_coeIdeal] at this
  obtain ⟨J', hJ'⟩ := this
  rw [← mul_inv_cancel_left₀ hJ I, ← hJ', count_mul K v hJ, le_add_iff_nonneg_right]
  · exact count_coe_nonneg K v J'
  · exact hJ' ▸ mul_ne_zero (inv_ne_zero hJ) hI

/-- If `I` is a nonzero fractional ideal, then `I` is equal to the product `∏_v v^(count K v I)`. -/
theorem finprod_heightOneSpectrum_factorization' {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (count K v I) = I := by
  have h := (Classical.choose_spec (Classical.choose_spec (exists_eq_spanSingleton_mul I))).2
  conv_rhs => rw [← finprod_heightOneSpectrum_factorization hI h]
  apply finprod_congr
  intro w
  apply congr_arg
  rw [count_ne_zero K w hI]

variable {K}

open scoped Classical in
/-- If `I ≠ 0`, then `val_v(I) = 0` for all but finitely many maximal ideals of `R`. -/
theorem finite_factors' {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) {a : R}
    {J : Ideal R} (haJ : I = spanSingleton R⁰ ((algebraMap R K) a)⁻¹ * ↑J) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite,
      ((Associates.mk v.asIdeal).count (Associates.mk J).factors : ℤ) -
        (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors = 0 := by
  have ha_ne_zero : Ideal.span {a} ≠ 0 := constant_factor_ne_zero hI haJ
  have hJ_ne_zero : J ≠ 0 := ideal_factor_ne_zero hI haJ
  have h_subset :
    {v : HeightOneSpectrum R | ¬((Associates.mk v.asIdeal).count (Associates.mk J).factors : ℤ) -
      ↑((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors) = 0} ⊆
    {v : HeightOneSpectrum R | v.asIdeal ∣ J} ∪
      {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {a}} := by
    intro v hv
    have hv_irred : Irreducible v.asIdeal := v.irreducible
    by_contra h_notMem
    rw [mem_union, mem_setOf_eq, mem_setOf_eq] at h_notMem
    push_neg at h_notMem
    rw [← Associates.count_ne_zero_iff_dvd ha_ne_zero hv_irred, not_not,
      ← Associates.count_ne_zero_iff_dvd hJ_ne_zero hv_irred, not_not] at h_notMem
    rw [mem_setOf_eq, h_notMem.1, h_notMem.2, sub_self] at hv
    exact hv (Eq.refl 0)
  exact Finite.subset (Finite.union (Ideal.finite_factors (ideal_factor_ne_zero hI haJ))
    (Ideal.finite_factors (constant_factor_ne_zero hI haJ))) h_subset

open Classical in
/-- `val_v(I) = 0` for all but finitely many maximal ideals of `R`. -/
theorem finite_factors (I : FractionalIdeal R⁰ K) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, count K v I = 0 := by
  by_cases hI : I = 0
  · simp only [hI, count_zero, Filter.eventually_cofinite, not_true_eq_false, setOf_false,
      finite_empty]
  · convert finite_factors' hI (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
    rw [count_ne_zero K _ hI]

end FractionalIdeal

section div

/-- In a Dedekind domain, for every ideals `0 < I ≤ J` there exists `a` such that `J = I + ⟨a⟩`.
TODO: Show that this property uniquely characterizes Dedekind domains. -/
lemma IsDedekindDomain.exists_sup_span_eq {I J : Ideal R} (hIJ : I ≤ J) (hI : I ≠ 0) :
    ∃ a, I ⊔ Ideal.span {a} = J := by
  classical
  obtain ⟨I, rfl⟩ := Ideal.dvd_iff_le.mpr hIJ
  simp only [ne_eq, mul_eq_zero, not_or] at hI
  obtain ⟨hJ, hI⟩ := hI
  suffices ∃ a, ∃ K, J * K = Ideal.span {a} ∧ I + K = ⊤ by
    obtain ⟨a, K, e, e'⟩ := this
    exact ⟨a, by rw [← e, ← Ideal.add_eq_sup, ← mul_add, e', Ideal.mul_top]⟩
  let s := (I.finite_factors hI).toFinset
  have : ∀ p ∈ s, J * ∏ q ∈ s, q.asIdeal < J * ∏ q ∈ s \ {p}, q.asIdeal := by
    intro p hps
    conv_rhs => rw [← mul_one (J * _)]
    rw [Finset.prod_eq_mul_prod_diff_singleton hps, ← mul_assoc,
      mul_right_comm _ p.asIdeal]
    refine mul_lt_mul_of_pos_left ?_ ?_
    · rw [Ideal.one_eq_top, lt_top_iff_ne_top]
      exact p.2.ne_top
    · rw [Ideal.zero_eq_bot, bot_lt_iff_ne_bot, ← Ideal.zero_eq_bot,
        mul_ne_zero_iff, Finset.prod_ne_zero_iff]
      exact ⟨hJ, fun x _ ↦ x.3⟩
  choose! a ha ha' using fun p hps ↦ SetLike.exists_of_lt (this p hps)
  obtain ⟨K, hK⟩ : J ∣ Ideal.span {∑ p ∈ s, a p} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact sum_mem fun p hp ↦ Ideal.mul_le_right (ha p hp)
  refine ⟨_, _, hK.symm, ?_⟩
  by_contra H
  obtain ⟨p, hp, h⟩ := Ideal.exists_le_maximal _ H
  let p' : HeightOneSpectrum R := ⟨p, hp.isPrime, fun e ↦ hI (by simp_all)⟩
  have hp's : p' ∈ s := by simpa [p', s, Ideal.dvd_iff_le] using le_sup_left.trans h
  have H₁ : J * K ≤ J * p := Ideal.mul_mono_right (le_sup_right.trans h)
  replace H₁ := hK.trans_le H₁ (Ideal.mem_span_singleton_self _)
  have H₂ : ∑ q ∈ s \ {p'}, a q ∈ J * p := by
    refine sum_mem fun q hq ↦ ?_
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hq
    refine Ideal.mul_mono_right ?_ (ha q hq.1)
    exact Ideal.prod_le_inf.trans (Finset.inf_le (b := p') (by simpa [hp's] using Ne.symm hq.2))
  apply ha' _ hp's
  have := IsDedekindDomain.inf_prime_pow_eq_prod s (fun i ↦ i.asIdeal) (fun _ ↦ 1)
    (fun i _ ↦ i.prime) (fun i _ j _ e ↦ mt HeightOneSpectrum.ext e)
  simp only [pow_one] at this
  have inst : Nonempty {x // x ∈ s} := ⟨_, hp's⟩
  rw [← this, Finset.inf_eq_iInf, iInf_subtype', Ideal.mul_iInf, Ideal.mem_iInf]
  rintro ⟨q, hq⟩
  by_cases hqp : q = p'
  · subst hqp
    convert sub_mem H₁ H₂
    rw [Finset.sum_eq_add_sum_diff_singleton hp's, add_sub_cancel_right]
  · refine Ideal.mul_mono_right ?_ (ha p' hp's)
    exact Ideal.prod_le_inf.trans (Finset.inf_le (b := q) (by simpa [hq] using hqp))

/-- In a Dedekind domain, any ideal is spanned by two elements, where one of the element
could be any fixed non-zero element in the ideal. -/
lemma IsDedekindDomain.exists_eq_span_pair {I : Ideal R} {x : R} (hxI : x ∈ I) (hx : x ≠ 0) :
    ∃ y, I = .span {x, y} := by
  obtain ⟨y, rfl⟩ := exists_sup_span_eq (I.span_singleton_le_iff_mem.mpr hxI) (by simpa)
  simp_rw [← Ideal.span_union, Set.union_singleton, Set.pair_comm x]
  use y

lemma IsDedekindDomain.exists_add_spanSingleton_mul_eq
    {a b c : FractionalIdeal R⁰ K} (hac : a ≤ c) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ x : K, a + FractionalIdeal.spanSingleton R⁰ x * b = c := by
  wlog hb' : b = 1
  · obtain ⟨x, e⟩ := this (a := b⁻¹ * a) (b := 1) (c := b⁻¹ * c) (by gcongr) (by simp [ha, hb])
      one_ne_zero rfl
    use x
    simpa [hb, ← mul_assoc, mul_add, mul_comm b (.spanSingleton _ _)] using congr(b * $e)
  subst hb'
  have H : Ideal.span {c.den.1} * a.num ≤ c.num * Ideal.span {a.den.1} := by
    rw [← FractionalIdeal.coeIdeal_le_coeIdeal K]
    simp only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton, ←
      FractionalIdeal.den_mul_self_eq_num']
    ring_nf
    gcongr
  obtain ⟨x, hx⟩ := exists_sup_span_eq H
    (by simpa using FractionalIdeal.num_eq_zero_iff.not.mpr ha)
  refine ⟨algebraMap R K x / algebraMap R K (a.den.1 * c.den.1), ?_⟩
  refine mul_left_injective₀ (b := .spanSingleton _
    (algebraMap R K (a.den.1 * c.den.1))) ?_ ?_
  · simp [FractionalIdeal.spanSingleton_eq_zero_iff]
  · simp only [map_mul, mul_one, add_mul, FractionalIdeal.spanSingleton_mul_spanSingleton,
      isUnit_iff_ne_zero, ne_eq, mul_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff,
      nonZeroDivisors.coe_ne_zero, or_self, not_false_eq_true, IsUnit.div_mul_cancel]
    rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, ← mul_assoc, mul_comm a,
      FractionalIdeal.den_mul_self_eq_num', ← mul_assoc, mul_right_comm,
      mul_comm c, FractionalIdeal.den_mul_self_eq_num', mul_comm]
    simp_rw [← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_mul,
      ← hx, ← FractionalIdeal.coeIdeal_sup]

namespace FractionalIdeal

/-- `c.divMod b a` (i.e. `c / b mod a`) is an arbitrary `x` such that `c = bx + a`.
This is zero if the above is not possible, i.e. when `a = 0` or `b = 0` or `¬ a ≤ c`. -/
noncomputable
def divMod (c b a : FractionalIdeal R⁰ K) : K :=
  letI := Classical.propDecidable
  if h : a ≤ c ∧ a ≠ 0 ∧ b ≠ 0 then
    (IsDedekindDomain.exists_add_spanSingleton_mul_eq h.1 h.2.1 h.2.2).choose else 0


lemma divMod_spec
    {a b c : FractionalIdeal R⁰ K} (hac : a ≤ c) (ha : a ≠ 0) (hb : b ≠ 0) :
    a + spanSingleton R⁰ (c.divMod b a) * b = c := by
  rw [divMod, dif_pos ⟨hac, ha, hb⟩]
  exact (IsDedekindDomain.exists_add_spanSingleton_mul_eq hac ha hb).choose_spec

@[simp]
lemma divMod_zero_left {I J : FractionalIdeal R⁰ K} : I.divMod 0 J = 0 := by
  simp [divMod]

@[simp]
lemma divMod_zero_right {I J : FractionalIdeal R⁰ K} : I.divMod J 0 = 0 := by
  simp [divMod]

@[simp]
lemma zero_divMod {I J : FractionalIdeal R⁰ K} :
    (0 : FractionalIdeal R⁰ K).divMod I J = 0 := by
  simp [divMod, ← and_assoc]

lemma divMod_zero_of_not_le {a b c : FractionalIdeal R⁰ K} (hac : ¬ a ≤ c) :
    c.divMod b a = 0 := by
  simp [divMod, hac]

set_option maxHeartbeats 210000 in
-- changed for new compiler
/-- Let `I J I' J'` be nonzero fractional ideals in a Dedekind domain with `J ≤ I` and `J' ≤ I'`.
If `I/J = I'/J'` in the group of fractional ideals (i.e. `I * J' = I' * J`),
then `I/J ≃ I'/J'` as quotient `R`-modules. -/
noncomputable
def quotientEquiv (I J I' J' : FractionalIdeal R⁰ K)
    (H : I * J' = I' * J) (h : J ≤ I) (h' : J' ≤ I') (hJ' : J' ≠ 0) (hI : I ≠ 0) :
    (I ⧸ J.coeToSubmodule.comap I.coeToSubmodule.subtype) ≃ₗ[R]
      I' ⧸ J'.coeToSubmodule.comap I'.coeToSubmodule.subtype := by
  haveI : J' ⊓ spanSingleton R⁰ (I'.divMod I J') * I = spanSingleton R⁰ (I'.divMod I J') * J := by
    have := FractionalIdeal.sup_mul_inf J' (spanSingleton R⁰ (I'.divMod I J') * I)
    rwa [FractionalIdeal.sup_eq_add, divMod_spec h' hJ' hI, mul_left_comm, mul_comm J' I, H,
      mul_comm I' J, ← mul_assoc, (mul_left_injective₀ _).eq_iff] at this
    rintro rfl
    exact hJ' (by simpa using h')
  refine .ofBijective (Submodule.mapQ _ _ (LinearMap.restrict
    (Algebra.lsmul R _ _ (I'.divMod I J')) ?_) ?_) ⟨?_, ?_⟩
  · intro x hx
    refine (divMod_spec h' hJ' hI).le ?_
    exact Submodule.mem_sup_right (mul_mem_mul (mem_spanSingleton_self _ _) hx)
  · rw [← Submodule.comap_comp, LinearMap.subtype_comp_restrict, LinearMap.domRestrict,
      Submodule.comap_comp]
    refine Submodule.comap_mono ?_
    intro x hx
    refine (Submodule.mem_inf.mp (this.ge ?_)).1
    simp only [val_eq_coe, Algebra.lsmul_coe, smul_eq_mul, mem_coe]
    exact mul_mem_mul (mem_spanSingleton_self _ _) hx
  · rw [← LinearMap.ker_eq_bot, Submodule.mapQ, Submodule.ker_liftQ,
      LinearMap.ker_comp, Submodule.ker_mkQ, ← Submodule.comap_comp,
      LinearMap.subtype_comp_restrict, ← le_bot_iff, Submodule.map_le_iff_le_comap,
      Submodule.comap_bot, Submodule.ker_mkQ, LinearMap.domRestrict,
      Submodule.comap_comp, ← Submodule.map_le_iff_le_comap,
      Submodule.map_comap_eq, Submodule.range_subtype]
    by_cases H' : I'.divMod I J' = 0
    · obtain rfl : J' = I' := by simpa [H'] using divMod_spec h' hJ' hI
      obtain rfl : I = J := mul_left_injective₀ hJ' (H.trans (mul_comm _ _))
      exact inf_le_left
    rw [← inv_mul_eq_iff_eq_mul₀ (by simpa [spanSingleton_eq_zero_iff] using H'), mul_inf₀
      (zero_le _), inv_mul_cancel_left₀ (by simpa [spanSingleton_eq_zero_iff] using H')] at this
    rw [← this, inf_comm, coe_inf]
    refine inf_le_inf ?_ le_rfl
    intro x hx
    rw [spanSingleton_inv]
    convert mul_mem_mul (mem_spanSingleton_self _ _) hx
    simp [H']
  · have H : Submodule.map (Algebra.lsmul R R K (I'.divMod I J')) ↑I =
        (spanSingleton R⁰ (I'.divMod I J') * I) := by
      ext x
      simp [Submodule.mem_span_singleton_mul]
    rw [← LinearMap.range_eq_top, Submodule.mapQ, Submodule.range_liftQ,
      LinearMap.range_comp, LinearMap.restrict, LinearMap.range_codRestrict,
      LinearMap.range_domRestrict, ← top_le_iff, H,
      ← LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _),
      ← Submodule.map_top, Submodule.map_le_iff_le_comap, Submodule.comap_map_eq, Submodule.ker_mkQ,
      ← Submodule.map_le_map_iff_of_injective I'.coeToSubmodule.injective_subtype,
      Submodule.map_top, Submodule.map_sup,
      Submodule.map_comap_eq, Submodule.map_comap_eq, Submodule.range_subtype, sup_comm,
      inf_eq_right.mpr, inf_eq_right.mpr]
    · exact le_trans (divMod_spec h' hJ' hI).ge (by simp)
    · exact le_trans (by simp) (divMod_spec h' hJ' hI).le
    · exact h'

end FractionalIdeal

end div

section primesOver

variable {S : Type*} [CommRing S] [Algebra S R] [Algebra.IsIntegral S R] [NoZeroSMulDivisors S R]

open IsDedekindDomain Ideal.IsDedekindDomain HeightOneSpectrum

/--
If `p` is a maximal ideal, then the lift of `p` in an extension is the product of the primes
over `p` to the power the ramification index.
-/
theorem Ideal.map_algebraMap_eq_finset_prod_pow {p : Ideal S} [p.IsMaximal] (hp : p ≠ 0) :
    map (algebraMap S R) p = ∏ P ∈ p.primesOver R, P ^ p.ramificationIdx (algebraMap S R) P := by
  classical
  have h : map (algebraMap S R) p ≠ 0 := map_ne_bot_of_ne_bot hp
  rw [← finprod_heightOneSpectrum_factorization (I := p.map (algebraMap S R)) h]
  let hF : Fintype {v : HeightOneSpectrum R | v.asIdeal ∣ map (algebraMap S R) p} :=
    (finite_factors h).fintype
  rw [finprod_eq_finset_prod_of_mulSupport_subset
    (s := {v | v.asIdeal ∣ p.map (algebraMap S R)}.toFinset), ← Finset.prod_set_coe,
    ← Finset.prod_set_coe]
  · let _ : Fintype {v : HeightOneSpectrum R // v.asIdeal ∣ map (algebraMap S R) p} := hF
    refine Fintype.prod_equiv (equivPrimesOver _ hp) _ _ fun ⟨v, _⟩ ↦ ?_
    simp [maxPowDividing_eq_pow_multiset_count _ h,
      ramificationIdx_eq_factors_count h v.isPrime v.ne_bot]
  · intro v hv
    simpa [maxPowDividing, Function.mem_mulSupport, IsPrime.ne_top _,
      Associates.count_ne_zero_iff_dvd h (irreducible v)] using hv

end primesOver
