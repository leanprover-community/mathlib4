/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.DedekindDomain.Ideal

#align_import ring_theory.dedekind_domain.factorization from "leanprover-community/mathlib"@"2f588be38bb5bec02f218ba14f82fc82eb663f87"

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

## Implementation notes
Since we are only interested in the factorization of nonzero fractional ideals, we define
`val_v(0) = 0` so that every `val_v` is in `ℤ` and we can avoid having to use `WithTop ℤ`.

## Tags
dedekind domain, fractional ideal, ideal, factorization
-/

noncomputable section

open scoped Classical nonZeroDivisors

open Set Function UniqueFactorizationMonoid IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
  Classical

variable {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ### Factorization of ideals of Dedekind domains -/

variable [IsDedekindDomain R] (v : HeightOneSpectrum R)

/-- Given a maximal ideal `v` and an ideal `I` of `R`, `maxPowDividing` returns the maximal
  power of `v` dividing `I`. -/
def IsDedekindDomain.HeightOneSpectrum.maxPowDividing (I : Ideal R) : Ideal R :=
  v.asIdeal ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors
#align is_dedekind_domain.height_one_spectrum.max_pow_dividing IsDedekindDomain.HeightOneSpectrum.maxPowDividing

/-- Only finitely many maximal ideals of `R` divide a given nonzero ideal. -/
theorem Ideal.finite_factors {I : Ideal R} (hI : I ≠ 0) :
    {v : HeightOneSpectrum R | v.asIdeal ∣ I}.Finite := by
  rw [← Set.finite_coe_iff, Set.coe_setOf]
  haveI h_fin := fintypeSubtypeDvd I hI
  refine
    Finite.of_injective (fun v => (⟨(v : HeightOneSpectrum R).asIdeal, v.2⟩ : { x // x ∣ I })) ?_
  intro v w hvw
  simp? at hvw says simp only [Subtype.mk.injEq] at hvw
  exact Subtype.coe_injective ((HeightOneSpectrum.ext_iff (R := R) ↑v ↑w).mpr hvw)
#align ideal.finite_factors Ideal.finite_factors

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
#align associates.finite_factors Associates.finite_factors

namespace Ideal

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
#align ideal.finite_mul_support Ideal.finite_mulSupport

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^(val_v(I))`, regarded as a fractional ideal, is not `(1)`. -/
theorem finite_mulSupport_coe {I : Ideal R} (hI : I ≠ 0) :
    (mulSupport fun v : HeightOneSpectrum R => (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ)).Finite := by
  rw [mulSupport]
  simp_rw [Ne, zpow_natCast, ← FractionalIdeal.coeIdeal_pow, FractionalIdeal.coeIdeal_eq_one]
  exact finite_mulSupport hI
#align ideal.finite_mul_support_coe Ideal.finite_mulSupport_coe

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^-(val_v(I))` is not the unit ideal. -/
theorem finite_mulSupport_inv {I : Ideal R} (hI : I ≠ 0) :
    (mulSupport fun v : HeightOneSpectrum R => (v.asIdeal : FractionalIdeal R⁰ K) ^
      (-((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ))).Finite := by
  rw [mulSupport]
  simp_rw [zpow_neg, Ne, inv_eq_one]
  exact finite_mulSupport_coe hI
#align ideal.finite_mul_support_inv Ideal.finite_mulSupport_inv

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
  exact (Finset.mem_erase.mp hw).1 (HeightOneSpectrum.ext w v (Eq.symm hvw))
#align ideal.finprod_not_dvd Ideal.finprod_not_dvd

end Ideal

theorem Associates.finprod_ne_zero (I : Ideal R) :
    Associates.mk (∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I) ≠ 0 := by
  rw [Associates.mk_ne_zero, finprod_def]
  split_ifs
  · rw [Finset.prod_ne_zero_iff]
    intro v _
    apply pow_ne_zero _ v.ne_bot
  · exact one_ne_zero
#align associates.finprod_ne_zero Associates.finprod_ne_zero

namespace Ideal

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
#align ideal.finprod_count Ideal.finprod_count

/-- The ideal `I` equals the finprod `∏_v v^(val_v(I))`. -/
theorem finprod_heightOneSpectrum_factorization {I : Ideal R} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I = I := by
  rw [← associated_iff_eq, ← Associates.mk_eq_mk_iff_associated]
  apply Associates.eq_of_eq_counts
  · apply Associates.finprod_ne_zero I
  · apply Associates.mk_ne_zero.mpr hI
  intro v hv
  obtain ⟨J, hJv⟩ := Associates.exists_rep v
  rw [← hJv, Associates.irreducible_mk] at hv
  rw [← hJv]
  apply Ideal.finprod_count
    ⟨J, Ideal.isPrime_of_prime (irreducible_iff_prime.mp hv), Irreducible.ne_zero hv⟩ I hI
#align ideal.finprod_height_one_spectrum_factorization Ideal.finprod_heightOneSpectrum_factorization

variable (K)

/-- The ideal `I` equals the finprod `∏_v v^(val_v(I))`, when both sides are regarded as fractional
ideals of `R`. -/
theorem finprod_heightOneSpectrum_factorization_coe {I : Ideal R} (hI : I ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ)) = I := by
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  rw [FractionalIdeal.coeIdeal_finprod R⁰ K (le_refl _)]
  simp_rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, FractionalIdeal.coeIdeal_pow,
    zpow_natCast]
#align ideal.finprod_height_one_spectrum_factorization_coe Ideal.finprod_heightOneSpectrum_factorization_coe

end Ideal

/-! ### Factorization of fractional ideals of Dedekind domains -/

namespace FractionalIdeal

open Int IsLocalization

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
    rw [← hnd, h, IsFractionRing.mk'_eq_div, _root_.map_zero,
      zero_div, spanSingleton_zero] at hk
    exact hI hk
  rw [finprod_heightOneSpectrum_factorization_principal_fraction hn0 d, hk, hnd]

variable (K)

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

lemma count_ne_zero {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    count K v I = ((Associates.mk v.asIdeal).count (Associates.mk
      (choose (choose_spec (exists_eq_spanSingleton_mul I)))).factors -
      (Associates.mk v.asIdeal).count
        (Associates.mk (Ideal.span {choose (exists_eq_spanSingleton_mul I)})).factors : ℤ) := by
  simp only [count, dif_neg hI]

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
  rw [count, dif_neg hI, sub_eq_sub_iff_add_eq_add, ← ofNat_add, ← ofNat_add, natCast_inj,
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
theorem count_mul' (I I' : FractionalIdeal R⁰ K) :
    count K v (I * I') = if I ≠ 0 ∧ I' ≠ 0 then count K v I + count K v I' else 0 := by
  split_ifs with h
  · exact count_mul K v h.1 h.2
  · push_neg at h
    by_cases hI : I = 0
    · rw [hI, MulZeroClass.zero_mul, count, dif_pos (Eq.refl _)]
    · rw [h hI, MulZeroClass.mul_zero, count, dif_pos (Eq.refl _)]

/-- val_v(1) = 0. -/
theorem count_one : count K v (1 : FractionalIdeal R⁰ K) = 0 := by
  have h1 : (1 : FractionalIdeal R⁰ K) =
      spanSingleton R⁰ ((algebraMap R K) 1)⁻¹ * ↑(1 : Ideal R) := by
    rw [(algebraMap R K).map_one, Ideal.one_eq_top, coeIdeal_top, mul_one, inv_one,
      spanSingleton_one]
  rw [count_well_defined K v one_ne_zero h1, Ideal.span_singleton_one, Ideal.one_eq_top, sub_self]

theorem count_prod {ι} (s : Finset ι) (I : ι → FractionalIdeal R⁰ K) (hS : ∀ i ∈ s, I i ≠ 0) :
    count K v (∏ i ∈ s, I i) = ∑ i ∈ s, count K v (I i) := by
  induction' s using Finset.induction with i s hi hrec
  · rw [Finset.prod_empty, Finset.sum_empty, count_one]
  · have hS' : ∀ i ∈ s, I i ≠ 0 := fun j hj => hS j (Finset.mem_insert_of_mem hj)
    have hS0 : ∏ i ∈ s, I i ≠ 0 := Finset.prod_ne_zero_iff.mpr hS'
    have hi0 : I i ≠ 0 := hS i (Finset.mem_insert_self i s)
    rw [Finset.prod_insert hi, Finset.sum_insert hi, count_mul K v hi0 hS0, hrec hS']

/-- For every `n ∈ ℕ` and every ideal `I`, `val_v(I^n) = n*val_v(I)`. -/
theorem count_pow (n : ℕ) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ n) = n * count K v I := by
  induction' n with n h
  · rw [pow_zero, ofNat_zero, MulZeroClass.zero_mul, count_one]
  · rw [pow_succ, count_mul']
    by_cases hI : I = 0
    · have h_neg : ¬(I ^ n ≠ 0 ∧ I ≠ 0) := by
        rw [not_and', not_not, ne_eq]
        intro h
        exact absurd hI h
      rw [if_neg h_neg, hI, count_zero, MulZeroClass.mul_zero]
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
  rw [count_well_defined K v hv h_self, Associates.count_self hv_irred, Ideal.span_singleton_one,
    ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one, Associates.count_zero hv_irred,
    ofNat_zero, sub_zero, ofNat_one]

/-- `val_v(v^n) = n` for every `n ∈ ℕ`. -/
theorem count_pow_self (n : ℕ) :
    count K v ((v.asIdeal : FractionalIdeal R⁰ K) ^ n) = n := by
  rw [count_pow, count_self, mul_one]

/-- `val_v(I⁻ⁿ) = -val_v(Iⁿ)` for every `n ∈ ℤ`. -/
theorem count_neg_zpow (n : ℤ) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ (-n)) = - count K v (I ^ n) := by
  by_cases hI : I = 0
  · by_cases hn : n = 0
    · rw [hn, neg_zero, zpow_zero, count_one, neg_zero]
    · rw [hI, zero_zpow n hn, zero_zpow (-n) (neg_ne_zero.mpr hn), count_zero, neg_zero]
  · rw [eq_neg_iff_add_eq_zero, ← count_mul K v (zpow_ne_zero _ hI) (zpow_ne_zero _ hI),
      ← zpow_add₀ hI, neg_add_self, zpow_zero]
    exact count_one K v

theorem count_inv  (I : FractionalIdeal R⁰ K) :
    count K v (I⁻¹) = - count K v I := by
  rw [← zpow_neg_one, count_neg_zpow K v (1 : ℤ) I, zpow_one]

/-- `val_v(Iⁿ) = n*val_v(I)` for every `n ∈ ℤ`. -/
theorem count_zpow (n : ℤ) (I : FractionalIdeal R⁰ K) :
    count K v (I ^ n) = n * count K v I := by
  cases' n with n
  · rw [ofNat_eq_coe, zpow_natCast]
    exact count_pow K v n I
  · rw [negSucc_coe, count_neg_zpow, zpow_natCast, count_pow]
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
  rw [count_well_defined K v hw_ne_zero hw_fact, Ideal.span_singleton_one, ← Ideal.one_eq_top,
    Associates.mk_one, Associates.factors_one, Associates.count_zero hv, ofNat_zero, sub_zero,
    natCast_eq_zero, ← pow_one (Associates.mk w.asIdeal), Associates.factors_prime_pow hw',
    Associates.count_some hv, Multiset.replicate_one, Multiset.count_eq_zero,
    Multiset.mem_singleton]
  simp only [Subtype.mk.injEq]
  rw [Associates.mk_eq_mk_iff_associated, associated_iff_eq, ← HeightOneSpectrum.ext_iff]
  exact Ne.symm hw

theorem count_maximal (w : HeightOneSpectrum R) :
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
    by_cases h : I ≠ 0 ∧ I' ≠ 0
    · rw [count_mul' K v, if_pos h, hI, hI', add_zero]
    · rw [count_mul' K v, if_neg h]
  · intro w hw
    rw [count_zpow, count_maximal_coprime K v hw, MulZeroClass.mul_zero]

theorem count_finsupp_prod (exps : HeightOneSpectrum R →₀ ℤ) :
    count K v (exps.prod (HeightOneSpectrum.asIdeal · ^ ·)) = exps v := by
  rw [Finsupp.prod, count_prod]
  · simp only [count_zpow, count_maximal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      exps.mem_support_iff, ne_eq, ite_not, ite_eq_right_iff, @eq_comm ℤ 0, imp_self]
  · exact fun v hv ↦ zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)

/-- If `exps` is finitely supported, then `val_v(∏_w w^{exps w}) = exps v`. -/
theorem count_finprod (exps : HeightOneSpectrum R → ℤ)
    (h_exps : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, exps v = 0) :
    count K v (∏ᶠ v : HeightOneSpectrum R,
      (v.asIdeal : FractionalIdeal R⁰ K) ^ exps v) = exps v := by
  convert count_finsupp_prod K v (Finsupp.mk h_exps.toFinset exps (fun _ ↦ h_exps.mem_toFinset))
  rw [finprod_eq_finset_prod_of_mulSupport_subset (s := h_exps.toFinset), Finsupp.prod]
  · rfl
  · rw [Finite.coe_toFinset]
    intro v hv h
    rw [mem_mulSupport, h, zpow_zero] at hv
    exact hv (Eq.refl 1)

theorem count_coe {J : Ideal R} (hJ : J ≠ 0) :
    count K v J = (Associates.mk v.asIdeal).count (Associates.mk J).factors := by
  rw [count_well_defined K (J := J) (a := 1), Ideal.span_singleton_one, sub_eq_self,
    Nat.cast_eq_zero, ← Ideal.one_eq_top, Associates.mk_one, Associates.factors_one,
    Associates.count_zero v.associates_irreducible]
  · simpa only [ne_eq, coeIdeal_eq_zero]
  · simp only [_root_.map_one, inv_one, spanSingleton_one, one_mul]

theorem count_coe_nonneg (J : Ideal R) : 0 ≤ count K v J := by
  by_cases hJ : J = 0
  · simp only [hJ, Submodule.zero_eq_bot, coeIdeal_bot, count_zero, le_refl]
  · simp only [count_coe K v hJ, Nat.cast_nonneg]

theorem count_mono {I J} (hI : I ≠ 0) (h : I ≤ J) : count K v J ≤ count K v I := by
  by_cases hJ : J = 0
  · exact (hI (FractionalIdeal.le_zero_iff.mp (h.trans hJ.le))).elim
  have := FractionalIdeal.mul_le_mul_left h J⁻¹
  rw [inv_mul_cancel hJ, FractionalIdeal.le_one_iff_exists_coeIdeal] at this
  obtain ⟨J', hJ'⟩ := this
  rw [← mul_inv_cancel_left₀ hJ I, ← hJ', count_mul K v hJ, le_add_iff_nonneg_right]
  · exact count_coe_nonneg K v J'
  · exact hJ' ▸ mul_ne_zero (inv_ne_zero hJ) hI

/-- If `I` is a nonzero fractional ideal, then `I` is equal to the product `∏_v v^(count K v I)`. -/
theorem finprod_heightOneSpectrum_factorization' {I : FractionalIdeal R⁰ K} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ (count K v I) = I := by
  have h := (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
  conv_rhs => rw [← finprod_heightOneSpectrum_factorization hI h]
  apply finprod_congr
  intro w
  apply congr_arg
  rw [count_ne_zero K w hI]

variable {K}

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
    by_contra h_nmem
    rw [mem_union, mem_setOf_eq, mem_setOf_eq] at h_nmem
    push_neg at h_nmem
    rw [← Associates.count_ne_zero_iff_dvd ha_ne_zero hv_irred, not_not,
      ← Associates.count_ne_zero_iff_dvd hJ_ne_zero hv_irred, not_not] at h_nmem
    rw [mem_setOf_eq, h_nmem.1, h_nmem.2, sub_self] at hv
    exact hv (Eq.refl 0)
  exact Finite.subset (Finite.union (Ideal.finite_factors (ideal_factor_ne_zero hI haJ))
    (Ideal.finite_factors (constant_factor_ne_zero hI haJ))) h_subset

/-- `val_v(I) = 0` for all but finitely many maximal ideals of `R`. -/
theorem finite_factors (I : FractionalIdeal R⁰ K) :
    ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, count K v I = 0 := by
  by_cases hI : I = 0
  · simp only [hI, count_zero, Filter.eventually_cofinite, not_true_eq_false, setOf_false,
      finite_empty]
  · convert finite_factors' hI (choose_spec (choose_spec (exists_eq_spanSingleton_mul I))).2
    rw [count_ne_zero K _ hI]

end FractionalIdeal
