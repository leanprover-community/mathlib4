/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
import Mathlib.RingTheory.DedekindDomain.Ideal

#align_import ring_theory.dedekind_domain.factorization from "leanprover-community/mathlib"@"2f588be38bb5bec02f218ba14f82fc82eb663f87"

/-!
# Factorization of ideals of Dedekind domains
Every nonzero ideal `I` of a Dedekind domain `R` can be factored as a product `∏_v v^{n_v}` over the
maximal ideals of `R`, where the exponents `n_v` are natural numbers.
TODO: Extend the results in this file to fractional ideals of `R`.
## Main results
- `Ideal.finite_factors` : Only finitely many maximal ideals of `R` divide a given nonzero ideal.
- `Ideal.finprod_heightOneSpectrum_factorization` : The ideal `I` equals the finprod
  `∏_v v^(val_v(I))`, where `val_v(I)` denotes the multiplicity of `v` in the factorization of `I`
  and `v` runs over the maximal ideals of `R`.
## Tags
dedekind domain, ideal, factorization
-/


noncomputable section

open scoped BigOperators Classical nonZeroDivisors

open Set Function UniqueFactorizationMonoid IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

/-! ### Factorization of ideals of Dedekind domains -/


variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

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
  refine'
    Finite.of_injective (fun v => (⟨(v : HeightOneSpectrum R).asIdeal, v.2⟩ : { x // x ∣ I })) _
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
    simp_rw [Int.coe_nat_eq_zero]
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
      rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, Int.coe_nat_eq_zero.mp h_zero,
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
  simp_rw [Ne.def, zpow_ofNat, ← FractionalIdeal.coeIdeal_pow, FractionalIdeal.coeIdeal_eq_one]
  exact finite_mulSupport hI
#align ideal.finite_mul_support_coe Ideal.finite_mulSupport_coe

/-- For every nonzero ideal `I` of `v`, there are finitely many maximal ideals `v` such that
`v^-(val_v(I))` is not the unit ideal. -/
theorem finite_mulSupport_inv {I : Ideal R} (hI : I ≠ 0) :
    (mulSupport fun v : HeightOneSpectrum R => (v.asIdeal : FractionalIdeal R⁰ K) ^
      (-((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ))).Finite := by
  rw [mulSupport]
  simp_rw [zpow_neg, Ne.def, inv_eq_one]
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
theorem finprod_heightOneSpectrum_factorization (I : Ideal R) (hI : I ≠ 0) :
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

/-- The ideal `I` equals the finprod `∏_v v^(val_v(I))`, when both sides are regarded as fractional
ideals of `R`. -/
theorem finprod_heightOneSpectrum_factorization_coe (I : Ideal R) (hI : I ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^
      ((Associates.mk v.asIdeal).count (Associates.mk I).factors : ℤ)) = I := by
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization I hI]
  rw [FractionalIdeal.coeIdeal_finprod R⁰ K (le_refl _)]
  simp_rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, FractionalIdeal.coeIdeal_pow,
    zpow_ofNat]
#align ideal.finprod_height_one_spectrum_factorization_coe Ideal.finprod_heightOneSpectrum_factorization_coe

end Ideal
