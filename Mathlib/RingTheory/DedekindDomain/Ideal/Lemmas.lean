/-
Copyright (c) 2020 Kenji Nakagawa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenji Nakagawa, Anne Baanen, Filippo A. E. Nuccio
-/
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.ChainOfDivisors
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.OrderIso

/-!
# Dedekind domains and ideals

In this file, we prove some results on the unique factorization monoid structure of the ideals.
The unique factorization of ideals and invertibility of fractional ideals can be found in
`Mathlib/RingTheory/DedekindDomain/Ideal/Basic.lean`.

## Main definitions

- `IsDedekindDomain.HeightOneSpectrum` defines the type of nonzero prime ideals of `R`.

## Implementation notes

Often, definitions assume that Dedekind domains are not fields. We found it more practical
to add a `(h : ¬ IsField A)` assumption whenever this is explicitly needed.

## References

* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

dedekind domain, dedekind ring
-/

variable (R A K : Type*) [CommRing R] [CommRing A] [Field K]

open scoped nonZeroDivisors Polynomial

section Inverse

variable [Algebra A K] [IsFractionRing A K]

variable {A K}

namespace FractionalIdeal

open Ideal

theorem exists_notMem_one_of_ne_bot [IsDedekindDomain A] {I : Ideal A} (hI0 : I ≠ ⊥)
    (hI1 : I ≠ ⊤) : ∃ x ∈ (I⁻¹ : FractionalIdeal A⁰ K), x ∉ (1 : FractionalIdeal A⁰ K) :=
  Set.not_subset.1 <| not_inv_le_one_of_ne_bot hI0 hI1

@[deprecated (since := "2025-05-23")]
alias exists_not_mem_one_of_ne_bot := exists_notMem_one_of_ne_bot

theorem mul_left_strictMono [IsDedekindDomain A] {I : FractionalIdeal A⁰ K} (hI : I ≠ 0) :
    StrictMono (I * ·) :=
  strictMono_of_le_iff_le fun _ _ => (mul_left_le_iff hI).symm

end FractionalIdeal

end Inverse

section IsDedekindDomain

variable {R A}
variable [IsDedekindDomain A] [Algebra A K] [IsFractionRing A K]

open FractionalIdeal

open Ideal

@[simp]
theorem Ideal.dvd_span_singleton {I : Ideal A} {x : A} : I ∣ Ideal.span {x} ↔ x ∈ I :=
  Ideal.dvd_iff_le.trans (Ideal.span_le.trans Set.singleton_subset_iff)

theorem Ideal.isPrime_of_prime {P : Ideal A} (h : Prime P) : IsPrime P := by
  refine ⟨?_, fun hxy => ?_⟩
  · rintro rfl
    rw [← Ideal.one_eq_top] at h
    exact h.not_unit isUnit_one
  · simp only [← Ideal.dvd_span_singleton, ← Ideal.span_singleton_mul_span_singleton] at hxy ⊢
    exact h.dvd_or_dvd hxy

theorem Ideal.prime_of_isPrime {P : Ideal A} (hP : P ≠ ⊥) (h : IsPrime P) : Prime P := by
  refine ⟨hP, mt Ideal.isUnit_iff.mp h.ne_top, fun I J hIJ => ?_⟩
  simpa only [Ideal.dvd_iff_le] using h.mul_le.mp (Ideal.le_of_dvd hIJ)

/-- In a Dedekind domain, the (nonzero) prime elements of the monoid with zero `Ideal A`
are exactly the prime ideals. -/
theorem Ideal.prime_iff_isPrime {P : Ideal A} (hP : P ≠ ⊥) : Prime P ↔ IsPrime P :=
  ⟨Ideal.isPrime_of_prime, Ideal.prime_of_isPrime hP⟩

/-- In a Dedekind domain, the prime ideals are the zero ideal together with the prime elements
of the monoid with zero `Ideal A`. -/
theorem Ideal.isPrime_iff_bot_or_prime {P : Ideal A} : IsPrime P ↔ P = ⊥ ∨ Prime P :=
  ⟨fun hp => (eq_or_ne P ⊥).imp_right fun hp0 => Ideal.prime_of_isPrime hp0 hp, fun hp =>
    hp.elim (fun h => h.symm ▸ Ideal.bot_prime) Ideal.isPrime_of_prime⟩

@[simp]
theorem Ideal.prime_span_singleton_iff {a : A} : Prime (Ideal.span {a}) ↔ Prime a := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [Set.singleton_zero, span_zero, ← Ideal.zero_eq_bot, ← not_iff_not]
    simp only [not_prime_zero, not_false_eq_true]
  · have ha' : span {a} ≠ ⊥ := by simpa only [ne_eq, span_singleton_eq_bot] using ha
    rw [Ideal.prime_iff_isPrime ha', Ideal.span_singleton_prime ha]

open Submodule.IsPrincipal in
theorem Ideal.prime_generator_of_prime {P : Ideal A} (h : Prime P) [P.IsPrincipal] :
    Prime (generator P) :=
  have : Ideal.IsPrime P := Ideal.isPrime_of_prime h
  prime_generator_of_isPrime _ h.ne_zero

open UniqueFactorizationMonoid in
nonrec theorem Ideal.mem_normalizedFactors_iff {p I : Ideal A} (hI : I ≠ ⊥) :
    p ∈ normalizedFactors I ↔ p.IsPrime ∧ I ≤ p := by
  rw [← Ideal.dvd_iff_le]
  by_cases hp : p = 0
  · rw [← zero_eq_bot] at hI
    simp only [hp, zero_notMem_normalizedFactors, zero_dvd_iff, hI, false_iff, not_and,
      not_false_eq_true, implies_true]
  · rwa [mem_normalizedFactors_iff hI, prime_iff_isPrime]

variable (A) in
open UniqueFactorizationMonoid in
theorem Ideal.mem_primesOver_iff_mem_normalizedFactors {p : Ideal R} [h : p.IsMaximal]
    [Algebra R A] [NoZeroSMulDivisors R A] (hp : p ≠ ⊥) {P : Ideal A} :
    P ∈ p.primesOver A ↔ P ∈ normalizedFactors (Ideal.map (algebraMap R A) p) := by
  rw [primesOver, Set.mem_setOf_eq, mem_normalizedFactors_iff (map_ne_bot_of_ne_bot hp),
    liesOver_iff, under_def, and_congr_right_iff, map_le_iff_le_comap]
  intro hP
  refine ⟨fun h ↦ le_of_eq h, fun h' ↦ ((IsCoatom.le_iff_eq (isMaximal_def.mp h) ?_).mp h').symm⟩
  exact comap_ne_top (algebraMap R A) (IsPrime.ne_top hP)

theorem Ideal.pow_right_strictAnti (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) :
    StrictAnti (I ^ · : ℕ → Ideal A) :=
  strictAnti_nat_of_succ_lt fun e =>
    Ideal.dvdNotUnit_iff_lt.mp ⟨pow_ne_zero _ hI0, I, mt isUnit_iff.mp hI1, pow_succ I e⟩

theorem Ideal.pow_lt_self (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) (he : 2 ≤ e) :
    I ^ e < I := by
  convert I.pow_right_strictAnti hI0 hI1 he
  dsimp only
  rw [pow_one]

theorem Ideal.exists_mem_pow_notMem_pow_succ (I : Ideal A) (hI0 : I ≠ ⊥) (hI1 : I ≠ ⊤) (e : ℕ) :
    ∃ x ∈ I ^ e, x ∉ I ^ (e + 1) :=
  SetLike.exists_of_lt (I.pow_right_strictAnti hI0 hI1 e.lt_succ_self)

@[deprecated (since := "2025-05-23")]
alias Ideal.exists_mem_pow_not_mem_pow_succ := Ideal.exists_mem_pow_notMem_pow_succ

open UniqueFactorizationMonoid

theorem Ideal.eq_prime_pow_of_succ_lt_of_le {P I : Ideal A} [P_prime : P.IsPrime] (hP : P ≠ ⊥)
    {i : ℕ} (hlt : P ^ (i + 1) < I) (hle : I ≤ P ^ i) : I = P ^ i := by
  refine le_antisymm hle ?_
  have P_prime' := Ideal.prime_of_isPrime hP P_prime
  have h1 : I ≠ ⊥ := (lt_of_le_of_lt bot_le hlt).ne'
  have := pow_ne_zero i hP
  have h3 := pow_ne_zero (i + 1) hP
  rw [← Ideal.dvdNotUnit_iff_lt, dvdNotUnit_iff_normalizedFactors_lt_normalizedFactors h1 h3,
    normalizedFactors_pow, normalizedFactors_irreducible P_prime'.irreducible,
    Multiset.nsmul_singleton, Multiset.lt_replicate_succ] at hlt
  rw [← Ideal.dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors, normalizedFactors_pow,
    normalizedFactors_irreducible P_prime'.irreducible, Multiset.nsmul_singleton]
  all_goals assumption

theorem Ideal.pow_succ_lt_pow {P : Ideal A} [P_prime : P.IsPrime] (hP : P ≠ ⊥) (i : ℕ) :
    P ^ (i + 1) < P ^ i :=
  lt_of_le_of_ne (Ideal.pow_le_pow_right (Nat.le_succ _))
    (mt (pow_inj_of_not_isUnit (mt Ideal.isUnit_iff.mp P_prime.ne_top) hP).mp i.succ_ne_self)

theorem Associates.le_singleton_iff (x : A) (n : ℕ) (I : Ideal A) :
    Associates.mk I ^ n ≤ Associates.mk (Ideal.span {x}) ↔ x ∈ I ^ n := by
  simp_rw [← Associates.dvd_eq_le, ← Associates.mk_pow, Associates.mk_dvd_mk,
    Ideal.dvd_span_singleton]

variable {K}

lemma FractionalIdeal.le_inv_comm {I J : FractionalIdeal A⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I ≤ J⁻¹ ↔ J ≤ I⁻¹ := by
  rw [inv_eq, inv_eq, le_div_iff_mul_le hI, le_div_iff_mul_le hJ, mul_comm]

lemma FractionalIdeal.inv_le_comm {I J : FractionalIdeal A⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) :
    I⁻¹ ≤ J ↔ J⁻¹ ≤ I := by
  simpa using le_inv_comm (A := A) (K := K) (inv_ne_zero hI) (inv_ne_zero hJ)

open FractionalIdeal


/-- Strengthening of `IsLocalization.exist_integer_multiples`:
Let `J ≠ ⊤` be an ideal in a Dedekind domain `A`, and `f ≠ 0` a finite collection
of elements of `K = Frac(A)`, then we can multiply the elements of `f` by some `a : K`
to find a collection of elements of `A` that is not completely contained in `J`. -/
theorem Ideal.exist_integer_multiples_notMem {J : Ideal A} (hJ : J ≠ ⊤) {ι : Type*} (s : Finset ι)
    (f : ι → K) {j} (hjs : j ∈ s) (hjf : f j ≠ 0) :
    ∃ a : K,
      (∀ i ∈ s, IsLocalization.IsInteger A (a * f i)) ∧
        ∃ i ∈ s, a * f i ∉ (J : FractionalIdeal A⁰ K) := by
  -- Consider the fractional ideal `I` spanned by the `f`s.
  let I : FractionalIdeal A⁰ K := spanFinset A s f
  have hI0 : I ≠ 0 := spanFinset_ne_zero.mpr ⟨j, hjs, hjf⟩
  -- We claim the multiplier `a` we're looking for is in `I⁻¹ \ (J / I)`.
  suffices ↑J / I < I⁻¹ by
    obtain ⟨_, a, hI, hpI⟩ := SetLike.lt_iff_le_and_exists.mp this
    rw [mem_inv_iff hI0] at hI
    refine ⟨a, fun i hi => ?_, ?_⟩
    -- By definition, `a ∈ I⁻¹` multiplies elements of `I` into elements of `1`,
    -- in other words, `a * f i` is an integer.
    · exact (mem_one_iff _).mp (hI (f i) (Submodule.subset_span (Set.mem_image_of_mem f hi)))
    · contrapose! hpI
      -- And if all `a`-multiples of `I` are an element of `J`,
      -- then `a` is actually an element of `J / I`, contradiction.
      refine (mem_div_iff_of_nonzero hI0).mpr fun y hy => Submodule.span_induction ?_ ?_ ?_ ?_ hy
      · rintro _ ⟨i, hi, rfl⟩; exact hpI i hi
      · rw [mul_zero]; exact Submodule.zero_mem _
      · intro x y _ _ hx hy; rw [mul_add]; exact Submodule.add_mem _ hx hy
      · intro b x _ hx; rw [mul_smul_comm]; exact Submodule.smul_mem _ b hx
  -- To show the inclusion of `J / I` into `I⁻¹ = 1 / I`, note that `J < I`.
  calc
    ↑J / I = ↑J * I⁻¹ := div_eq_mul_inv (↑J) I
    _ < 1 * I⁻¹ := mul_right_strictMono (inv_ne_zero hI0) ?_
    _ = I⁻¹ := one_mul _
  rw [← coeIdeal_top]
  -- And multiplying by `I⁻¹` is indeed strictly monotone.
  exact
    strictMono_of_le_iff_le (fun _ _ => (coeIdeal_le_coeIdeal K).symm)
      (lt_top_iff_ne_top.mpr hJ)

@[deprecated (since := "2025-05-23")]
alias Ideal.exist_integer_multiples_not_mem := Ideal.exist_integer_multiples_notMem

lemma Ideal.mul_iInf (I : Ideal A) {ι : Type*} [Nonempty ι] (J : ι → Ideal A) :
    I * ⨅ i, J i = ⨅ i, I * J i := by
  by_cases hI : I = 0
  · simp [hI]
  refine (le_iInf fun i ↦ Ideal.mul_mono_right (iInf_le _ _)).antisymm ?_
  have H : ⨅ i, I * J i ≤ I := (iInf_le _ (Nonempty.some ‹_›)).trans Ideal.mul_le_right
  obtain ⟨K, hK⟩ := Ideal.dvd_iff_le.mpr H
  grw [hK, le_iInf (a := K) fun i ↦ ?_]
  rw [← mul_le_mul_iff_of_pos_left (a := I), ← hK]
  · exact iInf_le _ _
  · exact bot_lt_iff_ne_bot.mpr hI

lemma Ideal.iInf_mul (I : Ideal A) {ι : Type*} [Nonempty ι] (J : ι → Ideal A) :
    (⨅ i, J i) * I = ⨅ i, J i * I := by
  simp only [mul_iInf, mul_comm _ I]

lemma Ideal.mul_inf (I J K : Ideal A) : I * (J ⊓ K) = I * J ⊓ I * K := by
  rw [inf_eq_iInf, Ideal.mul_iInf, inf_eq_iInf]
  congr! 2 with ⟨⟩

lemma Ideal.inf_mul (I J K : Ideal A) : (I ⊓ J) * K = I * K ⊓ J * K := by
  simp only [Ideal.mul_inf, mul_comm _ K]

lemma FractionalIdeal.mul_inf (I J K : FractionalIdeal A⁰ K) : I * (J ⊓ K) = I * J ⊓ I * K :=
  mul_inf₀ (zero_le _) _ _

lemma FractionalIdeal.inf_mul (I J K : FractionalIdeal A⁰ K) : (I ⊓ J) * K = I * K ⊓ J * K :=
  inf_mul₀ (zero_le _) _ _

section Gcd

namespace Ideal

/-! ### GCD and LCM of ideals in a Dedekind domain

We show that the gcd of two ideals in a Dedekind domain is just their supremum,
and the lcm is their infimum, and use this to instantiate `NormalizedGCDMonoid (Ideal A)`.
-/


@[simp]
theorem sup_mul_inf (I J : Ideal A) : (I ⊔ J) * (I ⊓ J) = I * J := by
  letI := UniqueFactorizationMonoid.toNormalizedGCDMonoid (Ideal A)
  have hgcd : gcd I J = I ⊔ J := by
    rw [gcd_eq_normalize _ _, normalize_eq]
    · rw [dvd_iff_le, sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
      exact ⟨gcd_dvd_left _ _, gcd_dvd_right _ _⟩
    · rw [dvd_gcd_iff, dvd_iff_le, dvd_iff_le]
      simp
  have hlcm : lcm I J = I ⊓ J := by
    rw [lcm_eq_normalize _ _, normalize_eq]
    · rw [lcm_dvd_iff, dvd_iff_le, dvd_iff_le]
      simp
    · rw [dvd_iff_le, le_inf_iff, ← dvd_iff_le, ← dvd_iff_le]
      exact ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩
  rw [← hgcd, ← hlcm, associated_iff_eq.mp (gcd_mul_lcm _ _)]

/-- Ideals in a Dedekind domain have gcd and lcm operators that (trivially) are compatible with
the normalization operator. -/
noncomputable instance : NormalizedGCDMonoid (Ideal A) :=
  { Ideal.normalizationMonoid with
    gcd := (· ⊔ ·)
    gcd_dvd_left := fun _ _ => by simpa only [dvd_iff_le] using le_sup_left
    gcd_dvd_right := fun _ _ => by simpa only [dvd_iff_le] using le_sup_right
    dvd_gcd := by
      simp only [dvd_iff_le]
      exact fun h1 h2 => @sup_le (Ideal A) _ _ _ _ h1 h2
    lcm := (· ⊓ ·)
    lcm_zero_left := fun _ => by simp only [zero_eq_bot, bot_inf_eq]
    lcm_zero_right := fun _ => by simp only [zero_eq_bot, inf_bot_eq]
    gcd_mul_lcm := fun _ _ => by rw [associated_iff_eq, sup_mul_inf]
    normalize_gcd := fun _ _ => normalize_eq _
    normalize_lcm := fun _ _ => normalize_eq _ }

-- In fact, any lawful gcd and lcm would equal sup and inf respectively.
@[simp]
theorem gcd_eq_sup (I J : Ideal A) : gcd I J = I ⊔ J := rfl

@[simp]
theorem lcm_eq_inf (I J : Ideal A) : lcm I J = I ⊓ J := rfl

theorem isCoprime_iff_gcd {I J : Ideal A} : IsCoprime I J ↔ gcd I J = 1 := by
  rw [Ideal.isCoprime_iff_codisjoint, codisjoint_iff, one_eq_top, gcd_eq_sup]

theorem factors_span_eq {p : K[X]} : factors (span {p}) = (factors p).map (fun q ↦ span {q}) := by
  rcases eq_or_ne p 0 with rfl | hp; · simpa [Set.singleton_zero] using normalizedFactors_zero
  have : ∀ q ∈ (factors p).map (fun q ↦ span {q}), Prime q := fun q hq ↦ by
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hq
    exact prime_span_singleton_iff.mpr <| prime_of_factor r hr
  rw [← span_singleton_eq_span_singleton.mpr (factors_prod hp), ← multiset_prod_span_singleton,
    factors_eq_normalizedFactors, normalizedFactors_prod_of_prime this]

lemma _root_.FractionalIdeal.sup_mul_inf (I J : FractionalIdeal A⁰ K) :
    (I ⊓ J) * (I ⊔ J) = I * J := by
  apply mul_left_injective₀ (b := spanSingleton A⁰ (algebraMap A K
    (I.den.1 * I.den.1 * J.den.1 * J.den.1))) (by simp [spanSingleton_eq_zero_iff])
  have := Ideal.sup_mul_inf (Ideal.span {J.den.1} * I.num) (Ideal.span {I.den.1} * J.num)
  simp only [← coeIdeal_inj (K := K), coeIdeal_mul, coeIdeal_sup, coeIdeal_inf,
    ← den_mul_self_eq_num', coeIdeal_span_singleton] at this
  rw [mul_left_comm, ← mul_add, ← mul_add, ← mul_inf₀ (FractionalIdeal.zero_le _),
    ← mul_inf₀ (FractionalIdeal.zero_le _)] at this
  simp only [FractionalIdeal.sup_eq_add, _root_.map_mul, ← spanSingleton_mul_spanSingleton]
  convert this using 1 <;> ring

end Ideal

end Gcd

end IsDedekindDomain

section IsDedekindDomain

variable {T : Type*} [CommRing T] [IsDedekindDomain T] {I J : Ideal T}

open Multiset UniqueFactorizationMonoid Ideal

theorem prod_normalizedFactors_eq_self (hI : I ≠ ⊥) : (normalizedFactors I).prod = I :=
  associated_iff_eq.1 (prod_normalizedFactors hI)

theorem count_le_of_ideal_ge [DecidableEq (Ideal T)]
    {I J : Ideal T} (h : I ≤ J) (hI : I ≠ ⊥) (K : Ideal T) :
    count K (normalizedFactors J) ≤ count K (normalizedFactors I) :=
  le_iff_count.1 ((dvd_iff_normalizedFactors_le_normalizedFactors (ne_bot_of_le_ne_bot hI h) hI).1
    (dvd_iff_le.2 h))
    _

theorem sup_eq_prod_inf_factors [DecidableEq (Ideal T)] (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    I ⊔ J = (normalizedFactors I ∩ normalizedFactors J).prod := by
  have H : normalizedFactors (normalizedFactors I ∩ normalizedFactors J).prod =
      normalizedFactors I ∩ normalizedFactors J := by
    apply normalizedFactors_prod_of_prime
    intro p hp
    rw [mem_inter] at hp
    exact prime_of_normalized_factor p hp.left
  have := Multiset.prod_ne_zero_of_prime (normalizedFactors I ∩ normalizedFactors J) fun _ h =>
      prime_of_normalized_factor _ (Multiset.mem_inter.1 h).1
  apply le_antisymm
  · rw [sup_le_iff, ← dvd_iff_le, ← dvd_iff_le]
    constructor
    · rw [dvd_iff_normalizedFactors_le_normalizedFactors this hI, H]
      exact inf_le_left
    · rw [dvd_iff_normalizedFactors_le_normalizedFactors this hJ, H]
      exact inf_le_right
  · rw [← dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors,
      normalizedFactors_prod_of_prime, le_iff_count]
    · intro a
      rw [Multiset.count_inter]
      exact le_min (count_le_of_ideal_ge le_sup_left hI a) (count_le_of_ideal_ge le_sup_right hJ a)
    · intro p hp
      rw [mem_inter] at hp
      exact prime_of_normalized_factor p hp.left
    · exact ne_bot_of_le_ne_bot hI le_sup_left
    · exact this

theorem irreducible_pow_sup [DecidableEq (Ideal T)] (hI : I ≠ ⊥) (hJ : Irreducible J) (n : ℕ) :
    J ^ n ⊔ I = J ^ min ((normalizedFactors I).count J) n := by
  rw [sup_eq_prod_inf_factors (pow_ne_zero n hJ.ne_zero) hI, min_comm,
    normalizedFactors_of_irreducible_pow hJ, normalize_eq J, replicate_inter, prod_replicate]

theorem irreducible_pow_sup_of_le (hJ : Irreducible J) (n : ℕ) (hn : n ≤ emultiplicity J I) :
    J ^ n ⊔ I = J ^ n := by
  classical
  by_cases hI : I = ⊥
  · simp_all
  rw [irreducible_pow_sup hI hJ, min_eq_right]
  rw [emultiplicity_eq_count_normalizedFactors hJ hI, normalize_eq J] at hn
  exact_mod_cast hn

theorem irreducible_pow_sup_of_ge (hI : I ≠ ⊥) (hJ : Irreducible J) (n : ℕ)
    (hn : emultiplicity J I ≤ n) : J ^ n ⊔ I = J ^ multiplicity J I := by
  classical
  rw [irreducible_pow_sup hI hJ, min_eq_left]
  · congr
    rw [← Nat.cast_inj (R := ℕ∞), ← FiniteMultiplicity.emultiplicity_eq_multiplicity,
      emultiplicity_eq_count_normalizedFactors hJ hI, normalize_eq J]
    rw [← emultiplicity_lt_top]
    apply hn.trans_lt
    simp
  · rw [emultiplicity_eq_count_normalizedFactors hJ hI, normalize_eq J] at hn
    exact_mod_cast hn

theorem Ideal.eq_prime_pow_mul_coprime [DecidableEq (Ideal T)] {I : Ideal T} (hI : I ≠ ⊥)
    (P : Ideal T) [hpm : P.IsMaximal] :
    ∃ Q : Ideal T, P ⊔ Q = ⊤ ∧ I = P ^ (Multiset.count P (normalizedFactors I)) * Q := by
  use (filter (¬ P = ·) (normalizedFactors I)).prod
  constructor
  · refine P.sup_multiset_prod_eq_top (fun p hpi ↦ ?_)
    have hp : Prime p := prime_of_normalized_factor p (filter_subset _ (normalizedFactors I) hpi)
    exact hpm.coprime_of_ne ((isPrime_of_prime hp).isMaximal hp.ne_zero) (of_mem_filter hpi)
  · nth_rw 1 [← prod_normalizedFactors_eq_self hI, ← filter_add_not (P = ·) (normalizedFactors I)]
    rw [prod_add, pow_count]

end IsDedekindDomain

/-!
### Height one spectrum of a Dedekind domain
If `R` is a Dedekind domain of Krull dimension 1, the maximal ideals of `R` are exactly its nonzero
prime ideals.
We define `HeightOneSpectrum` and provide lemmas to recover the facts that prime ideals of height
one are prime and irreducible.
-/


namespace IsDedekindDomain

variable [IsDedekindDomain R]

/-- The height one prime spectrum of a Dedekind domain `R` is the type of nonzero prime ideals of
`R`. Note that this equals the maximal spectrum if `R` has Krull dimension 1. -/
@[ext, nolint unusedArguments]
structure HeightOneSpectrum where
  asIdeal : Ideal R
  isPrime : asIdeal.IsPrime
  ne_bot : asIdeal ≠ ⊥

attribute [instance] HeightOneSpectrum.isPrime

variable (v : HeightOneSpectrum R) {R}

namespace HeightOneSpectrum

instance isMaximal : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot

theorem prime : Prime v.asIdeal := Ideal.prime_of_isPrime v.ne_bot v.isPrime

/--
The (nonzero) prime elements of the monoid with zero `Ideal R` correspond
to an element of type `HeightOneSpectrum R`.

See `IsDedekindDomain.HeightOneSpectrum.prime` for the inverse direction. -/
@[simps]
def ofPrime {p : Ideal R} (hp : Prime p) : HeightOneSpectrum R :=
  ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩

theorem irreducible : Irreducible v.asIdeal :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mpr v.prime

theorem associates_irreducible : Irreducible <| Associates.mk v.asIdeal :=
  Associates.irreducible_mk.mpr v.irreducible

/-- An equivalence between the height one and maximal spectra for rings of Krull dimension 1. -/
def equivMaximalSpectrum (hR : ¬IsField R) : HeightOneSpectrum R ≃ MaximalSpectrum R where
  toFun v := ⟨v.asIdeal, v.isPrime.isMaximal v.ne_bot⟩
  invFun v :=
    ⟨v.asIdeal, v.isMaximal.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField v.isMaximal hR⟩

/-- An ideal of `R` is not the whole ring if and only if it is contained in an element of
`HeightOneSpectrum R` -/
theorem ideal_ne_top_iff_exists (hR : ¬IsField R) (I : Ideal R) :
    I ≠ ⊤ ↔ ∃ P : HeightOneSpectrum R, I ≤ P.asIdeal := by
  rw [Ideal.ne_top_iff_exists_maximal]
  constructor
  · rintro ⟨M, hMmax, hIM⟩
    exact ⟨(equivMaximalSpectrum hR).symm ⟨M, hMmax⟩, hIM⟩
  · rintro ⟨P, hP⟩
    exact ⟨((equivMaximalSpectrum hR) P).asIdeal, ((equivMaximalSpectrum hR) P).isMaximal, hP⟩

variable (R)

/-- A Dedekind domain is equal to the intersection of its localizations at all its height one
non-zero prime ideals viewed as subalgebras of its field of fractions. -/
theorem iInf_localization_eq_bot [Algebra R K] [hK : IsFractionRing R K] :
    (⨅ v : HeightOneSpectrum R,
        Localization.subalgebra.ofField K _ v.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  ext x
  rw [Algebra.mem_iInf]
  constructor
  on_goal 1 => by_cases hR : IsField R
  · rcases Function.bijective_iff_has_inverse.mp
      (IsField.localization_map_bijective (Rₘ := K) (flip nonZeroDivisors.ne_zero rfl : 0 ∉ R⁰) hR)
      with ⟨algebra_map_inv, _, algebra_map_right_inv⟩
    exact fun _ => Algebra.mem_bot.mpr ⟨algebra_map_inv x, algebra_map_right_inv x⟩
  all_goals rw [← MaximalSpectrum.iInf_localization_eq_bot, Algebra.mem_iInf]
  · exact fun hx ⟨v, hv⟩ => hx ((equivMaximalSpectrum hR).symm ⟨v, hv⟩)
  · exact fun hx ⟨v, hv, hbot⟩ => hx ⟨v, hv.isMaximal hbot⟩

end HeightOneSpectrum

end IsDedekindDomain

section

open Ideal

variable {R A}
variable [IsDedekindDomain A] {I : Ideal R} {J : Ideal A}

/-- The map from ideals of `R` dividing `I` to the ideals of `A` dividing `J` induced by
  a homomorphism `f : R/I →+* A/J` -/
@[simps]
def idealFactorsFunOfQuotHom {f : R ⧸ I →+* A ⧸ J} (hf : Function.Surjective f) :
    {p : Ideal R // p ∣ I} →o {p : Ideal A // p ∣ J} where
  toFun X := ⟨comap (Ideal.Quotient.mk J) (map f (map (Ideal.Quotient.mk I) X)), by
    have : RingHom.ker (Ideal.Quotient.mk J) ≤
        comap (Ideal.Quotient.mk J) (map f (map (Ideal.Quotient.mk I) X)) :=
      ker_le_comap (Ideal.Quotient.mk J)
    rw [mk_ker] at this
    exact dvd_iff_le.mpr this⟩
  monotone' := by
    rintro ⟨X, hX⟩ ⟨Y, hY⟩ h
    rw [← Subtype.coe_le_coe, Subtype.coe_mk, Subtype.coe_mk] at h ⊢
    rw [Subtype.coe_mk, comap_le_comap_iff_of_surjective (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective, map_le_iff_le_comap, Subtype.coe_mk,
      comap_map_of_surjective _ hf (map (Ideal.Quotient.mk I) Y)]
    suffices map (Ideal.Quotient.mk I) X ≤ map (Ideal.Quotient.mk I) Y by
      exact le_sup_of_le_left this
    rwa [map_le_iff_le_comap, comap_map_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot, mk_ker,
      sup_eq_left.mpr <| le_of_dvd hY]

@[simp]
theorem idealFactorsFunOfQuotHom_id :
    idealFactorsFunOfQuotHom (RingHom.id (A ⧸ J)).surjective = OrderHom.id :=
  OrderHom.ext _ _
    (funext fun X => by
      simp only [idealFactorsFunOfQuotHom, map_id, OrderHom.coe_mk, OrderHom.id_coe, id,
        comap_map_of_surjective (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective, ←
        RingHom.ker_eq_comap_bot (Ideal.Quotient.mk J), mk_ker,
        sup_eq_left.mpr (dvd_iff_le.mp X.prop), Subtype.coe_eta])

variable {B : Type*} [CommRing B] [IsDedekindDomain B] {L : Ideal B}

theorem idealFactorsFunOfQuotHom_comp {f : R ⧸ I →+* A ⧸ J} {g : A ⧸ J →+* B ⧸ L}
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    (idealFactorsFunOfQuotHom hg).comp (idealFactorsFunOfQuotHom hf) =
      idealFactorsFunOfQuotHom (show Function.Surjective (g.comp f) from hg.comp hf) := by
  refine OrderHom.ext _ _ (funext fun x => ?_)
  rw [idealFactorsFunOfQuotHom, idealFactorsFunOfQuotHom, OrderHom.comp_coe, OrderHom.coe_mk,
    OrderHom.coe_mk, Function.comp_apply, idealFactorsFunOfQuotHom, OrderHom.coe_mk,
    Subtype.mk_eq_mk, Subtype.coe_mk, map_comap_of_surjective (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective, map_map]

variable [IsDedekindDomain R] (f : R ⧸ I ≃+* A ⧸ J)

/-- The bijection between ideals of `R` dividing `I` and the ideals of `A` dividing `J` induced by
  an isomorphism `f : R/I ≅ A/J`. -/
def idealFactorsEquivOfQuotEquiv : { p : Ideal R | p ∣ I } ≃o { p : Ideal A | p ∣ J } := by
  have f_surj : Function.Surjective (f : R ⧸ I →+* A ⧸ J) := f.surjective
  have fsym_surj : Function.Surjective (f.symm : A ⧸ J →+* R ⧸ I) := f.symm.surjective
  refine OrderIso.ofHomInv (idealFactorsFunOfQuotHom f_surj) (idealFactorsFunOfQuotHom fsym_surj)
    ?_ ?_
  · have := idealFactorsFunOfQuotHom_comp fsym_surj f_surj
    simp only [RingEquiv.comp_symm, idealFactorsFunOfQuotHom_id] at this
    rw [← this, OrderHom.coe_eq, OrderHom.coe_eq]
  · have := idealFactorsFunOfQuotHom_comp f_surj fsym_surj
    simp only [RingEquiv.symm_comp, idealFactorsFunOfQuotHom_id] at this
    rw [← this, OrderHom.coe_eq, OrderHom.coe_eq]

theorem idealFactorsEquivOfQuotEquiv_symm :
    (idealFactorsEquivOfQuotEquiv f).symm = idealFactorsEquivOfQuotEquiv f.symm := rfl

theorem idealFactorsEquivOfQuotEquiv_is_dvd_iso {L M : Ideal R} (hL : L ∣ I) (hM : M ∣ I) :
    (idealFactorsEquivOfQuotEquiv f ⟨L, hL⟩ : Ideal A) ∣ idealFactorsEquivOfQuotEquiv f ⟨M, hM⟩ ↔
      L ∣ M := by
  suffices
    idealFactorsEquivOfQuotEquiv f ⟨M, hM⟩ ≤ idealFactorsEquivOfQuotEquiv f ⟨L, hL⟩ ↔
      (⟨M, hM⟩ : { p : Ideal R | p ∣ I }) ≤ ⟨L, hL⟩
    by rw [dvd_iff_le, dvd_iff_le, Subtype.coe_le_coe, this, Subtype.mk_le_mk]
  exact (idealFactorsEquivOfQuotEquiv f).le_iff_le

open UniqueFactorizationMonoid

theorem idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors (hJ : J ≠ ⊥)
    {L : Ideal R} (hL : L ∈ normalizedFactors I) :
    ↑(idealFactorsEquivOfQuotEquiv f ⟨L, dvd_of_mem_normalizedFactors hL⟩)
      ∈ normalizedFactors J := by
  have hI : I ≠ ⊥ := by
    intro hI
    rw [hI, bot_eq_zero, normalizedFactors_zero, ← Multiset.empty_eq_zero] at hL
    exact Finset.notMem_empty _ hL
  refine mem_normalizedFactors_factor_dvd_iso_of_mem_normalizedFactors hI hJ hL
    (d := (idealFactorsEquivOfQuotEquiv f).toEquiv) ?_
  rintro ⟨l, hl⟩ ⟨l', hl'⟩
  rw [Subtype.coe_mk, Subtype.coe_mk]
  apply idealFactorsEquivOfQuotEquiv_is_dvd_iso f

/-- The bijection between the sets of normalized factors of I and J induced by a ring
isomorphism `f : R/I ≅ A/J`. -/
def normalizedFactorsEquivOfQuotEquiv (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    { L : Ideal R | L ∈ normalizedFactors I } ≃ { M : Ideal A | M ∈ normalizedFactors J } where
  toFun j :=
    ⟨idealFactorsEquivOfQuotEquiv f ⟨↑j, dvd_of_mem_normalizedFactors j.prop⟩,
      idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors f hJ j.prop⟩
  invFun j :=
    ⟨(idealFactorsEquivOfQuotEquiv f).symm ⟨↑j, dvd_of_mem_normalizedFactors j.prop⟩, by
      rw [idealFactorsEquivOfQuotEquiv_symm]
      exact
        idealFactorsEquivOfQuotEquiv_mem_normalizedFactors_of_mem_normalizedFactors f.symm hI
          j.prop⟩
  left_inv := fun ⟨j, hj⟩ => by simp
  right_inv := fun ⟨j, hj⟩ => by simp [-Set.coe_setOf]

@[simp]
theorem normalizedFactorsEquivOfQuotEquiv_symm (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    (normalizedFactorsEquivOfQuotEquiv f hI hJ).symm =
      normalizedFactorsEquivOfQuotEquiv f.symm hJ hI := rfl

/-- The map `normalizedFactorsEquivOfQuotEquiv` preserves multiplicities. -/
theorem normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (L : Ideal R) (hL : L ∈ normalizedFactors I) :
    emultiplicity (↑(normalizedFactorsEquivOfQuotEquiv f hI hJ ⟨L, hL⟩)) J = emultiplicity L I := by
  rw [normalizedFactorsEquivOfQuotEquiv, Equiv.coe_fn_mk, Subtype.coe_mk]
  refine emultiplicity_factor_dvd_iso_eq_emultiplicity_of_mem_normalizedFactors hI hJ hL
    (d := (idealFactorsEquivOfQuotEquiv f).toEquiv) ?_
  exact fun ⟨l, hl⟩ ⟨l', hl'⟩ => idealFactorsEquivOfQuotEquiv_is_dvd_iso f hl hl'

end

section ChineseRemainder

open Ideal UniqueFactorizationMonoid

variable {R}

theorem Ring.DimensionLeOne.prime_le_prime_iff_eq [Ring.DimensionLEOne R] {P Q : Ideal R}
    [hP : P.IsPrime] [hQ : Q.IsPrime] (hP0 : P ≠ ⊥) : P ≤ Q ↔ P = Q :=
  ⟨(hP.isMaximal hP0).eq_of_le hQ.ne_top, Eq.le⟩

section DedekindDomain

variable [IsDedekindDomain R]

theorem Ideal.IsPrime.mul_mem_pow (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : ℕ}
    (h : a * b ∈ I ^ n) : a ∈ I ∨ b ∈ I ^ n := by
  cases n; · simp
  by_cases hI0 : I = ⊥; · simpa [pow_succ, hI0] using h
  simp only [← Submodule.span_singleton_le_iff_mem, Ideal.submodule_span_eq, ← Ideal.dvd_iff_le, ←
    Ideal.span_singleton_mul_span_singleton] at h ⊢
  by_cases ha : I ∣ span {a}
  · exact Or.inl ha
  rw [mul_comm] at h
  exact Or.inr (Prime.pow_dvd_of_dvd_mul_right ((Ideal.prime_iff_isPrime hI0).mpr hI) _ ha h)

theorem Ideal.IsPrime.mem_pow_mul (I : Ideal R) [hI : I.IsPrime] {a b : R} {n : ℕ}
    (h : a * b ∈ I ^ n) : a ∈ I ^ n ∨ b ∈ I := by
  rw [mul_comm] at h
  rw [or_comm]
  exact Ideal.IsPrime.mul_mem_pow _ h

section

theorem Ideal.count_normalizedFactors_eq {p x : Ideal R} [hp : p.IsPrime] {n : ℕ} (hle : x ≤ p ^ n)
    [DecidableEq (Ideal R)] (hlt : ¬x ≤ p ^ (n + 1)) : (normalizedFactors x).count p = n :=
  count_normalizedFactors_eq' ((Ideal.isPrime_iff_bot_or_prime.mp hp).imp_right Prime.irreducible)
    (normalize_eq _) (Ideal.dvd_iff_le.mpr hle) (mt Ideal.le_of_dvd hlt)

/-- The number of times an ideal `I` occurs as normalized factor of another ideal `J` is stable
when regarding these ideals as associated elements of the monoid of ideals. -/
theorem count_associates_factors_eq [DecidableEq (Ideal R)] [DecidableEq <| Associates (Ideal R)]
    [∀ (p : Associates <| Ideal R), Decidable (Irreducible p)]
    {I J : Ideal R} (hI : I ≠ 0) (hJ : J.IsPrime) (hJ₀ : J ≠ ⊥) :
    (Associates.mk J).count (Associates.mk I).factors = Multiset.count J (normalizedFactors I) := by
  replace hI : Associates.mk I ≠ 0 := Associates.mk_ne_zero.mpr hI
  have hJ' : Irreducible (Associates.mk J) := by
    simpa only [Associates.irreducible_mk] using (Ideal.prime_of_isPrime hJ₀ hJ).irreducible
  apply (Ideal.count_normalizedFactors_eq (p := J) (x := I) _ _).symm
  all_goals
    rw [← Ideal.dvd_iff_le, ← Associates.mk_dvd_mk, Associates.mk_pow]
    simp only [Associates.dvd_eq_le]
    rw [Associates.prime_pow_dvd_iff_le hI hJ']
  cutsat

/-- Variant of `UniqueFactorizationMonoid.count_normalizedFactors_eq` for associated Ideals. -/
theorem Ideal.count_associates_eq [DecidableEq (Associates (Ideal R))]
    [∀ (p : Associates <| Ideal R), Decidable (Irreducible p)]
    {a a₀ x : R} {n : ℕ} (hx : Prime x) (ha : ¬x ∣ a) (heq : a₀ = x ^ n * a) :
    (Associates.mk (span {x})).count (Associates.mk (span {a₀})).factors = n := by
  have hx0 : x ≠ 0 := Prime.ne_zero hx
  classical
  rw [count_associates_factors_eq, UniqueFactorizationMonoid.count_normalizedFactors_eq]
  · exact (prime_span_singleton_iff.mpr hx).irreducible
  · exact normalize_eq _
  · simp only [span_singleton_pow, heq, dvd_span_singleton]
    exact Ideal.mul_mem_right _ _ (mem_span_singleton_self (x ^ n))
  · simp only [span_singleton_pow, heq, dvd_span_singleton, mem_span_singleton]
    rw [pow_add, pow_one, mul_dvd_mul_iff_left (pow_ne_zero n hx0)]
    exact ha
  · simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot]
    aesop
  · exact (span_singleton_prime hx0).mpr hx
  · simp only [ne_eq, span_singleton_eq_bot]; exact hx0

/-- Variant of `UniqueFactorizationMonoid.count_normalizedFactors_eq` for associated Ideals. -/
theorem Ideal.count_associates_eq' [DecidableEq (Associates (Ideal R))]
    [∀ (p : Associates <| Ideal R), Decidable (Irreducible p)]
    {a x : R} (hx : Prime x) {n : ℕ} (hle : x ^ n ∣ a) (hlt : ¬x ^ (n + 1) ∣ a) :
    (Associates.mk (span {x})).count (Associates.mk (span {a})).factors = n := by
  obtain ⟨q, hq⟩ := hle
  apply Ideal.count_associates_eq hx _ hq
  contrapose! hlt with hdvd
  obtain ⟨q', hq'⟩ := hdvd
  use q'
  rw [hq, hq']
  ring

end

theorem Ideal.le_mul_of_no_prime_factors {I J K : Ideal R}
    (coprime : ∀ P, J ≤ P → K ≤ P → ¬IsPrime P) (hJ : I ≤ J) (hK : I ≤ K) : I ≤ J * K := by
  simp only [← Ideal.dvd_iff_le] at coprime hJ hK ⊢
  by_cases hJ0 : J = 0
  · simpa only [hJ0, zero_mul] using hJ
  obtain ⟨I', rfl⟩ := hK
  rw [mul_comm]
  refine mul_dvd_mul_left K
    (UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors (b := K) hJ0 ?_ hJ)
  exact fun hPJ hPK => mt Ideal.isPrime_of_prime (coprime _ hPJ hPK)

/-- The intersection of distinct prime powers in a Dedekind domain is the product of these
prime powers. -/
theorem IsDedekindDomain.inf_prime_pow_eq_prod {ι : Type*} (s : Finset ι) (f : ι → Ideal R)
    (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (f i))
    (coprime : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → f i ≠ f j) :
    (s.inf fun i => f i ^ e i) = ∏ i ∈ s, f i ^ e i := by
  letI := Classical.decEq ι
  revert prime coprime
  refine s.induction ?_ ?_
  · simp
  intro a s ha ih prime coprime
  specialize
    ih (fun i hi => prime i (Finset.mem_insert_of_mem hi)) fun i hi j hj =>
      coprime i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj)
  rw [Finset.inf_insert, Finset.prod_insert ha, ih]
  refine le_antisymm (Ideal.le_mul_of_no_prime_factors ?_ inf_le_left inf_le_right) Ideal.mul_le_inf
  intro P hPa hPs hPp
  obtain ⟨b, hb, hPb⟩ := hPp.prod_le.mp hPs
  haveI := Ideal.isPrime_of_prime (prime a (Finset.mem_insert_self a s))
  haveI := Ideal.isPrime_of_prime (prime b (Finset.mem_insert_of_mem hb))
  refine coprime a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb) ?_ ?_
  · exact (ne_of_mem_of_not_mem hb ha).symm
  · refine ((Ring.DimensionLeOne.prime_le_prime_iff_eq ?_).mp (hPp.le_of_pow_le hPa)).trans
      ((Ring.DimensionLeOne.prime_le_prime_iff_eq ?_).mp (hPp.le_of_pow_le hPb)).symm
    · exact (prime a (Finset.mem_insert_self a s)).ne_zero
    · exact (prime b (Finset.mem_insert_of_mem hb)).ne_zero

/-- **Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i, P i ^ e i`, then `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`. -/
noncomputable def IsDedekindDomain.quotientEquivPiOfProdEq {ι : Type*} [Fintype ι] (I : Ideal R)
    (P : ι → Ideal R) (e : ι → ℕ) (prime : ∀ i, Prime (P i))
    (coprime : Pairwise fun i j => P i ≠ P j)
    (prod_eq : ∏ i, P i ^ e i = I) : R ⧸ I ≃+* ∀ i, R ⧸ P i ^ e i :=
  (Ideal.quotEquivOfEq
    (by
      simp only [← prod_eq, Finset.inf_eq_iInf, Finset.mem_univ, ciInf_pos,
        ← IsDedekindDomain.inf_prime_pow_eq_prod _ _ _ (fun i _ => prime i)
        (coprime.set_pairwise _)])).trans <|
    Ideal.quotientInfRingEquivPiQuotient _ fun i j hij => Ideal.coprime_of_no_prime_ge <| by
      intro P hPi hPj hPp
      haveI := Ideal.isPrime_of_prime (prime i)
      haveI := Ideal.isPrime_of_prime (prime j)
      exact coprime hij <| ((Ring.DimensionLeOne.prime_le_prime_iff_eq (prime i).ne_zero).mp
        (hPp.le_of_pow_le hPi)).trans <| Eq.symm <|
          (Ring.DimensionLeOne.prime_le_prime_iff_eq (prime j).ne_zero).mp (hPp.le_of_pow_le hPj)

open scoped Classical in
/-- **Chinese remainder theorem** for a Dedekind domain: `R ⧸ I` factors as `Π i, R ⧸ (P i ^ e i)`,
where `P i` ranges over the prime factors of `I` and `e i` over the multiplicities. -/
noncomputable def IsDedekindDomain.quotientEquivPiFactors {I : Ideal R} (hI : I ≠ ⊥) :
    R ⧸ I ≃+* ∀ P : (factors I).toFinset, R ⧸ (P : Ideal R) ^ (Multiset.count ↑P (factors I)) :=
  IsDedekindDomain.quotientEquivPiOfProdEq _ _ _
    (fun P : (factors I).toFinset => prime_of_factor _ (Multiset.mem_toFinset.mp P.prop))
    (fun _ _ hij => Subtype.coe_injective.ne hij)
    (calc
      (∏ P : (factors I).toFinset, (P : Ideal R) ^ (factors I).count (P : Ideal R)) =
          ∏ P ∈ (factors I).toFinset, P ^ (factors I).count P :=
        (factors I).toFinset.prod_coe_sort fun P => P ^ (factors I).count P
      _ = ((factors I).map fun P => P).prod := (Finset.prod_multiset_map_count (factors I) id).symm
      _ = (factors I).prod := by rw [Multiset.map_id']
      _ = I := associated_iff_eq.mp (factors_prod hI)
      )

@[simp]
theorem IsDedekindDomain.quotientEquivPiFactors_mk {I : Ideal R} (hI : I ≠ ⊥) (x : R) :
    IsDedekindDomain.quotientEquivPiFactors hI (Ideal.Quotient.mk I x) = fun _P =>
      Ideal.Quotient.mk _ x := rfl

/-- **Chinese remainder theorem** for a Dedekind domain: if the ideal `I` factors as
`∏ i ∈ s, P i ^ e i`, then `R ⧸ I` factors as `Π (i : s), R ⧸ (P i ^ e i)`.

This is a version of `IsDedekindDomain.quotientEquivPiOfProdEq` where we restrict
the product to a finite subset `s` of a potentially infinite indexing type `ι`.
-/
noncomputable def IsDedekindDomain.quotientEquivPiOfFinsetProdEq {ι : Type*} {s : Finset ι}
    (I : Ideal R) (P : ι → Ideal R) (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (P i))
    (coprime : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → P i ≠ P j)
    (prod_eq : ∏ i ∈ s, P i ^ e i = I) : R ⧸ I ≃+* ∀ i : s, R ⧸ P i ^ e i :=
  IsDedekindDomain.quotientEquivPiOfProdEq I (fun i : s => P i) (fun i : s => e i)
    (fun i => prime i i.2) (fun i j h => coprime i i.2 j j.2 (Subtype.coe_injective.ne h))
    (_root_.trans (Finset.prod_coe_sort s fun i => P i ^ e i) prod_eq)

/-- Corollary of the Chinese remainder theorem: given elements `x i : R / P i ^ e i`,
we can choose a representative `y : R` such that `y ≡ x i (mod P i ^ e i)`. -/
theorem IsDedekindDomain.exists_representative_mod_finset {ι : Type*} {s : Finset ι}
    (P : ι → Ideal R) (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (P i))
    (coprime : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → P i ≠ P j) (x : ∀ i : s, R ⧸ P i ^ e i) :
    ∃ y, ∀ (i) (hi : i ∈ s), Ideal.Quotient.mk (P i ^ e i) y = x ⟨i, hi⟩ := by
  let f := IsDedekindDomain.quotientEquivPiOfFinsetProdEq _ P e prime coprime rfl
  obtain ⟨y, rfl⟩ := f.surjective x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨z, fun i _hi => rfl⟩

/-- Corollary of the Chinese remainder theorem: given elements `x i : R`,
we can choose a representative `y : R` such that `y - x i ∈ P i ^ e i`. -/
theorem IsDedekindDomain.exists_forall_sub_mem_ideal {ι : Type*} {s : Finset ι} (P : ι → Ideal R)
    (e : ι → ℕ) (prime : ∀ i ∈ s, Prime (P i))
    (coprime : ∀ᵉ (i ∈ s) (j ∈ s), i ≠ j → P i ≠ P j) (x : s → R) :
    ∃ y, ∀ (i) (hi : i ∈ s), y - x ⟨i, hi⟩ ∈ P i ^ e i := by
  obtain ⟨y, hy⟩ :=
    IsDedekindDomain.exists_representative_mod_finset P e prime coprime fun i =>
      Ideal.Quotient.mk _ (x i)
  exact ⟨y, fun i hi => Ideal.Quotient.eq.mp (hy i hi)⟩

end DedekindDomain

end ChineseRemainder

section PID

open UniqueFactorizationMonoid Ideal

variable {R}
variable [IsDomain R] [IsPrincipalIdealRing R]

theorem span_singleton_dvd_span_singleton_iff_dvd {a b : R} :
    Ideal.span {a} ∣ Ideal.span ({b} : Set R) ↔ a ∣ b :=
  ⟨fun h => mem_span_singleton.mp (dvd_iff_le.mp h (mem_span_singleton.mpr (dvd_refl b))), fun h =>
    dvd_iff_le.mpr fun _d hd => mem_span_singleton.mpr (dvd_trans h (mem_span_singleton.mp hd))⟩

@[simp]
theorem Ideal.squarefree_span_singleton {a : R} :
    Squarefree (span {a}) ↔ Squarefree a := by
  refine ⟨fun h x hx ↦ ?_, fun h I hI ↦ ?_⟩
  · rw [← span_singleton_dvd_span_singleton_iff_dvd, ← span_singleton_mul_span_singleton] at hx
    simpa using h _ hx
  · rw [← span_singleton_generator I, span_singleton_mul_span_singleton,
      span_singleton_dvd_span_singleton_iff_dvd] at hI
    exact isUnit_iff.mpr <| eq_top_of_isUnit_mem _ (Submodule.IsPrincipal.generator_mem I) (h _ hI)

theorem singleton_span_mem_normalizedFactors_of_mem_normalizedFactors [NormalizationMonoid R]
    {a b : R} (ha : a ∈ normalizedFactors b) :
    Ideal.span ({a} : Set R) ∈ normalizedFactors (Ideal.span ({b} : Set R)) := by
  by_cases hb : b = 0
  · rw [Ideal.span_singleton_eq_bot.mpr hb, bot_eq_zero, normalizedFactors_zero]
    rw [hb, normalizedFactors_zero] at ha
    exact absurd ha (Multiset.notMem_zero a)
  · suffices Prime (Ideal.span ({a} : Set R)) by
      obtain ⟨c, hc, hc'⟩ := exists_mem_normalizedFactors_of_dvd ?_ this.irreducible
          (dvd_iff_le.mpr (span_singleton_le_span_singleton.mpr (dvd_of_mem_normalizedFactors ha)))
      rwa [associated_iff_eq.mp hc']
    · by_contra h
      exact hb (span_singleton_eq_bot.mp h)
    rw [prime_iff_isPrime]
    · exact (span_singleton_prime (prime_of_normalized_factor a ha).ne_zero).mpr
        (prime_of_normalized_factor a ha)
    · by_contra h
      exact (prime_of_normalized_factor a ha).ne_zero (span_singleton_eq_bot.mp h)

theorem emultiplicity_eq_emultiplicity_span {a b : R} :
    emultiplicity (Ideal.span {a}) (Ideal.span ({b} : Set R)) = emultiplicity a b := by
  by_cases h : FiniteMultiplicity a b
  · rw [h.emultiplicity_eq_multiplicity]
    apply emultiplicity_eq_of_dvd_of_not_dvd <;>
      rw [Ideal.span_singleton_pow, span_singleton_dvd_span_singleton_iff_dvd]
    · exact pow_multiplicity_dvd a b
    · apply h.not_pow_dvd_of_multiplicity_lt
      apply lt_add_one
  · suffices ¬FiniteMultiplicity (Ideal.span ({a} : Set R)) (Ideal.span ({b} : Set R)) by
      rw [emultiplicity_eq_top.2 h, emultiplicity_eq_top.2 this]
    exact FiniteMultiplicity.not_iff_forall.mpr fun n => by
      rw [Ideal.span_singleton_pow, span_singleton_dvd_span_singleton_iff_dvd]
      exact FiniteMultiplicity.not_iff_forall.mp h n

section NormalizationMonoid
variable [NormalizationMonoid R]

/-- The bijection between the (normalized) prime factors of `r` and the (normalized) prime factors
of `span {r}` -/
noncomputable def normalizedFactorsEquivSpanNormalizedFactors {r : R} (hr : r ≠ 0) :
    { d : R | d ∈ normalizedFactors r } ≃
      { I : Ideal R | I ∈ normalizedFactors (Ideal.span ({r} : Set R)) } := by
  refine Equiv.ofBijective ?_ ?_
  · exact fun d =>
      ⟨Ideal.span {↑d}, singleton_span_mem_normalizedFactors_of_mem_normalizedFactors d.prop⟩
  · refine ⟨?_, ?_⟩
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ h
      rw [Subtype.mk_eq_mk, Ideal.span_singleton_eq_span_singleton, Subtype.coe_mk,
          Subtype.coe_mk] at h
      exact Subtype.mk_eq_mk.mpr (mem_normalizedFactors_eq_of_associated ha hb h)
    · rintro ⟨i, hi⟩
      have : i.IsPrime := isPrime_of_prime (prime_of_normalized_factor i hi)
      have := exists_mem_normalizedFactors_of_dvd hr
        (Submodule.IsPrincipal.prime_generator_of_isPrime i
        (prime_of_normalized_factor i hi).ne_zero).irreducible ?_
      · obtain ⟨a, ha, ha'⟩ := this
        use ⟨a, ha⟩
        simp only [← span_singleton_eq_span_singleton.mpr ha',
            Ideal.span_singleton_generator]
      · exact (Submodule.IsPrincipal.mem_iff_generator_dvd i).mp
          ((show Ideal.span {r} ≤ i from dvd_iff_le.mp (dvd_of_mem_normalizedFactors hi))
            (mem_span_singleton.mpr (dvd_refl r)))

/-- The bijection `normalizedFactorsEquivSpanNormalizedFactors` between the set of prime
factors of `r` and the set of prime factors of the ideal `⟨r⟩` preserves multiplicities. See
`count_normalizedFactorsSpan_eq_count` for the version stated in terms of multisets `count`. -/
theorem emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity {r d : R}
    (hr : r ≠ 0) (hd : d ∈ normalizedFactors r) :
    emultiplicity d r =
      emultiplicity (normalizedFactorsEquivSpanNormalizedFactors hr ⟨d, hd⟩ : Ideal R)
        (Ideal.span {r}) := by
  simp only [normalizedFactorsEquivSpanNormalizedFactors, emultiplicity_eq_emultiplicity_span,
    Subtype.coe_mk, Equiv.ofBijective_apply]

/-- The bijection `normalized_factors_equiv_span_normalized_factors.symm` between the set of prime
factors of the ideal `⟨r⟩` and the set of prime factors of `r` preserves multiplicities. -/
theorem emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity {r : R}
    (hr : r ≠ 0) (I : { I : Ideal R | I ∈ normalizedFactors (Ideal.span ({r} : Set R)) }) :
    emultiplicity ((normalizedFactorsEquivSpanNormalizedFactors hr).symm I : R) r =
      emultiplicity (I : Ideal R) (Ideal.span {r}) := by
  obtain ⟨x, hx⟩ := (normalizedFactorsEquivSpanNormalizedFactors hr).surjective I
  obtain ⟨a, ha⟩ := x
  rw [hx.symm, Equiv.symm_apply_apply, Subtype.coe_mk,
    emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_emultiplicity hr ha]

variable [DecidableEq R] [DecidableEq (Ideal R)]

/-- The bijection between the set of prime factors of the ideal `⟨r⟩` and the set of prime factors
  of `r` preserves `count` of the corresponding multisets. See
  `multiplicity_normalizedFactorsEquivSpanNormalizedFactors_eq_multiplicity` for the version
  stated in terms of multiplicity. -/
theorem count_span_normalizedFactors_eq {r X : R} (hr : r ≠ 0) (hX : Prime X) :
    Multiset.count (Ideal.span {X} : Ideal R) (normalizedFactors (Ideal.span {r}))  =
        Multiset.count (normalize X) (normalizedFactors r) := by
  have := emultiplicity_eq_emultiplicity_span (R := R) (a := X) (b := r)
  rw [emultiplicity_eq_count_normalizedFactors (Prime.irreducible hX) hr,
    emultiplicity_eq_count_normalizedFactors (Prime.irreducible ?_), normalize_apply,
    normUnit_eq_one, Units.val_one, one_eq_top, mul_top, Nat.cast_inj] at this
  · simp only [normalize_apply, this]
  · simp only [Submodule.zero_eq_bot, ne_eq, span_singleton_eq_bot, hr, not_false_eq_true]
  · simpa only [prime_span_singleton_iff]

theorem count_span_normalizedFactors_eq_of_normUnit {r X : R}
    (hr : r ≠ 0) (hX₁ : normUnit X = 1) (hX : Prime X) :
      Multiset.count (Ideal.span {X} : Ideal R) (normalizedFactors (Ideal.span {r})) =
        Multiset.count X (normalizedFactors r) := by
  simpa [hX₁, normalize_apply] using count_span_normalizedFactors_eq hr hX

end NormalizationMonoid

end PID

section primesOverFinset

open UniqueFactorizationMonoid Ideal

open scoped Classical in
/-- The finite set of all prime factors of the pushforward of `p`. -/
noncomputable abbrev primesOverFinset {A : Type*} [CommRing A] (p : Ideal A) (B : Type*)
    [CommRing B] [IsDedekindDomain B] [Algebra A B] : Finset (Ideal B) :=
  (factors (p.map (algebraMap A B))).toFinset

variable {A : Type*} [CommRing A] {p : Ideal A} (hpb : p ≠ ⊥) [hpm : p.IsMaximal]
  (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra A B] [NoZeroSMulDivisors A B]

include hpb in
theorem coe_primesOverFinset : primesOverFinset p B = primesOver p B := by
  classical
  ext P
  rw [primesOverFinset, factors_eq_normalizedFactors, Finset.mem_coe, Multiset.mem_toFinset]
  exact (P.mem_normalizedFactors_iff (map_ne_bot_of_ne_bot hpb)).trans <| Iff.intro
    (fun ⟨hPp, h⟩ => ⟨hPp, ⟨hpm.eq_of_le (comap_ne_top _ hPp.ne_top) (le_comap_of_map_le h)⟩⟩)
    (fun ⟨hPp, h⟩ => ⟨hPp, map_le_of_le_comap h.1.le⟩)

variable {R} (A) in
theorem IsLocalRing.primesOverFinset_eq [IsLocalRing A] [IsDedekindDomain A]
    [Algebra R A] [FaithfulSMul R A] [Module.Finite R A] {p : Ideal R} [p.IsMaximal] (hp0 : p ≠ ⊥) :
    primesOverFinset p A = {IsLocalRing.maximalIdeal A} := by
  rw [← Finset.coe_eq_singleton, coe_primesOverFinset hp0, IsLocalRing.primesOver_eq A hp0]

namespace IsDedekindDomain.HeightOneSpectrum

/--
The bijection between the elements of the height one prime spectrum of `B` that divide the lift
of the maximal ideal `p` in `B` and the primes over `p` in `B`.
-/
noncomputable def equivPrimesOver (hp : p ≠ 0) :
    {v : HeightOneSpectrum B // v.asIdeal ∣ map (algebraMap A B) p} ≃ p.primesOver B :=
  Set.BijOn.equiv HeightOneSpectrum.asIdeal
    ⟨fun v hv ↦ ⟨v.isPrime, by rwa [liesOver_iff_dvd_map v.isPrime.ne_top]⟩,
    fun _ _ _ _ h ↦ HeightOneSpectrum.ext_iff.mpr h,
    fun Q hQ ↦ ⟨⟨Q, hQ.1, ne_bot_of_mem_primesOver hp hQ⟩,
      (liesOver_iff_dvd_map hQ.1.ne_top).mp hQ.2, rfl⟩⟩

@[simp]
theorem equivPrimesOver_apply (hp : p ≠ 0)
    (v : {v : HeightOneSpectrum B // v.asIdeal ∣ map (algebraMap A B) p}) :
    equivPrimesOver B hp v = v.1.asIdeal := rfl

end IsDedekindDomain.HeightOneSpectrum

variable (p) [Algebra.IsIntegral A B]

theorem primesOver_finite : (primesOver p B).Finite := by
  by_cases hpb : p = ⊥
  · rw [hpb] at hpm ⊢
    haveI : IsDomain A := IsDomain.of_bot_isPrime A
    rw [primesOver_bot A B]
    exact Set.finite_singleton ⊥
  · rw [← coe_primesOverFinset hpb B]
    exact (primesOverFinset p B).finite_toSet

noncomputable instance : Fintype (p.primesOver B) := Set.Finite.fintype (primesOver_finite p B)

theorem primesOver_ncard_ne_zero : (primesOver p B).ncard ≠ 0 := by
  rcases exists_ideal_liesOver_maximal_of_isIntegral p B with ⟨P, hPm, hp⟩
  exact Set.ncard_ne_zero_of_mem ⟨hPm.isPrime, hp⟩ (primesOver_finite p B)

theorem one_le_primesOver_ncard : 1 ≤ (primesOver p B).ncard :=
  Nat.one_le_iff_ne_zero.mpr (primesOver_ncard_ne_zero p B)

end primesOverFinset
