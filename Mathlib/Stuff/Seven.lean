import Mathlib.Stuff.Inertia
import Mathlib.Stuff.Factorization
import Mathlib.NumberTheory.Cyclotomic.PID
import Mathlib.Tactic

set_option linter.style.header false

open NumberField Module NumberField.InfinitePlace Nat Real RingOfIntegers Finset Multiset
  IsCyclotomicExtension.Rat Polynomial cyclotomic UniqueFactorizationMonoid

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

theorem PNat.prime_seven : (7 : ℕ+).Prime :=
  Nat.prime_seven

instance Nat.fact_prime_seven : Fact (Nat.Prime 7) :=
  ⟨prime_seven⟩

instance PNat.fact_prime_seven : Fact (7 : ℕ+).Prime :=
  ⟨prime_seven⟩

lemma crazy7 : ⌊(4 / π) ^ 3 * (6! / 6 ^ 6 * √16807)⌋₊ = 4 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 3 * (6! / 6 ^ 6 * √16807) := by
        gcongr; exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 3 * (6! / 6 ^ 6 * 129) := by
        gcongr; exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 4 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 3 * (6! / 6 ^ 6 * √16807) := by
        gcongr; exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 3 * (6! / 6 ^ 6 * 130) := by
        gcongr; exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ _ := by norm_num

variable [IsCyclotomicExtension {7} ℚ K]

theorem M7 : ⌊(M K)⌋₊ = 4 := by
  rw [absdiscr_prime 7 K, IsCyclotomicExtension.finrank (n := 7) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 7, totient_prime
      PNat.prime_seven]
  simp only [PNat.val_ofNat, Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg,
    Int.reducePow, reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact crazy7

theorem cyclotomic_7 : cyclotomic 7 ℤ = 1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 := by
  simp [cyclotomic_prime, sum_range_succ]

namespace IsCyclotomicExtension.Rat.seven

instance : IsGalois ℚ K := isGalois 7 ℚ K

local notation3 "θ" => (zeta_spec 7 ℚ K).toInteger

lemma exponent : exponent θ = 1 := by
  simp [exponent_eq_one_iff, ← ((zeta_spec 7 ℚ K).integralPowerBasis').adjoin_gen_eq_top]

lemma ne_dvd_exponent (p : ℕ) (hp : 1 < p := by norm_num) : ¬ (p ∣ RingOfIntegers.exponent θ) := by
  rw [exponent, dvd_one]
  omega

lemma minpoly : minpoly ℤ θ = cyclotomic 7 ℤ := by
  have := cyclotomic_eq_minpoly (zeta_spec 7 ℚ K) (by norm_num)
  rw [PNat.val_ofNat, ← (zeta_spec 7 ℚ K).coe_toInteger] at this
  simpa [this] using (minpoly.algebraMap_eq RingOfIntegers.coe_injective θ).symm

section factors

namespace two

local notation3 "poly" => (X ^ 3 + X ^ 2 + 1 : (ZMod 2)[X])

lemma dvd : poly ∣ cyclotomic 7 (ZMod 2) := by
  refine ⟨X ^ 3 + X + 1, ?_,⟩
  rw [← map_cyclotomic_int, cyclotomic_7]
  refine stupid _ ⟨X ^ 3, X ^ 3 + X ^ 2 + 1, X ^ 3 + X + 1, by simp, by simp, ?_⟩
  ring

lemma monic : Monic poly := by
  monicity!

lemma natDegree : natDegree poly = 3 := by
  compute_degree!

lemma irreducible : Irreducible poly := by
  refine baz (f := 1) (p := 2) (by simp) (by rw [pow_one]; decide) dvd ?_
  symm
  rw [natDegree, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun n hnlt hnpos ↦ ?_⟩
  have : n ∈ Finset.Ioo 0 3 := by simp [hnpos, hnlt]
  fin_cases this <;> decide

lemma fact_mem : poly ∈ monicFactorsMod θ 2 := by
  simp only [Finset.mem_coe, minpoly, map_cyclotomic, mem_toFinset]
  obtain ⟨P, hPmem, hPass⟩ :=
    exists_mem_normalizedFactors_of_dvd (cyclotomic_ne_zero 7 (ZMod 2)) irreducible dvd
  convert hPmem
  refine eq_of_monic_of_associated monic ?_ hPass
  rw [← normalize_normalized_factor _ hPmem]
  refine monic_normalize (prime_of_normalized_factor _ hPmem).ne_zero

end two

namespace three

local notation3 "poly" => (X ^ 6 + X^5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1 : (ZMod 3)[X])

lemma dvd : poly ∣ cyclotomic 7 (ZMod 3) := by
  refine ⟨1, ?_,⟩
  rw [← map_cyclotomic_int, cyclotomic_7]
  refine stupid _ ⟨0, X ^ 6 + X^5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1, 1, by simp, by simp, ?_⟩
  ring

lemma monic : Monic poly := by
  monicity!

lemma natDegree : natDegree poly = 6 := by
  compute_degree!

lemma irreducible : Irreducible poly := by
  refine baz (f := 1) (p := 3) (by simp) (by rw [pow_one]; decide) dvd ?_
  symm
  rw [natDegree, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun n hnlt hnpos ↦ ?_⟩
  have : n ∈ Finset.Ioo 0 6 := by simp [hnpos, hnlt]
  fin_cases this <;> decide

lemma fact_mem : poly ∈ monicFactorsMod θ 3 := by
  simp only [Finset.mem_coe, minpoly, map_cyclotomic, mem_toFinset]
  obtain ⟨P, hPmem, hPass⟩ :=
    exists_mem_normalizedFactors_of_dvd (cyclotomic_ne_zero 7 (ZMod 3)) irreducible dvd
  convert hPmem
  refine eq_of_monic_of_associated monic ?_ hPass
  rw [← normalize_normalized_factor _ hPmem]
  refine monic_normalize (prime_of_normalized_factor _ hPmem).ne_zero

end three

end factors

theorem pid : IsPrincipalIdealRing (𝓞 K) := by
  apply
    isPrincipalIdealRing_of_isPrincipal_of_pow_inertiaDeg_le_of_mem_primesOver_of_mem_Icc.Galois
  rw [M7]
  intro p hp Hp
  fin_cases hp; any_goals norm_num at Hp
  · let f := Ideal.primesOverSpanEquivMonicFactorsMod (K := K) (ne_dvd_exponent 2)
    refine ⟨_, (f.symm ⟨_, two.fact_mem⟩).2, ?_⟩
    left
    rw [Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' (ne_dvd_exponent _)
      two.fact_mem, two.natDegree]
    norm_num
  · let f := Ideal.primesOverSpanEquivMonicFactorsMod (K := K) (ne_dvd_exponent 3)
    refine ⟨_, (f.symm ⟨_, three.fact_mem⟩).2, ?_⟩
    left
    rw [Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' (ne_dvd_exponent _)
      three.fact_mem, three.natDegree]
    norm_num

end IsCyclotomicExtension.Rat.seven
