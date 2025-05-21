import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.NumberTheory.Cyclotomic.Embeddings
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Data.Real.Pi.Bounds

set_option linter.style.header false

open Ideal NumberField Module NumberField.InfinitePlace Nat Real
  IsCyclotomicExtension.Rat Polynomial.cyclotomic

variable {K : Type*} [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

section seven

theorem PNat.prime_seven : (7 : ℕ+).Prime :=
  Nat.prime_seven

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

theorem M7 [IsCyclotomicExtension {7} ℚ K] : ⌊(M K)⌋₊ = 4 := by
  rw [absdiscr_prime 7 K, IsCyclotomicExtension.finrank (n := 7) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 7, totient_prime
      PNat.prime_seven]
  simp only [PNat.val_ofNat, Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg,
    Int.reducePow, reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact crazy7

end seven

section eleven

theorem PNat.prime_eleven : (11 : ℕ+).Prime :=
  Nat.prime_eleven

instance PNat.fact_prime_eleven : Fact (11 : ℕ+).Prime :=
  ⟨prime_eleven⟩

lemma crazy11 : ⌊(4 / π) ^ 5 * (10! / 10 ^ 10 * √2357947691)⌋₊ = 58 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 5 * (10! / 10 ^ 10 * √2357947691) := by
        gcongr; exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 5 * (10! / 10 ^ 10 * 48558) := by
        gcongr; exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 58 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 5 * (10! / 10 ^ 10 * √2357947691) := by
        gcongr; exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 5 * (10! / 10 ^ 10 * 48559) := by
        gcongr; exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ 58 + 1 := by norm_num

theorem M11 [IsCyclotomicExtension {11} ℚ K] : ⌊(M K)⌋₊ = 58 := by
  rw [absdiscr_prime 11 K, IsCyclotomicExtension.finrank (n := 11) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 11, totient_prime
      PNat.prime_eleven]
  simp only [PNat.val_ofNat, Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg,
    Int.reducePow, reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact crazy11

end eleven

section thirteen

theorem Nat.prime_thirteen : Prime 13 := by decide

theorem PNat.prime_thirteen : (13 : ℕ+).Prime :=
  Nat.prime_thirteen

instance PNat.fact_prime_thirteen : Fact (13 : ℕ+).Prime :=
  ⟨prime_thirteen⟩

lemma crazy13 : ⌊(4 / π) ^ 6 * (12! / 12 ^ 12 * √1792160394037)⌋₊ = 306 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 6 * (12! / 12 ^ 12 * √1792160394037) := by
        gcongr; exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 6 * (12! / 12 ^ 12 * 1338715) := by
        gcongr; exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 306 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 6 * (12! / 12 ^ 12 * √1792160394037) := by
        gcongr; exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 6 * (12! / 12 ^ 12 * 1338716) := by
        gcongr; exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ _ := by norm_num

theorem M13 [IsCyclotomicExtension {13} ℚ K] : ⌊(M K)⌋₊ = 306 := by
  rw [absdiscr_prime 13 K, IsCyclotomicExtension.finrank (n := 13) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 13, totient_prime
      PNat.prime_thirteen]
  simp only [PNat.val_ofNat, Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg,
    Int.reducePow, reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact crazy13

end thirteen

section seventeen

theorem Nat.prime_seventeen : Prime 17 := by decide

theorem PNat.prime_seventeen : (17 : ℕ+).Prime :=
  Nat.prime_seventeen

instance PNat.fact_prime_seventeen : Fact (17 : ℕ+).Prime :=
  ⟨prime_seventeen⟩

lemma crazy17 : ⌊(4 / π) ^ 8 * (16! / 16 ^ 16 * √2862423051509815793)⌋₊ = 13254 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 8 * (16! / 16 ^ 16 * √2862423051509815793) := by
        gcongr; exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 8 * (16! / 16 ^ 16 * 1691869691) := by
        gcongr; exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 13254 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 8 * (16! / 16 ^ 16 * √2862423051509815793) := by
        gcongr; exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 8 * (16! / 16 ^ 16 * 1691869692) := by
        gcongr; exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ _ := by norm_num

theorem M17 [IsCyclotomicExtension {17} ℚ K] : ⌊(M K)⌋₊ = 13254 := by
  rw [absdiscr_prime 17 K, IsCyclotomicExtension.finrank (n := 17) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 17, totient_prime
      PNat.prime_seventeen]
  simp only [PNat.val_ofNat, Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg,
    Int.reducePow, reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact crazy17

end seventeen

section nineteen

theorem Nat.prime_nineteen : Prime 19 := by decide

theorem PNat.prime_nineteen : (19 : ℕ+).Prime :=
  Nat.prime_nineteen

instance PNat.fact_prime_nineteen : Fact (19 : ℕ+).Prime :=
  ⟨prime_nineteen⟩

lemma crazy19 : ⌊(4 / π) ^ 9 * (18! / 18 ^ 18 * √5480386857784802185939)⌋₊ = 105933 := by
  refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
  · calc
      _ ≥ (4 / 3.14159265358979323847) ^ 9 * (18! / 18 ^ 18 * √5480386857784802185939) := by
        gcongr; exact pi_lt_d20.le
      _ ≥ (4 / 3.14159265358979323847) ^ 9 * (18! / 18 ^ 18 * 74029634996) := by
        gcongr; exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
      _ ≥ 105933 := by norm_num
  · calc
      _ < (4 / 3.14159265358979323846) ^ 9 * (18! / 18 ^ 18 * √5480386857784802185939) := by
        gcongr; exact pi_gt_d20
      _ ≤ (4 / 3.14159265358979323846) ^ 9 * (18! / 18 ^ 18 * 74029634997) := by
        gcongr; exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
      _ ≤ _ := by norm_num

theorem M19 [IsCyclotomicExtension {19} ℚ K] : ⌊(M K)⌋₊ = 105933 := by
  rw [absdiscr_prime 19 K, IsCyclotomicExtension.finrank (n := 19) K
    (irreducible_rat (by norm_num)), nrComplexPlaces_eq_totient_div_two 19, totient_prime
      PNat.prime_nineteen]
  simp only [PNat.val_ofNat, Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg,
    Int.reducePow, reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
  exact crazy19

end nineteen
