import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Interval
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Factorization.Basic

open Finset Nat BigOperators ArithmeticFunction

/-- # An upper bound for a Möbius function summation

We show that the sum of `μ(n)/n` as `n` ranges from `1` to `N` is at most `1` in absolute value.
This was an undergraduate number theory exercise and its solution as given by Harald Helfgott at
the workshop "Machine-Checked Mathematics" at Lorentz Center, Leiden, 10-14 July 2023.
-/

/- ## Lemmas
We first prove two lemmas that might be put elsewhere. -/

@[simp]
/- Natural number division coincides with the floor of rational division. -/
lemma floor_div_nat_cast (a b : ℕ) : ⌊a / (b : ℚ)⌋ = a / b := by
  rw [← Nat.cast_floor_eq_int_floor, Nat.floor_div_eq_div] <;> simp; positivity

/- In a sum ranging from 1 to N, we may split off the first term. -/
lemma split_off_first {a : ℕ} (f : ℕ → ℚ) (N : ℕ) (hN : a < N) :
  ∑ n in Ioc a N, f n = f (a + 1) + ∑ n in Ioc (a + 1) N, f n := by
  rw [←Icc_succ_left, ←Finset.Ioc_insert_left, sum_insert]
  · simp only [mem_Ioc, lt_self_iff_false, false_and, not_false_eq_true]
  exact hN

/-- The absolute value of the Möbius function is bounded above by 1. -/
@[simp]
lemma abs_moebius_le_one (n : ℕ) : |μ n| ≤ 1 := by by_cases (Squarefree n) <;> simp [h]

/-- The sum of the Möbius function over all divisors of `m` is the indicator function of `1`.-/
theorem sum_divisors_mu (m : ℕ) : ∑ n in m.divisors, μ n = if m = 1 then 1 else 0 :=
  by rw [←coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]

/- ## The sum of floors
We first show that the sum of μ(n) * ⌊N/n⌋  as n ranges from 1 to N is equal to 1. -/

lemma moebius_mul_floor_div_sum_eq_one (N : ℕ) (hN : 0 < N) :
  ∑ n in Ioc 0 N, μ n * ⌊(N / n : ℚ)⌋ = 1 :=
calc
  _ = ∑ m in Ioc 0 N, ∑ n in Ioc 0 N, if n ∣ m then μ n else 0 := by
    rw [sum_comm]
    exact sum_congr rfl fun x _ ↦ by simp [←sum_filter, mul_comm, Ioc_filter_dvd_card_eq_div]
  _ = ∑ m in Ioc 0 N, ∑ n in m.divisors, μ n := by
    refine sum_congr rfl fun x hx => ?_
    rw [mem_Ioc] at hx
    rw [←sum_filter]
    refine sum_congr ?_ (fun x _ => rfl)
    simp only [divisors, Ico_succ_left, mem_filter, mem_Ioc, mem_Ioo, and_congr_left_iff,
      lt_add_one_iff, and_congr_right_iff, Finset.ext_iff]
    exact fun i h _ => ⟨fun _ => le_of_dvd hx.1 h, fun h' => h'.trans hx.2⟩
  _ = 1 := by simp [sum_divisors_mu, hN.ne']

/- ## The sum of fractional parts
Next, we will show that μ(n) times the fractional part of a rational is at most `1`. -/

lemma moebius_mul_le_one (n : ℕ) (q : ℚ): |μ n * Int.fract q| ≤ 1 := by
  rw [abs_mul]
  refine mul_le_one ?_ (abs_nonneg _) ?_
  · norm_cast; simp
  rw [Int.abs_fract]; exact (Int.fract_lt_one _).le

/- It follows that the absolute value of the sum of the Möbius function times the
   fractional parts of N/n is at most N-1, since it is 0 for n = 1. -/
theorem fract_sum_le_N_minus_one (N : ℕ) (hN : 0 < N) :
  |∑ n in Ioc 0 N, μ n * Int.fract (N / n : ℚ)| ≤ N - 1 :=
calc _ = |∑ n in Ioc 1 N, μ n * Int.fract (N / n : ℚ)| := by
      simp only [split_off_first, hN, cast_one, div_one, Int.fract_natCast, mul_zero, zero_add]
  _ ≤ ∑ n in Ioc 1 N, |μ n * Int.fract (N / n : ℚ)| := abs_sum_le_sum_abs _ _
  _ ≤ card (Ioc 1 N) • (1 : ℚ) := sum_le_card_nsmul _ _ 1 (fun x _ => moebius_mul_le_one _ _)
  _ = N - 1 := by simp [hN]

/- ## Putting everything together
   To finish the argument, we decompose each summand, μ(n) / n, into a floor and fractional part,
   and we combine the two upper bounds calculated above. -/
theorem abs_of_moebius_sum_le_one : ∀ N, |∑ n in Ioc 0 N, (μ n / n : ℚ)| ≤ 1 := by
  intro N
  rcases eq_zero_or_pos N with rfl | hnz
  · simp
  suffices key : |∑ n in Ioc 0 N, (μ n / n : ℚ)| * N ≤ N
  · rwa [←le_div_iff, div_self] at key
    all_goals positivity
  calc _ = |∑ n in Ioc 0 N, μ n * ⌊(N / n : ℚ)⌋ + ∑ n in Ioc 0 N, μ n * Int.fract (N / n : ℚ)| := by
        simp only [Int.cast_sum, Int.cast_mul, ←sum_add_distrib, ←mul_add, Int.floor_add_fract,
          mul_div_assoc', ←div_mul_eq_mul_div, ←sum_mul, abs_mul, abs_cast]
      _ ≤ |∑ n in Ioc 0 N, μ n * ⌊(N / n : ℚ)⌋| + |∑ n in Ioc 0 N, μ n * Int.fract (N / n : ℚ)| :=
          (abs_add _ _).trans_eq (by simp)
      _ ≤ (1 : ℚ) + (N - 1) := by
          refine add_le_add ?_ (fract_sum_le_N_minus_one _ hnz)
          rw [←Int.cast_one, Int.cast_le, moebius_mul_floor_div_sum_eq_one _ hnz, abs_one]
      _ = _ := add_sub_cancel'_right _ _
