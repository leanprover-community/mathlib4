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
  rw [@sum_eq_add_sum_diff_singleton (i := a+1)]
  have h : Ioc a N \ {a + 1} = Ioc (a + 1) N := by
    rw [←Icc_succ_left a, sdiff_singleton_eq_erase]; simp
  rw [h]
  simp; linarith


/- ## The sum of floors
We first show that the sum of μ(n) * ⌊N/n⌋  as n ranges from 1 to N is equal to 1. -/

lemma moebius_mul_floor_div_sum_eq_one (N : ℕ) (hN : 0 < N) :
  ∑ n in Ioc 0 N, (μ n * ⌊N / (n : ℚ)⌋ : ℚ) = 1 :=
calc
  ∑ n in Ioc 0 N, (μ n * ⌊N / (n : ℚ)⌋ : ℚ) =
  ∑ n in Ioc 0 N, (⌊N / (n : ℚ)⌋  * μ n : ℚ) := by congr; ext1 n; ring
  _ = ∑ n in Ioc 0 N, ∑ _m in (Ioc 0 N).filter (fun x ↦ n ∣ x), μ n := by
    norm_cast; apply sum_congr rfl; simp
  _ = ∑ n in Ioc 0 N, ∑ m in Ioc 0 N, if n ∣ m then μ n else 0 := by simp_rw [sum_filter]
  _ = ∑ m in Ioc 0 N, ∑ n in Ioc 0 N, if n ∣ m then μ n else 0 := by rw [sum_comm]
  _ = ∑ m in Ioc 0 N, ∑ n in m.divisors, μ n := by
    simp
    apply sum_congr rfl
    intro m hm
    simp at hm
    rw[←sum_filter]
    apply sum_congr
    · ext x
      simp at hm
      cases' hm with hm1 hm2
      have hm3 : 0 < m := by linarith
      simp
      simp_rw [← Ne.def, ←pos_iff_ne_zero, hm3]
      simp
      intro hx
      have h := (le_of_dvd hm3 hx)
      have h' := (ne_zero_of_dvd_ne_zero hm3.ne' hx)
      constructor
      · exact Iff.mpr one_le_iff_ne_zero h'
      · linarith
    · simp
  _ = ∑ m in Ioc 0 N, (μ * ζ) m                  := by simp_rw [coe_mul_zeta_apply]
  _ = ∑ m in Ioc 0 N, if m = 1 then 1 else 0     := by
                                                    simp_rw [moebius_mul_coe_zeta, one_apply]; simp
  _ = 1                                          := by simp [hN.ne']

/- ## The sum of fractional parts
Next, we will show that μ(n) times the fractional part of a rational is at most `1`. -/

@[simp]
lemma abs_moebius_le_one (n : ℕ) : |μ n| ≤ 1 := by by_cases (Squarefree n) <;> simp [h]

lemma moebius_le_one (n : ℕ) (q : ℚ): |μ n * (Int.fract q)| ≤ 1 := by
  rw [abs_mul]
  have h1 : |(μ n : ℚ)| ≤ 1 := by norm_cast; simp
  have h2: |Int.fract q| ≤ 1 := by rw [Int.abs_fract]; exact (Int.fract_lt_one _).le
  have h3 : 0 ≤ |(μ n : ℚ)| := abs_nonneg _
  nlinarith

/- It follows that the absolute value of the sum of the Möbius function times the
   fractional parts of N/n is at most N-1, since it is 0 for n = 1. -/
theorem fract_sum_le_N_minus_one (N : ℕ) (hN : 0 < N) :
  |∑ n in Ioc 0 N, (μ n * (Int.fract ((N/n) : ℚ)))| ≤ N - 1 :=
calc
 |∑ n in Ioc 0 N, (μ n * (Int.fract ((N/n) : ℚ)))|
   = |μ 1 * (Int.fract ((N / (1 : ℚ)))) + ∑ n in Ioc 1 N, (μ n * (Int.fract ((N/n) : ℚ)))| := by
                                                          congr; apply (split_off_first _ N hN)
 _ = |∑ n in Ioc 1 N, (μ n * (Int.fract ((N/n) : ℚ)))| := by simp
 _ ≤ ∑ n in Ioc 1 N, |(μ n * (Int.fract ((N/n) : ℚ)))| := by apply abs_sum_le_sum_abs
 _ ≤ ∑ n in Ioc 1 N, 1 := sum_le_sum (fun n _ ↦ moebius_le_one _ _)
 _ = N - 1 := by simp [hN]

/- ## Putting everything together
   To finish the argument, we decompose each summand, μ(n) / n, into a floor and fractional part,
   and we combine the two upper bounds calculated above. -/
theorem abs_of_moebius_sum_le_one : ∀ N, |∑ n in Ioc 0 N, (μ n / (n:ℚ))| ≤ 1 := by
  intro N
  rcases eq_zero_or_pos N with hz | hnz
  · simp_rw [hz]
  · have key : |∑ n in Ioc 0 N, (μ n / (n:ℚ))| * N ≤ N :=
    calc |∑ n in Ioc 0 N, (μ n / (n:ℚ))| * N
        = |∑ n in Ioc 0 N, (μ n / (n:ℚ))| * |(N:ℚ)|      := by congr; rw [abs_cast]
      _ = |∑ n in Ioc 0 N, (μ n / (n:ℚ)) * N|            := by rw [←abs_mul]; rw [sum_mul]
      _ = |∑ n in Ioc 0 N, (μ n * (N / (n:ℚ)))|          := by congr; ext1 n; ring
      _ = |∑ n in Ioc 0 N, (μ n * (⌊N / (n:ℚ)⌋ + (Int.fract ((N/n) : ℚ))))| := by
            congr; ext1 n; simp; left; rw [←Int.floor_add_fract (N / (n : ℚ))]; simp[hnz]
      _ = |(∑ n in Ioc 0 N, (μ n * ⌊N / (n:ℚ)⌋):ℚ) +
                ∑ n in Ioc 0 N, (μ n * (Int.fract ((N/n) : ℚ)))|  := by
                                            congr; rw [← sum_add_distrib]; congr; ext1 n; ring
      _ ≤ |((∑ n in Ioc 0 N, (μ n * ⌊N / (n:ℚ)⌋)):ℚ)| +
                |∑ n in Ioc 0 N, (μ n * (Int.fract ((N/n) : ℚ)))| := abs_add _ _
      _ ≤ 1 + |∑ n in Ioc 0 N, (μ n * (Int.fract ((N/n) : ℚ)))|   := by
                                            rw [moebius_mul_floor_div_sum_eq_one N hnz]; rfl
      _ ≤ 1 + (N-1)   := by linarith [fract_sum_le_N_minus_one N hnz]
      _ = N           := by ring
    rw [←le_div_iff] at key
    apply le_trans key
    rw [div_self]
    all_goals norm_cast <;> linarith
