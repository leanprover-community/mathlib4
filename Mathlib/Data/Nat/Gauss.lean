/-
Copyright (c) 2024 Alena Gusakov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alena Gusakov
-/
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Polynomial.Basic
import Mathlib.Data.Polynomial.Div
import Mathlib.Data.Polynomial.Eval
import Mathlib.Data.Polynomial.FieldDivision
import Mathlib.FieldTheory.RatFunc
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.GeomSum



/-!
# Gaussian Binomial Coefficients

This file defines Gaussian binomial coefficients and proves simple lemmas (i.e. those not
requiring more imports).

## Main definition and results

## Tags

gaussian binomial coefficient
-/

noncomputable section

/-variables (α : Type*)

instance (priority := 100) NoZeroDivisors.to_isCancelMulZero' [Semiring α] [NoZeroDivisors α] :
    IsCancelMulZero α :=
  { mul_left_cancel_of_ne_zero := fun ha h ↦ by
      rw [← sub_eq_zero, ← mul_sub] at h
      exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left ha)
    mul_right_cancel_of_ne_zero := fun hb h ↦ by
      rw [← sub_eq_zero, ← sub_mul] at h
      exact sub_eq_zero.1 ((eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hb) }-/

open Nat

namespace Nat

open Polynomial

open Finset BigOperators

-- polynomials? this should output a polynomial, not a nat

lemma degree_sum (n : ℕ) : degree (∑ i in range (n + 1), (X ^ i) : ℚ[X]) ≤ n := by
  induction' n with n hn
  · rw [range_one, sum_singleton]
    simp
  · rw [sum_range_succ]
    apply le_trans (degree_add_le (∑ x in range (n + 1), X ^ x : ℚ[X]) (X ^ (n + 1)))
      (max_le (le_trans hn (WithBot.coe_le_coe.2 (le_succ n)))
      (le_of_eq (@degree_X_pow ℚ _ _ (n + 1))))

lemma degree_sum_eq (n : ℕ) : degree (∑ i in range (n + 1), (X ^ i) : ℤ[X]) = n := by
  induction' n with n hn
  · rw [range_one, sum_singleton]
    simp
  · rw [sum_range_succ, degree_add_eq_right_of_degree_lt, degree_X_pow]
    simp [hn]
    apply WithBot.lt_coe_iff.2 fun a hna => by simp [← WithBot.coe_eq_coe.1 hna]

/-- `q_factorial n` is the q-analog factorial of `n`. -/
def q_factorial : ℕ → ℤ[X]
  | 0 => 1
  | succ n => (∑ i in range (n + 1), (X ^ i)) * q_factorial n

@[simp] theorem q_factorial_zero : q_factorial 0 = 1 :=
  rfl

theorem q_factorial_succ (n : ℕ) : q_factorial (n + 1) =
  (∑ i in range (n + 1), (X ^ i)) * q_factorial n :=
  rfl

lemma q_factorial_Monic (n : ℕ) : Monic (q_factorial n) := by
  induction' n with n hn
  · rw [q_factorial_zero]
    simp
  · rw [q_factorial_succ]
    apply Monic.mul (@Polynomial.monic_geom_sum_X ℕ _ _ (succ_ne_zero n)) hn

@[simp] theorem q_factorial_ne_zero (k : ℕ) : q_factorial k ≠ 0 :=
  Monic.ne_zero (q_factorial_Monic k)

lemma q_factorial_degree (n : ℕ) : degree (q_factorial n) = (∑ i in range (n), i) := by
  induction' n with n hn
  · simp
  · rw [sum_range_succ, q_factorial_succ, Monic.degree_mul (q_factorial_Monic n), hn,
      degree_sum_eq, add_comm]
    simp

/-def gauss' (n k : ℕ) : RatFunc ℚ :=
  RatFunc.mk (q_factorial n) ((q_factorial k) * (q_factorial (n - k)))

@[simp]
theorem gauss'_zero_right (n : ℕ) : gauss' n 0 = 1 := by
  simp [gauss']

lemma RatFunc.mk_pow (p q : ℚ[X]) (n : ℕ) : (RatFunc.mk p q) ^ n = RatFunc.mk (p ^ n) (q ^ n) := by
  simp_all only [RatFunc.mk_eq_div, div_pow, map_pow]

lemma RatFunc.mk_add (p q r : ℚ[X]) :
  (RatFunc.mk p q) - (RatFunc.mk r q) = RatFunc.mk (p - r) (q) := by
  simp_all only [RatFunc.mk_eq_div, map_sub, div_eq_mul_inv, sub_mul]

lemma gauss'_succ (n k : ℕ) (hk : k ≤ n) (h1 : (@RatFunc.X ℚ _ _) ≠ 1) : (gauss' (succ n) k) =
(RatFunc.mk (X ^ (n + 1) - 1) (X ^ (n + 1 - k) - 1)) * (gauss' n k) := by
  unfold gauss'
  simp [succ_sub hk, q_factorial_succ, RatFunc.mk_eq_div, map_mul (algebraMap ℚ[X] (RatFunc ℚ)),
    (algebraMap ℚ[X] (RatFunc ℚ)).map_geom_sum X (n + 1), map_pow (algebraMap ℚ[X] (RatFunc ℚ)),
    RatFunc.algebraMap_X, @geom_sum_eq (RatFunc ℚ) _ RatFunc.X h1 (succ n),
    @geom_sum_eq (RatFunc ℚ) _ RatFunc.X h1 (succ (n - k))]
  rw [← mul_assoc, mul_comm ((algebraMap ℚ[X] (RatFunc ℚ)) (q_factorial k)),
    mul_assoc, ← map_mul (algebraMap ℚ[X] (RatFunc ℚ)), mul_div_mul_comm, div_div_div_eq,
    mul_comm _ (RatFunc.X - 1), mul_div_mul_comm, div_self (sub_ne_zero.2 h1), one_mul]

lemma gauss'_succ_succ (n k : ℕ) (h1 : (@RatFunc.X ℚ _ _) ≠ 1) :
(gauss' (succ n) (succ k)) = (RatFunc.mk (X ^ (n + 1) - 1) (X ^ (k + 1) - 1)) * (gauss' n k) := by
  unfold gauss'
  simp [succ_sub_succ_eq_sub, q_factorial_succ, q_factorial_succ, RatFunc.mk_eq_div,
    map_mul (algebraMap ℚ[X] (RatFunc ℚ)), (algebraMap ℚ[X] (RatFunc ℚ)).map_geom_sum X (n + 1),
    (algebraMap ℚ[X] (RatFunc ℚ)).map_geom_sum X (k + 1), RatFunc.algebraMap_X,
    @geom_sum_eq (RatFunc ℚ) _ RatFunc.X h1 (succ n), @geom_sum_eq (RatFunc ℚ) _ RatFunc.X h1 (succ k)]
  rw [mul_comm ((algebraMap ℚ[X] (RatFunc ℚ)) (q_factorial k)), mul_assoc, mul_div_mul_comm,
    div_div_div_eq, mul_comm _ (RatFunc.X - 1), mul_div_mul_comm, div_self (sub_ne_zero.2 h1),
    one_mul, mul_comm ((algebraMap ℚ[X] (RatFunc ℚ)) (q_factorial (n - k))) _]

lemma gauss'_id (n k : ℕ) (hk : succ k ≤ n) (h1 : (@RatFunc.X ℚ _ _) ≠ 1) :
gauss' n k = (RatFunc.mk (X ^ (k + 1) - 1) (X ^ (n - k) - 1)) * (gauss' n (succ k)) := by
  have h2 := gauss'_succ _ _ hk h1
  rw [gauss'_succ_succ n k h1, succ_sub_succ_eq_sub] at h2
  --rw [← @mul_left_cancel_iff _ _ _ (RatFunc.mk (X ^ (n + 1) - 1) (X ^ (k + 1) - 1)) _ _] at h2
  rw [← @mul_cancel_left_coe_nonZeroDivisors (RatFunc ℚ) _
    (gauss' n k)]
  sorry
  --have h3 := nonZeroDivisors.ne_zero
  --have h4 :=
  sorry

@[simp]
theorem degree_gauss' (n k : ℕ) : RatFunc.intDegree (gauss' n k) = k • (n - k) := by sorry

theorem gauss'_recurrence (n k : ℕ) : (gauss' (succ n) (succ k)) =
  (algebraMap ℚ[X] (RatFunc ℚ) X ^ k) * (gauss' n (succ k)) + (gauss' n k) := by sorry-/

/-- `gauss n k`, when evaluated at a prime power `q`, is the number of `k`-dimensional subspaces
  in an `n`-dimensional vector space over `fin q → 𝔽`. Also known as Gaussian binomial coefficients. -/
def gauss : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => gauss n k + X ^ (k + 1) * gauss n (k + 1)

@[simp]
theorem gauss_zero_right (n : ℕ) : gauss n 0 = 1 := by cases n <;> rfl

@[simp]
theorem gauss_zero_succ (k : ℕ) : gauss 0 (k + 1) = 0 :=
  rfl

theorem gauss_succ_succ (n k : ℕ) :
gauss (n + 1) (k + 1) = gauss n k + X ^ (k + 1) * gauss n (succ k) := rfl

theorem gauss_eval_one_eq_choose (n k : ℕ) :
(gauss n k).eval 1 = choose n k := by
  induction' n with n hn generalizing k <;> induction' k with k <;>
    simp [gauss_succ_succ, choose_succ_succ]
  rw [hn k, hn (succ k)]

theorem gauss_eq_zero_of_lt : ∀ {n k}, n < k → gauss n k = 0
  | _, 0, hk => absurd hk (Nat.not_lt_zero _)
  | 0, k + 1, _ => gauss_zero_succ _
  | n + 1, k + 1, hk => by
    have hnk : n < k := lt_of_succ_lt_succ hk
    have hnk1 : n < k + 1 := lt_of_succ_lt hk
    rw [gauss_succ_succ, gauss_eq_zero_of_lt hnk, gauss_eq_zero_of_lt hnk1, mul_zero, zero_add]

theorem gauss_lt_of_eq_zero : ∀ {n k}, gauss n k = 0 → n < k
  | _, 0, hk => by simp at hk
  | 0, k + 1, _ => zero_lt_succ k
  | n + 1, k + 1, hk => succ_lt_succ (gauss_lt_of_eq_zero (Polynomial.ext_iff.2 (fun m => by
    simp only [gauss_succ_succ, Polynomial.ext_iff, coeff_add, coeff_zero, add_eq_zero] at hk
    rw [coeff_zero, (hk m).1])))

theorem gauss_eq_zero_iff {n k : ℕ} : gauss n k = 0 ↔ n < k :=
  ⟨gauss_lt_of_eq_zero, gauss_eq_zero_of_lt⟩

@[simp]
theorem gauss_self (n : ℕ) : gauss n n = 1 := by
  induction n <;> simp [*, gauss, gauss_eq_zero_of_lt (lt_succ_self _)]

@[simp]
theorem gauss_succ_self (n : ℕ) : gauss n (succ n) = 0 :=
  gauss_eq_zero_of_lt (lt_succ_self _)

@[simp]
theorem gauss_one_right (n : ℕ) : gauss n 1 = (∑ i in range n, (X ^ i) : ℤ[X]) := by
  induction n <;> simp [*, gauss, sum_range_succ', add_comm, ← monomial_one_one_eq_X, mul_sum,
  monomial_mul_monomial]

theorem succ_mul_gauss_eq : ∀ n k, (∑ i in range (succ n), (X ^ i)) * gauss n k =
  gauss (succ n) (succ k) * (∑ i in range (succ k), (X ^ i))
  | 0, 0 => by simp
  | 0, k + 1 => by simp [gauss]
  | n + 1, 0 => by
    simp [gauss, mul_succ, sum_range_succ']
    rw [mul_add, add_comm _ 1, add_comm _ X, ← mul_assoc, ← pow_two, mul_sum]
    simp [← pow_add, add_comm 2]
  | n + 1, k + 1 => by
    rw [gauss_succ_succ (succ n) (succ k), add_mul, mul_assoc, ← succ_mul_gauss_eq n (succ k)]
    simp [sum_range_succ' _ (k + 1), pow_add, ← sum_mul, mul_add]
    rw [← mul_assoc (gauss (succ n) (succ k)), ← succ_mul_gauss_eq n, add_right_comm, mul_comm _ X,
      mul_comm _ X, mul_assoc X, mul_comm (X ^ (succ k)), mul_assoc, ← mul_assoc X, ← mul_assoc X,
      ← mul_add, mul_comm _ (X ^ (succ k)), ← gauss_succ_succ, sum_range_succ', add_mul, mul_sum]
    simp [pow_add, mul_comm X]

theorem gauss_mul_q_factorial_mul_q_factorial : ∀ {n k}, k ≤ n →
  gauss n k * (q_factorial k) * (q_factorial (n - k)) = q_factorial n
  | 0, _, hk => by simp [Nat.eq_zero_of_le_zero hk]
  | n + 1, 0, _ => by simp
  | n + 1, k + 1, hk => by
    rcases lt_or_eq_of_le hk with hk₁ | hk₁
    · have h : gauss n k * q_factorial k.succ * q_factorial (n - k) =
          (∑ i in range (k + 1), (X ^ i)) * q_factorial n := by
        rw [← gauss_mul_q_factorial_mul_q_factorial (le_of_succ_le_succ hk)]
        simp [q_factorial_succ, mul_comm, mul_left_comm, mul_assoc]
      have h₁ : q_factorial (n - k) = (∑ i in range (n - k), (X ^ i)) * q_factorial (n - k.succ) := by
        rw [← succ_sub_succ, succ_sub (le_of_lt_succ hk₁), q_factorial_succ]
      have h₂ : gauss n (succ k) * q_factorial k.succ * ((∑ i in range (n - k), (X ^ i)) *
        (q_factorial (n - k.succ))) = (∑ i in range (n - k), (X ^ i)) * q_factorial n := by
        rw [← gauss_mul_q_factorial_mul_q_factorial (le_of_lt_succ hk₁)]
        simp [factorial_succ, mul_comm, mul_left_comm, mul_assoc]
      rw [gauss_succ_succ, add_mul, add_mul, succ_sub_succ, h, h₁, mul_assoc, mul_assoc,
        ← mul_assoc (gauss n (succ k)), h₂, ← mul_assoc, ← add_mul, q_factorial_succ, mul_sum]
      simp [← pow_add]
      rw [← sum_range_add, add_comm k 1, add_assoc, add_comm k, Nat.sub_add_cancel
        (le_of_lt (succ_lt_succ_iff.1 hk₁)), add_comm]
    · rw [hk₁]; simp [hk₁, mul_comm, gauss, tsub_self]

-- don't have mul_right_cancel instance for ℤ[X]
theorem gauss_mul {n k s : ℕ} (hkn : k ≤ n) (hsk : s ≤ k) :
    n.gauss k * k.gauss s = n.gauss s * (n - s).gauss (k - s) :=
  have h : q_factorial (n - k) * q_factorial (k - s) * q_factorial s ≠ 0 :=
    by apply_rules [q_factorial_ne_zero, mul_ne_zero]
  mul_right_cancel₀ h <|
  sorry

@[simp]
theorem gauss_succ_self_right : ∀ n : ℕ, gauss (n + 1) n = (∑ i in range (n + 1), (X ^ i) : ℤ[X])
  | 0 => by simp
  | n + 1 => by rw [gauss_succ_succ, gauss_succ_self_right n, gauss_self, mul_one, ← sum_range_succ]


/-theorem gauss_eq_factorial_div_factorial {n k : ℕ} (hk : k ≤ n) :
    gauss n k = q_factorial n / (q_factorial k * q_factorial (n - k)) := by
  rw [← gauss_mul_factorial_mul_factorial hk, mul_assoc]
  exact (mul_div_left _ (mul_pos (factorial_pos _) (factorial_pos _))).symm-/

theorem gauss_symm (n k : ℕ) : gauss n k = gauss n (n - k) := by sorry

@[simp]
theorem gauss_pred_right (n : ℕ) : gauss n (n - 1) = (∑ i in range n, (X ^ i) : ℤ[X]) := by
  induction n <;> simp [*, gauss, sum_range_succ', add_comm, ← monomial_one_one_eq_X, mul_sum,
  monomial_mul_monomial]
  sorry

theorem gauss_natDegree : ∀ {n k}, k ≤ n → natDegree (gauss n k) = k * (n - k)
  | 0, _, hk => by simp [Nat.eq_zero_of_le_zero hk]
  | n + 1, 0, _ => by simp
  | n + 1, k + 1, hkn => by
    by_cases h3 : succ k ≤ n
    · rw [gauss_succ_succ, natDegree_add_eq_right_of_natDegree_lt, X_pow_mul, natDegree_mul_X_pow,
        gauss_natDegree h3, succ_sub_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_left_distrib,
        mul_succ, Nat.sub_add_eq, Nat.sub_add_cancel]
      rw [← Nat.mul_sub_left_distrib (succ k) n k, le_mul_iff_one_le_right (zero_lt_succ _)]
      apply (Nat.le_sub_iff_add_le (le_of_lt (succ_le.1 h3))).2
      rw [add_comm]
      apply h3
      by_cases h5 : succ k = n
      · rw [h5]
        simp
      apply ne_zero_of_natDegree_gt
      rw [gauss_natDegree h3]
      apply mul_pos (zero_lt_succ _) (Nat.lt_sub_of_add_lt _)
      simp [lt_of_le_of_ne h3 h5]
      rw [natDegree_mul _ (gauss_eq_zero_iff.1.mt (not_lt.2 h3)), natDegree_X_pow, gauss_natDegree h3,
        gauss_natDegree (le_of_lt (succ_le.1 h3)), ← mul_one (k + 1), ← mul_add, add_comm _ (n - succ k),
        sub_succ, add_one (pred (n - k)), succ_pred (pos_iff_ne_zero.1
        (Nat.sub_pos_iff_lt.2 (succ_le.1 h3)))]
      apply mul_lt_mul_of_pos_right (lt_succ_self _) (Nat.sub_pos_iff_lt.2 (succ_le.1 h3))
      rw [← add_zero (X^(k+1))]
      nth_rewrite 1 [← C_0]
      apply X_pow_add_C_ne_zero (zero_lt_succ _)
    · simp [gauss_succ_succ, gauss_eq_zero_iff.2 (not_le.1 h3), le_antisymm hkn (succ_le.2 (not_le.1 h3)),
        Order.succ_eq_succ_iff.1 (le_antisymm hkn (succ_le.2 (not_le.1 h3)))]

theorem gauss_degree : ∀ {n k}, degree (gauss n k) = if n < k then ⊥ else ↑(k * (n - k)) := by
  intros n k
  by_cases h2 : n < k
  · rw [gauss_eq_zero_iff.2 h2, if_pos h2, degree_zero]
  · rw [if_neg h2, degree_eq_natDegree (gauss_eq_zero_iff.1.mt h2), gauss_natDegree (not_lt.1 h2)]

theorem gauss_Monic (n k : ℕ) (hkn : k ≤ n) : Monic (gauss n k) := by
  induction' n with n hn generalizing k <;> induction' k with k hk <;>
    simp [gauss_succ_succ, choose_succ_succ]
  simp at hkn
  by_cases hkn2 : k = n
  · rw [hkn2]
    simp
  apply Monic.add_of_right (Monic.mul (monic_X_pow _)
    (hn _ (lt_succ.1 (lt_of_le_of_ne hkn (succ_ne_succ.2 hkn2)))))
  rw [degree_mul, degree_X_pow, gauss_degree, if_neg (not_lt.2 (succ_le_succ_iff.1 hkn)),
    gauss_degree, if_neg (not_lt.2 (lt_succ.1 (lt_of_le_of_ne hkn (succ_ne_succ.2 hkn2)))),
    ← mul_one (k + 1), ← cast_add, ← mul_add, add_comm _ (n - succ k), sub_succ,
    add_one (pred (n - k)), succ_pred (pos_iff_ne_zero.1 (Nat.sub_pos_iff_lt.2 (succ_le.1
    (succ_le.1 (lt_succ.1 (lt_of_le_of_ne hkn (succ_ne_succ.2 hkn2))))))), cast_lt]
  apply mul_lt_mul_of_pos_right (lt_succ_self _) (Nat.sub_pos_iff_lt.2 (succ_le.1
    (lt_succ.1 (lt_of_le_of_ne hkn (succ_ne_succ.2 hkn2)))))

--theorem gauss_eq_zero_iff {n k : ℕ} : n.gauss k = 0 ↔ n < k := by sorry

end Nat
