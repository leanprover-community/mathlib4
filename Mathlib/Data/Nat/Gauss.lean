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
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Quotient
import Mathlib.Algebra.Module.Projective


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
open scoped Classical

-- polynomials? this should output a polynomial, not a nat

lemma degree_sum (n : ℕ) : degree (∑ i in range (n + 1), (X ^ i) : ℚ[X]) ≤ n := by
  induction' n with n hn
  · rw [range_one, sum_singleton]
    simp
  · rw [sum_range_succ]
    apply le_trans (degree_add_le (∑ x in range (n + 1), X ^ x : ℚ[X]) (X ^ (n + 1)))
      (max_le (le_trans hn (WithBot.coe_le_coe.2 (le_succ n)))
      (le_of_eq (@degree_X_pow ℚ _ _ (n + 1))))

lemma degree_sum_eq (n : ℕ) : degree (∑ i in range (n + 1), (X ^ i) : ℕ[X]) = n := by
  induction' n with n hn
  · rw [range_one, sum_singleton]
    simp
  · rw [sum_range_succ, degree_add_eq_right_of_degree_lt, degree_X_pow]
    simp [hn]
    apply WithBot.lt_coe_iff.2 fun a hna => by simp [← WithBot.coe_eq_coe.1 hna]

/-- `q_factorial n` is the q-analog factorial of `n`. -/
def q_factorial : ℕ → ℕ[X]
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

--lemma num_one_dim_subspaces (n : ℕ) :

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
def gauss : ℕ → ℕ → ℕ[X]
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
theorem gauss_one_right (n : ℕ) : gauss n 1 = (∑ i in range n, (X ^ i) : ℕ[X]) := by
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

instance : IsRightCancelMulZero (ℕ[X]) where
  mul_right_cancel_of_ne_zero := by
    intro a b c hb h_eq
    have h_inj: Function.Injective (Polynomial.map Int.ofNatHom) :=
      fun f g hfg => by simpa [Polynomial.ext_iff] using hfg
    apply_fun Polynomial.map Int.ofNatHom using h_inj
    apply_fun Polynomial.map Int.ofNatHom at h_eq
    simp only [Polynomial.map_mul, mul_eq_mul_right_iff] at h_eq
    obtain (h | h) := h_eq
    · exact h
    refine (hb ?_).elim
    rwa [Polynomial.map_eq_zero_iff] at h
    exact RingHom.injective_nat Int.ofNatHom

theorem gauss_mul {n k s : ℕ} (hkn : k ≤ n) (hsk : s ≤ k) :
    n.gauss k * k.gauss s = n.gauss s * (n - s).gauss (k - s) :=
  have h : q_factorial (n - k) * q_factorial (k - s) * q_factorial s ≠ 0 :=
    by apply_rules [q_factorial_ne_zero, mul_ne_zero]
  mul_right_cancel₀ h <|
  calc
    n.gauss k * k.gauss s * (q_factorial (n - k) * q_factorial (k - s) * q_factorial s) =
        n.gauss k * (k.gauss s * q_factorial s * q_factorial (k - s)) * q_factorial (n - k) :=
      by rw [mul_assoc, mul_assoc, mul_assoc, mul_assoc _ (q_factorial s), mul_assoc,
        mul_comm (q_factorial (n - k)), mul_comm (q_factorial s)]
    _ = q_factorial n :=
      by rw [gauss_mul_q_factorial_mul_q_factorial hsk, gauss_mul_q_factorial_mul_q_factorial hkn]
    _ = n.gauss s * q_factorial s * ((n - s).gauss (k - s) * q_factorial (k - s)
      * q_factorial (n - s - (k - s))) :=
      by rw [gauss_mul_q_factorial_mul_q_factorial (tsub_le_tsub_right hkn _),
        gauss_mul_q_factorial_mul_q_factorial (hsk.trans hkn)]
    _ = n.gauss s * (n - s).gauss (k - s) * (q_factorial (n - k) * q_factorial (k - s)
      * q_factorial s) :=
      by rw [tsub_tsub_tsub_cancel_right hsk, mul_assoc, mul_left_comm (q_factorial s), mul_assoc,
        mul_comm (q_factorial (k - s)), mul_comm (q_factorial s), mul_right_comm, ← mul_assoc]

@[simp]
theorem gauss_succ_self_right : ∀ n : ℕ, gauss (n + 1) n = (∑ i in range (n + 1), (X ^ i) : ℕ[X])
  | 0 => by simp
  | n + 1 => by rw [gauss_succ_succ, gauss_succ_self_right n, gauss_self, mul_one, ← sum_range_succ]

@[simp]
theorem gauss_symm {n k : ℕ} (hk : k ≤ n) : gauss n (n - k) = gauss n k :=
  have h : q_factorial (n - k) * q_factorial (n - (n - k)) ≠ 0 :=
    by apply_rules [q_factorial_ne_zero, mul_ne_zero]
  mul_right_cancel₀ h <|
  calc
    n.gauss (n - k) * (q_factorial (n - k) * q_factorial (n - (n - k))) = q_factorial n :=
        by rw [← mul_assoc, gauss_mul_q_factorial_mul_q_factorial (sub_le n k)]
    _ = n.gauss k * q_factorial (n - k) * q_factorial (k) := by
        rw [← gauss_mul_q_factorial_mul_q_factorial hk, mul_assoc, mul_comm (q_factorial k),
          ← mul_assoc]
    _ = n.gauss k * (q_factorial (n - k) * q_factorial (n - (n - k))) := by
        rw [@Nat.sub_eq_of_eq_add n (n - k) k, ← mul_assoc]
        rw [Nat.add_sub_of_le hk]

theorem gauss_symm_of_eq_add {n a b : ℕ} (h : n = a + b) : gauss n a = gauss n b := by
  suffices gauss n (n - b) = gauss n b by
    rw [h, add_tsub_cancel_right] at this; rwa [h]
  exact gauss_symm (h ▸ le_add_left _ _)

theorem gauss_symm_add {a b : ℕ} : gauss (a + b) a = gauss (a + b) b :=
  gauss_symm_of_eq_add rfl

theorem gauss_symm_half (m : ℕ) : gauss (2 * m + 1) (m + 1) = gauss (2 * m + 1) m := by
  apply gauss_symm_of_eq_add
  rw [add_comm m 1, add_assoc 1 m m, add_comm (2 * m) 1, two_mul m]

theorem gauss_eq_gauss {n k : ℕ} :
  gauss n k + X ^ (k + 1) * gauss n (k + 1) = X ^ (n - k) * gauss n k + gauss n (k + 1) := sorry

/-theorem gauss_succ_right_eq (n k : ℕ) : gauss n (k + 1) * (∑ i in range (k + 1), (X ^ i)) =
  gauss n k * (∑ i in range (n - k), (X ^ i)) := by
  have e : (∑ i in range (n + 1), (X ^ i)) * gauss n k = gauss n k * (∑ i in range (k + 1), (X ^ i))
    + X ^ (k + 1) * gauss n (k + 1) * (∑ i in range (k + 1), (X ^ i)) := by
    rw [← right_distrib, ← gauss_succ_succ, succ_mul_gauss_eq]
  rw [← tsub_eq_of_eq_add_rev e, mul_comm, ← mul_tsub, add_tsub_add_eq_tsub_right]-/

/-theorem gauss_eq_factorial_div_factorial {n k : ℕ} (hk : k ≤ n) :
    gauss n k = q_factorial n / (q_factorial k * q_factorial (n - k)) := by
  rw [← gauss_mul_factorial_mul_factorial hk, mul_assoc]
  exact (mul_div_left _ (mul_pos (factorial_pos _) (factorial_pos _))).symm-/

@[simp]
theorem gauss_pred_right (n : ℕ) : gauss n (n - 1) = (∑ i in range n, (X ^ i) : ℕ[X]) := by
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
  induction' n with n hn generalizing k <;> induction' k with k <;>
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

def q_factorial'_desc : ℕ → ℕ → ℤ[X]
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n, k + 1 => (X ^ n - X ^ k) * q_factorial'_desc n k

@[simp] theorem q_factorial'_desc_zero (n : ℕ) : q_factorial'_desc n 0 = 1 := by
  rw [q_factorial'_desc]

end Nat

universe u v

variable {K : Type u} {V : Type v}

section subspacesCard

variable [Field K] [AddCommGroup V] [Module K V]

/- Auxiliary function to construct the list of all sublists of a given length. Given an
integer `n`, a list `l`, a function `f` and an auxiliary list `L`, it returns the list made of
`f` applied to all sublists of `l` of length `n`, concatenated with `L`. -/
/-def sublistsLenAux {α β : Type*} : ℕ → List α → (List α → β) → List β → List β
  | 0, _, f, r => f [] :: r
  | _ + 1, [], _, r => r
  | n + 1, a :: l, f, r => sublistsLenAux (n + 1) l f (sublistsLenAux n l (f ∘ List.cons a) r)
#align list.sublists_len_aux List.sublistsLenAux-/

-- exists_linearIndependent_cons_of_lt_finrank
-- exists_linearIndependent_cons_of_lt_rank
/-def linearIndependentChoose [Module.Finite K V] [Fintype K] [FiniteDimensional K V] (k : ℕ)
(hkn : k ≤ FiniteDimensional.finrank K V) : List V
  | _, _, _, _, _, _, 0, _ => []-/

/-
X^n - 1 picks 1st vector
X^(n-1) - 1 picks 2nd vector from (n-1)-dim subspace
...
X^(n-k + 1) - 1 picks kth vector
-/

/-- A rank `n` free module has a basis indexed by `Fin n`. -/
lemma finBasisOfFinrankEq [Module.Finite K V] {n : ℕ} :
    FiniteDimensional.finrank K V = n ↔ ∃ (v : Fin n → V), LinearIndependent K v ∧
    Submodule.span K (Set.range v) = ⊤ := by

    sorry

def Grassmannian (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
[Fintype K] [FiniteDimensional K V] (k : ℕ) :=
{W : Submodule K V | FiniteDimensional.finrank K W = k}

variable [FiniteDimensional K V] [Fintype K]

-- show bijection with projection first
-- count linear independent sets as subtype of powerset?

-- LinearEquiv.submoduleMap

open Submodule


/-def proj2 (p : Submodule K V) : (V →ₗ[K] (V ⧸ p)) × (V →ₗ[K] p) :=
  have f := p.mkQ
  have hf : ∀ (x : V), f x = x := by sorry

  have h3 := LinearMap.isCompl_of_proj

  --let ⟨q, hq⟩ := (p).exists_isCompl
 --linearProjOfIsCompl
  sorry-/

/-def proj2 (a : V) : (V →ₗ[K] (V ⧸ span K {a})) × (V →ₗ[K] span K {a}) :=
  let ⟨q, hq⟩ := (span K {a}).exists_isCompl
 --linearProjOfIsCompl
  sorry-/

noncomputable def truc (a : V) : V ≃ₗ[K] (V ⧸ span K {a}) ×  span K {a} :=
  (Classical.choice (quotient_prod_linearEquiv (span K {a}))).symm

-- linearProjOfIsCompl
/-noncomputable def equivSubspaces (a : V) (ha : a ≠ 0) (k : ℕ) :
{W : Submodule K V | FiniteDimensional.finrank K W = k} ≃
  {W : Submodule K ((V ⧸ (K ∙ a)) × (K ∙ a)) | FiniteDimensional.finrank K W = k} where
    toFun := λ x => by sorry
      --have h2 := Submodule.quotientEquivOfIsCompl
      /-obtain ⟨f, hf⟩ := Classical.choice ((Module.projective_lifting_property (Submodule.mkQ (K ∙ a))
        (LinearMap.id) (Submodule.mkQ_surjective (K ∙ a))))-/
      --have h3 := (Classical.choice (quotient_prod_linearEquiv (span K {a}))).symm

      /-have h3 := Submodule.prodEquivOfIsCompl (Submodule.comapMkQOrderEmbedding (K ∙ a)
        (⊤ : Submodule K (V ⧸ (K ∙ a)))) (K ∙ a) {
          disjoint := by
            intros x hx1 hx2

            sorry
          codisjoint := by
            simp
        }
      -- Fintype.card_congr
      have h4 := @AddSubgroup.addGroupEquivQuotientProdAddSubgroup V _ (K ∙ a).toAddSubgroup
      have h5 := h4.toFun '' (x.1)-/


    invFun := _
    left_inv := _
    right_inv := _-/

-- needs a decidablepred instance that i don't like
/- Finset of linear independent vectors of card n in V -/

/-def equivThing (a : V) (x : Submodule K V) (ha : a ∈ x) :
  ↥(map (mkQ (span K {a})) ↑x) ≃ₗ[K] x ⧸ span K {(⟨a, ha⟩ : x)} where
    toFun := λ e => sorry
    map_add' := sorry
    map_smul' := sorry
    invFun := sorry
    left_inv := sorry
    right_inv := sorry-/

variable {K : Type u} {W : Type v}

variable [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-def subspacesBijection' : {X : Submodule K (V × W) | Submodule.snd K V W ≤ X} ≃
  {X : Submodule K (V × W) | ∀ x ∈ X, x.2 = 0 } where
    toFun := λ r => ⟨(Submodule.map (LinearMap.inl K V W) ∘
      Submodule.map (LinearMap.fst K V W)) r, by simp ⟩
    invFun := λ s => ⟨s ⊔  Submodule.snd K V W, by simp ⟩
    left_inv := λ r => by
      simp
      ext x;
      simp
      rw [mem_sup]
      refine ⟨λ h => ?_, λ h => ?_⟩
      obtain ⟨y, ⟨hy, ⟨z, ⟨hz, rfl⟩⟩⟩⟩ := h
      simp at hy
      obtain ⟨z2, hz2⟩ := hy
      obtain ⟨a, ha⟩ := z2
      have h3 : (0, a) ∈ r.1 := by
        apply Set.mem_of_subset_of_mem r.2.subset
        simp
        rw [Submodule.mem_snd]
      have h7 := add_mem ha (neg_mem h3)
      simp at h7
      rw [← hz2] at h7
      apply add_mem h7 (Set.mem_of_subset_of_mem r.2.subset ?_)
      simp
      refine ⟨(x.1, 0), ⟨?_, ⟨(0, x.2), ⟨by simp, by simp⟩⟩⟩⟩
      simp
      refine ⟨x.2, h⟩
      sorry
    right_inv := _-/

-- Why not prove that subspaces of X x Y containing 0 + Y biject with subspaces of X x Y
-- having trivial intersection with Y first?
def subspacesBijection : {X : Submodule K (V × W) | Submodule.map (LinearMap.inr K V W) ⊤ ≤ X} ≃
  {X : Submodule K (V × W) | ∀ x ∈ X, x.2 = 0 } where
    toFun := λ r => ⟨(Submodule.map (LinearMap.inl K V W) ∘
      Submodule.map (LinearMap.fst K V W)) r, by simp ⟩
    invFun := λ s => ⟨s ⊔ Submodule.map (LinearMap.inr K V W) ⊤, by simp ⟩
    left_inv := λ r => by
      simp
      ext x;
      simp
      rw [mem_sup]
      refine ⟨λ h => ?_, λ h => ?_⟩
      obtain ⟨y, ⟨hy, ⟨z, ⟨hz, rfl⟩⟩⟩⟩ := h
      simp at hy
      obtain ⟨z2, hz2⟩ := hy
      simp at hz
      obtain ⟨a, ha⟩ := z2
      obtain ⟨b, rfl⟩ := hz
      have h3 : (0, a) ∈ r.1 := by
        apply Set.mem_of_subset_of_mem r.2.subset
        simp
      have h7 := add_mem ha (neg_mem h3)
      simp at h7
      rw [← hz2] at h7
      apply add_mem h7 (Set.mem_of_subset_of_mem r.2.subset ?_)
      simp
      refine ⟨(x.1, 0), ⟨?_, ⟨(0, x.2), ⟨by simp, by simp⟩⟩⟩⟩
      simp
      refine ⟨x.2, h⟩
    right_inv := λ s => by
      simp
      ext x;
      simp
      refine ⟨λ ⟨h1, h2⟩ => ?_, λ h => ⟨?_, ?_⟩⟩
      rw [mem_sup] at h1
      obtain ⟨y, ⟨hy, ⟨z, ⟨hz, hzy⟩⟩⟩⟩ := h1
      simp at hz
      rw [← hz] at hzy
      simp at hzy
      simp at hy
      obtain ⟨z2, hz2⟩ := hy
      have h4 := s.2 _ hz2
      simp at h4
      simp_rw [h4, hzy, ← h2] at hz2
      apply hz2
      apply mem_sup_left
      simp
      refine ⟨x.2, h⟩
      apply s.2 x h

/-lemma subspacesBijection.map (X : {X : Submodule K (V × W) | Submodule.map (LinearMap.inr K V W) ⊤ ≤ X}) :
  (Submodule.map (LinearMap.inr K V W) ∘
      Submodule.map (LinearMap.snd K V W)) X = Submodule.map (LinearMap.inr K V W) ⊤ := by

  simp
  sorry-/

/-lemma prodSubmod (X : Submodule K (V × W)) : X = (Submodule.map (LinearMap.inl K V W) ∘
      Submodule.map (LinearMap.fst K V W)) X ⊔ (Submodule.map (LinearMap.inr K V W) ∘
      Submodule.map (LinearMap.snd K V W)) X := by
  rw [← Submodule.map_sup]
  --rw [← LinearMap.coe_comp]
  rw [← LinearMap.prod_eq_sup_map]
  simp
  rw [LinearMap.prod]
  ext x;
  refine ⟨λ hx => ?_, λ hx => ?_⟩
  simp
  refine ⟨⟨x.2, hx⟩, ⟨x.1, hx⟩⟩
  simp at hx
  obtain ⟨⟨x2, hx2⟩, ⟨x1, hx1⟩⟩ := hx
  sorry-/

variable [FiniteDimensional K V] [FiniteDimensional K W]

lemma subspacesDimBijection (X : {X : Submodule K (V × W) | Submodule.map (LinearMap.inr K V W) ⊤ ≤ X}) :
FiniteDimensional.finrank K X = FiniteDimensional.finrank K (subspacesBijection X) + FiniteDimensional.finrank K W := by
  rw [subspacesBijection]
  simp
  rw [← LinearMap.finrank_range_of_inj (@LinearMap.inr_injective K V W _ _ _ _ _),
    ← Submodule.map_top, ← finrank_sup_add_finrank_inf_eq, disjoint_iff.1]
  simp
  have h3 : X = (map (LinearMap.inl K V W) (map (LinearMap.fst K V W) ↑X) ⊔ map (LinearMap.inr K V W) ⊤) := by
    apply le_antisymm
    intros x hx
    rw [mem_sup]
    refine ⟨⟨x.1, 0⟩, ⟨?_, ⟨⟨0, x.2⟩, ⟨by simp, by simp⟩⟩⟩⟩
    simp
    refine ⟨x.2, hx⟩
    apply sup_le
    simp
    intros x hx
    simp at hx
    obtain ⟨⟨x1, hx1⟩, hx2⟩ := hx
    have h3 : (0, x1) ∈ X.1 := by
      apply Set.mem_of_subset_of_mem X.2.subset
      simp
    have h7 := add_mem hx1 (neg_mem h3)
    simp at h7
    rw [← hx2] at h7
    apply h7
    intros x hx
    simp at hx
    obtain ⟨x2, rfl⟩ := hx
    have hX := X.2
    simp at hX
    apply Set.mem_of_subset_of_mem (hX.subset)
    simp
  rw [← h3]
  simp
  rw [disjoint_iff]
  ext x;
  simp
  refine ⟨λ hx => ?_, λ hx => ?_⟩
  obtain ⟨⟨⟨x1, hx1⟩, hx22⟩, ⟨x2, rfl⟩⟩ := hx
  simp at hx22
  rw [hx22]
  simp
  refine ⟨⟨⟨0, ?_⟩, (Prod.mk_eq_zero.1 hx).2⟩, ⟨0, ?_⟩⟩
  rw [(Prod.mk_eq_zero.1 hx).1]
  apply zero_mem
  rw [hx]
  simp

lemma subspacesDimBijection' (X : {X : Submodule K (V × W) | ∀ x ∈ X, x.2 = 0 }) :
FiniteDimensional.finrank K (subspacesBijection.invFun X) = FiniteDimensional.finrank K X + FiniteDimensional.finrank K W := by
  rw [subspacesDimBijection]
  have h2 := (@subspacesBijection V K W).right_inv X
  simp at h2
  simp
  rw [h2]



lemma divNatThing (j : ℕ) : (j * (j + 1) / 2 : ℕ) = (j * (j + 1) : ℚ) / 2 := by
  sorry

-- ¬ Submodule.map (LinearMap.inr K V W) ⊤ ≤ X (this is probably easier for by_cases)
-- Submodule.map (LinearMap.inr K V W) ⊤ ∩ X ≠ Submodule.map (LinearMap.inr K V W) ⊤

-- the second one is dependent on the first
def subspacesBijection2 : {X : Submodule K (V × W) | ¬ Submodule.map (LinearMap.inr K V W) ⊤ ≤ X} ≃
  {((X, φ) : (Submodule K V × W) × (V × W →ₗ[K] W)) | ∀ x ∈ X, x.2 = 0 ∧ ∀ x ∉ X, φ x = 0} where
    toFun := _
    invFun := _
    left_inv := _
    right_inv := _

/-def succDimSubspaces_equivDimSubspaces (a : V) (ha : a ≠ 0) (k : ℕ) :
  {W : Submodule K ((V ⧸ (K ∙ a)) × (K ∙ a))| FiniteDimensional.finrank K W = k + 1 ∧ ⟨0, ⟨a, mem_span_singleton_self a⟩⟩ ∈ W} ≃
  {W : Submodule K ((V ⧸ (K ∙ a)) × (K ∙ a)) | FiniteDimensional.finrank K W = k ∧ ∀ x ∈ W, x.2 = 0} where
    toFun := λ r => ⟨(Submodule.map (LinearMap.inl K (V ⧸ (K ∙ a)) (K ∙ a)) ∘
      Submodule.map ((LinearMap.fst K (V ⧸ (K ∙ a)) (K ∙ a)))) r, by
      simp
      obtain ⟨hs1, hs2⟩ := r.2
      have h2 : (⟨0, ⟨a, mem_span_singleton_self a⟩⟩ : ((V ⧸ (K ∙ a)) × (K ∙ a))) ∉
        (prod (map (LinearMap.fst K (V ⧸ span K {a}) (span K {a})) r) ⊥) := by
        simp
        intros x hx hxr
        apply ha
      rw [← disjoint_span_singleton'] at h2
      have h4 : (span K {(⟨0, ⟨a, mem_span_singleton_self a⟩⟩ : ((V ⧸ (K ∙ a)) × (K ∙ a)))}) =
        Submodule.prod ⊥ (map (LinearMap.snd K (V ⧸ span K {a}) (span K {a})) ↑r) := by
        simp
        apply span_eq_of_le
        apply Set.singleton_subset_iff.2
        simp
        refine ⟨0, hs2⟩
        intros v hv
        rw [mem_span_singleton]
        simp at hv
        obtain ⟨hv1, ⟨a_1, ha_1⟩⟩ := hv
        obtain ⟨a_2, ha_2⟩ := mem_span_singleton.1 v.2.2
        refine ⟨a_2, ?_⟩
        simp
        simp_rw [← hv1, ha_2]
      have h3 : (prod (map (LinearMap.fst K (V ⧸ span K {a}) (span K {a})) r) ⊥) ⊔
        (span K {(0, { val := a, property := mem_span_singleton_self a })}) = r.1 := by
        rw [h4, prod_sup_prod]
        simp
        ext x;
        simp
        refine ⟨λ hx => ?_, λ hx => ?_⟩
        obtain ⟨⟨a_1, ⟨b, hb⟩⟩, ⟨a_2, ha_2⟩⟩ := hx
        sorry
        refine ⟨⟨0, ⟨zero_mem _, ?_⟩⟩, ?_⟩
        obtain ⟨c, hc⟩ := mem_span_singleton.1 x.2.2
        have h2 : (⟨0, ⟨x.2, x.2.2⟩⟩ : ((V ⧸ (K ∙ a)) × (K ∙ a))) ∈ r.1 := by
          simp_rw [← hc]
          have h3 := smul_mem r c hs2
          simp at h3
          apply h3
        have h4 := sub_mem hx h2
        simp at h4
        have h5 : x - ((0 : (V ⧸ (K ∙ a))), x.2) = (x.1, (⟨0, zero_mem _⟩ : (K ∙ a))) := by
          rw [Prod.mk.inj_iff]
          simp

          sorry
          /-have h3 := @add_neg_self (K ∙ a) _ x.2
          simp_rw [← h3]
          rw [← add_zero x.1]
          have h6 : (x.1 + 0, x.2 + -x.2) = (x.1, x.2) + (0, -x.2) := by
            exact rfl
          rw [h6]
          simp
          have h7 : -((0 : (V ⧸ (K ∙ a))), x.2) = (-0, -x.2) := by
            exact rfl
          simp_rw [h7]
          simp-/
        rw [← h5]
        apply h4
        refine ⟨x.1, hx⟩
      rw [← h3] at hs1
      rw [disjoint_iff, ← Submodule.finrank_eq_zero] at h2
      rw [← add_zero (FiniteDimensional.finrank K _), ← h2, finrank_sup_add_finrank_inf_eq,
        finrank_span_singleton, add_right_cancel_iff] at hs1
      apply hs1
      apply Prod.mk_eq_zero.1.mt
      simp
      apply ha

      apply Prod.mk_eq_zero.1.mt
      simp
      apply ha⟩
    invFun := λ s => ⟨span K (insert (⟨0, ⟨a, mem_span_singleton_self a⟩⟩ : ((V ⧸ (K ∙ a)) × (K ∙ a))) s), by
      simp
      refine ⟨?_, Set.mem_of_subset_of_mem (subset_span) (Set.mem_insert _ _)⟩
      rw [span_insert, span_eq]
      have h2 : (⟨0, ⟨a, mem_span_singleton_self a⟩⟩ : ((V ⧸ (K ∙ a)) × (K ∙ a))) ∉ s.1 := by
        by_contra h4
        have h3 := s.2.2
        specialize h3 _ h4
        simp at h3
        apply ha h3
      rw [← disjoint_span_singleton', disjoint_iff, inf_comm, ← Submodule.finrank_eq_zero] at h2
      rw [← add_zero (FiniteDimensional.finrank K _), ← h2, finrank_sup_add_finrank_inf_eq]
      rw [finrank_span_singleton, s.2.1, add_comm]
      simp
      apply ha
      simp
      apply ha⟩
    left_inv := λ r => by
      have h3 := r.2.2
      ext;
      refine ⟨λ hx => ?_, λ hx => ?_⟩
      simp at hx
      rw [mem_span_insert] at hx
      obtain ⟨a_1, ⟨z, ⟨hz1, rfl⟩⟩⟩ := hx
      apply Submodule.add_mem
      apply Submodule.smul_mem
      apply h3
      sorry
    right_inv := _-/

/-def succDimSubspaces_equivDimSubspaces' (a : V) (ha : a ≠ 0) (k : ℕ) :
  {W : Submodule K V | FiniteDimensional.finrank K W = k + 1 ∧ a ∈ W} ≃
  {W : Submodule K (V ⧸ (K ∙ a)) | FiniteDimensional.finrank K W = k} where
    toFun := λ x => ⟨Submodule.map (K ∙ a).mkQ x, by
      simp
      obtain ⟨hx1, hx2⟩ := x.2
      rw [← Submodule.finrank_quotient_add_finrank (K ∙ ⟨a, hx2⟩), finrank_span_singleton] at hx1
      simp [Order.succ_eq_succ_iff] at hx1
      simp [← hx1]
      apply LinearEquiv.finrank_eq
      --have h2 := LinearEquiv.quotEquivOfEquiv

      --apply LinearEquiv.quotEquivOfEquiv
      sorry
      simp
      apply ha⟩
    invFun := λ y => ⟨Submodule.comapMkQOrderEmbedding (K ∙ a) y ⊔ (K ∙ a), by
      simp
      sorry⟩
    left_inv := λ x => by
      simp
      sorry
    right_inv := λ y => by
      simp
      sorry-/

/-def linIndCard (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] [Fintype K] [Fintype V]
[FiniteDimensional K V] [∀ n : ℕ, DecidablePred fun (v : ((Fin n) → V)) ↦ LinearIndependent K v]
(n : ℕ) : Finset ((Fin n) → V) :=
  (@Finset.univ ((Fin n) → V)).filter (λ v => LinearIndependent K v)

variable [Fintype V] [DecidableEq (Submodule K V)]
variable [∀ n : ℕ, DecidablePred fun (v : ((Fin n) → V)) ↦ LinearIndependent K v]

lemma linIndCardEqQFactDesc (n k : ℕ) :
  (q_factorial'_desc n k).eval ↑(Fintype.card K) = (linIndCard K V k).card := by
  induction' k with k hk
  rw [linIndCard, q_factorial'_desc_zero]
  simp
  rw [Finset.filter_singleton, if_pos]
  simp
  rw [default]
  rw [Fintype.linearIndependent_iff]
  intros g hg i
  sorry

  sorry

lemma dim_unique_subspaces [Nontrivial V] (h : 0 < FiniteDimensional.finrank K V) :
∃ (X : Finset (Submodule K V)), ∀ (y : Submodule K V), y ∈ X → FiniteDimensional.finrank K y = 1 ∧
Finset.card X = FiniteDimensional.finrank K V ∧ (Sup X) = V := by
  have B := (FiniteDimensional.finBasis K V)
  use Finset.image (λ x => K ∙ ((DFunLike.coe B) x)) (@Finset.univ (Fin (FiniteDimensional.finrank K V)) _)
  intros y hyX
  obtain ⟨a, ⟨ha1, rfl⟩⟩ := Finset.mem_image.1 hyX
  refine ⟨finrank_span_singleton (B.ne_zero a), ⟨?_, ?_⟩⟩
  apply Eq.symm
  apply FiniteDimensional.finrank_eq_of_rank_eq
  rw [rank_eq_card_basis B]
  sorry
  --rw [← Submodule.span_iUnion]
  --rw [Submodule.span_eq_iSup_of_singleton_spans]
  --simp
  --have h2 := FiniteDimensional.finrank_eq_card_basis B

  --rw [FiniteDimensional.finrank_eq_card_basis']

  --simp
  --rw [← ⊤.range_subtype, ← Submodule.map_top, ← B.span_eq]

  /-have M := λ x : (fin (finite_dimensional.finrank K ↥S)), K ∙ B ↑x,
  --have M2 := λ (y : subspace K V), ∃ x : fin (finite_dimensional.finrank K ↥S), (M x) = y.to_submodule,
  have M2 := set.image M (@univ (fin (finite_dimensional.finrank K ↥S)) _),
  use M2,-/
  sorry


-- linearIndependent_fin_cons
theorem grassmannian_finite [Fintype K] [FiniteDimensional K V] (k : ℕ) :
Fintype (Grassmannian K V k) := by
  induction' k with k hk
  · simp
    rw [Grassmannian]
    simp
    sorry
  · rw [Grassmannian]
    simp [finBasisOfFinrankEq, linearIndependent_fin_succ]

    sorry

def fintypeOfFintype [Fintype K] [FiniteDimensional K V] : Fintype (Submodule K V) where
  elems := sorry
  complete := sorry

/-- Given a `Module K V` and a nat `k`, then `subspacesDim n s` is the finset of submodules of
`V` of dimension `k`. -/
def subspacesDim [FiniteDimensional K V] (k : ℕ) : Finset (Submodule K V) := sorry
  /-⟨((s.1.powersetCard n).pmap Finset.mk) fun _t h => nodup_of_le (mem_powersetCard.1 h).1 s.2,
    s.2.powersetCard.pmap fun _a _ha _b _hb => congr_arg Finset.val⟩-/-/


end subspacesCard
