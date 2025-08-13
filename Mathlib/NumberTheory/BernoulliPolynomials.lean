/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, David Loeffler
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.NumberTheory.Bernoulli

/-!
# Bernoulli polynomials

The [Bernoulli polynomials](https://en.wikipedia.org/wiki/Bernoulli_polynomials)
are an important tool obtained from Bernoulli numbers.

## Mathematical overview

The $n$-th Bernoulli polynomial is defined as
$$ B_n(X) = ∑_{k = 0}^n {n \choose k} (-1)^k B_k X^{n - k} $$
where $B_k$ is the $k$-th Bernoulli number. The Bernoulli polynomials are generating functions,
$$ \frac{t e^{tX} }{ e^t - 1} = ∑_{n = 0}^{\infty} B_n(X) \frac{t^n}{n!} $$

## Implementation detail

Bernoulli polynomials are defined using `bernoulli`, the Bernoulli numbers.

## Main theorems

- `sum_bernoulli`: The sum of the $k^\mathrm{th}$ Bernoulli polynomial with binomial
  coefficients up to `n` is `(n + 1) * X^n`.
- `Polynomial.bernoulli_generating_function`: The Bernoulli polynomials act as generating functions
  for the exponential.

## TODO

- `bernoulli_eval_one_neg` : $$ B_n(1 - x) = (-1)^n B_n(x) $$

-/


noncomputable section

open Nat Polynomial

open Nat Finset

namespace Polynomial

/-- The Bernoulli polynomials are defined in terms of the negative Bernoulli numbers. -/
def bernoulli (n : ℕ) : ℚ[X] :=
  ∑ i ∈ range (n + 1), Polynomial.monomial (n - i) (_root_.bernoulli i * choose n i)

theorem bernoulli_def (n : ℕ) : bernoulli n =
    ∑ i ∈ range (n + 1), Polynomial.monomial i (_root_.bernoulli (n - i) * choose n i) := by
  rw [← sum_range_reflect, add_succ_sub_one, add_zero, bernoulli]
  apply sum_congr rfl
  rintro x hx
  rw [mem_range_succ_iff] at hx
  rw [choose_symm hx, tsub_tsub_cancel_of_le hx]

/-
### examples
-/
section Examples

@[simp]
theorem bernoulli_zero : bernoulli 0 = 1 := by simp [bernoulli]

@[simp]
theorem bernoulli_eval_zero (n : ℕ) : (bernoulli n).eval 0 = _root_.bernoulli n := by
  rw [bernoulli, eval_finset_sum, sum_range_succ]
  have : ∑ x ∈ range n, _root_.bernoulli x * n.choose x * 0 ^ (n - x) = 0 := by
    apply sum_eq_zero fun x hx => _
    intros x hx
    simp [tsub_eq_zero_iff_le, mem_range.1 hx]
  simp [this]

@[simp]
theorem bernoulli_eval_one (n : ℕ) : (bernoulli n).eval 1 = bernoulli' n := by
  simp only [bernoulli, eval_finset_sum]
  simp only [← succ_eq_add_one, sum_range_succ, mul_one, cast_one, choose_self,
    (_root_.bernoulli _).mul_comm, sum_bernoulli, one_pow, mul_one, eval_monomial, one_mul]
  by_cases h : n = 1
  · norm_num [h]
  · simp [h, bernoulli_eq_bernoulli'_of_ne_one h]

end Examples

theorem derivative_bernoulli_add_one (k : ℕ) :
    Polynomial.derivative (bernoulli (k + 1)) = (k + 1) * bernoulli k := by
  simp_rw [bernoulli, derivative_sum, derivative_monomial, Nat.sub_sub, Nat.add_sub_add_right]
  -- LHS sum has an extra term, but the coefficient is zero:
  rw [range_add_one, sum_insert notMem_range_self, tsub_self, cast_zero, mul_zero,
    map_zero, zero_add, mul_sum]
  -- the rest of the sum is termwise equal:
  refine sum_congr (by rfl) fun m _ => ?_
  conv_rhs => rw [← Nat.cast_one, ← Nat.cast_add, ← C_eq_natCast, C_mul_monomial, mul_comm]
  rw [mul_assoc, mul_assoc, ← Nat.cast_mul, ← Nat.cast_mul]
  congr 3
  rw [(choose_mul_succ_eq k m).symm]

theorem derivative_bernoulli (k : ℕ) :
    Polynomial.derivative (bernoulli k) = k * bernoulli (k - 1) := by
  cases k with
  | zero => rw [Nat.cast_zero, zero_mul, bernoulli_zero, derivative_one]
  | succ k => exact mod_cast derivative_bernoulli_add_one k

@[simp]
nonrec theorem sum_bernoulli (n : ℕ) :
    (∑ k ∈ range (n + 1), ((n + 1).choose k : ℚ) • bernoulli k) = monomial n (n + 1 : ℚ) := by
  simp_rw [bernoulli_def, Finset.smul_sum, Finset.range_eq_Ico, ← Finset.sum_Ico_Ico_comm,
    Finset.sum_Ico_eq_sum_range]
  simp only [add_tsub_cancel_left, tsub_zero, zero_add, map_add]
  simp_rw [smul_monomial, mul_comm (_root_.bernoulli _) _, smul_eq_mul, ← mul_assoc]
  conv_lhs =>
    apply_congr
    · skip
    · conv =>
      apply_congr
      · skip
      · rw [← Nat.cast_mul, choose_mul ((le_tsub_iff_left <| mem_range_le (by assumption)).1 <|
            mem_range_le (by assumption)) (le.intro rfl),
          Nat.cast_mul, add_tsub_cancel_left, mul_assoc, mul_comm, ← smul_eq_mul, ←
          smul_monomial]
  simp_rw [← sum_smul]
  rw [sum_range_succ_comm]
  simp only [add_eq_left, mul_one, cast_one, cast_add, add_tsub_cancel_left,
    choose_succ_self_right, one_smul, _root_.bernoulli_zero, sum_singleton, zero_add,
    map_add, range_one, mul_one]
  apply sum_eq_zero fun x hx => _
  have f : ∀ x ∈ range n, ¬n + 1 - x = 1 := by grind [Finset.mem_range]
  intro x hx
  rw [sum_bernoulli]
  have g : ite (n + 1 - x = 1) (1 : ℚ) 0 = 0 := by
    simp only [ite_eq_right_iff, one_ne_zero]
    intro h₁
    exact (f x hx) h₁
  rw [g, zero_smul]

/-- Another version of `Polynomial.sum_bernoulli`. -/
theorem bernoulli_eq_sub_sum (n : ℕ) :
    (n.succ : ℚ) • bernoulli n =
      monomial n (n.succ : ℚ) - ∑ k ∈ Finset.range n, ((n + 1).choose k : ℚ) • bernoulli k := by
  rw [Nat.cast_succ, ← sum_bernoulli n, sum_range_succ, add_sub_cancel_left, choose_succ_self_right,
    Nat.cast_succ]

/-- Another version of `sum_range_pow`. -/
theorem sum_range_pow_eq_bernoulli_sub (n p : ℕ) :
    ((p + 1 : ℚ) * ∑ k ∈ range n, (k : ℚ) ^ p) = (bernoulli p.succ).eval (n : ℚ) -
    _root_.bernoulli p.succ := by
  rw [sum_range_pow, bernoulli_def, eval_finset_sum, ← sum_div, mul_div_cancel₀ _ _]
  · simp_rw [eval_monomial]
    symm
    rw [← sum_flip _, sum_range_succ]
    simp only [tsub_self, tsub_zero, choose_zero_right, cast_one, mul_one, _root_.pow_zero,
      add_tsub_cancel_right]
    apply sum_congr rfl fun x hx => _
    intro x hx
    apply congr_arg₂ _ (congr_arg₂ _ _ _) rfl
    · rw [Nat.sub_sub_self (mem_range_le hx)]
    · rw [← choose_symm (mem_range_le hx)]
  · norm_cast

/-- Rearrangement of `Polynomial.sum_range_pow_eq_bernoulli_sub`. -/
theorem bernoulli_succ_eval (n p : ℕ) : (bernoulli p.succ).eval (n : ℚ) =
    _root_.bernoulli p.succ + (p + 1 : ℚ) * ∑ k ∈ range n, (k : ℚ) ^ p := by
  apply eq_add_of_sub_eq'
  rw [sum_range_pow_eq_bernoulli_sub]

theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
    (bernoulli n).eval (1 + x) = (bernoulli n).eval x + n * x ^ (n - 1) := by
  refine Nat.strong_induction_on n fun d hd => ?_
  have nz : ((d.succ : ℕ) : ℚ) ≠ 0 := by norm_cast
  apply (mul_right_inj' nz).1
  rw [← smul_eq_mul, ← eval_smul, bernoulli_eq_sub_sum, mul_add, ← smul_eq_mul, ← eval_smul,
    bernoulli_eq_sub_sum, eval_sub, eval_finset_sum]
  conv_lhs =>
    congr
    · skip
    · apply_congr
      · skip
      · rw [eval_smul, hd _ (mem_range.1 (by assumption))]
  rw [eval_sub, eval_finset_sum]
  simp_rw [eval_smul, smul_add]
  rw [sum_add_distrib, sub_add, sub_eq_sub_iff_sub_eq_sub, _root_.add_sub_sub_cancel]
  conv_rhs =>
    congr
    · skip
    · congr
      rw [succ_eq_add_one, ← choose_succ_self_right d]
  rw [Nat.cast_succ, ← smul_eq_mul, ← sum_range_succ _ d, eval_monomial_one_add_sub]
  simp_rw [smul_eq_mul]

open PowerSeries

variable {A : Type*} [CommRing A] [Algebra ℚ A]

-- TODO: define exponential generating functions, and use them here
-- This name should probably be updated afterwards
/-- The theorem that $(e^X - 1) * ∑ Bₙ(t)* X^n/n! = Xe^{tX}$ -/
theorem bernoulli_generating_function (t : A) :
    (mk fun n => aeval t ((1 / n ! : ℚ) • bernoulli n)) * (exp A - 1) =
      PowerSeries.X * rescale t (exp A) := by
  -- check equality of power series by checking coefficients of X^n
  ext n
  -- n = 0 case solved by `simp`
  cases n with | zero => simp | succ n =>
  -- n ≥ 1, the coefficients is a sum to n+2, so use `sum_range_succ` to write as
  -- last term plus sum to n+1
  rw [coeff_succ_X_mul, coeff_rescale, coeff_exp, PowerSeries.coeff_mul,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ]
  -- last term is zero so kill with `add_zero`
  simp only [RingHom.map_sub, tsub_self, constantCoeff_one, constantCoeff_exp,
    coeff_zero_eq_constantCoeff, mul_zero, sub_self, add_zero]
  -- Let's multiply both sides by (n+1)! (OK because it's a unit)
  have hnp1 : IsUnit ((n + 1)! : ℚ) := IsUnit.mk0 _ (mod_cast factorial_ne_zero (n + 1))
  rw [← (hnp1.map (algebraMap ℚ A)).mul_right_inj]
  -- do trivial rearrangements to make RHS (n+1)*t^n
  rw [mul_left_comm, ← RingHom.map_mul]
  change _ = t ^ n * algebraMap ℚ A (((n + 1) * n ! : ℕ) * (1 / n !))
  rw [cast_mul, mul_assoc,
    mul_one_div_cancel (show (n ! : ℚ) ≠ 0 from cast_ne_zero.2 (factorial_ne_zero n)), mul_one,
    mul_comm (t ^ n), ← aeval_monomial, cast_add, cast_one]
  -- But this is the RHS of `Polynomial.sum_bernoulli`
  rw [← sum_bernoulli, Finset.mul_sum, map_sum]
  -- and now we have to prove a sum is a sum, but all the terms are equal.
  apply Finset.sum_congr rfl
  -- The rest is just trivialities, hampered by the fact that we're coercing
  -- factorials and binomial coefficients between ℕ and ℚ and A.
  intro i hi
  -- deal with coefficients of e^X-1
  simp only [Nat.cast_choose ℚ (mem_range_le hi), coeff_mk, if_neg (mem_range_sub_ne_zero hi),
    one_div, PowerSeries.coeff_one, coeff_exp, sub_zero, LinearMap.map_sub,
    Algebra.smul_def, mul_right_comm _ ((aeval t) _), ← mul_assoc, ←
    RingHom.map_mul, ← Polynomial.C_eq_algebraMap, Polynomial.aeval_mul,
    Polynomial.aeval_C]
  -- finally cancel the Bernoulli polynomial and the algebra_map
  field_simp

end Polynomial
