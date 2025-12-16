/-
Copyright (c) 2021 Ashvni Narayanan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ashvni Narayanan, David Loeffler
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.NumberTheory.Bernoulli

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

-/

@[expose] public section


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

theorem coeff_bernoulli (n i : ℕ) :
    (bernoulli n).coeff i = if i ≤ n then (_root_.bernoulli (n - i) * choose n i) else 0 := by
  simp only [bernoulli, finset_sum_coeff, coeff_monomial]
  split_ifs with h
  · convert sum_ite_eq_of_mem (range (n + 1)) (n - i) _ (by grind) using 3 <;> grind [choose_symm]
  · exact Finset.sum_eq_zero <| by grind

/-
### examples
-/
section Examples

@[simp]
theorem bernoulli_zero : bernoulli 0 = 1 := by simp [bernoulli]

@[simp]
theorem bernoulli_one : bernoulli 1 = X - C 2⁻¹ := by
  simp [bernoulli, ← smul_X_eq_monomial, sum_range_succ, ← C_1, -map_one, neg_div, sub_eq_add_neg]

@[simp]
theorem bernoulli_eval_zero (n : ℕ) : (bernoulli n).eval 0 = _root_.bernoulli n := by
  rw [bernoulli, eval_finset_sum, sum_range_succ]
  have : ∑ x ∈ range n, _root_.bernoulli x * n.choose x * 0 ^ (n - x) = 0 := by
    apply sum_eq_zero fun x hx => _
    intro x hx
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

theorem bernoulli_three_eval_one_quarter :
    (Polynomial.bernoulli 3).eval (1 / 4) = 3 / 64 := by
  simp_rw [Polynomial.bernoulli, Finset.sum_range_succ, Polynomial.eval_add,
    Polynomial.eval_monomial]
  rw [Finset.sum_range_zero, Polynomial.eval_zero, zero_add, _root_.bernoulli_one]
  rw [bernoulli_eq_bernoulli'_of_ne_one zero_ne_one, bernoulli'_zero,
    bernoulli_eq_bernoulli'_of_ne_one (by decide : 2 ≠ 1), bernoulli'_two,
    bernoulli_eq_bernoulli'_of_ne_one (by decide : 3 ≠ 1), bernoulli'_three]
  norm_num

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
      · rw [← Nat.cast_mul, choose_mul (le_add_right _ _), Nat.cast_mul, add_tsub_cancel_left,
          mul_assoc, mul_comm, ← smul_eq_mul, ← smul_monomial]
  simp_rw [← sum_smul]
  rw [sum_range_succ_comm]
  simp only [add_eq_left, mul_one, cast_one, cast_add, add_tsub_cancel_left,
    choose_succ_self_right, one_smul, _root_.bernoulli_zero, sum_singleton, zero_add,
    map_add, range_one, mul_one]
  apply sum_eq_zero fun x hx => _
  have f : ∀ x ∈ range n, ¬n + 1 - x = 1 := by grind
  intro x hx
  rw [sum_bernoulli]
  have g : ite (n + 1 - x = 1) (1 : ℚ) 0 = 0 := by
    simp only [ite_eq_right_iff, one_ne_zero]
    intro h₁
    exact (f x hx) h₁
  rw [g, zero_smul]

/-- Another version of `Polynomial.sum_bernoulli`. -/
theorem bernoulli_eq_sub_sum (n : ℕ) :
    (n + 1) • bernoulli n =
      (n + 1) • X ^ n - ∑ k ∈ Finset.range n, ((n + 1).choose k) • bernoulli k := by
  simp_rw [← cast_smul_eq_nsmul (R := ℚ), smul_X_eq_monomial,
    Nat.cast_succ, ← sum_bernoulli n, sum_range_succ_sub_sum, choose_succ_self_right,
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

theorem bernoulli_comp_one_add_X (n : ℕ) :
    (bernoulli n).comp (1 + X) = bernoulli n + n • X ^ (n - 1) := by
  refine Nat.strong_induction_on n fun d hd => ?_
  cases d with
  | zero => simp
  | succ d =>
  rw [← smul_right_inj (show d + 2 ≠ 0 by positivity), ← smul_comp, smul_add]
  simp only [bernoulli_eq_sub_sum, sub_comp, sum_comp, add_assoc, one_add_one_eq_two, smul_smul]
  conv_lhs =>
    congr
    · skip
    · apply_congr
      · skip
      · rw [smul_comp, hd _ (mem_range.1 (by assumption))]
  simp_rw [smul_add, sum_add_distrib, sub_add, sub_add_eq_sub_sub_swap, sub_sub_eq_add_sub]
  congr 1
  rw [show ∀ a b c d : ℚ[X], a - b = c + d ↔ a - c = b + d by grind]
  calc ((d + 2) • X ^ (d + 1)).comp (1 + X) - (d + 2) • X ^ (d + 1)
    _ = (d + 2) • ∑ i ∈ range (d + 1), (d + 1).choose i • X ^ i := by
      rw [smul_comp, ← smul_sub, X_pow_comp, one_add_X_pow_sub_X_pow]
    _ = ∑ i ∈ range (d + 1), ((d + 2).choose (i + 1) * (i + 1)) • X ^ i := by
      simp_rw [smul_sum, smul_smul, ← add_one_mul_choose_eq (d + 1)]
    _ = ∑ i ∈ range (d + 1), ((d + 2).choose i * i) • X ^ (i - 1) +
          (((d + 2).choose (d + 1)) * (d + 1)) • X ^ (d + 1 - 1) := by
      rw [← sum_range_succ _ (d + 1)]; simp [sum_range_succ']
    _ = ∑ i ∈ range (d + 1), (d + 2).choose i • i • X ^ (i - 1) +
          ((d + 2) * (d + 1)) • X ^ (d + 1 - 1) := by
      simp [choose_succ_self_right, add_assoc, mul_assoc]

theorem bernoulli_eval_one_add (n : ℕ) (x : ℚ) :
    (bernoulli n).eval (1 + x) = (bernoulli n).eval x + n * x ^ (n - 1) := by
  have := bernoulli_comp_one_add_X n
  simpa using congr(Polynomial.eval x $this)

theorem bernoulli_comp_neg_X (n : ℕ) :
    (bernoulli n).comp (-X) = (-1) ^ n • (bernoulli n + n • X ^ (n - 1)) := by
  cases n with
  | zero => simp
  | succ n =>
  ext i
  rw [← neg_one_mul, ← C_1, ← C_neg, Polynomial.comp_C_mul_X_coeff, coeff_smul, coeff_add,
    coeff_smul, coeff_bernoulli, coeff_X_pow]
  split_ifs with h h'
  · subst h'
    simp
    grind
  · cases (n + 1 - i).even_or_odd with
    | inl h => grind [neg_one_pow_eq_ite]
    | inr h => rw [bernoulli_eq_zero_of_odd] <;> grind
  · grind
  · simp

theorem bernoulli_eval_neg (n : ℕ) (x : ℚ) :
    (bernoulli n).eval (-x) = (-1) ^ n * ((bernoulli n).eval x + n * x ^ (n - 1)) := by
  simpa [mul_add] using congr_arg (Polynomial.eval x) (bernoulli_comp_neg_X n)

theorem bernoulli_comp_one_sub_X (n : ℕ) :
    (bernoulli n).comp (1 -X) = (-1) ^ n * bernoulli n := by
  cases n with
  | zero => simp
  | succ n =>
    trans ((bernoulli (n + 1)).comp (1 + X)).comp (-X)
    · simp [comp_assoc, sub_eq_add_neg]
    simp [bernoulli_comp_one_add_X, bernoulli_comp_neg_X, neg_pow (X : Polynomial ℚ), add_assoc]
    ring

theorem bernoulli_eval_one_sub (n : ℕ) (x : ℚ) :
    (bernoulli n).eval (1 - x) = (-1) ^ n * (bernoulli n).eval x := by
  simpa using congr_arg (Polynomial.eval x) (bernoulli_comp_one_sub_X n)

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
  simp only [map_sub, tsub_self, constantCoeff_one, constantCoeff_exp,
    coeff_zero_eq_constantCoeff, mul_zero, sub_self, add_zero]
  -- Let's multiply both sides by (n+1)! (OK because it's a unit)
  have hnp1 : IsUnit ((n + 1)! : ℚ) := IsUnit.mk0 _ (mod_cast factorial_ne_zero (n + 1))
  rw [← (hnp1.map (algebraMap ℚ A)).mul_right_inj]
  -- do trivial rearrangements to make RHS (n+1)*t^n
  rw [mul_left_comm, ← map_mul]
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
    one_div, PowerSeries.coeff_one, coeff_exp, sub_zero, Algebra.smul_def,
    mul_right_comm _ ((aeval t) _), ← mul_assoc, ← map_mul, ← Polynomial.C_eq_algebraMap,
    Polynomial.aeval_mul, Polynomial.aeval_C]
  -- finally cancel the Bernoulli polynomial and the algebra_map
  field_simp

end Polynomial
