/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.Group.Nat.Units
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Field
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-!
# Special values of Hurwitz and Riemann zeta functions

This file gives the formula for `ζ (2 * k)`, for `k` a non-zero integer, in terms of Bernoulli
numbers. More generally, we give formulae for any Hurwitz zeta functions at any (strictly) negative
integer in terms of Bernoulli polynomials.

(Note that most of the actual work for these formulae is done elsewhere, in
`Mathlib/NumberTheory/ZetaValues.lean`. This file has only those results which really need the
definition of Hurwitz zeta and related functions, rather than working directly with the defining
sums in the convergence range.)

## Main results

- `hurwitzZeta_neg_nat`: for `k : ℕ` with `k ≠ 0`, and any `x ∈ ℝ / ℤ`, the special value
  `hurwitzZeta x (-k)` is equal to `-(Polynomial.bernoulli (k + 1) x) / (k + 1)`.
- `riemannZeta_neg_nat_eq_bernoulli` : for any `k ∈ ℕ` we have the formula
  `riemannZeta (-k) = (-1) ^ k * bernoulli (k + 1) / (k + 1)`
- `riemannZeta_two_mul_nat`: formula for `ζ(2 * k)` for `k ∈ ℕ, k ≠ 0` in terms of Bernoulli
  numbers

## TODO

* Extend to cover Dirichlet L-functions.
* The formulae are correct for `s = 0` as well, but we do not prove this case, since this requires
  Fourier series which are only conditionally convergent, which is difficult to approach using the
  methods in the library at the present time (May 2024).
-/

public section

open Complex Real Set

open scoped Nat

namespace HurwitzZeta

variable {k : ℕ} {x : ℝ}

/-- Express the value of `cosZeta` at a positive even integer as a value
of the Bernoulli polynomial. -/
theorem cosZeta_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc 0 1) :
    cosZeta x (2 * k) = (-1) ^ (k + 1) * (2 * π) ^ (2 * k) / 2 / (2 * k)! *
      ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [← (hasSum_nat_cosZeta x (?_ : 1 < re (2 * k))).tsum_eq]
  · refine Eq.trans ?_ <|
      (congr_arg ofReal (hasSum_one_div_nat_pow_mul_cos hk hx).tsum_eq).trans ?_
    · rw [ofReal_tsum]
      refine tsum_congr fun n ↦ ?_
      norm_cast
      ring_nf
    · push_cast
      congr 1
      have : (Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ) = _ :=
        (Polynomial.map_map (algebraMap ℚ ℝ) ofRealHom _).symm
      rw [this, ← ofRealHom_eq_coe, ← ofRealHom_eq_coe]
      apply Polynomial.map_aeval_eq_aeval_map (by simp)
  · norm_cast
    lia

/--
Express the value of `sinZeta` at an odd integer `> 1` as a value of the Bernoulli polynomial.

Note that this formula is also correct for `k = 0` (i.e. for the value at `s = 1`), but we do not
prove it in this case, owing to the additional difficulty of working with series that are only
conditionally convergent.
-/
theorem sinZeta_two_mul_nat_add_one (hk : k ≠ 0) (hx : x ∈ Icc 0 1) :
    sinZeta x (2 * k + 1) = (-1) ^ (k + 1) * (2 * π) ^ (2 * k + 1) / 2 / (2 * k + 1)! *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [← (hasSum_nat_sinZeta x (?_ : 1 < re (2 * k + 1))).tsum_eq]
  · refine Eq.trans ?_ <|
      (congr_arg ofReal (hasSum_one_div_nat_pow_mul_sin hk hx).tsum_eq).trans ?_
    · rw [ofReal_tsum]
      refine tsum_congr fun n ↦ ?_
      norm_cast
      ring_nf
    · push_cast
      congr 1
      have : (Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ) = _ :=
        (Polynomial.map_map (algebraMap ℚ ℝ) ofRealHom _).symm
      rw [this, ← ofRealHom_eq_coe, ← ofRealHom_eq_coe]
      apply Polynomial.map_aeval_eq_aeval_map (by simp)
  · norm_cast
    lia

/-- Reformulation of `cosZeta_two_mul_nat` using `Gammaℂ`. -/
theorem cosZeta_two_mul_nat' (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    cosZeta x (2 * k) = (-1) ^ (k + 1) / (2 * k) / Gammaℂ (2 * k) *
      ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [cosZeta_two_mul_nat hk hx]
  congr 1
  have : (2 * k)! = (2 * k) * Complex.Gamma (2 * k) := by
    rw [(by { norm_cast; lia } : 2 * (k : ℂ) = ↑(2 * k - 1) + 1), Complex.Gamma_nat_eq_factorial,
      ← Nat.cast_add_one, ← Nat.cast_mul, ← Nat.factorial_succ, Nat.sub_add_cancel (by lia)]
  simp_rw [this, Gammaℂ, cpow_neg, ← div_div, div_inv_eq_mul, div_mul_eq_mul_div, div_div,
    mul_right_comm (2 : ℂ) (k : ℂ)]
  norm_cast

/-- Reformulation of `sinZeta_two_mul_nat_add_one` using `Gammaℂ`. -/
theorem sinZeta_two_mul_nat_add_one' (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    sinZeta x (2 * k + 1) = (-1) ^ (k + 1) / (2 * k + 1) / Gammaℂ (2 * k + 1) *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rw [sinZeta_two_mul_nat_add_one hk hx]
  congr 1
  have : (2 * k + 1)! = (2 * k + 1) * Complex.Gamma (2 * k + 1) := by
    rw [(by simp : Complex.Gamma (2 * k + 1) = Complex.Gamma (↑(2 * k) + 1)),
       Complex.Gamma_nat_eq_factorial, ← Nat.cast_ofNat (R := ℂ), ← Nat.cast_mul,
      ← Nat.cast_add_one, ← Nat.cast_mul, ← Nat.factorial_succ]
  simp_rw [this, Gammaℂ, cpow_neg, ← div_div, div_inv_eq_mul, div_mul_eq_mul_div, div_div]
  rw [(by simp : 2 * (k : ℂ) + 1 = ↑(2 * k + 1)), cpow_natCast]
  ring

theorem hurwitzZetaEven_one_sub_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZetaEven x (1 - 2 * k) =
      -1 / (2 * k) * ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  have h1 (n : ℕ) : (2 * k : ℂ) ≠ -n := by
    rw [← Int.cast_ofNat, ← Int.cast_natCast, ← Int.cast_mul, ← Int.cast_natCast n, ← Int.cast_neg,
      Ne, Int.cast_inj, ← Ne]
    refine ne_of_gt ((neg_nonpos_of_nonneg n.cast_nonneg).trans_lt (mul_pos two_pos ?_))
    exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have h2 : (2 * k : ℂ) ≠ 1 := by norm_cast; simp
  have h3 : Gammaℂ (2 * k) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero h1)
    simp [pi_ne_zero]
  rw [hurwitzZetaEven_one_sub _ h1 (Or.inr h2), ← Gammaℂ, cosZeta_two_mul_nat' hk hx, ← mul_assoc,
    ← mul_div_assoc, mul_assoc, mul_div_cancel_left₀ _ h3, ← mul_div_assoc]
  congr 2
  rw [mul_div_assoc, mul_div_cancel_left₀ _ two_ne_zero, ← ofReal_natCast, ← ofReal_mul,
    ← ofReal_cos, mul_comm π, ← sub_zero (k * π), cos_nat_mul_pi_sub, Real.cos_zero, mul_one,
    ofReal_pow, ofReal_neg, ofReal_one, pow_succ, mul_neg_one, mul_neg, ← mul_pow, neg_one_mul,
    neg_neg, one_pow]

theorem hurwitzZetaOdd_neg_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZetaOdd x (-(2 * k)) =
    -1 / (2 * k + 1) * ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  have h1 (n : ℕ) : (2 * k + 1 : ℂ) ≠ -n := by
    rw [← Int.cast_ofNat, ← Int.cast_natCast, ← Int.cast_mul, ← Int.cast_natCast n, ← Int.cast_neg,
      ← Int.cast_one, ← Int.cast_add, Ne, Int.cast_inj, ← Ne]
    refine ne_of_gt ((neg_nonpos_of_nonneg n.cast_nonneg).trans_lt ?_)
    positivity
  have h3 : Gammaℂ (2 * k + 1) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) (Gamma_ne_zero h1)
    simp [pi_ne_zero]
  rw [(by simp : -(2 * k : ℂ) = 1 - (2 * k + 1)),
    hurwitzZetaOdd_one_sub _ h1, ← Gammaℂ, sinZeta_two_mul_nat_add_one' hk hx, ← mul_assoc,
    ← mul_div_assoc, mul_assoc, mul_div_cancel_left₀ _ h3, ← mul_div_assoc]
  congr 2
  rw [mul_div_assoc, add_div, mul_div_cancel_left₀ _ two_ne_zero, ← ofReal_natCast,
    ← ofReal_one, ← ofReal_ofNat, ← ofReal_div, ← ofReal_add, ← ofReal_mul,
    ← ofReal_sin, mul_comm π, add_mul, mul_comm (1 / 2), mul_one_div, Real.sin_add_pi_div_two,
    ← sub_zero (k * π), cos_nat_mul_pi_sub, Real.cos_zero, mul_one,
    ofReal_pow, ofReal_neg, ofReal_one, pow_succ, mul_neg_one, mul_neg, ← mul_pow, neg_one_mul,
    neg_neg, one_pow]

-- private because it is superseded by `hurwitzZeta_neg_nat` below
private lemma hurwitzZeta_one_sub_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZeta x (1 - 2 * k) =
      -1 / (2 * k) * ((Polynomial.bernoulli (2 * k)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  suffices hurwitzZetaOdd x (1 - 2 * k) = 0 by
    rw [hurwitzZeta, this, add_zero, hurwitzZetaEven_one_sub_two_mul_nat hk hx]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [Nat.cast_succ, show (1 : ℂ) - 2 * (k + 1) = -2 * k - 1 by ring,
    hurwitzZetaOdd_neg_two_mul_nat_sub_one]

-- private because it is superseded by `hurwitzZeta_neg_nat` below
private lemma hurwitzZeta_neg_two_mul_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZeta x (-(2 * k)) = -1 / (2 * k + 1) *
      ((Polynomial.bernoulli (2 * k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  suffices hurwitzZetaEven x (-(2 * k)) = 0 by
    rw [hurwitzZeta, this, zero_add, hurwitzZetaOdd_neg_two_mul_nat hk hx]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  simpa using hurwitzZetaEven_neg_two_mul_nat_add_one x k

/-- Values of Hurwitz zeta functions at (strictly) negative integers.

TODO: This formula is also correct for `k = 0`; but our current proof does not work in this
case. -/
theorem hurwitzZeta_neg_nat (hk : k ≠ 0) (hx : x ∈ Icc (0 : ℝ) 1) :
    hurwitzZeta x (-k) =
    -1 / (k + 1) * ((Polynomial.bernoulli (k + 1)).map (algebraMap ℚ ℂ)).eval (x : ℂ) := by
  rcases Nat.even_or_odd' k with ⟨n, (rfl | rfl)⟩
  · exact_mod_cast hurwitzZeta_neg_two_mul_nat (by lia : n ≠ 0) hx
  · exact_mod_cast hurwitzZeta_one_sub_two_mul_nat (by lia : n + 1 ≠ 0) hx

end HurwitzZeta

open HurwitzZeta

/-- Explicit formula for `ζ (2 * k)`, for `k ∈ ℕ` with `k ≠ 0`, in terms of the Bernoulli number
`bernoulli (2 * k)`.

Compare `hasSum_zeta_nat` for a version formulated in terms of a sum over `1 / n ^ (2 * k)`, and
`riemannZeta_neg_nat_eq_bernoulli` for values at negative integers (equivalent to the above via
the functional equation). -/
theorem riemannZeta_two_mul_nat {k : ℕ} (hk : k ≠ 0) :
    riemannZeta (2 * k) = (-1) ^ (k + 1) * (2 : ℂ) ^ (2 * k - 1)
      * (π : ℂ) ^ (2 * k) * bernoulli (2 * k) / (2 * k)! := by
  convert congr_arg ((↑) : ℝ → ℂ) (hasSum_zeta_nat hk).tsum_eq
  · rw [← Nat.cast_two, ← Nat.cast_mul, zeta_nat_eq_tsum_of_gt_one (by lia)]
    simp [push_cast]
  · norm_cast

theorem riemannZeta_two : riemannZeta 2 = (π : ℂ) ^ 2 / 6 := by
  convert congr_arg ((↑) : ℝ → ℂ) hasSum_zeta_two.tsum_eq
  · rw [← Nat.cast_two, zeta_nat_eq_tsum_of_gt_one one_lt_two]
    simp [push_cast]
  · norm_cast

theorem riemannZeta_four : riemannZeta 4 = π ^ 4 / 90 := by
  convert congr_arg ((↑) : ℝ → ℂ) hasSum_zeta_four.tsum_eq
  · rw [← Nat.cast_one, show (4 : ℂ) = (4 : ℕ) by simp,
      zeta_nat_eq_tsum_of_gt_one (by simp : 1 < 4)]
    simp only [push_cast]
  · norm_cast

/-- Value of Riemann zeta at `-ℕ` in terms of `bernoulli'`. -/
theorem riemannZeta_neg_nat_eq_bernoulli' (k : ℕ) :
    riemannZeta (-k) = -bernoulli' (k + 1) / (k + 1) := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [Nat.cast_zero, neg_zero, riemannZeta_zero, zero_add, zero_add, div_one,
      bernoulli'_one, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, neg_div]
  · rw [← hurwitzZeta_zero, ← QuotientAddGroup.mk_zero, hurwitzZeta_neg_nat hk
      (left_mem_Icc.mpr zero_le_one), ofReal_zero, Polynomial.eval_zero_map,
      Polynomial.bernoulli_eval_zero, Algebra.algebraMap_eq_smul_one, Rat.smul_one_eq_cast,
      div_mul_eq_mul_div, neg_one_mul, bernoulli_eq_bernoulli'_of_ne_one (by simp [hk])]

/-- Value of Riemann zeta at `-ℕ` in terms of `bernoulli`. -/
theorem riemannZeta_neg_nat_eq_bernoulli (k : ℕ) :
    riemannZeta (-k) = (-1 : ℂ) ^ k * bernoulli (k + 1) / (k + 1) := by
  rw [riemannZeta_neg_nat_eq_bernoulli', bernoulli, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg,
    Rat.cast_one, ← neg_one_mul, ← mul_assoc, pow_succ, ← mul_assoc, ← mul_pow, neg_one_mul (-1),
    neg_neg, one_pow, one_mul]
