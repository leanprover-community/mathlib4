/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Pietro Monticone
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Init
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Real
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

/-!
# Bounds for sums and integrals of `x ^ k * exp (-c * x)`

We bound the integral and sums of `x ^ k * exp (-c * x)` by `k ! / c ^ (k + 1)`,
using the Gamma function.
-/

open scoped Nat
open Real MeasureTheory Set Filter

@[expose] public section

lemma intervalIntegral_pow_mul_exp_neg_le {k : ℕ} {M c : ℝ} (hM : 0 ≤ M) (hc : 0 < c) :
    ∫ x in (0 : ℝ)..M, x ^ k * rexp (- (c * x)) ≤ k ! / c ^ (k + 1) := by
  have hk : (0 : ℝ) < ↑k + 1 := by positivity
  have key := integral_rpow_mul_exp_neg_mul_Ioi hk hc
  have hint : IntegrableOn (fun x ↦ x ^ ((↑k + 1 : ℝ) - 1) * rexp (-(c * x))) (Ioi 0) :=
    .of_integral_ne_zero (by rw [key]; positivity)
  rw [intervalIntegral.integral_of_le hM]
  calc ∫ x in Ioc (0 : ℝ) M, x ^ k * rexp (-(c * x))
    _ = ∫ x in Ioc (0 : ℝ) M, x ^ ((↑k + 1 : ℝ) - 1) * rexp (-(c * x)) := by
        simp [add_sub_cancel_right, rpow_natCast]
    _ ≤ ∫ x in Ioi (0 : ℝ), x ^ ((↑k + 1 : ℝ) - 1) * rexp (-(c * x)) := by
        apply setIntegral_mono_set hint _ Ioc_subset_Ioi_self.eventuallyLE
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact mul_nonneg (rpow_nonneg hx.le _) (exp_nonneg _)
    _ = k ! / c ^ (k + 1) := by
        simp_rw [key, Gamma_nat_eq_factorial, div_eq_mul_inv,
          one_mul, mul_comm, inv_rpow hc.le, ← rpow_natCast]
        norm_cast

lemma sum_Ico_pow_mul_exp_neg_le {k : ℕ} {M : ℕ} {c : ℝ} (hc : 0 < c) :
    ∑ i ∈ Finset.Ico 0 M, i ^ k * rexp (- (c * i)) ≤ rexp c * k ! / c ^ (k + 1) := calc
  ∑ i ∈ Finset.Ico 0 M, i ^ k * rexp (- (c * i))
  _ ≤ ∫ x in (0 : ℕ)..M, x ^ k * rexp (- (c * (x - 1))) := by
    apply sum_mul_Ico_le_integral_of_monotone_antitone
      (f := fun x ↦ x ^ k) (g := fun x ↦ rexp (- (c * x)))
    · exact Nat.zero_le M
    · intro x hx y hy hxy
      apply pow_le_pow_left₀ (by simpa using hx.1) hxy
    · intro x hx y hy hxy
      apply exp_monotone
      simp only [neg_le_neg_iff]
      gcongr
    · simp
    · apply exp_nonneg
  _ ≤ (k ! / c ^ (k + 1)) * rexp c := by
    simp only [mul_sub, mul_one, neg_sub, CharP.cast_eq_zero]
    simp only [sub_eq_add_neg, Real.exp_add, mul_comm (rexp c), ← mul_assoc]
    rw [intervalIntegral.integral_mul_const]
    gcongr
    exact intervalIntegral_pow_mul_exp_neg_le (by simp) hc
  _ = _ := by ring

lemma sum_Iic_pow_mul_exp_neg_le {k : ℕ} {M : ℕ} {c : ℝ} (hc : 0 < c) :
    ∑ i ∈ Finset.Iic M, i ^ k * rexp (- (c * i)) ≤ rexp c * k ! / c ^ (k + 1) :=
  sum_Ico_pow_mul_exp_neg_le (M := M + 1) hc

lemma sum_Iic_pow_mul_two_pow_neg_le {k : ℕ} {M : ℕ} {c : ℝ} (hc : 0 < c) :
    ∑ i ∈ Finset.Iic M, i ^ k * (2 : ℝ) ^ (- (c * i)) ≤
      2 ^ c * k ! / (Real.log 2 * c) ^ (k + 1) := by
  have A (i : ℕ) : (2 : ℝ) ^ (- (c * i)) = rexp (- (Real.log 2 * c) * i) := by
    conv_lhs => rw [← exp_log zero_lt_two, ← exp_mul]
    congr 1
    ring
  simp only [A, neg_mul]
  apply (sum_Iic_pow_mul_exp_neg_le (by positivity)).trans_eq
  rw [exp_mul, exp_log zero_lt_two]

end
