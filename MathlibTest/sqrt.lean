import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.Eval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.ToExpr
import Mathlib

namespace Nat

/--
Approximate `√x` as a rational number, to within `1/prec`.
-/
def ratSqrt (x : ℕ) (prec : ℕ) : ℚ := ((x * prec^2).sqrt : ℚ) / prec

theorem ratSqrt_nonneg {x prec : ℕ} (h : 0 < prec) : 0 ≤ ratSqrt x prec := by
  unfold ratSqrt
  positivity

theorem ratSqrt_sq_le {x prec : ℕ} (h : 0 < prec) : (ratSqrt x prec)^2 ≤ x := by
  unfold ratSqrt
  rw [div_pow, div_le_iff₀ (by positivity)]
  norm_cast
  exact sqrt_le' (x * prec ^ 2)

theorem lt_ratSqrt_add_inv_prec_eq {x prec : ℕ} (h : 0 < prec) : x < (ratSqrt x prec + 1 / prec)^2 := by
  unfold ratSqrt
  rw [← mul_lt_mul_iff_of_pos_right (a := (prec^2 : ℚ)) (by positivity)]
  rw [← mul_pow, add_mul]
  rw [div_mul_cancel₀, div_mul_cancel₀]
  · norm_cast
    exact lt_succ_sqrt' (x * prec ^ 2)
  all_goals norm_cast; positivity

theorem ratSqrt_le_realSqrt {x prec : ℕ} (h : 0 < prec) : ratSqrt x prec ≤ √x := by
  have := ratSqrt_sq_le (x := x) h
  have : (x.ratSqrt prec ^ 2 : ℝ) ≤ ↑x := by norm_cast
  have := Real.sqrt_monotone this
  rwa [Real.sqrt_sq] at this
  simpa only [Rat.cast_nonneg] using ratSqrt_nonneg h

theorem realSqrt_lt_ratSqrt_add_inv_prec {x prec : ℕ} (h : 0 < prec) :
    √x < ratSqrt x prec + 1 / prec := by
  have := lt_ratSqrt_add_inv_prec_eq (x := x) h
  have : (x : ℝ) < ↑((x.ratSqrt prec + 1 / prec) ^ 2 : ℚ) := by norm_cast
  have := Real.sqrt_lt_sqrt (by simp) this
  rw [Rat.cast_pow] at this
  rw [Real.sqrt_sq] at this
  · push_cast at this
    exact this
  · push_cast
    exact add_nonneg (by simpa using ratSqrt_nonneg h) (by simp)

theorem realSqrt_mem_Ico {x prec : ℕ} (h : 0 < prec) :
    √x ∈ Set.Ico (ratSqrt x prec : ℝ) (ratSqrt x prec + 1 / prec : ℝ) := by
  grind [ratSqrt_le_realSqrt, realSqrt_lt_ratSqrt_add_inv_prec]

theorem ratSqrt_mem_Ioc {x prec : ℕ} (h : 0 < prec) :
    (ratSqrt x prec : ℝ) ∈ Set.Ioc (√x - 1 / prec) √x := by
  grind [ratSqrt_le_realSqrt, realSqrt_lt_ratSqrt_add_inv_prec]

end Nat

open Nat

open Lean in
instance : ToExpr ℚ where
  toExpr q := mkApp2 (.const ``mkRat []) (toExpr q.num) (toExpr q.den)
  toTypeExpr := .const ``Rat [0]

/-- Compute an explicit rational approximation of `√10005`, accurate to 2 million decimal places. -/
def sqrt_10005_approx : ℚ := eval% ratSqrt 10005 (10^(2 * 10^6))

theorem sqrt_10005_approx_eq : sqrt_10005_approx = ratSqrt 10005 (10^(2 * 10^6)) := by
  norm_num [sqrt_10005_approx, ratSqrt]

theorem sqrt_10005 :
    √(10005 : ℝ) ∈
      Set.Ico (sqrt_10005_approx : ℝ)
              (sqrt_10005_approx + 1 / 10^(2 * 10^6) : ℝ) := by
  rw [sqrt_10005_approx_eq]
  exact_mod_cast realSqrt_mem_Ico (x := 10005) (by norm_num)
