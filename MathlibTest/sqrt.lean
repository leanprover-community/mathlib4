import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.Eval
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.ToExpr
import Mathlib

namespace Nat

def ratSqrt (x : ℕ) (prec : ℕ) : ℚ := ((x * prec^2).sqrt : ℚ) / prec

theorem ratSqrt_sq_le {x prec : ℕ} : (ratSqrt x prec)^2 ≤ x := sorry
theorem lt_ratSqrt_add_inv_prec_eq {x prec : ℕ} : x < (ratSqrt x prec + 1 / prec)^2 := sorry

theorem ratSqrt_le_realSqrt {x prec : ℕ} : ratSqrt x prec ≤ √x := sorry
theorem realSqrt_lt_ratSqrt_add_inv_prec {x prec : ℕ} : √x < ratSqrt x prec + 1 / prec := sorry

end Nat

def sqrtApproxLower : ℚ := ((640320 * 10^(2 * 10^6) * 10^(2 * 10^6)).sqrt : ℚ) / (10^(2 * 10^6) : ℕ)
def sqrtApproxUpper : ℚ := ((640320 * 10^(2 * 10^6) * 10^(2 * 10^6)).sqrt + 1 : ℚ) / 10^(2 * 10^6)

theorem Real.natCast_sqrt_le (n : ℕ) : (n.sqrt : ℝ) ≤ (n : ℝ)^(1/2 : ℝ) := sorry

theorem sqrtApproxLower_le_sqrt : sqrtApproxLower ≤ (640320 : ℝ)^(1/2 : ℝ) := by
  unfold sqrtApproxLower
  simp only [Rat.cast_div, Rat.cast_pow, Nat.cast_ofNat, Rat.cast_ofNat, Rat.cast_natCast,
    Nat.cast_pow]
  rw [div_le_iff₀ (by norm_num)]
  apply le_trans (Real.natCast_sqrt_le _)
  have : ∀ x y : ℝ, x^2 ≤ y^2 → x ≤ y := sorry
  apply this
  rw [mul_pow]
  rw [← Real.rpow_two, ← Real.rpow_mul (by norm_num)]
  rw [← Real.rpow_two, ← Real.rpow_mul (by norm_num)]
  rw [show (1 / 2 * 2 : ℝ) = 1 by norm_num, Real.rpow_one, Real.rpow_one, pow_two]
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]





open Lean in
instance : ToExpr ℚ where
  toExpr q := mkApp2 (.const ``mkRat []) (toExpr q.num) (toExpr q.den)
  toTypeExpr := .const ``Rat [0]

-- example : sqrtApproxLower = eval% sqrtApproxLower := by
--   unfold sqrtApproxLower
--   norm_num
