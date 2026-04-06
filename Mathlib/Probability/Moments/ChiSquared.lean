import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# MGF of the Square of a Standard Normal

The moment generating function of `X²` when `X ∼ N(0,1)` is `(1−2t)^{−1/2}`,
valid for `t < 1/2`. This identity is the key ingredient in the chi-squared
Chernoff bound used in the Johnson–Lindenstrauss proof.

## Main results

* `mgf_sq_gaussianReal` : `mgf (· ^ 2) (gaussianReal 0 1) t = (1 − 2t)^{−1/2}` for `t < 1/2`

## References

Dasgupta, S. and Gupta, A. (2003). An elementary proof of a theorem of Johnson
and Lindenstrauss. *Random Structures & Algorithms* 22(1), 60–65.

## Status

-- STAGING: pending Mathlib PR targeting Mathlib.Probability.Moments.ChiSquared
-- Retire this file once the PR is merged into Mathlib.
-/

/-- The MGF of `X²` for `X ∼ N(0,1)` equals `(1 − 2t)^{−1/2}`, valid for `t < 1/2`.

Proof: write `mgf (·^2) γ t = ∫ x, (√(2π))⁻¹ · exp(−x²/2) · exp(t·x²) dx`,
combine the exponentials to `exp(−((1−2t)/2)·x²)`, then apply the Gaussian
integral formula `∫ exp(−a·x²) dx = √(π/a)` and simplify algebraically.

**STATUS:** staging for `Mathlib.Probability.Moments.ChiSquared`.
Retire once merged into Mathlib. -/
lemma mgf_sq_gaussianReal {t : ℝ} (ht : t < 1 / 2) :
    ProbabilityTheory.mgf (fun x : ℝ => x ^ 2) (ProbabilityTheory.gaussianReal 0 1) t =
    (1 - 2 * t) ^ (-(1 / 2 : ℝ)) := by
  have h12 : (1 : NNReal) ≠ 0 := one_ne_zero
  have ht' : 0 < (1 - 2 * t) / 2 := by linarith
  have ht12 : 0 < 1 - 2 * t := by linarith
  -- mgf (·^2) γ t = ∫ x, exp(t·x²) ∂γ = ∫ x, pdfReal(x)·exp(t·x²) dx
  rw [ProbabilityTheory.mgf, ProbabilityTheory.integral_gaussianReal_eq_integral_smul (by exact_mod_cast h12)]
  simp only [ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
  -- Combine the two exponentials under the integral
  simp_rw [show ∀ x : ℝ,
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * Real.exp (t * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 - 2 * t) / 2) * x ^ 2) from fun x => by
    rw [mul_assoc, ← Real.exp_add]; congr 1; ring]
  rw [MeasureTheory.integral_const_mul, integral_gaussian ((1 - 2 * t) / 2)]
  -- Goal: (√(2π))⁻¹ * √(π/((1-2t)/2)) = (1-2t)^{-1/2}
  -- Algebraic simplification: (√(2π))⁻¹ * √(2π/(1-2t)) = (1-2t)^{-1/2}
  have hsqrt2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have h_simpl : Real.pi / ((1 - 2 * t) / 2) = Real.sqrt (2 * Real.pi) ^ 2 / (1 - 2 * t) := by
    rw [Real.sq_sqrt (by positivity)]; field_simp
  have h_sqrt_eq : Real.sqrt (Real.pi / ((1 - 2 * t) / 2)) =
      Real.sqrt (2 * Real.pi) * (1 - 2 * t) ^ (-(1/2:ℝ)) := by
    rw [h_simpl, Real.sqrt_div' _ (le_of_lt ht12),
        Real.sqrt_sq (le_of_lt hsqrt2pi_pos)]
    simp only [Real.sqrt_eq_rpow]
    rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt ht12)]
  rw [h_sqrt_eq]
  field_simp [hsqrt2pi_pos.ne']
