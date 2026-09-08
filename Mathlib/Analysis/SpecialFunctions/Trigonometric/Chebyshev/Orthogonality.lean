/-
Copyright (c) 2026 Yuval Filmus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuval Filmus, En-Tsai Kao
-/
module

public import Mathlib.RingTheory.Polynomial.Chebyshev
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial

/-!
# Chebyshev polynomials over the reals: orthogonality

Chebyshev T polynomials are orthogonal with respect to `√(1 - x ^ 2)⁻¹`, and Chebyshev U
polynomials are orthogonal with respect to `√(1 - x ^ 2)`.

## Main statements

* `integrable_measureT`: continuous functions are integrable with respect to Lebesgue measure
  scaled by `√(1 - x ^ 2)⁻¹` and restricted to `(-1, 1]`.
* `integral_eval_T_real_mul_evalT_real_measureT_of_ne`:
  if `n ≠ m` then the integral of `T_n * T_m` equals `0`.
* `integral_eval_T_real_mul_self_measureT_zero`:
  if `n = m = 0` then the integral equals `π`.
* `integral_eval_T_real_mul_self_measureT_of_ne_zero`:
  if `n = m ≠ 0` then the integral equals `π / 2`.
* `integral_eval_U_real_mul_eval_U_real_measureU_of_ne`:
  if `n ≠ m` then the integral of `U_n * U_m` against `measureU` equals `0`.
* `integral_eval_U_real_mul_self_measureU`: the integral of `U_n ^ 2` equals `π / 2`.

## Implementation notes

The second-kind results are reduced to the first-kind ones rather than reproved: the two weights
differ by the polynomial factor `1 - x ^ 2` (`sqrt_eq_mul_sqrt_inv`), so absorbing that
factor into the integrand lets `integral_measureT_eq_integral_cos` supply the substitution
`x = cos θ` for free. The identity `U_n (cos θ) * sin θ = sin ((n + 1) * θ)` then pairs each `U`
with one of the two factors of `sin θ` produced by `1 - cos θ ^ 2`.

## TODO

* Bundle Chebyshev T polynomials into a HilbertBasis for MeasureTheory.Lp ℝ 2 measureT
* Prove an analogue of `integrable_measureT` for `measureU`

-/
public section

namespace Polynomial.Chebyshev

open Real intervalIntegral MeasureTheory

open scoped NNReal

/-- Lebesgue measure scaled by √(1 - x ^ 2)⁻¹. -/
noncomputable def measureT : Measure ℝ :=
  (volume.withDensity
    fun x ↦ ENNReal.ofNNReal (.mk (√(1 - x ^ 2)⁻¹) (by positivity))).restrict (Set.Ioc (-1) 1)

theorem integral_measureT (f : ℝ → ℝ) :
    ∫ x, f x ∂measureT = ∫ x in -1..1, f x * √(1 - x ^ 2)⁻¹ := by
  rw [integral_of_le (by norm_num), measureT,
    restrict_withDensity (by measurability),
    integral_withDensity_eq_integral_smul (by fun_prop)]
  congr! 2 with x hx
  simp [NNReal.smul_def, mul_comm]

theorem intervalIntegrable_sqrt_one_sub_sq_inv :
    IntervalIntegrable (fun x ↦ √(1 - x ^ 2)⁻¹) volume (-1) 1 := by
  rw [intervalIntegrable_iff]
  refine integrableOn_deriv_of_nonneg continuous_arccos.neg.continuousOn (fun x hx ↦ ?_) (by simp)
  simpa using! (hasDerivAt_arccos (by aesop) (by aesop)).neg

theorem integrable_measureT {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (-1) 1)) :
    Integrable f measureT := by
  replace hf : ContinuousOn f (Set.uIcc (-1) 1) := by rwa [Set.uIcc_of_lt (by norm_num)]
  have := intervalIntegrable_sqrt_one_sub_sq_inv.continuousOn_mul hf
  rw [intervalIntegrable_iff, Set.uIoc_of_le (by norm_num)] at this
  rw [measureT, restrict_withDensity (by measurability),
    integrable_withDensity_iff (by fun_prop) (by simp)]
  unfold IntegrableOn at this
  convert! this

open Set in
theorem integral_measureT_eq_integral_cos {f : ℝ → ℝ} :
    ∫ x, f x ∂measureT = ∫ θ in 0..π, f (cos θ) := calc
  ∫ x, f x ∂measureT = ∫ x in -1..1, f x * √(1 - x ^ 2)⁻¹ := integral_measureT f
  _ = ∫ x in 1..-1, f x * -(√(1 - x ^ 2)⁻¹) := by
    rw [integral_symm, ← intervalIntegral.integral_neg]
    simp
  _ = ∫ θ in (arccos 1)..(arccos (-1)), f (cos θ) := by
    rw [← integral_comp_mul_deriv_of_deriv_nonpos (f' := fun x => -(1 / √(1 - x ^ 2)))]
    · simp_rw [Function.comp_apply]
      exact integral_congr <| fun x hx => by simp [cos_arccos (x := x) (by aesop) (by aesop)]
    · fun_prop
    · exact fun x hx ↦ (hasDerivAt_arccos (by aesop) (by aesop))
    · simp
  _ = ∫ θ in 0..π, f (cos θ) := by simp

@[deprecated (since := "2026-03-19")]
alias integral_measureT_eq_integral_cos_of_continuous := integral_measureT_eq_integral_cos

theorem integral_eval_T_real_measureT_zero :
    ∫ x, (T ℝ 0).eval x ∂measureT = π := by
  rw [integral_measureT_eq_integral_cos]; simp

theorem integral_eval_T_real_measureT_of_ne_zero {n : ℤ} (hn : n ≠ 0) :
    ∫ x, (T ℝ n).eval x ∂measureT = 0 := by
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  suffices ∫ θ in 0..n * π, cos θ = 0 by
    rw [integral_measureT_eq_integral_cos]
    simp_rw [T_real_cos]
    rwa [integral_comp_mul_left _ (Int.cast_ne_zero.mpr hn), smul_eq_zero_iff_right (by aesop),
      mul_zero]
  trans ∫ θ in 0..n * π, (deriv sin) θ
  · refine integral_congr <| fun x hx => (congrFun deriv_sin x).symm
  by_cases! 0 ≤ n
  case pos => rw [integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn (by positivity)]; simp
  case neg hn =>
    rw [integral_symm, integral_deriv_of_contDiffOn_Icc contDiff_sin.contDiffOn]
    · simp
    exact mul_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr <| le_of_lt hn) pi_nonneg

theorem integral_eval_T_real_mul_eval_T_real_measureT (n m : ℤ) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂measureT =
    ((∫ x, (T ℝ (n + m)).eval x ∂measureT) +
     (∫ x, (T ℝ (n - m)).eval x ∂measureT)) / 2 := by
  suffices ∫ x, (2 * T ℝ n * T ℝ m).eval x ∂measureT =
      (∫ x, (T ℝ (n + m)).eval x ∂measureT) +
      (∫ x, (T ℝ (n - m)).eval x ∂measureT) by
    simp_rw [eval_mul, eval_ofNat, mul_assoc] at this
    rw [MeasureTheory.integral_const_mul] at this
    grind
  simp_rw [T_mul_T, eval_add]
  rw [MeasureTheory.integral_add
    (integrable_measureT (by fun_prop)) (integrable_measureT (by fun_prop))]

theorem integral_eval_T_real_mul_eval_T_real_measureT_of_ne {n m : ℕ} (h : n ≠ m) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂measureT = 0 := by
  rw [integral_eval_T_real_mul_eval_T_real_measureT,
    integral_eval_T_real_measureT_of_ne_zero (by grind),
    integral_eval_T_real_measureT_of_ne_zero (by grind)]
  simp

theorem integral_eval_T_real_mul_self_measureT_zero :
    ∫ x, (T ℝ 0).eval x * (T ℝ 0).eval x ∂measureT = π := by
  simp_rw [← eval_mul, show (T ℝ 0) * (T ℝ 0) = T ℝ 0 by simp]
  exact integral_eval_T_real_measureT_zero

theorem integral_T_real_mul_self_measureT_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∫ x, (T ℝ n).eval x * (T ℝ n).eval x ∂measureT = π / 2 := by
  rw [integral_eval_T_real_mul_eval_T_real_measureT,
    integral_eval_T_real_measureT_of_ne_zero (by grind), sub_self,
    integral_eval_T_real_measureT_zero, zero_add]

/-! ### Chebyshev polynomials of the second kind -/

/-- Lebesgue measure scaled by `√(1 - x ^ 2)`. -/
noncomputable def measureU : Measure ℝ :=
  (volume.withDensity
    fun x ↦ ENNReal.ofNNReal (.mk (√(1 - x ^ 2)) (by positivity))).restrict (Set.Ioc (-1) 1)

theorem integral_measureU (f : ℝ → ℝ) :
    ∫ x, f x ∂measureU = ∫ x in -1..1, f x * √(1 - x ^ 2) := by
  rw [integral_of_le (by norm_num), measureU,
    restrict_withDensity (by measurability),
    integral_withDensity_eq_integral_smul (by fun_prop)]
  congr! 2 with x hx
  simp [NNReal.smul_def, mul_comm]

/-- `√x = x * √x⁻¹`, with no side condition: for `x < 0` both sides vanish because `Real.sqrt` is
zero on nonpositive arguments, and for `x = 0` because `0⁻¹ = 0`.

This is what relates the two Chebyshev weights: the second-kind weight `√(1 - x ^ 2)` is the
first-kind weight `√(1 - x ^ 2)⁻¹` scaled by the polynomial `1 - x ^ 2`. -/
private theorem sqrt_eq_mul_sqrt_inv (x : ℝ) : √x = x * √x⁻¹ := by
  rw [sqrt_inv]
  rcases eq_or_ne (√x) 0 with h | h
  · rw [h, inv_zero, mul_zero]
  · have hx : 0 ≤ x := not_lt.mp fun hlt ↦ h (sqrt_eq_zero'.mpr hlt.le)
    rw [← div_eq_mul_inv, eq_div_iff h, mul_self_sqrt hx]

theorem integral_measureU_eq_integral_measureT (f : ℝ → ℝ) :
    ∫ x, f x ∂measureU = ∫ x, (1 - x ^ 2) * f x ∂measureT := by
  rw [integral_measureU, integral_measureT]
  refine integral_congr fun x _ ↦ ?_
  conv_lhs => rw [sqrt_eq_mul_sqrt_inv (1 - x ^ 2)]
  ring

/-- Integration against the second-kind weight becomes `∫ θ in 0..π, f (cos θ) * sin θ ^ 2`.

The extra `sin θ ^ 2`, compared with `integral_measureT_eq_integral_cos`, is exactly what pairs up
with the two `U` factors through `U_real_cos`. -/
theorem integral_measureU_eq_integral_sin_sq (f : ℝ → ℝ) :
    ∫ x, f x ∂measureU = ∫ θ in 0..π, f (cos θ) * sin θ ^ 2 := by
  rw [integral_measureU_eq_integral_measureT, integral_measureT_eq_integral_cos]
  refine integral_congr fun θ _ ↦ ?_
  rw [← sin_sq]
  ring

/-- `∫ θ in 0..π, cos (n * θ)` is `π` when `n = 0` and `0` otherwise.

Integrality of `n` is essential: it is what makes `sin (n * π) = 0`. -/
private theorem integral_cos_intCast_mul (n : ℤ) :
    ∫ θ in (0 : ℝ)..π, cos ((n : ℝ) * θ) = if n = 0 then π else 0 := by
  have key : ∫ θ in (0 : ℝ)..π, cos ((n : ℝ) * θ) = ∫ x, (T ℝ n).eval x ∂measureT := by
    rw [integral_measureT_eq_integral_cos]
    exact integral_congr fun θ _ ↦ by simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp [key, hn, integral_eval_T_real_measureT_of_ne_zero hn]

/-- Orthogonality of `fun θ ↦ sin ((n + 1) * θ)` over `[0, π]`.

Product-to-sum turns the integrand into two cosines of integer frequency; the frequency
`n + m + 2` is never zero, so only the `n = m` case survives. -/
private theorem integral_sin_mul_sin (n m : ℕ) :
    ∫ θ in (0 : ℝ)..π, sin (((n : ℝ) + 1) * θ) * sin (((m : ℝ) + 1) * θ) =
      if n = m then π / 2 else 0 := by
  have key : ∀ θ : ℝ, sin (((n : ℝ) + 1) * θ) * sin (((m : ℝ) + 1) * θ) =
      2⁻¹ * (cos ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * θ) -
        cos ((((n : ℤ) + (m : ℤ) + 2 : ℤ) : ℝ) * θ)) := by
    intro θ
    have e₁ : ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ)) * θ = ((n : ℝ) + 1) * θ - ((m : ℝ) + 1) * θ := by
      push_cast; ring
    have e₂ : ((((n : ℤ) + (m : ℤ) + 2 : ℤ) : ℝ)) * θ = ((n : ℝ) + 1) * θ + ((m : ℝ) + 1) * θ := by
      push_cast; ring
    rw [e₁, e₂, cos_sub, cos_add]
    ring
  simp_rw [key]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    integral_cos_intCast_mul, integral_cos_intCast_mul]
  have h₂ : ¬((n : ℤ) + (m : ℤ) + 2 = 0) := by omega
  simp only [sub_eq_zero, Nat.cast_inj, h₂, ite_false, sub_zero]
  split_ifs <;> ring

theorem integral_eval_U_real_mul_eval_U_real_measureU (n m : ℕ) :
    ∫ x, (U ℝ n).eval x * (U ℝ m).eval x ∂measureU = if n = m then π / 2 else 0 := by
  rw [integral_measureU_eq_integral_sin_sq]
  have key : ∀ θ : ℝ, (U ℝ (n : ℤ)).eval (cos θ) * (U ℝ (m : ℤ)).eval (cos θ) * sin θ ^ 2 =
      sin (((n : ℝ) + 1) * θ) * sin (((m : ℝ) + 1) * θ) := by
    intro θ
    calc (U ℝ (n : ℤ)).eval (cos θ) * (U ℝ (m : ℤ)).eval (cos θ) * sin θ ^ 2
        = ((U ℝ (n : ℤ)).eval (cos θ) * sin θ) * ((U ℝ (m : ℤ)).eval (cos θ) * sin θ) := by ring
      _ = sin (((n : ℝ) + 1) * θ) * sin (((m : ℝ) + 1) * θ) := by
          rw [U_real_cos, U_real_cos]; push_cast; ring
  simp_rw [key]
  exact integral_sin_mul_sin n m

theorem integral_eval_U_real_mul_eval_U_real_measureU_of_ne {n m : ℕ} (h : n ≠ m) :
    ∫ x, (U ℝ n).eval x * (U ℝ m).eval x ∂measureU = 0 := by
  simp [integral_eval_U_real_mul_eval_U_real_measureU, h]

theorem integral_eval_U_real_mul_self_measureU (n : ℕ) :
    ∫ x, (U ℝ n).eval x * (U ℝ n).eval x ∂measureU = π / 2 := by
  simp [integral_eval_U_real_mul_eval_U_real_measureU]

end Polynomial.Chebyshev
