/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrability.Log

/-!
# Integrability of Functions Prominently Involving the Logarithm
-/

/-!
## Integrability for Logarithms of Meromorphic Functions

We establish integrability for functions of the form `log ‖meromorphic‖`. In the real setting, these
functions are interval integrable over every interval of the real line. This implies in particular
that logarithms of trigonometric functions are interval integrable. In the complex setting, the
functions are circle integrable over every circle in the complex plane.
-/

public section

open Filter Interval MeasureTheory MeromorphicOn Metric Real

/-!
### Interval Integrability for Logarithms of Real Meromorphic Functions
-/

section IntervalIntegrable

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E} {a b : ℝ}


/--
If `f` is real-meromorphic on a compact interval, then `log ‖f ·‖` is interval integrable on this
interval.
-/
theorem MeromorphicOn.intervalIntegrable_posLog_norm (hf : MeromorphicOn f [[a, b]]) :
    IntervalIntegrable (log⁺ ‖f ·‖) volume a b := by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply IntervalIntegrable.add
  · apply hf.intervalIntegrable_log_norm.const_mul
  · apply hf.intervalIntegrable_log_norm.abs.const_mul

@[deprecated (since := "2026-03-28")]
alias MeromorphicOn.intervalIntegrable_posLog_norm_meromorphicOn := intervalIntegrable_posLog_norm

end IntervalIntegrable

/-!
### Circle Integrability for Logarithms of Complex Meromorphic Functions
-/

section CircleIntegrable

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {c : ℂ} {R : ℝ} {f : ℂ → E}

/--
If `f` is complex meromorphic on a circle in the complex plane, then `log⁺ ‖f ·‖` is circle
integrable over that circle.
-/
theorem MeromorphicOn.circleIntegrable_posLog_norm (hf : MeromorphicOn f (sphere c |R|)) :
    CircleIntegrable (log⁺ ‖f ·‖) c R := by
  simp_rw [← half_mul_log_add_log_abs, mul_add]
  apply CircleIntegrable.add
  · apply hf.circleIntegrable_log_norm.const_mul
  · apply hf.circleIntegrable_log_norm.abs.const_mul

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_posLog_norm_meromorphicOn := MeromorphicOn.circleIntegrable_posLog_norm

/--
Variant of `MeromorphicOn.circleIntegrable_posLog_norm` for non-negative radii.
-/
theorem MeromorphicOn.circleIntegrable_posLog_norm_of_nonneg (hf : MeromorphicOn f (sphere c R))
    (hR : 0 ≤ R) :
    CircleIntegrable (log⁺ ‖f ·‖) c R := by
  rw [← abs_of_nonneg hR] at hf
  exact hf.circleIntegrable_posLog_norm

@[deprecated (since := "2026-03-28")]
alias circleIntegrable_posLog_norm_meromorphicOn_of_nonneg :=
    MeromorphicOn.circleIntegrable_posLog_norm_of_nonneg

end CircleIntegrable
