/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

#align_import measure_theory.integral.exp_decay from "leanprover-community/mathlib"@"d4817f8867c368d6c5571f7379b3888aaec1d95a"

/-!
# Integrals with exponential decay at ∞

As easy special cases of general theorems in the library, we prove the following test
for integrability:

* `integrable_of_isBigO_exp_neg`: If `f` is continuous on `[a,∞)`, for some `a ∈ ℝ`, and there
  exists `b > 0` such that `f(x) = O(exp(-b x))` as `x → ∞`, then `f` is integrable on `(a, ∞)`.
-/


noncomputable section

open Real intervalIntegral MeasureTheory Set Filter

open scoped Topology

/-- `exp (-b * x)` is integrable on `(a, ∞)`. -/
theorem exp_neg_integrableOn_Ioi (a : ℝ) {b : ℝ} (h : 0 < b) :
    IntegrableOn (fun x : ℝ => exp (-b * x)) (Ioi a) := by
  have : Tendsto (fun x => -exp (-b * x) / b) atTop (𝓝 (-0 / b)) := by
    refine Tendsto.div_const (Tendsto.neg ?_) _
    exact tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 h))
  refine integrableOn_Ioi_deriv_of_nonneg' (fun x _ => ?_) (fun x _ => (exp_pos _).le) this
  simpa [h.ne'] using ((hasDerivAt_id x).const_mul b).neg.exp.neg.div_const b
#align exp_neg_integrable_on_Ioi exp_neg_integrableOn_Ioi

/-- If `f` is continuous on `[a, ∞)`, and is `O (exp (-b * x))` at `∞` for some `b > 0`, then
`f` is integrable on `(a, ∞)`. -/
theorem integrable_of_isBigO_exp_neg {f : ℝ → ℝ} {a b : ℝ} (h0 : 0 < b)
    (hf : ContinuousOn f (Ici a)) (ho : f =O[atTop] fun x => exp (-b * x)) :
    IntegrableOn f (Ioi a) :=
  integrableOn_Ici_iff_integrableOn_Ioi.mp <|
    (hf.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop
    ho ⟨Ioi b, Ioi_mem_atTop b, exp_neg_integrableOn_Ioi b h0⟩
set_option linter.uppercaseLean3 false in
#align integrable_of_is_O_exp_neg integrable_of_isBigO_exp_neg
