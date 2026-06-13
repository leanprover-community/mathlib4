/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integrals with exponential decay at ∞

As easy special cases of general theorems in the library, we prove the following test
for integrability:

* `integrable_of_isBigO_exp_neg`: If `f` is continuous on `[a,∞)`, for some `a ∈ ℝ`, and there
  exists `b > 0` such that `f(x) = O(exp(-b x))` as `x → ∞`, then `f` is integrable on `(a, ∞)`.
-/

public section


noncomputable section

open Real intervalIntegral MeasureTheory Set Filter Asymptotics

open scoped Topology

/-- `exp (-b * x)` is integrable on `(a, ∞)`. -/
theorem exp_neg_integrableOn_Ioi (a : ℝ) {b : ℝ} (h : 0 < b) :
    IntegrableOn (fun x : ℝ => exp (-b * x)) (Ioi a) := by
  have : Tendsto (fun x => -exp (-b * x) / b) atTop (𝓝 (-0 / b)) := by
    refine Tendsto.div_const (Tendsto.neg ?_) _
    exact tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 h))
  refine integrableOn_Ioi_deriv_of_nonneg' (fun x _ => ?_) (fun x _ => (exp_pos _).le) this
  simpa [h.ne'] using ((hasDerivAt_id x).const_mul b).neg.exp.neg.div_const b

/-- If `f` is continuous on `[a, ∞)`, and is `O (exp (-b * x))` at `∞` for some `b > 0`, then
`f` is integrable on `(a, ∞)`. -/
theorem integrable_of_isBigO_exp_neg {f : ℝ → ℝ} {a b : ℝ} (h0 : 0 < b)
    (hf : ContinuousOn f (Ici a)) (ho : f =O[atTop] fun x => exp (-b * x)) :
    IntegrableOn f (Ioi a) :=
  integrableOn_Ici_iff_integrableOn_Ioi (by finiteness) |>.mp <|
    (hf.locallyIntegrableOn measurableSet_Ici).integrableOn_of_isBigO_atTop
    ho ⟨Ioi b, Ioi_mem_atTop b, exp_neg_integrableOn_Ioi b h0⟩

/-- Exponential decay beats exponential growth: if `f` is locally integrable on `[c, ∞)` and
`f x = O(exp (a * x))` at `∞`, then `exp (-b * x) * ‖f x‖` is integrable on `(c, ∞)`
for every `a < b`. -/
theorem integrableOn_exp_neg_mul_norm_of_isBigO_exp {E : Type*} [NormedAddCommGroup E]
    {a b c : ℝ} {f : ℝ → E} (hfc : LocallyIntegrableOn f (Ici c))
    (hf : f =O[atTop] fun x : ℝ => exp (a * x)) (hab : a < b) :
    IntegrableOn (fun x : ℝ => exp (-b * x) * ‖f x‖) (Ioi c) := by
  refine integrableOn_Ici_iff_integrableOn_Ioi (by finiteness) |>.mp ?_
  have hloc : LocallyIntegrableOn (fun x : ℝ => exp (-b * x) * ‖f x‖) (Ici c) := by
    simpa [mul_comm] using hfc.norm.mul_continuousOn
      ((by fun_prop : Continuous fun x : ℝ => exp (-b * x)).continuousOn)
      isClosed_Ici.isLocallyClosed
  refine hloc.integrableOn_of_isBigO_atTop (g := fun x : ℝ => exp ((a - b) * x))
    (((isBigO_refl _ atTop).mul hf.norm_left).congr_right fun x => by rw [← exp_add]; ring_nf)
    ⟨Ioi c, Ioi_mem_atTop c, by
      simpa [neg_sub] using exp_neg_integrableOn_Ioi c (sub_pos.mpr hab)⟩
