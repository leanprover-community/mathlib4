/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
A supplement to the file
# Links between an integral and its "improper" version

-/


open scoped Classical Topology
open Filter Set MeasureTheory Real
set_option autoImplicit true

noncomputable section

theorem Real.atBot_le_cocompact : atBot ≤ cocompact ℝ := by simp
theorem Real.atTop_le_cocompact : atTop ≤ cocompact ℝ := by simp

theorem Filter.EventuallyEq.tendsto [TopologicalSpace β] {f : α → β} {l : Filter α} {a : β}
    (hf : f =ᶠ[l] fun _ ↦ a) : Tendsto f l (𝓝 a) :=
  tendsto_nhds_of_eventually_eq hf


/-! ## Semi-infinite versions of the fundamental theorem of calculus -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {f f' : ℝ → E} {a b : ℝ} {m : E}

/-- **Fundamental theorem of calculus-2**, on semi-infinite intervals `(-∞, a)`.
When a function has a limit `m` at `-∞`, and its derivative is integrable, then the
integral of the derivative on `(-∞, a)` is `f a - m`. Version assuming differentiability
on `(-∞, a)` and continuity on `(-∞, a]`.-/
theorem integral_Iio_of_hasDerivAt_of_tendsto (hcont : ContinuousOn f (Iic a))
    (hderiv : ∀ x ∈ Iio a, HasDerivAt f (f' x) x) (f'int : IntegrableOn f' (Iic a))
    (hf : Tendsto f atBot (𝓝 m)) : ∫ x in Iic a, f' x = f a - m := by
  refine' tendsto_nhds_unique (intervalIntegral_tendsto_integral_Iic a f'int tendsto_id) _
  apply Tendsto.congr' _ (hf.const_sub _)
  filter_upwards [Iic_mem_atBot a] with x hx
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx
    (hcont.mono Icc_subset_Iic_self) fun y hy => hderiv y hy.2
  rw [intervalIntegrable_iff_integrable_Ioc_of_le hx]
  exact f'int.mono (fun y hy => hy.2) le_rfl

-- very special case of `integral_Iio_of_hasDerivAt_of_tendsto`.
theorem HasCompactSupport.integral_deriv_eq {f : ℝ → E} (hf : ContDiff ℝ 1 f)
    (h2f : HasCompactSupport f) (b : ℝ) : ∫ x in Iic b, _root_.deriv f x = f b := by
  have := fun x (_ : x ∈ Iio b) ↦ hf.differentiable le_rfl x |>.hasDerivAt
  rw [integral_Iio_of_hasDerivAt_of_tendsto hf.continuous.continuousOn this, sub_zero]
  refine hf.continuous_deriv le_rfl |>.integrable_of_hasCompactSupport h2f.deriv |>.integrableOn
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact] at h2f
  exact h2f.filter_mono atBot_le_cocompact |>.tendsto
