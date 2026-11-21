/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# The Lemma on Logarithmic Derivatives

This file will, in the future, establish Nevanlinna's "Lemma on Logarithmic Derivatives". At
present, it collects material that will be used in the proof.

See Section VI.4 of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion. A full formalized proof of the lemma on logarithmic derivatives is available at
https://github.com/kebekus/ProjectVD
-/

public section

open Metric Real Set

/-!
## A Jensen-Type Inequality for Circle Averages
-/

/-- If `u` is circle integrable and nonnegative on the circle, then `log (1 + u)` is circle
integrable. -/
lemma CircleIntegrable.log_one_add {u : ℂ → ℝ} {r : ℝ}
    (h₀ : ∀ z ∈ sphere (0 : ℂ) |r|, 0 ≤ u z) (hu : CircleIntegrable u 0 r) :
    CircleIntegrable (fun z ↦ Real.log (1 + u z)) 0 r := by
  apply IntervalIntegrable.mono_fun (IntervalIntegrable.abs hu)
  · apply AEMeasurable.aestronglyMeasurable
    exact Real.measurable_log.comp_aemeasurable
      (aemeasurable_const.add (intervalIntegrable_iff.1 hu).aemeasurable)
  · filter_upwards with θ
    have h₁ : 0 ≤ u (circleMap 0 r θ) := h₀ _ (circleMap_mem_sphere' 0 r θ)
    simp only [norm_eq_abs, abs_abs]
    grw [abs_of_nonneg (log_nonneg (by linarith)), abs_of_nonneg h₁,
      log_one_add_le_self (by linarith)]

/--
For a nonnegative circle-integrable function `u`, the circle average of `log⁺ u` is at most `log⁺`
of the circle average, up to an additive constant `log 2`. This can be seen as an analogue of
Jensen's inequality `ConcaveOn.le_map_set_average` for circle averages, where `log⁺` takes the roles
of the concave function.
-/
theorem Real.circleAverage_posLog_le_posLog_circleAverage {u : ℂ → ℝ} {r : ℝ}
    (h₀ : ∀ z ∈ sphere (0 : ℂ) |r|, 0 ≤ u z) (hu : CircleIntegrable u 0 r) :
    circleAverage (log⁺ ∘ u) 0 r ≤ log⁺ (circleAverage u 0 r) + Real.log 2 := by
  have hInt : CircleIntegrable (fun z ↦ log (1 + u z)) 0 r := hu.log_one_add h₀
  grw [circleAverage_mono hu.posLog_comp hInt (fun z hz ↦ posLog_le_log_one_add (h₀ z hz)),
    ← log_one_add_le_posLog, circleAverage_eq_intervalAverage, circleAverage_eq_intervalAverage]
  have hConcave : ConcaveOn ℝ (Ici 0) (fun x ↦ log (1 + x)) :=
    (strictConcaveOn_log_one_add.subset (Ici_subset_Ioi.2 neg_one_lt_zero)
      (convex_Ici 0)).concaveOn
  exact hConcave.le_map_set_average
    (ContinuousOn.log (by fun_prop) (by grind))
    isClosed_Ici (by simp [uIoc_of_le Real.two_pi_pos.le, Real.pi_pos])
    measure_uIoc_lt_top.ne
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc
      fun θ _ ↦ h₀ _ (circleMap_mem_sphere' 0 r θ))
    (intervalIntegrable_iff.1 hu) (intervalIntegrable_iff.1 hInt)
