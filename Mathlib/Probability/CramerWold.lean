/-
Copyright (c) 2026 Ivo Malinowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivo Malinowski
-/
module

public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
public import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Cramèr-Wold Theorem

We prove the Cramér-Wold theorem: convergence in distribution of a sequence of
random variables in a finite-dimensional real inner product space is equivalent
to convergence in distribution of all their 1-dimensional scalar projections.
-/

open MeasureTheory Filter Complex BoundedContinuousFunction RealInnerProductSpace ProbabilityMeasure

open scoped Topology

public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {Ω : Type*} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω}
  {Ω' : Type*} [MeasurableSpace Ω'] {Q : ProbabilityMeasure Ω'}
  {X : Ω' → E} {Xn : ℕ → Ω → E}

lemma charFun_map_eq_integral_map_inner {α : Type*} {mα : MeasurableSpace α}
  (μ : ProbabilityMeasure α) {Y : α → E} (hY : Measurable Y) (t : E) :
  charFun (μ.map hY.aemeasurable) t =
    ∫ ω, innerProbChar (1 : ℝ) ω ∂((μ.map (hY.inner_const (c := t)).aemeasurable).toMeasure) := by
  simp_rw [charFun_eq_integral_innerProbChar, toMeasure_map]
  rw [MeasureTheory.integral_map (hY.inner_const (c := t)).aemeasurable
    (innerProbChar (1 : ℝ)).continuous.stronglyMeasurable.aestronglyMeasurable]
  rw [MeasureTheory.integral_map hY.aemeasurable
    (innerProbChar t).continuous.stronglyMeasurable.aestronglyMeasurable]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  simp only [innerProbChar_apply, real_inner_comm]
  have H : ⟪t, Y ω⟫ • (1 : ℝ) = ⟪t, Y ω⟫ := by simp
  conv_rhs => rw [← H]
  rw [inner_smul_left]
  simp

lemma tendsto_charFun_of_tendsto_inner (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n))
  (hconv : ∀ t : E, Tendsto (fun n : ℕ => P.map ((hXn n).inner_const (c := t)).aemeasurable)
    atTop (𝓝 (Q.map (hX.inner_const (c := t)).aemeasurable : ProbabilityMeasure ℝ))) :
  ∀ t : E, Tendsto (fun n ↦ charFun (P.map (hXn n).aemeasurable) t)
    atTop (𝓝 (charFun (Q.map hX.aemeasurable) t)) := by
  intro t
  let f : ℝ →ᵇ ℂ := innerProbChar (1 : ℝ)
  convert (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp (hconv t) f using 1
  · ext n
    exact charFun_map_eq_integral_map_inner P (hXn n) t
  · exact congr_arg 𝓝 (charFun_map_eq_integral_map_inner Q hX t)

/-- **Cramér-Wold device (one direction only)**

Convergence in distribution of all 1-dimensional scalar projections of a sequence of
random variables in a finite-dimensional real inner product space implies the
convergence in distribution of the sequence itself. -/
theorem tendsto_map_of_tendsto_map_inner (hX : Measurable X) (hXn : ∀ n, Measurable (Xn n)) :
  (∀ t : E, Tendsto (fun n : ℕ => P.map ((hXn n).inner_const (c := t)).aemeasurable)
  atTop (𝓝 (Q.map (hX.inner_const (c := t)).aemeasurable : ProbabilityMeasure ℝ))) →
  (Tendsto (fun n : ℕ => P.map (hXn n).aemeasurable) atTop (𝓝 (Q.map hX.aemeasurable))) := by
  intro h
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  exact tendsto_charFun_of_tendsto_inner hX hXn h

end
