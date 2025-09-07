/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl
-/
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Markov's inequality

The classical form of Markov's inequality states that for a nonnegative random variable `X` and
real number `ε > 0`, `P(X ≥ ε) ≤ E(X) / ε`. Multiplying both sides by the measure of the space gives
the measure-theoretic form:
```
μ { x | ε ≤ f x } ≤ (∫⁻ a, f a ∂μ) / ε
```
This file proves a few variants of the inequality and other lemmas that depend on it.
-/

namespace MeasureTheory

open Set Filter ENNReal Topology

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A version of **Markov's inequality** for two functions. It doesn't follow from the standard
Markov's inequality because we only assume measurability of `g`, not `f`. -/
theorem lintegral_add_mul_meas_add_le_le_lintegral {f g : α → ℝ≥0∞} (hle : f ≤ᵐ[μ] g)
    (hg : AEMeasurable g μ) (ε : ℝ≥0∞) :
    ∫⁻ a, f a ∂μ + ε * μ { x | f x + ε ≤ g x } ≤ ∫⁻ a, g a ∂μ := by
  rcases exists_measurable_le_lintegral_eq μ f with ⟨φ, hφm, hφ_le, hφ_eq⟩
  calc
    ∫⁻ x, f x ∂μ + ε * μ { x | f x + ε ≤ g x } = ∫⁻ x, φ x ∂μ + ε * μ { x | f x + ε ≤ g x } := by
      rw [hφ_eq]
    _ ≤ ∫⁻ x, φ x ∂μ + ε * μ { x | φ x + ε ≤ g x } := by
      gcongr
      exact hφ_le _
    _ = ∫⁻ x, φ x + indicator { x | φ x + ε ≤ g x } (fun _ => ε) x ∂μ := by
      rw [lintegral_add_left hφm, lintegral_indicator₀, setLIntegral_const]
      exact measurableSet_le (hφm.nullMeasurable.measurable'.add_const _) hg.nullMeasurable
    _ ≤ ∫⁻ x, g x ∂μ := lintegral_mono_ae (hle.mono fun x hx₁ => ?_)
  simp only [indicator_apply]; split_ifs with hx₂
  exacts [hx₂, (add_zero _).trans_le <| (hφ_le x).trans hx₁]

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. -/
theorem mul_meas_ge_le_lintegral₀ {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ := by
  simpa only [lintegral_zero, zero_add] using
    lintegral_add_mul_meas_add_le_le_lintegral (ae_of_all _ fun x => zero_le (f x)) hf ε

/-- **Markov's inequality** also known as **Chebyshev's first inequality**. For a version assuming
`AEMeasurable`, see `mul_meas_ge_le_lintegral₀`. -/
theorem mul_meas_ge_le_lintegral {f : α → ℝ≥0∞} (hf : Measurable f) (ε : ℝ≥0∞) :
    ε * μ { x | ε ≤ f x } ≤ ∫⁻ a, f a ∂μ :=
  mul_meas_ge_le_lintegral₀ hf.aemeasurable ε

lemma meas_le_lintegral₀ {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    {s : Set α} (hs : ∀ x ∈ s, 1 ≤ f x) : μ s ≤ ∫⁻ a, f a ∂μ := by
  apply le_trans _ (mul_meas_ge_le_lintegral₀ hf 1)
  rw [one_mul]
  exact measure_mono hs

lemma lintegral_le_meas {s : Set α} {f : α → ℝ≥0∞} (hf : ∀ a, f a ≤ 1) (h'f : ∀ a ∈ sᶜ, f a = 0) :
    ∫⁻ a, f a ∂μ ≤ μ s := by
  apply (lintegral_mono (fun x ↦ ?_)).trans (lintegral_indicator_one_le s)
  by_cases hx : x ∈ s
  · simpa [hx] using hf x
  · simpa [hx] using h'f x hx

lemma setLIntegral_le_meas {s t : Set α} (hs : MeasurableSet s)
    {f : α → ℝ≥0∞} (hf : ∀ a ∈ s, a ∈ t → f a ≤ 1)
    (hf' : ∀ a ∈ s, a ∉ t → f a = 0) : ∫⁻ a in s, f a ∂μ ≤ μ t := by
  rw [← lintegral_indicator hs]
  refine lintegral_le_meas (fun a ↦ ?_) (by aesop)
  by_cases has : a ∈ s <;> [by_cases hat : a ∈ t; skip] <;> simp [*]

theorem lintegral_eq_top_of_measure_eq_top_ne_zero {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hμf : μ {x | f x = ∞} ≠ 0) : ∫⁻ x, f x ∂μ = ∞ :=
  eq_top_iff.mpr <|
    calc
      ∞ = ∞ * μ { x | ∞ ≤ f x } := by simp [hμf]
      _ ≤ ∫⁻ x, f x ∂μ := mul_meas_ge_le_lintegral₀ hf ∞

theorem setLIntegral_eq_top_of_measure_eq_top_ne_zero {f : α → ℝ≥0∞} {s : Set α}
    (hf : AEMeasurable f (μ.restrict s)) (hμf : μ ({x ∈ s | f x = ∞}) ≠ 0) :
    ∫⁻ x in s, f x ∂μ = ∞ :=
  lintegral_eq_top_of_measure_eq_top_ne_zero hf <|
    mt (eq_bot_mono <| by rw [← setOf_inter_eq_sep]; exact Measure.le_restrict_apply _ _) hμf

@[deprecated (since := "2025-04-22")]
alias setLintegral_eq_top_of_measure_eq_top_ne_zero := setLIntegral_eq_top_of_measure_eq_top_ne_zero

theorem measure_eq_top_of_lintegral_ne_top {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hμf : ∫⁻ x, f x ∂μ ≠ ∞) : μ {x | f x = ∞} = 0 :=
  of_not_not fun h => hμf <| lintegral_eq_top_of_measure_eq_top_ne_zero hf h

theorem measure_eq_top_of_setLIntegral_ne_top {f : α → ℝ≥0∞} {s : Set α}
    (hf : AEMeasurable f (μ.restrict s)) (hμf : ∫⁻ x in s, f x ∂μ ≠ ∞) :
    μ ({x ∈ s | f x = ∞}) = 0 :=
  of_not_not fun h => hμf <| setLIntegral_eq_top_of_measure_eq_top_ne_zero hf h

@[deprecated (since := "2025-04-22")]
alias measure_eq_top_of_setLintegral_ne_top := measure_eq_top_of_setLIntegral_ne_top

/-- **Markov's inequality**, also known as **Chebyshev's first inequality**. -/
theorem meas_ge_le_lintegral_div {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) {ε : ℝ≥0∞} (hε : ε ≠ 0)
    (hε' : ε ≠ ∞) : μ { x | ε ≤ f x } ≤ (∫⁻ a, f a ∂μ) / ε :=
  (ENNReal.le_div_iff_mul_le (Or.inl hε) (Or.inl hε')).2 <| by
    rw [mul_comm]
    exact mul_meas_ge_le_lintegral₀ hf ε

theorem ae_eq_of_ae_le_of_lintegral_le {f g : α → ℝ≥0∞} (hfg : f ≤ᵐ[μ] g) (hf : ∫⁻ x, f x ∂μ ≠ ∞)
    (hg : AEMeasurable g μ) (hgf : ∫⁻ x, g x ∂μ ≤ ∫⁻ x, f x ∂μ) : f =ᵐ[μ] g := by
  have : ∀ n : ℕ, ∀ᵐ x ∂μ, g x < f x + (n : ℝ≥0∞)⁻¹ := by
    intro n
    simp only [ae_iff, not_lt]
    have : ∫⁻ x, f x ∂μ + (↑n)⁻¹ * μ { x : α | f x + (n : ℝ≥0∞)⁻¹ ≤ g x } ≤ ∫⁻ x, f x ∂μ :=
      (lintegral_add_mul_meas_add_le_le_lintegral hfg hg n⁻¹).trans hgf
    rw [(ENNReal.cancel_of_ne hf).add_le_iff_nonpos_right, nonpos_iff_eq_zero, mul_eq_zero] at this
    exact this.resolve_left (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
  refine hfg.mp ((ae_all_iff.2 this).mono fun x hlt hle => hle.antisymm ?_)
  suffices Tendsto (fun n : ℕ => f x + (n : ℝ≥0∞)⁻¹) atTop (𝓝 (f x)) from
    ge_of_tendsto' this fun i => (hlt i).le
  simpa only [inv_top, add_zero] using
    tendsto_const_nhds.add (ENNReal.tendsto_inv_iff.2 ENNReal.tendsto_nat_nhds_top)

theorem lintegral_strict_mono_of_ae_le_of_frequently_ae_lt {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h_le : f ≤ᵐ[μ] g) (h : ∃ᵐ x ∂μ, f x ≠ g x) :
    ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ := by
  contrapose! h
  simp only [not_frequently, Ne, Classical.not_not]
  exact ae_eq_of_ae_le_of_lintegral_le h_le hfi hg h

theorem lintegral_strict_mono_of_ae_le_of_ae_lt_on {f g : α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h_le : f ≤ᵐ[μ] g) {s : Set α} (hμs : μ s ≠ 0)
    (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) : ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ :=
  lintegral_strict_mono_of_ae_le_of_frequently_ae_lt hg hfi h_le <|
    ((frequently_ae_mem_iff.2 hμs).and_eventually h).mono fun _x hx => (hx.2 hx.1).ne

theorem lintegral_strict_mono {f g : α → ℝ≥0∞} (hμ : μ ≠ 0) (hg : AEMeasurable g μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) (h : ∀ᵐ x ∂μ, f x < g x) : ∫⁻ x, f x ∂μ < ∫⁻ x, g x ∂μ := by
  rw [Ne, ← Measure.measure_univ_eq_zero] at hμ
  refine lintegral_strict_mono_of_ae_le_of_ae_lt_on hg hfi (ae_le_of_ae_lt h) hμ ?_
  simpa using h

theorem setLIntegral_strict_mono {f g : α → ℝ≥0∞} {s : Set α} (hsm : MeasurableSet s)
    (hs : μ s ≠ 0) (hg : Measurable g) (hfi : ∫⁻ x in s, f x ∂μ ≠ ∞)
    (h : ∀ᵐ x ∂μ, x ∈ s → f x < g x) : ∫⁻ x in s, f x ∂μ < ∫⁻ x in s, g x ∂μ :=
  lintegral_strict_mono (by simp [hs]) hg.aemeasurable hfi ((ae_restrict_iff' hsm).mpr h)

theorem ae_lt_top' {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) (h2f : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ := by
  simp_rw [ae_iff, ENNReal.not_lt_top]
  exact measure_eq_top_of_lintegral_ne_top hf h2f

theorem ae_lt_top {f : α → ℝ≥0∞} (hf : Measurable f) (h2f : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, f x < ∞ :=
  ae_lt_top' hf.aemeasurable h2f

end MeasureTheory
