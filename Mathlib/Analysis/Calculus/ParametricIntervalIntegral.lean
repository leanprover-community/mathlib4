/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Derivatives of interval integrals depending on parameters

In this file we restate theorems about derivatives of integrals depending on parameters for interval
integrals. In the real case, we also show that parametric integrals of Cⁿ functions are Cⁿ. -/

universe u

public section


open TopologicalSpace MeasureTheory Filter Metric Set

open scoped Topology Filter Interval

variable {𝕜 : Type*} [RCLike 𝕜] {μ : Measure ℝ} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace 𝕜 E] {H : Type*} [NormedAddCommGroup H]
  [NormedSpace 𝕜 H] {s : Set H} {a b : ℝ} {bound : ℝ → ℝ}

namespace intervalIntegral

/-- Differentiation under integral of `x ↦ ∫ t in a..b, F x t` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a neighborhood of `x₀` for ae `a`
(with a neighborhood independent of `a`) with integrable Lipschitz bound, and `F x` is ae-measurable
for `x` in a possibly smaller neighborhood of `x₀`. -/
nonrec theorem hasFDerivAt_integral_of_dominated_loc_of_lip
    {F : H → ℝ → E} {F' : ℝ → H →L[𝕜] E} {x₀ : H}
    (hs : s ∈ 𝓝 x₀) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable F' (μ.restrict (Ι a b)))
    (h_lip : ∀ᵐ t ∂μ, t ∈ Ι a b →
      LipschitzOnWith (Real.nnabs <| bound t) (fun x => F x t) s)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → HasFDerivAt (fun x => F x t) (F' t) x₀) :
    IntervalIntegrable F' μ a b ∧
      HasFDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' t ∂μ) x₀ := by
  rw [← ae_restrict_iff' measurableSet_uIoc] at h_lip h_diff
  simp only [intervalIntegrable_iff] at hF_int bound_integrable ⊢
  simp only [intervalIntegral_eq_integral_uIoc]
  have := hasFDerivAt_integral_of_dominated_loc_of_lip hs hF_meas hF_int hF'_meas h_lip
    bound_integrable h_diff
  exact ⟨this.1, this.2.const_smul _⟩

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on a neighborhood of `x₀` for ae `a` with
derivative norm uniformly bounded by an integrable function (the neighborhood independent of `a`),
and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
nonrec theorem hasFDerivAt_integral_of_dominated_of_fderiv_le
    {F : H → ℝ → E} {F' : H → ℝ → H →L[𝕜] E} {x₀ : H} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀) (μ.restrict (Ι a b)))
    (h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ s, ‖F' x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ s, HasFDerivAt (fun x => F x t) (F' x t) x) :
    HasFDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀ := by
  rw [← ae_restrict_iff' measurableSet_uIoc] at h_bound h_diff
  simp only [intervalIntegrable_iff] at hF_int bound_integrable
  simp only [intervalIntegral_eq_integral_uIoc]
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le hs hF_meas hF_int hF'_meas h_bound
    bound_integrable h_diff).const_smul _

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`,
assuming `F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a neighborhood of `x₀` for ae `a`
(with a neighborhood independent of `a`) with integrable Lipschitz bound, and `F x` is
ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
nonrec theorem hasDerivAt_integral_of_dominated_loc_of_lip {F : 𝕜 → ℝ → E} {F' : ℝ → E} {x₀ : 𝕜}
    {s : Set 𝕜} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable F' (μ.restrict (Ι a b)))
    (h_lipsch : ∀ᵐ t ∂μ, t ∈ Ι a b →
      LipschitzOnWith (Real.nnabs <| bound t) (fun x => F x t) s)
    (bound_integrable : IntervalIntegrable (bound : ℝ → ℝ) μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → HasDerivAt (fun x => F x t) (F' t) x₀) :
    IntervalIntegrable F' μ a b ∧
      HasDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' t ∂μ) x₀ := by
  rw [← ae_restrict_iff' measurableSet_uIoc] at h_lipsch h_diff
  simp only [intervalIntegrable_iff] at hF_int bound_integrable ⊢
  simp only [intervalIntegral_eq_integral_uIoc]
  have := hasDerivAt_integral_of_dominated_loc_of_lip hs hF_meas hF_int hF'_meas h_lipsch
    bound_integrable h_diff
  exact ⟨this.1, this.2.const_smul _⟩

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`,
assuming `F x₀` is integrable, `x ↦ F x a` is differentiable on a neighborhood of `x₀` for ae `a`
(with a neighborhood independent of `a`) with derivative uniformly bounded by an integrable
function, and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
nonrec theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le
    {F : 𝕜 → ℝ → E} {F' : 𝕜 → ℝ → E} {x₀ : 𝕜} {s : Set 𝕜}
    (hs : s ∈ 𝓝 x₀) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀) (μ.restrict (Ι a b)))
    (h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ s, ‖F' x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ s, HasDerivAt (fun x => F x t) (F' x t) x) :
    IntervalIntegrable (F' x₀) μ a b ∧
      HasDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀ := by
  rw [← ae_restrict_iff' measurableSet_uIoc] at h_bound h_diff
  simp only [intervalIntegrable_iff] at hF_int bound_integrable ⊢
  simp only [intervalIntegral_eq_integral_uIoc]
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas h_bound
    bound_integrable h_diff
  exact ⟨this.1, this.2.const_smul _⟩

/-- A convenient special case of `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`:
if there exists a neighbourhood `u` of `x₀` such that `f.uncurry : H × ℝ → E` is continuous on
`u ×ˢ [[a, b]]` and differentiable on `u` in the first argument for every `t ∈ [[a, b]]` and that
derivative is continuous on `u ×ˢ [[a, b]]`, then a derivative of
`fun x => ∫ t in a..b, f x t ∂μ` in `x₀` can be computed as
`∫ t in a..b, fderiv 𝕜 (fun x ↦ f x t) x₀ ∂μ`. -/
theorem hasFDerivAt_integral_of_continuousOn_fderiv [IsLocallyFiniteMeasure μ]
    {f : H → ℝ → E} {x₀ : H} {u : Set H} (hu : u ∈ 𝓝 x₀) {a b : ℝ}
    (hF₁ : ContinuousOn f.uncurry (u ×ˢ [[a, b]]))
    (hF₂ : ∀ t ∈ [[a, b]], DifferentiableOn 𝕜 (fun x ↦ f x t) u)
    (hF₃ : ContinuousOn (fun x ↦ fderiv 𝕜 (fun y ↦ f y x.2) x.1) (u ×ˢ [[a, b]])) :
    HasFDerivAt (fun x => ∫ t in a..b, f x t ∂μ)
      (∫ t in a..b, fderiv 𝕜 (fun x ↦ f x t) x₀ ∂μ) x₀ := by
  wlog hab : a ≤ b with h
  · simp_rw [integral_symm b a]
    exact (h hu (uIcc_comm a b ▸ hF₁) (uIcc_comm a b ▸ hF₂) (uIcc_comm a b ▸ hF₃)
      (le_of_not_ge hab)).neg
  simp_rw [integral_of_le hab, ← uIoc_of_le hab]
  apply _root_.hasFDerivAt_integral_of_continuousOn_fderiv_of_t2Space
    hu isCompact_uIcc ?_ uIoc_subset_uIcc hF₁ hF₂ hF₃
  exact ((measure_mono uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top).ne

/-- A convenient special case of `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`:
if `f.uncurry : H × ℝ → E` is continuously differentiable on `u ×ˢ [[a, b]]` for a neighbourhood `u`
of `x₀`, then a derivative of `fun x => ∫ t in a..b, f x t ∂μ` in `x₀` can be computed as
`∫ t in a..b, fderiv ℝ (fun x ↦ f x t) x₀ ∂μ`. -/
theorem hasFDerivAt_integral_of_contDiffOn [IsLocallyFiniteMeasure μ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f : H → ℝ → E} {x₀ : H} {u : Set H} (hu : u ∈ 𝓝 x₀) {a b : ℝ}
    (hF : ContDiffOn ℝ 1 f.uncurry (u ×ˢ [[a, b]])) :
    HasFDerivAt (fun x => ∫ t in a..b, f x t ∂μ)
      (∫ t in a..b, fderiv ℝ (fun x ↦ f x t) x₀ ∂μ) x₀ := by
  wlog hab : a < b with h
  · obtain hab | hab := lt_or_eq_of_le <| le_of_not_gt hab
    · simpa only [integral_symm b a] using (h hu (uIcc_comm a b ▸ hF) hab).neg
    · simp [hab, hasFDerivAt_const]
  simp_rw [integral_of_le hab.le, ← uIoc_of_le hab.le]
  apply _root_.hasFDerivAt_integral_of_contDiffOn hu isCompact_uIcc ?_ uIoc_subset_uIcc hF
  exact ((measure_mono uIoc_subset_uIcc).trans_lt isCompact_uIcc.measure_lt_top).ne

end intervalIntegral

/-- If `f.uncurry : H × ℝ → E` is Cⁿ on `u ×ˢ [[a, b]]`, the parametric integral
`fun x ↦ ∫ t in a..b, f x t ∂μ` is Cⁿ on `u` too. -/
lemma ContDiffOn.parametric_intervalIntegral {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f : H → ℝ → E} {u : Set H} (hu : IsOpen u) {a b : ℝ} {n : ℕ∞}
    (hf : ContDiffOn ℝ n f.uncurry (u ×ˢ [[a, b]])) :
    ContDiffOn ℝ n (fun x ↦ ∫ t in a..b, f x t ∂μ) u := by
  wlog hab : a < b with h
  · obtain hab | hab := lt_or_eq_of_le <| le_of_not_gt hab
    · simp_rw [intervalIntegral.integral_symm b a]
      exact (h hu (uIcc_comm a b ▸ hf) hab).neg
    · simp [hab, contDiffOn_const]
  simp_rw [intervalIntegral.integral_of_le hab.le]
  apply hf.parametric_integral hu isCompact_Icc
  · simpa [hab.le] using Ioc_subset_Icc_self
  · exact ((measure_mono Ioc_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top).ne

/-- If `f : H × ℝ → E` is Cⁿ, the parametric integral
`fun x ↦ ∫ t in a..b, f (x, t) ∂μ` is Cⁿ too. -/
lemma ContDiff.parametric_intervalIntegral {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f : H × ℝ → E} {a b : ℝ} {n : ℕ∞}
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (fun x ↦ ∫ t in a..b, f (x, t) ∂μ) :=
  contDiffOn_univ.1 <| hf.contDiffOn.parametric_intervalIntegral isOpen_univ
