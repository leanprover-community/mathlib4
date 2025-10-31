/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Derivatives of interval integrals depending on parameters

In this file we restate theorems about derivatives of integrals depending on parameters for interval
integrals. -/

universe u

open TopologicalSpace MeasureTheory Filter Metric

open scoped Topology Filter Interval

variable {𝕜 : Type*} [RCLike 𝕜] {μ : Measure ℝ} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [NormedSpace 𝕜 E] {H : Type*} [NormedAddCommGroup H]
  [NormedSpace 𝕜 H] {a b ε : ℝ} {bound : ℝ → ℝ}

namespace intervalIntegral

/-- Differentiation under integral of `x ↦ ∫ t in a..b, F x t` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a`
(with a ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is ae-measurable
for `x` in a possibly smaller neighborhood of `x₀`. -/
nonrec theorem hasFDerivAt_integral_of_dominated_loc_of_lip
    {F : H → ℝ → E} {F' : ℝ → H →L[𝕜] E} {x₀ : H}
    (ε_pos : 0 < ε) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable F' (μ.restrict (Ι a b)))
    (h_lip : ∀ᵐ t ∂μ, t ∈ Ι a b →
      LipschitzOnWith (Real.nnabs <| bound t) (fun x => F x t) (ball x₀ ε))
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → HasFDerivAt (fun x => F x t) (F' t) x₀) :
    IntervalIntegrable F' μ a b ∧
      HasFDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' t ∂μ) x₀ := by
  rw [← ae_restrict_iff' measurableSet_uIoc] at h_lip h_diff
  simp only [intervalIntegrable_iff] at hF_int bound_integrable ⊢
  simp only [intervalIntegral_eq_integral_uIoc]
  have := hasFDerivAt_integral_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas h_lip
    bound_integrable h_diff
  exact ⟨this.1, this.2.const_smul _⟩

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on a ball around `x₀` for ae `a` with
derivative norm uniformly bounded by an integrable function (the ball radius is independent of `a`),
and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
nonrec theorem hasFDerivAt_integral_of_dominated_of_fderiv_le
    {F : H → ℝ → E} {F' : H → ℝ → H →L[𝕜] E} {x₀ : H} (ε_pos : 0 < ε)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀) (μ.restrict (Ι a b)))
    (h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, ‖F' x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, HasFDerivAt (fun x => F x t) (F' x t) x) :
    HasFDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀ := by
  rw [← ae_restrict_iff' measurableSet_uIoc] at h_bound h_diff
  simp only [intervalIntegrable_iff] at hF_int bound_integrable
  simp only [intervalIntegral_eq_integral_uIoc]
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le ε_pos hF_meas hF_int hF'_meas h_bound
    bound_integrable h_diff).const_smul _

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`,
assuming `F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a`
(with ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is
ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
nonrec theorem hasDerivAt_integral_of_dominated_loc_of_lip {F : 𝕜 → ℝ → E} {F' : ℝ → E} {x₀ : 𝕜}
    (ε_pos : 0 < ε) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable F' (μ.restrict (Ι a b)))
    (h_lipsch : ∀ᵐ t ∂μ, t ∈ Ι a b →
      LipschitzOnWith (Real.nnabs <| bound t) (fun x => F x t) (ball x₀ ε))
    (bound_integrable : IntervalIntegrable (bound : ℝ → ℝ) μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → HasDerivAt (fun x => F x t) (F' t) x₀) :
    IntervalIntegrable F' μ a b ∧
      HasDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' t ∂μ) x₀ := by
  rw [← ae_restrict_iff' measurableSet_uIoc] at h_lipsch h_diff
  simp only [intervalIntegrable_iff] at hF_int bound_integrable ⊢
  simp only [intervalIntegral_eq_integral_uIoc]
  have := hasDerivAt_integral_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas h_lipsch
    bound_integrable h_diff
  exact ⟨this.1, this.2.const_smul _⟩

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`,
assuming `F x₀` is integrable, `x ↦ F x a` is differentiable on an interval around `x₀` for ae `a`
(with interval radius independent of `a`) with derivative uniformly bounded by an integrable
function, and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
nonrec theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le
    {F : 𝕜 → ℝ → E} {F' : 𝕜 → ℝ → E} {x₀ : 𝕜}
    (ε_pos : 0 < ε) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀) (μ.restrict (Ι a b)))
    (h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, ‖F' x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, HasDerivAt (fun x => F x t) (F' x t) x) :
    IntervalIntegrable (F' x₀) μ a b ∧
      HasDerivAt (fun x => ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀ := by
  rw [← ae_restrict_iff' measurableSet_uIoc] at h_bound h_diff
  simp only [intervalIntegrable_iff] at hF_int bound_integrable ⊢
  simp only [intervalIntegral_eq_integral_uIoc]
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le ε_pos hF_meas hF_int hF'_meas h_bound
    bound_integrable h_diff
  exact ⟨this.1, this.2.const_smul _⟩

open Set in
/-- A convenient special case of `intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le`:
if `f : H × ℝ → E` is continuously differentiable on `u ×ˢ [[a, b]]` for a neighbourhood `u`
of `x₀`, then a derivative of `fun x => ∫ t in a..b, f (x, t) ∂μ` in `x₀` can be computed as
`∫ t in a..b, fderiv ℝ (fun x ↦ f (x, t)) x₀ ∂μ`. -/
nonrec theorem hasFDerivAt_integral_of_contDiffOn
    {μ : Measure ℝ} [IsLocallyFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f : H × ℝ → E} {x₀ : H} {u : Set H} (hu : u ∈ 𝓝 x₀) {a b : ℝ}
    (hF : ContDiffOn ℝ 1 f (u ×ˢ [[a, b]])) :
    HasFDerivAt (fun x => ∫ t in a..b, f (x, t) ∂μ)
      (∫ t in a..b, fderiv ℝ (fun x ↦ f (x, t)) x₀ ∂μ) x₀ := by
  wlog hab : a < b with h
  · obtain hab | hab := lt_or_eq_of_le <| le_of_not_gt hab
    · simp_rw [intervalIntegral.integral_symm b a]
      exact (h (μ := μ) hu (Set.uIcc_comm a b ▸ hF) hab).neg
    · simp [hab, hasFDerivAt_const]
  rw [uIcc_of_le hab.le] at hF
  replace ⟨u, hu, hxu, hF⟩ : ∃ u, IsOpen u ∧ x₀ ∈ u ∧ ContDiffOn ℝ 1 f (u ×ˢ Icc a b) := by
    have ⟨u', hu'⟩ := _root_.mem_nhds_iff.1 hu
    exact ⟨u', hu'.2.1, hu'.2.2, hF.mono <| prod_mono_left hu'.1⟩
  let F' := fun x : H × ℝ ↦ fderiv ℝ (fun y ↦ f (y, x.2)) x.1
  have hF' : ContinuousOn F' (u ×ˢ Icc a b) := by
    refine .congr (f := fun x ↦ (fderivWithin ℝ f (u ×ˢ Set.Icc a b) x).comp (.inl ℝ H ℝ))
      ?_ fun x hx ↦ ?_
    · refine ((ContinuousLinearMap.compL ℝ H (H × ℝ) E).flip
        (.inl ℝ H ℝ)).continuous.comp_continuousOn ?_
      refine (hF.continuousOn_fderivWithin ?_ le_rfl)
      exact hu.uniqueDiffOn.prod <| uniqueDiffOn_Icc hab
    · dsimp [F']; rw [show (fun y ↦ f (y, x.2)) = (f ∘ fun y ↦ (y, x.2)) by rfl]
      rw [← fderivWithin_eq_fderiv (s := u) (hu.uniqueDiffWithinAt hx.1) <| by
        refine DifferentiableOn.differentiableAt (s := u) ?_ (hu.mem_nhds hx.1)
        exact ((hF.differentiableOn le_rfl).comp (by fun_prop) (fun y hy ↦ ⟨hy, hx.2⟩))]
      rw [fderivWithin_comp _ (t := u ×ˢ Set.Icc a b) (hF.differentiableOn (by simp) _ ⟨hx.1, hx.2⟩)
        (by fun_prop) (by exact fun y hy ↦ ⟨hy, hx.2⟩) (hu.uniqueDiffWithinAt hx.1)]
      congr
      exact (hasFDerivAt_prodMk_left _ x.2).hasFDerivWithinAt.fderivWithin
        (hu.uniqueDiffWithinAt hx.1)
  let F'' := fun x ↦ ‖F' x‖
  have hF'' : ContinuousOn F'' _ := continuous_norm.comp_continuousOn hF'
  let ⟨ε, hε, hε', B, hB⟩ :
      ∃ ε > 0, Metric.ball x₀ ε ⊆ u ∧ ∃ B, ∀ x ∈ Metric.ball x₀ ε ×ˢ Icc a b, F'' x < B := by
    let ⟨B, hB⟩ := (isCompact_singleton.prod isCompact_Icc).bddAbove_image <|
      hF''.mono <| prod_mono_left <| singleton_subset_iff.2 hxu
    have ⟨v, hv, hv'⟩ := generalized_tube_lemma_left (s := {x₀}) isCompact_singleton
      (t := Icc a b) isCompact_Icc (s' := u) (n := F'' ⁻¹' (Iio (B + 1))) (by
        refine nhdsSetWithin_mono_left ?_ <| hF''.preimage_mem_nhdsSetWithin_of_mem_nhdsSet
          (t := Iic B) (u := Iio (B + 1)) <| isOpen_Iio.mem_nhdsSet.2 (by simp)
        intro x hx
        exact ⟨prod_mono_left (by simp [hxu]) hx, mem_upperBounds.1 hB _ <| mem_image_of_mem _ hx⟩)
    rw [nhdsSetWithin_singleton, hu.nhdsWithin_eq hxu] at hv
    have ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hv (hu.mem_nhds hxu))
    exact ⟨ε, hε, hε'.trans inter_subset_right, B + 1,
      fun x hx ↦ hv' <| prod_mono_left (hε'.trans inter_subset_left) hx⟩
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ ↦ B)
    (F' := fun x t ↦ fderiv ℝ (fun x ↦ f (x, t)) x) hε ?_ ?_ ?_ ?_ ?_ ?_
  · refine eventually_nhds_iff.2 ⟨u, fun x hx ↦ ?_, hu, hxu⟩
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine .mono ?_ <| (uIoc_of_le hab.le).trans_le Ioc_subset_Icc_self
    exact hF.continuousOn.comp (by fun_prop) fun t ht ↦ ⟨hx, ht⟩
  · apply ContinuousOn.intervalIntegrable
    exact hF.continuousOn.comp (by fun_prop) fun t ht ↦ ⟨hxu, uIcc_of_le hab.le ▸ ht⟩
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    refine .mono ?_ <| (uIoc_of_le hab.le).trans_le Ioc_subset_Icc_self
    exact hF'.comp (f := fun t ↦ (x₀, t)) (by fun_prop) fun t ht ↦ ⟨hxu, ht⟩
  · refine .of_forall fun t ht x hx ↦ ?_
    exact (hB (x, t) ⟨hx, Ioc_subset_Icc_self <| uIoc_of_le hab.le ▸ ht⟩).le
  · exact intervalIntegrable_const
  · refine .of_forall fun t ht x hx ↦ ?_
    refine (DifferentiableOn.differentiableAt ?_ (hu.mem_nhds <| hε' hx)).hasFDerivAt
    exact hF.differentiableOn_one.comp (by fun_prop) fun x hx ↦
      ⟨hx, Ioc_subset_Icc_self <| uIoc_of_le hab.le ▸ ht⟩

lemma _root_.ContDiffOn.parametric_intervalIntegral {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    [NoAtoms μ] {E H : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup H]
    [NormedSpace ℝ H] {f : H × ℝ → E} {u : Set H} (hu : IsOpen u) {a b : ℝ} {n : ℕ∞}
    (hf : ContDiffOn ℝ n f (u ×ˢ [[a, b]])) :
    ContDiffOn ℝ n (fun x ↦ ∫ t in a..b, f (x, t) ∂μ) u := by
  wlog hab : a < b with h
  · obtain hab | hab := lt_or_eq_of_le <| le_of_not_gt hab
    · simp_rw [intervalIntegral.integral_symm b a]
      exact (h hu (Set.uIcc_comm a b ▸ hf) hab).neg
    · simp [hab, contDiffOn_const]
  revert E; change ∀ E : _, _
  refine ENat.nat_induction n ?_ ?_ ?_
  · intro E _ _ f
    simp_rw [WithTop.coe_zero, contDiffOn_zero]
    exact ContinuousOn.parametric_intervalIntegral
  · intro k h E _ _ f hf
    refine (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := k) hu).2 ⟨?_, by simp, ?_⟩
    · intro x hx
      have h := intervalIntegral.hasFDerivAt_integral_of_contDiffOn (μ := μ)
        (hu.mem_nhds hx) (hf.of_le <| by simp)
      exact h.differentiableAt.differentiableWithinAt
    · have := hf.fderivWithin (hu.uniqueDiffOn.prod <| Set.uIcc_of_le hab.le ▸ uniqueDiffOn_Icc hab)
        (m := k) le_rfl
      refine (h _ (f := fun x ↦ (fderivWithin ℝ f (u ×ˢ [[a, b]]) x).comp (.inl ℝ H ℝ))
        (by fun_prop)).congr ?_
      intro x hx
      have h := intervalIntegral.hasFDerivAt_integral_of_contDiffOn (μ := μ)
        (hu.mem_nhds hx) (hf.of_le <| by simp)
      rw [h.fderiv]
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [show (fun x ↦ f (x, t)) = (f ∘ fun x ↦ (x, t)) by rfl]
      rw [← fderivWithin_eq_fderiv (hu.uniqueDiffWithinAt hx) (((hf.differentiableOn (by simp)).comp
        (by fun_prop) (fun x hx ↦ ⟨hx, ht⟩)).differentiableAt (hu.mem_nhds hx))]
      rw [fderivWithin_comp _ (t := u ×ˢ [[a, b]]) (hf.differentiableOn (by simp) _ ⟨hx, ht⟩)
        (by fun_prop) (fun x hx ↦ ⟨hx, ht⟩) (hu.uniqueDiffWithinAt hx)]
      congr
      exact (hasFDerivAt_prodMk_left x t).hasFDerivWithinAt.fderivWithin (hu.uniqueDiffWithinAt hx)
  · intro h E _ _ f hf
    exact contDiffOn_infty.2 fun n ↦ h n E <| hf.of_le <| WithTop.coe_le_coe.2 le_top

end intervalIntegral
