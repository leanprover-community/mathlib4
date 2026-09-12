/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!  # Derivatives of parametric circle integrals

In this file we restate theorems about derivatives of integrals depending on parameters for circle
integrals `∮ z in C(c, R), F x z`. These are direct analogues of the corresponding results for
interval integrals, but these take hypotheses on the circle as a set in `ℂ` instead of on the
interval `Set.uIoc 0 (2 * π)`.

One notable difference: some of the assumptions for interval integrals which only require properties
to hold almost everywhere have been changed so that they must hold everywhere on the circle. This
means they are slightly less general, but we suspect they will be easier to use in practice. In the
worst case, users can always fall back to interval integrals.
-/

public section

open MeasureTheory Metric Set Filter

open scoped Real Topology Interval NNReal

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℂ E] [SMulCommClass 𝕜 ℂ E]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {c : ℂ} {R : ℝ} {s : Set H} {bound : ℂ → ℝ}

section Aux

/- here we collect a few private theorems whose statements exactly match the ones necessary
in each of the several repeated applications below. -/

private theorem aestronglyMeasurable_deriv_circleMap_smul {f : ℂ → E}
    (hf : AEStronglyMeasurable (f <| circleMap c R ·) (volume.restrict (Ι 0 (2 * π)))) :
    AEStronglyMeasurable (fun θ : ℝ ↦ deriv (circleMap c R) θ • f (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))) := by
  have : Continuous (deriv (circleMap c R) ·) := by simp only [deriv_circleMap]; fun_prop
  exact this.aestronglyMeasurable.smul hf

private theorem lipschitzOnWith_deriv_circleMap_smul {α : Type*} [PseudoEMetricSpace α]
    {t : Set α} {g : α → E} {θ b : ℝ} (hg : LipschitzOnWith ‖b‖₊ g t) :
    LipschitzOnWith ‖|R| * b‖₊ (fun x ↦ deriv (circleMap c R) θ • g x) t := by
  have := (lipschitzWith_smul (deriv (circleMap c R) θ)).comp_lipschitzOnWith hg
  simpa

private theorem norm_deriv_circleMap_smul_le {v : E} {θ b : ℝ} (h : ‖v‖ ≤ b) :
    ‖deriv (circleMap c R) θ • v‖ ≤ |R| * b := by
  grw [norm_smul_le, h]; simp

end Aux

/-- Differentiation under a parametric circle integral for `x ↦ ∮ z in C(c, R), F x z` at a given
point `x₀`, assuming `F x₀` is circle integrable, `x ↦ F x z` is Lipschitz on a neighborhood of
`x₀` for every `z` on the circle (with a neighborhood independent of `z`) with circle integrable
Lipschitz bound, and `F x` is a.e. strongly measurable along `circleMap c R` for `x` in a possibly
smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_circleIntegral_of_dominated_loc_of_lip
    {F : H → ℂ → E} {F' : ℂ → H →L[𝕜] E} {x₀ : H} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun θ : ℝ ↦ F x (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))))
    (hF_int : CircleIntegrable (F x₀) c R)
    (hF'_meas : AEStronglyMeasurable (fun θ : ℝ ↦ F' (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))))
    (h_lip : ∀ z ∈ sphere c |R|, LipschitzOnWith ‖bound z‖₊ (fun x ↦ F x z) s)
    (bound_integrable : CircleIntegrable bound c R)
    (h_diff : ∀ z ∈ sphere c |R|, HasFDerivAt (fun x ↦ F x z) (F' z) x₀) :
    CircleIntegrable F' c R ∧
      HasFDerivAt (fun x ↦ ∮ z in C(c, R), F x z) (∮ z in C(c, R), F' z) x₀ := by
  rw [circleIntegrable_iff]
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
    (bound := fun θ ↦ |R| * bound (circleMap c R θ)) hs
    (hF_meas.mono fun _ hx ↦ aestronglyMeasurable_deriv_circleMap_smul hx)
    ((circleIntegrable_iff R).mp hF_int) (aestronglyMeasurable_deriv_circleMap_smul hF'_meas)
    (.of_forall fun θ _ ↦
      lipschitzOnWith_deriv_circleMap_smul (h_lip _ (circleMap_mem_sphere' c R θ)))
    (bound_integrable.const_mul _)
    (.of_forall fun θ _ ↦ (h_diff _ (circleMap_mem_sphere' c R θ)).const_smul _)

/-- Differentiation under a parametric circle integral for `x ↦ ∮ z in C(c, R), F x z` at a given
point `x₀`, assuming `F x₀` is circle integrable, `x ↦ F x z` is differentiable on a neighborhood
of `x₀` for every `z` on the circle with derivative norm uniformly bounded by a circle integrable
function (the neighborhood independent of `z`), and `F x` is a.e. strongly measurable along
`circleMap c R` for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_circleIntegral_of_dominated_of_fderiv_le
    {F : H → ℂ → E} {F' : H → ℂ → H →L[𝕜] E} {x₀ : H} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun θ : ℝ ↦ F x (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))))
    (hF_int : CircleIntegrable (F x₀) c R)
    (hF'_meas : AEStronglyMeasurable (fun θ : ℝ ↦ F' x₀ (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))))
    (h_bound : ∀ z ∈ sphere c |R|, ∀ x ∈ s, ‖F' x z‖ ≤ bound z)
    (bound_integrable : CircleIntegrable bound c R)
    (h_diff : ∀ z ∈ sphere c |R|, ∀ x ∈ s, HasFDerivAt (fun x ↦ F x z) (F' x z) x) :
    HasFDerivAt (fun x ↦ ∮ z in C(c, R), F x z) (∮ z in C(c, R), F' x₀ z) x₀ :=
  intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (bound := fun θ ↦ |R| * bound (circleMap c R θ)) hs
    (hF_meas.mono fun _ hx ↦ aestronglyMeasurable_deriv_circleMap_smul hx)
    ((circleIntegrable_iff R).mp hF_int) (aestronglyMeasurable_deriv_circleMap_smul hF'_meas)
    (.of_forall fun θ _ x hx ↦
      norm_deriv_circleMap_smul_le (h_bound _ (circleMap_mem_sphere' c R θ) x hx))
    (bound_integrable.const_mul _)
    (.of_forall fun θ _ x hx ↦ (h_diff _ (circleMap_mem_sphere' c R θ) x hx).const_smul _)

/-- Derivative under a parametric circle integral for `x ↦ ∮ z in C(c, R), F x z` at a given point
`x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`, assuming `F x₀` is circle integrable, `x ↦ F x z` is Lipschitz on a
neighborhood of `x₀` for every `z` on the circle (with a neighborhood independent of `z`) with
circle integrable Lipschitz bound, and `F x` is a.e. strongly measurable along `circleMap c R` for
`x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasDerivAt_circleIntegral_of_dominated_loc_of_lip
    {F : 𝕜 → ℂ → E} {F' : ℂ → E} {x₀ : 𝕜} {s : Set 𝕜} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun θ : ℝ ↦ F x (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))))
    (hF_int : CircleIntegrable (F x₀) c R)
    (hF'_meas : AEStronglyMeasurable (fun θ : ℝ ↦ F' (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))))
    (h_lipsch : ∀ z ∈ sphere c |R|, LipschitzOnWith ‖bound z‖₊ (fun x ↦ F x z) s)
    (bound_integrable : CircleIntegrable bound c R)
    (h_diff : ∀ z ∈ sphere c |R|, HasDerivAt (fun x ↦ F x z) (F' z) x₀) :
    CircleIntegrable F' c R ∧
      HasDerivAt (fun x ↦ ∮ z in C(c, R), F x z) (∮ z in C(c, R), F' z) x₀ := by
  rw [circleIntegrable_iff]
  exact intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_lip
    (bound := fun θ ↦ |R| * bound (circleMap c R θ)) hs
    (hF_meas.mono fun _ hx ↦ aestronglyMeasurable_deriv_circleMap_smul hx)
    ((circleIntegrable_iff R).mp hF_int) (aestronglyMeasurable_deriv_circleMap_smul hF'_meas)
    (.of_forall fun θ _ ↦
      lipschitzOnWith_deriv_circleMap_smul (h_lipsch _ (circleMap_mem_sphere' c R θ)))
    (bound_integrable.const_mul _)
    (.of_forall fun θ _ ↦ (h_diff _ (circleMap_mem_sphere' c R θ)).const_smul _)

/-- Derivative under a parametric circle integral for `x ↦ ∮ z in C(c, R), F x z` at a given point
`x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`, assuming `F x₀` is circle integrable, `x ↦ F x z` is differentiable
on a neighborhood of `x₀` for every `z` on the circle (with a neighborhood independent of `z`) with
derivative uniformly bounded by a circle integrable function, and `F x` is a.e. strongly measurable
along `circleMap c R` for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasDerivAt_circleIntegral_of_dominated_loc_of_deriv_le
    {F : 𝕜 → ℂ → E} {F' : 𝕜 → ℂ → E} {x₀ : 𝕜} {s : Set 𝕜} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun θ : ℝ ↦ F x (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))))
    (hF_int : CircleIntegrable (F x₀) c R)
    (hF'_meas : AEStronglyMeasurable (fun θ : ℝ ↦ F' x₀ (circleMap c R θ))
      (volume.restrict (Ι 0 (2 * π))))
    (h_bound : ∀ z ∈ sphere c |R|, ∀ x ∈ s, ‖F' x z‖ ≤ bound z)
    (bound_integrable : CircleIntegrable bound c R)
    (h_diff : ∀ z ∈ sphere c |R|, ∀ x ∈ s, HasDerivAt (fun x ↦ F x z) (F' x z) x) :
    CircleIntegrable (F' x₀) c R ∧
      HasDerivAt (fun x ↦ ∮ z in C(c, R), F x z) (∮ z in C(c, R), F' x₀ z) x₀ := by
  rw [circleIntegrable_iff]
  exact intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := fun θ ↦ |R| * bound (circleMap c R θ)) hs
    (hF_meas.mono fun _ hx ↦ aestronglyMeasurable_deriv_circleMap_smul hx)
    ((circleIntegrable_iff R).mp hF_int) (aestronglyMeasurable_deriv_circleMap_smul hF'_meas)
    (.of_forall fun θ _ x hx ↦
      norm_deriv_circleMap_smul_le (h_bound _ (circleMap_mem_sphere' c R θ) x hx))
    (bound_integrable.const_mul _)
    (.of_forall fun θ _ x hx ↦ (h_diff _ (circleMap_mem_sphere' c R θ) x hx).const_smul _)
