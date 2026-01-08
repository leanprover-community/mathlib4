/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.LocallyConvex.SeparatingDual

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Derivatives of integrals depending on parameters

A parametric integral is a function with shape `f = fun x : H ↦ ∫ a : α, F x a ∂μ` for some
`F : H → α → E`, where `H` and `E` are normed spaces and `α` is a measured space with measure `μ`.

We already know from `continuous_of_dominated`
in `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` how
to guarantee that `f` is continuous using the dominated convergence theorem. In this file,
we want to express the derivative of `f` as the integral of the derivative of `F` with respect
to `x`.


## Main results

As explained above, all results express the derivative of a parametric integral as the integral of
a derivative. The variations come from the assumptions and from the different ways of expressing
derivative, especially Fréchet derivatives vs elementary derivative of function of one real
variable.

* `hasFDerivAt_integral_of_dominated_loc_of_lip`: this version assumes that
  - `F x` is ae-measurable for x near `x₀`,
  - `F x₀` is integrable,
  - `fun x ↦ F x a` has derivative `F' a : H →L[ℝ] E` at `x₀` which is ae-measurable,
  - `fun x ↦ F x a` is locally Lipschitz near `x₀` for almost every `a`,
    with a Lipschitz bound which is integrable with respect to `a`.

  A subtle point is that the "near x₀" in the last condition has to be uniform in `a`. This is
  controlled by a positive number `ε`.

* `hasFDerivAt_integral_of_dominated_of_fderiv_le`: this version assumes `fun x ↦ F x a` has
  derivative `F' x a` for `x` near `x₀` and `F' x` is bounded by an integrable function independent
  from `x` near `x₀`.

`hasDerivAt_integral_of_dominated_loc_of_lip` and
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` are versions of the above two results that
assume `H = ℝ` or `H = ℂ` and use the high-school derivative `deriv` instead of Fréchet derivative
`fderiv`.

We also provide versions of these theorems for set integrals.

## Tags
integral, derivative
-/

public section


noncomputable section

open TopologicalSpace MeasureTheory Filter Metric

open scoped Topology Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E] {H : Type*}
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

variable {F : H → α → E} {x₀ : H} {bound : α → ℝ} {ε : ℝ}

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming `F x₀` is
integrable, `‖F x a - F x₀ a‖ ≤ bound a * ‖x - x₀‖` for `x` in a ball around `x₀` for ae `a` with
integrable Lipschitz bound `bound` (with a ball radius independent of `a`), and `F x` is
ae-measurable for `x` in the same ball. See `hasFDerivAt_integral_of_dominated_loc_of_lip` for a
slightly less general but usually more useful version. -/
theorem hasFDerivAt_integral_of_dominated_loc_of_lip' {F' : α → H →L[𝕜] E} (ε_pos : 0 < ε)
    (hF_meas : ∀ x ∈ ball x₀ ε, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lipsch : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ‖F x a - F x₀ a‖ ≤ bound a * ‖x - x₀‖)
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (F' a) x₀) :
    Integrable F' μ ∧ HasFDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  have nneg : ∀ x, 0 ≤ ‖x - x₀‖⁻¹ := fun x ↦ inv_nonneg.mpr (norm_nonneg _)
  set b : α → ℝ := fun a ↦ |bound a|
  have b_int : Integrable b μ := bound_integrable.norm
  have b_nonneg : ∀ a, 0 ≤ b a := fun a ↦ abs_nonneg _
  replace h_lipsch : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ‖F x a - F x₀ a‖ ≤ b a * ‖x - x₀‖ :=
    h_lipsch.mono fun a ha x hx ↦
      (ha x hx).trans <| mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  have hF_int' : ∀ x ∈ ball x₀ ε, Integrable (F x) μ := fun x x_in ↦ by
    have : ∀ᵐ a ∂μ, ‖F x₀ a - F x a‖ ≤ ε * b a := by
      simp only [norm_sub_rev (F x₀ _)]
      refine h_lipsch.mono fun a ha ↦ (ha x x_in).trans ?_
      rw [mul_comm ε]
      rw [mem_ball, dist_eq_norm] at x_in
      exact mul_le_mul_of_nonneg_left x_in.le (b_nonneg _)
    exact integrable_of_norm_sub_le (hF_meas x x_in) hF_int
      (bound_integrable.norm.const_mul ε) this
  have hF'_int : Integrable F' μ :=
    have : ∀ᵐ a ∂μ, ‖F' a‖ ≤ b a := by
      apply (h_diff.and h_lipsch).mono
      rintro a ⟨ha_diff, ha_lip⟩
      exact ha_diff.le_of_lip' (b_nonneg a) (mem_of_superset (ball_mem_nhds _ ε_pos) <| ha_lip)
    b_int.mono' hF'_meas this
  refine ⟨hF'_int, ?_⟩
  /- Discard the trivial case where `E` is not complete, as all integrals vanish. -/
  by_cases hE : CompleteSpace E; swap
  · rcases subsingleton_or_nontrivial H with hH | hH
    · have : Subsingleton (H →L[𝕜] E) := inferInstance
      convert hasFDerivAt_of_subsingleton _ x₀
    · have : ¬(CompleteSpace (H →L[𝕜] E)) := by
        simpa [SeparatingDual.completeSpace_continuousLinearMap_iff] using hE
      simp only [integral, hE, ↓reduceDIte, this]
      exact hasFDerivAt_const 0 x₀
  have h_ball : ball x₀ ε ∈ 𝓝 x₀ := ball_mem_nhds x₀ ε_pos
  have : ∀ᶠ x in 𝓝 x₀, ‖x - x₀‖⁻¹ * ‖((∫ a, F x a ∂μ) - ∫ a, F x₀ a ∂μ) - (∫ a, F' a ∂μ) (x - x₀)‖ =
      ‖∫ a, ‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀)) ∂μ‖ := by
    apply mem_of_superset (ball_mem_nhds _ ε_pos)
    intro x x_in; simp only
    rw [Set.mem_setOf_eq, ← norm_smul_of_nonneg (nneg _), integral_smul, integral_sub, integral_sub,
      ← ContinuousLinearMap.integral_apply hF'_int]
    exacts [hF_int' x x_in, hF_int, (hF_int' x x_in).sub hF_int,
      hF'_int.apply_continuousLinearMap _]
  rw [hasFDerivAt_iff_tendsto, tendsto_congr' this, ← tendsto_zero_iff_norm_tendsto_zero, ←
    show (∫ a : α, ‖x₀ - x₀‖⁻¹ • (F x₀ a - F x₀ a - (F' a) (x₀ - x₀)) ∂μ) = 0 by simp]
  apply tendsto_integral_filter_of_dominated_convergence
  · filter_upwards [h_ball] with _ x_in
    apply AEStronglyMeasurable.const_smul
    exact ((hF_meas _ x_in).sub (hF_meas _ x₀_in)).sub (hF'_meas.apply_continuousLinearMap _)
  · refine mem_of_superset h_ball fun x hx ↦ ?_
    apply (h_diff.and h_lipsch).mono
    on_goal 1 => rintro a ⟨-, ha_bound⟩
    show ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀))‖ ≤ b a + ‖F' a‖
    replace ha_bound : ‖F x a - F x₀ a‖ ≤ b a * ‖x - x₀‖ := ha_bound x hx
    calc
      ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀))‖ =
          ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a) - ‖x - x₀‖⁻¹ • F' a (x - x₀)‖ := by rw [smul_sub]
      _ ≤ ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a)‖ + ‖‖x - x₀‖⁻¹ • F' a (x - x₀)‖ := norm_sub_le _ _
      _ = ‖x - x₀‖⁻¹ * ‖F x a - F x₀ a‖ + ‖x - x₀‖⁻¹ * ‖F' a (x - x₀)‖ := by
        rw [norm_smul_of_nonneg, norm_smul_of_nonneg] <;> exact nneg _
      _ ≤ ‖x - x₀‖⁻¹ * (b a * ‖x - x₀‖) + ‖x - x₀‖⁻¹ * (‖F' a‖ * ‖x - x₀‖) := by
        gcongr; exact (F' a).le_opNorm _
      _ ≤ b a + ‖F' a‖ := ?_
    simp only [← div_eq_inv_mul]
    apply_rules [add_le_add, div_le_of_le_mul₀] <;> first | rfl | positivity
  · exact b_int.add hF'_int.norm
  · apply h_diff.mono
    intro a ha
    suffices Tendsto (fun x ↦ ‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀))) (𝓝 x₀) (𝓝 0) by simpa
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have : (fun x ↦ ‖x - x₀‖⁻¹ * ‖F x a - F x₀ a - F' a (x - x₀)‖) = fun x ↦
        ‖‖x - x₀‖⁻¹ • (F x a - F x₀ a - F' a (x - x₀))‖ := by
      ext x
      rw [norm_smul_of_nonneg (nneg _)]
    rwa [hasFDerivAt_iff_tendsto, this] at ha

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a`
(with a ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is ae-measurable
for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_integral_of_dominated_loc_of_lip {F' : α → H →L[𝕜] E}
    (ε_pos : 0 < ε) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (hF_int : Integrable (F x₀) μ) (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lip : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs <| bound a) (F · a) (ball x₀ ε))
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (F' a) x₀) :
    Integrable F' μ ∧ HasFDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  obtain ⟨δ, δ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ ball x₀ δ, AEStronglyMeasurable (F x) μ ∧ x ∈ ball x₀ ε :=
    eventually_nhds_iff_ball.mp (hF_meas.and (ball_mem_nhds x₀ ε_pos))
  choose hδ_meas hδε using hδ
  replace h_lip : ∀ᵐ a : α ∂μ, ∀ x ∈ ball x₀ δ, ‖F x a - F x₀ a‖ ≤ |bound a| * ‖x - x₀‖ :=
    h_lip.mono fun a lip x hx ↦ lip.norm_sub_le (hδε x hx) (mem_ball_self ε_pos)
  replace bound_integrable := bound_integrable.norm
  apply hasFDerivAt_integral_of_dominated_loc_of_lip' δ_pos <;> assumption

open scoped Interval in
/-- Differentiation under integral of `x ↦ ∫ x in a..b, F x t` at a given point `x₀ ∈ (a,b)`,
assuming `F x₀` is integrable on `(a,b)`, that `x ↦ F x t` is Lipschitz on a ball around `x₀`
for almost every `t` (with a ball radius independent of `t`) with integrable Lipschitz bound,
and `F x` is a.e.-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_integral_of_dominated_loc_of_lip_interval [NormedSpace ℝ H] {μ : Measure ℝ}
    {F : H → ℝ → E} {F' : ℝ → H →L[ℝ] E} {a b : ℝ} {bound : ℝ → ℝ} (ε_pos : 0 < ε)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) <| μ.restrict (Ι a b))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable F' <| μ.restrict (Ι a b))
    (h_lip : ∀ᵐ t ∂μ.restrict (Ι a b),
      LipschitzOnWith (Real.nnabs <| bound t) (F · t) (ball x₀ ε))
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ.restrict (Ι a b), HasFDerivAt (F · t) (F' t) x₀) :
    IntervalIntegrable F' μ a b ∧
      HasFDerivAt (fun x ↦ ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' t ∂μ) x₀ := by
  simp_rw [AEStronglyMeasurable.aestronglyMeasurable_uIoc_iff, eventually_and] at hF_meas hF'_meas
  rw [ae_restrict_uIoc_iff] at h_lip h_diff
  have H₁ :=
    hasFDerivAt_integral_of_dominated_loc_of_lip ε_pos hF_meas.1 hF_int.1 hF'_meas.1 h_lip.1
      bound_integrable.1 h_diff.1
  have H₂ :=
    hasFDerivAt_integral_of_dominated_loc_of_lip ε_pos hF_meas.2 hF_int.2 hF'_meas.2 h_lip.2
      bound_integrable.2 h_diff.2
  exact ⟨⟨H₁.1, H₂.1⟩, H₁.2.sub H₂.2⟩

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on a ball around `x₀` for ae `a` with
derivative norm uniformly bounded by an integrable function (the ball radius is independent of `a`),
and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_integral_of_dominated_of_fderiv_le {F' : H → α → H →L[𝕜] E} (ε_pos : 0 < ε)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ‖F' x a‖ ≤ bound a)
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, HasFDerivAt (F · a) (F' x a) x) :
    HasFDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ := by
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  have diff_x₀ : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (F' x₀ a) x₀ :=
    h_diff.mono fun a ha ↦ ha x₀ x₀_in
  have : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs (bound a)) (F · a) (ball x₀ ε) := by
    apply (h_diff.and h_bound).mono
    rintro a ⟨ha_deriv, ha_bound⟩
    refine (convex_ball _ _).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x x_in ↦ (ha_deriv x x_in).hasFDerivWithinAt) fun x x_in ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
    exact (ha_bound x x_in).trans (le_abs_self _)
  exact (hasFDerivAt_integral_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas this
    bound_integrable diff_x₀).2

open scoped Interval in
/-- Differentiation under integral of `x ↦ ∫ x in a..b, F x a` at a given point `x₀`, assuming
`F x₀` is integrable on `(a,b)`, `x ↦ F x a` is differentiable on a ball around `x₀` for ae `a` with
derivative norm uniformly bounded by an integrable function (the ball radius is independent of `a`),
and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_integral_of_dominated_of_fderiv_le'' [NormedSpace ℝ H] {μ : Measure ℝ}
    {F : H → ℝ → E} {F' : H → ℝ → H →L[ℝ] E} {a b : ℝ} {bound : ℝ → ℝ} (ε_pos : 0 < ε)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) <| μ.restrict (Ι a b))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀) <| μ.restrict (Ι a b))
    (h_bound : ∀ᵐ t ∂μ.restrict (Ι a b), ∀ x ∈ ball x₀ ε, ‖F' x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ.restrict (Ι a b), ∀ x ∈ ball x₀ ε, HasFDerivAt (F · t) (F' x t) x) :
    HasFDerivAt (fun x ↦ ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀ := by
  rw [ae_restrict_uIoc_iff] at h_diff h_bound
  simp_rw [AEStronglyMeasurable.aestronglyMeasurable_uIoc_iff, eventually_and] at hF_meas hF'_meas
  exact
    (hasFDerivAt_integral_of_dominated_of_fderiv_le ε_pos hF_meas.1 hF_int.1 hF'_meas.1 h_bound.1
          bound_integrable.1 h_diff.1).sub
      (hasFDerivAt_integral_of_dominated_of_fderiv_le ε_pos hF_meas.2 hF_int.2 hF'_meas.2 h_bound.2
        bound_integrable.2 h_diff.2)

section

open Real ContinuousLinearMap Asymptotics Interval
open Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem hasFDerivAt_parametric_primitive_of_lip' (F : H → ℝ → E) (F' : ℝ → H →L[ℝ] E) {x₀ : H}
    {G' : H →L[ℝ] E} {bound : ℝ → ℝ} {s : H → ℝ} {ε : ℝ} (ε_pos : 0 < ε) {a a₀ b₀ : ℝ}
    {s' : H →L[ℝ] ℝ} (ha : a ∈ Ioo a₀ b₀) (hsx₀ : s x₀ ∈ Ioo a₀ b₀)
    (hF_meas : ∀ x ∈ ball x₀ ε, AEStronglyMeasurable (F x) (volume.restrict (Ioo a₀ b₀)))
    (hF_int : IntegrableOn (F x₀) (Ioo a₀ b₀)) (hF_cont : ContinuousAt (F x₀) (s x₀))
    (hF'_meas : AEStronglyMeasurable F' (volume.restrict <| Ι a (s x₀)))
    (h_lipsch :
      ∀ᵐ t ∂volume.restrict <| Ioo a₀ b₀,
        LipschitzOnWith (nnabs <| bound t) (fun x ↦ F x t) (ball x₀ ε))
    (bound_integrable : IntegrableOn bound (Ioo a₀ b₀)) (bound_cont : ContinuousAt bound (s x₀))
    (bound_nonneg : ∀ t, 0 ≤ bound t)
    -- This assumption could be weakened, but this way is much more convenient.
    (h_diff : ∀ᵐ a ∂volume.restrict (Ι a (s x₀)), HasFDerivAt (fun x ↦ F x a) (F' a) x₀)
    (s_diff : HasFDerivAt s s' x₀)
    (hG' : (∫ t in a..s x₀, F' t) + (toSpanSingleton ℝ (F x₀ (s x₀))).comp s' = G') :
    IntervalIntegrable F' volume a (s x₀) ∧
      HasFDerivAt (fun x : H ↦ ∫ t in a..s x, F x t) G' x₀ := by
  subst hG'
  let φ : H → ℝ → E := fun x t ↦ ∫ s in a..t, F x s
  have Ioo_nhds : Ioo a₀ b₀ ∈ 𝓝 (s x₀) := Ioo_mem_nhds hsx₀.1 hsx₀.2
  have bound_int {s u} (hs : s ∈ Ioo a₀ b₀) (hu : u ∈ Ioo a₀ b₀) :
      IntervalIntegrable bound volume s u :=
    (bound_integrable.mono_set <| ordConnected_Ioo.uIcc_subset hs hu).intervalIntegrable
  have mem_nhds : ball x₀ ε ∩ s ⁻¹' Ioo a₀ b₀ ∈ 𝓝 x₀ :=
    Filter.inter_mem (ball_mem_nhds x₀ ε_pos) (s_diff.continuousAt.preimage_mem_nhds Ioo_nhds)
  have hx₀ : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  have hF_meas_ball {x} (hx : x ∈ ball x₀ ε) {s u} (hs : s ∈ Ioo a₀ b₀) (hu : u ∈ Ioo a₀ b₀) :
      AEStronglyMeasurable (F x) (volume.restrict <| Ι s u) :=
    (hF_meas _ hx).mono_set (ordConnected_Ioo.uIoc_subset hs hu)
  have hF_int_ball {x} (hx : x ∈ ball x₀ ε) {s u} (hs : s ∈ Ioo a₀ b₀) (hu : u ∈ Ioo a₀ b₀) :
      IntervalIntegrable (F x) volume s u := by
    have : IntegrableOn (F x) (Ioo a₀ b₀) := by
      apply integrable_of_norm_sub_le (hF_meas x hx) hF_int (bound_integrable.mul_const ‖x - x₀‖)
      apply h_lipsch.mono
      intro t ht
      rw [norm_sub_rev]
      rw [lipschitzOnWith_iff_norm_sub_le] at ht
      simpa [bound_nonneg t] using ht hx hx₀
    exact (this.mono_set <| ordConnected_Ioo.uIcc_subset hs hu).intervalIntegrable
  constructor
  · apply (bound_int ha hsx₀).mono_fun' hF'_meas _
    replace h_lipsch : ∀ᵐ t ∂volume.restrict (Ι a (s x₀)),
        LipschitzOnWith (nnabs (bound t)) (fun x : H ↦ F x t) (ball x₀ ε) :=
      ae_restrict_of_ae_restrict_of_subset (ordConnected_Ioo.uIoc_subset ha hsx₀) h_lipsch
    filter_upwards [h_lipsch, h_diff] with t ht_lip ht_diff
    rw [show bound t = nnabs (bound t) by simp [bound_nonneg t] ]
    exact ht_diff.le_of_lipschitzOn (ball_mem_nhds x₀ ε_pos) ht_lip
  · have D₁ : HasFDerivAt (fun x ↦ φ x (s x₀)) (∫ t in a..s x₀, F' t) x₀ := by
      replace hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (volume.restrict (Ι a (s x₀))) :=
        Eventually.mono (ball_mem_nhds x₀ ε_pos) fun x hx ↦ hF_meas_ball hx ha hsx₀
      exact (hasFDerivAt_integral_of_dominated_loc_of_lip_interval ε_pos hF_meas
        (hF_int_ball hx₀ ha hsx₀) hF'_meas
        (ae_restrict_of_ae_restrict_of_subset (ordConnected_Ioo.uIoc_subset ha hsx₀) h_lipsch)
        (bound_int ha hsx₀) h_diff).2
    have D₂ : HasFDerivAt (fun x ↦ φ x₀ (s x)) ((toSpanSingleton ℝ (F x₀ (s x₀))).comp s') x₀ := by
      suffices HasFDerivAt (φ x₀) (toSpanSingleton ℝ (F x₀ (s x₀))) (s x₀) from this.comp _ s_diff
      rw [hasFDerivAt_iff_hasDerivAt, toSpanSingleton_apply, one_smul]
      exact intervalIntegral.integral_hasDerivAt_right (hF_int_ball hx₀ ha hsx₀)
        ⟨Ioo a₀ b₀, Ioo_nhds, hF_meas x₀ hx₀⟩ hF_cont
    have D₃ : HasFDerivAt (𝕜 := ℝ) (fun x ↦ ∫ t in s x₀..s x, F x t - F x₀ t) 0 x₀ := by
      refine IsBigO.hasFDerivAt (𝕜 := ℝ) ?_ one_lt_two
      have O₁ : (fun x ↦ ∫ s in s x₀..s x, bound s) =O[𝓝 x₀] fun x ↦ ‖x - x₀‖ := by
        have : (fun x ↦ s x - s x₀) =O[𝓝 x₀] fun x ↦ ‖x - x₀‖ := s_diff.isBigO_sub.norm_right
        refine IsBigO.trans ?_ this
        change ((fun t ↦ ∫ s in s x₀..t, bound s) ∘ s) =O[𝓝 x₀] ((fun t ↦ t - s x₀) ∘ s)
        refine IsBigO.comp_tendsto ?_ s_diff.continuousAt
        have M : StronglyMeasurableAtFilter bound (𝓝 (s x₀)) volume :=
          ⟨Ioo a₀ b₀, Ioo_nhds, bound_integrable.1⟩
        refine (intervalIntegral.integral_hasDerivAt_right (bound_int ha hsx₀)
          M bound_cont).hasFDerivAt.isBigO_sub.congr' ?_ EventuallyEq.rfl
        filter_upwards [Ioo_nhds] with t ht
        rw [intervalIntegral.integral_interval_sub_left (bound_int ha ht) (bound_int ha hsx₀)]
      have O₂ : (fun x ↦ ‖x - x₀‖) =O[𝓝 x₀] fun x ↦ ‖x - x₀‖ := isBigO_refl _ _
      have O₃ : (fun x ↦ ∫ t : ℝ in s x₀..s x, F x t - F x₀ t) =O[𝓝 x₀] fun x ↦
          (∫ t' in s x₀..s x, bound t') * ‖x - x₀‖ := by
        have bdd : ∀ᶠ x in 𝓝 x₀,
            ‖∫ s in s x₀..s x, F x s - F x₀ s‖ ≤ |∫ s in s x₀..s x, bound s| * ‖x - x₀‖ := by
          filter_upwards [mem_nhds]
          rintro x ⟨hx : x ∈ ball x₀ ε, hsx : s x ∈ Ioo a₀ b₀⟩
          rw [← abs_of_nonneg (norm_nonneg <| x - x₀), ← abs_mul, ←
            intervalIntegral.integral_mul_const]
          apply intervalIntegral.norm_integral_le_abs_of_norm_le _
            ((bound_int hsx₀ hsx).mul_const _)
          apply ae_restrict_of_ae_restrict_of_subset (ordConnected_Ioo.uIoc_subset hsx₀ hsx)
          apply h_lipsch.mono
          intro t ht
          rw [lipschitzOnWith_iff_norm_sub_le] at ht
          simp only [coe_nnabs] at ht
          rw [← abs_of_nonneg (bound_nonneg t)]
          exact ht hx (mem_ball_self ε_pos)
        rw [← isBigO_norm_right]
        simp only [norm_eq_abs, abs_mul, abs_norm]
        exact bdd.isBigO
      simp_rw [pow_two]
      exact O₃.trans (O₁.mul O₂)
    have : ∀ᶠ x in 𝓝 x₀,
        ∫ t in a..s x, F x t =
          (φ x (s x₀) + φ x₀ (s x) + ∫ t in s x₀..s x, F x t - F x₀ t) - φ x₀ (s x₀) := by
      filter_upwards [mem_nhds]
      rintro x ⟨hx : x ∈ ball x₀ ε, hsx : s x ∈ Ioo a₀ b₀⟩
      have int₁ : IntervalIntegrable (F x₀) volume (s x₀) (s x) := hF_int_ball hx₀ hsx₀ hsx
      have int₂ : IntervalIntegrable (F x) volume (s x₀) (s x) := hF_int_ball hx hsx₀ hsx
      dsimp [φ]
      rw [intervalIntegral.integral_sub int₂ int₁, add_sub, add_right_comm, sub_sub,
        intervalIntegral.integral_add_adjacent_intervals (hF_int_ball hx ha hsx₀) int₂,
        ← intervalIntegral.integral_add_adjacent_intervals (hF_int_ball hx₀ ha hsx₀) int₁]
      abel
    apply HasFDerivAt.congr_of_eventuallyEq _ this
    simpa [Pi.sub_def] using ((D₁.add D₂).add D₃).sub (hasFDerivAt_const (φ x₀ (s x₀)) x₀)

@[inherit_doc] local notation:70 u " ⬝ " φ =>
  ContinuousLinearMap.comp (ContinuousLinearMap.toSpanSingleton ℝ u) φ

end

section

variable {F : 𝕜 → α → E} {x₀ : 𝕜}

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`,
assuming `F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a ball around `x₀` for ae `a`
(with ball radius independent of `a`) with integrable Lipschitz bound, and `F x` is
ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasDerivAt_integral_of_dominated_loc_of_lip {F' : α → E} (ε_pos : 0 < ε)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lipsch : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs <| bound a) (F · a) (ball x₀ ε))
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, HasDerivAt (F · a) (F' a) x₀) :
    Integrable F' μ ∧ HasDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  set L : E →L[𝕜] 𝕜 →L[𝕜] E := ContinuousLinearMap.smulRightL 𝕜 𝕜 E 1
  replace h_diff : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (L (F' a)) x₀ :=
    h_diff.mono fun x hx ↦ hx.hasFDerivAt
  have hm : AEStronglyMeasurable (L ∘ F') μ := L.continuous.comp_aestronglyMeasurable hF'_meas
  obtain ⟨hF'_int, key⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip
    ε_pos hF_meas hF_int hm h_lipsch bound_integrable h_diff
  replace hF'_int : Integrable F' μ := by
    rw [← integrable_norm_iff hm] at hF'_int
    simpa [L, (· ∘ ·), integrable_norm_iff hF'_meas] using hF'_int
  refine ⟨hF'_int, ?_⟩
  by_cases hE : CompleteSpace E; swap
  · simpa [integral, hE] using hasDerivAt_const x₀ 0
  simp_rw [hasDerivAt_iff_hasFDerivAt] at h_diff ⊢
  simpa only [(· ∘ ·), ContinuousLinearMap.integral_comp_comm _ hF'_int] using key

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : ℝ`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on an interval around `x₀` for ae `a`
(with interval radius independent of `a`) with derivative uniformly bounded by an integrable
function, and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le (ε_pos : 0 < ε)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    {F' : 𝕜 → α → E} (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ‖F' x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, HasDerivAt (F · a) (F' x a) x) :
    Integrable (F' x₀) μ ∧ HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ := by
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  have diff_x₀ : ∀ᵐ a ∂μ, HasDerivAt (F · a) (F' x₀ a) x₀ :=
    h_diff.mono fun a ha ↦ ha x₀ x₀_in
  have : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs (bound a)) (fun x : 𝕜 ↦ F x a) (ball x₀ ε) := by
    apply (h_diff.and h_bound).mono
    rintro a ⟨ha_deriv, ha_bound⟩
    refine (convex_ball _ _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x x_in ↦ (ha_deriv x x_in).hasDerivWithinAt) fun x x_in ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
    exact (ha_bound x x_in).trans (le_abs_self _)
  exact
    hasDerivAt_integral_of_dominated_loc_of_lip ε_pos hF_meas hF_int hF'_meas this bound_integrable
      diff_x₀

end
