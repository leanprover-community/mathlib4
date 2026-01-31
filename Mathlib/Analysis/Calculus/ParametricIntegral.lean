/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

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
  controlled by a fixed neighborhood `s` of `x₀`.

* `hasFDerivAt_integral_of_dominated_of_fderiv_le`: this version assumes `fun x ↦ F x a` has
  derivative `F' x a` for `x` near `x₀` and `F' x` is bounded by an integrable function independent
  from `x` near `x₀`.

* `hasFDerivAt_integral_of_continuousOn_fderiv`: this version assumes that `F : H → α → E` is
  continuously differentiable in the first argument near `x₀` in the sense that:
  - `F.uncurry : H × α → E` is continuous on `u ×ˢ k` for a neighbourhood `u` of `x₀`,
  - `fun x ↦ F x a` is differentiable on `u` for each parameter `a ∈ k`,
  - `fun (x, a) ↦ fderiv 𝕜 (fun y ↦ F y a) x` is continuous on `u ×ˢ k`.

  Here `k : Set α` is the domain of integration and is required to be compact, regarding some
  sufficiently compatible topology on `α`.

* `ContDiffOn.parametric_integral` : If `f.uncurry : H × H' → E` is `Cⁿ` on `u ×ˢ k` for an open
  set `u` and a compact set `k`, then given any subset `s₀` of `k` the parametric
  integral `fun x ↦ ∫ a in s₀, f x a ∂μ` is `Cⁿ` on `u` too.

`hasDerivAt_integral_of_dominated_loc_of_lip` and
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` are versions of the above two results that
assume `H = ℝ` or `H = ℂ` and use the high-school derivative `deriv` instead of Fréchet derivative
`fderiv`.

## Tags
integral, derivative
-/

public section


noncomputable section

open TopologicalSpace MeasureTheory Filter Metric Set

open scoped Topology Filter

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace 𝕜 E]
  {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]
  {H' : Type*} [NormedAddCommGroup H'] [NormedSpace 𝕜 H'] [MeasurableSpace H']
  [OpensMeasurableSpace H']

variable {F : H → α → E} {x₀ : H} {bound : α → ℝ} {s : Set H}

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming `F x₀` is
integrable, `‖F x a - F x₀ a‖ ≤ bound a * ‖x - x₀‖` for `x` in a neighborhood of `x₀` for ae `a`
integrable Lipschitz bound `bound` (with a neighborhood independent of `a`), and `F x` is
ae-measurable for `x` in the same ball. See `hasFDerivAt_integral_of_dominated_loc_of_lip` for a
slightly less general but usually more useful version. -/
theorem hasFDerivAt_integral_of_dominated_loc_of_lip' {F' : α → H →L[𝕜] E} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ x ∈ s, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lipsch : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F x a - F x₀ a‖ ≤ bound a * ‖x - x₀‖)
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (F' a) x₀) :
    Integrable F' μ ∧ HasFDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  obtain ⟨ε, ε_pos, hε⟩ := Metric.mem_nhds_iff.1 hs
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  have nneg : ∀ x, 0 ≤ ‖x - x₀‖⁻¹ := fun x ↦ inv_nonneg.mpr (norm_nonneg _)
  set b : α → ℝ := fun a ↦ |bound a|
  have b_int : Integrable b μ := bound_integrable.norm
  have b_nonneg : ∀ a, 0 ≤ b a := fun a ↦ abs_nonneg _
  replace h_lipsch : ∀ᵐ a ∂μ, ∀ x ∈ ball x₀ ε, ‖F x a - F x₀ a‖ ≤ b a * ‖x - x₀‖ :=
    h_lipsch.mono fun a ha x hx ↦
      (ha x (hε hx)).trans <| mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
  have hF_int' : ∀ x ∈ ball x₀ ε, Integrable (F x) μ := fun x x_in ↦ by
    have : ∀ᵐ a ∂μ, ‖F x₀ a - F x a‖ ≤ ε * b a := by
      simp only [norm_sub_rev (F x₀ _)]
      refine h_lipsch.mono fun a ha ↦ (ha x x_in).trans ?_
      rw [mul_comm ε]
      rw [mem_ball, dist_eq_norm] at x_in
      exact mul_le_mul_of_nonneg_left x_in.le (b_nonneg _)
    exact integrable_of_norm_sub_le (hF_meas x (hε x_in)) hF_int
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
    rw [mem_setOf_eq, ← norm_smul_of_nonneg (nneg _), integral_smul, integral_sub, integral_sub,
      ← ContinuousLinearMap.integral_apply hF'_int]
    exacts [hF_int' x x_in, hF_int, (hF_int' x x_in).sub hF_int,
      hF'_int.apply_continuousLinearMap _]
  rw [hasFDerivAt_iff_tendsto, tendsto_congr' this, ← tendsto_zero_iff_norm_tendsto_zero, ←
    show (∫ a : α, ‖x₀ - x₀‖⁻¹ • (F x₀ a - F x₀ a - (F' a) (x₀ - x₀)) ∂μ) = 0 by simp]
  apply tendsto_integral_filter_of_dominated_convergence
  · filter_upwards [h_ball] with _ x_in
    apply AEStronglyMeasurable.const_smul
    exact ((hF_meas _ (hε x_in)).sub (hF_meas _ (hε x₀_in))).sub
      (hF'_meas.apply_continuousLinearMap _)
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
`F x₀` is integrable, `x ↦ F x a` is locally Lipschitz in a neighborhood of `x₀` for ae `a`
(with a neighborhood independent of `a`) with integrable Lipschitz bound, and `F x` is ae-measurable
for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_integral_of_dominated_loc_of_lip {F' : α → H →L[𝕜] E}
    (hs : s ∈ 𝓝 x₀) (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ)
    (hF_int : Integrable (F x₀) μ) (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lip : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs <| bound a) (F · a) s)
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (F' a) x₀) :
    Integrable F' μ ∧ HasFDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  obtain ⟨δ, δ_pos, hδ⟩ : ∃ δ > 0, ∀ x ∈ ball x₀ δ, AEStronglyMeasurable (F x) μ ∧ x ∈ s :=
    eventually_nhds_iff_ball.mp (hF_meas.and hs)
  choose hδ_meas hδε using hδ
  replace h_lip : ∀ᵐ a : α ∂μ, ∀ x ∈ ball x₀ δ, ‖F x a - F x₀ a‖ ≤ |bound a| * ‖x - x₀‖ :=
    h_lip.mono fun a lip x hx ↦ lip.norm_sub_le (hδε x hx) (mem_of_mem_nhds hs)
  replace bound_integrable := bound_integrable.norm
  apply hasFDerivAt_integral_of_dominated_loc_of_lip' (ball_mem_nhds x₀ δ_pos) <;> assumption

open scoped Interval in
/-- Differentiation under integral of `x ↦ ∫ x in a..b, F x t` at a given point `x₀ ∈ (a,b)`,
assuming `F x₀` is integrable on `(a,b)`, that `x ↦ F x t` is Lipschitz on a neighborhood of `x₀`
for almost every `t` (with a neighborhood independent of `t`) with integrable Lipschitz bound,
and `F x` is a.e.-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_integral_of_dominated_loc_of_lip_interval [NormedSpace ℝ H] {μ : Measure ℝ}
    {F : H → ℝ → E} {F' : ℝ → H →L[ℝ] E} {a b : ℝ} {bound : ℝ → ℝ} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) <| μ.restrict (Ι a b))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable F' <| μ.restrict (Ι a b))
    (h_lip : ∀ᵐ t ∂μ.restrict (Ι a b),
      LipschitzOnWith (Real.nnabs <| bound t) (F · t) s)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ.restrict (Ι a b), HasFDerivAt (F · t) (F' t) x₀) :
    IntervalIntegrable F' μ a b ∧
      HasFDerivAt (fun x ↦ ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' t ∂μ) x₀ := by
  simp_rw [AEStronglyMeasurable.aestronglyMeasurable_uIoc_iff, eventually_and] at hF_meas hF'_meas
  rw [ae_restrict_uIoc_iff] at h_lip h_diff
  have H₁ :=
    hasFDerivAt_integral_of_dominated_loc_of_lip hs hF_meas.1 hF_int.1 hF'_meas.1 h_lip.1
      bound_integrable.1 h_diff.1
  have H₂ :=
    hasFDerivAt_integral_of_dominated_loc_of_lip hs hF_meas.2 hF_int.2 hF'_meas.2 h_lip.2
      bound_integrable.2 h_diff.2
  exact ⟨⟨H₁.1, H₂.1⟩, H₁.2.sub H₂.2⟩

/-- Differentiation under integral of `x ↦ ∫ F x a` at a given point `x₀`, assuming
`F x₀` is integrable, `x ↦ F x a` is differentiable on a neighborhood of `x₀` for ae `a` with
derivative norm uniformly bounded by an integrable function (the neighborhood is independent
of `a`), and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_integral_of_dominated_of_fderiv_le {F' : H → α → H →L[𝕜] E} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a)
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasFDerivAt (F · a) (F' x a) x) :
    HasFDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ := by
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ 𝕜 H
  rcases Metric.mem_nhds_iff.1 hs with ⟨ε, ε_pos, hε⟩
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  have diff_x₀ : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (F' x₀ a) x₀ :=
    h_diff.mono fun a ha ↦ ha x₀ (hε x₀_in)
  have : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs (bound a)) (F · a) (ball x₀ ε) := by
    apply (h_diff.and h_bound).mono
    rintro a ⟨ha_deriv, ha_bound⟩
    refine (convex_ball _ _).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x x_in ↦ (ha_deriv x (hε x_in)).hasFDerivWithinAt) fun x x_in ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
    exact (ha_bound x (hε x_in)).trans (le_abs_self _)
  apply (hasFDerivAt_integral_of_dominated_loc_of_lip (ball_mem_nhds x₀ ε_pos)
    hF_meas hF_int hF'_meas this bound_integrable diff_x₀).2

open scoped Interval in
/-- Differentiation under integral of `x ↦ ∫ x in a..b, F x a` at a given point `x₀`, assuming
`F x₀` is integrable on `(a,b)`, `x ↦ F x a` is differentiable on a neighborhood of `x₀` for ae `a`
 with derivative norm uniformly bounded by an integrable function (the neighborhood is independent
 of `a`), and `F x` is ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasFDerivAt_integral_of_dominated_of_fderiv_le'' [NormedSpace ℝ H] {μ : Measure ℝ}
    {F : H → ℝ → E} {F' : H → ℝ → H →L[ℝ] E} {a b : ℝ} {bound : ℝ → ℝ} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) <| μ.restrict (Ι a b))
    (hF_int : IntervalIntegrable (F x₀) μ a b)
    (hF'_meas : AEStronglyMeasurable (F' x₀) <| μ.restrict (Ι a b))
    (h_bound : ∀ᵐ t ∂μ.restrict (Ι a b), ∀ x ∈ s, ‖F' x t‖ ≤ bound t)
    (bound_integrable : IntervalIntegrable bound μ a b)
    (h_diff : ∀ᵐ t ∂μ.restrict (Ι a b), ∀ x ∈ s, HasFDerivAt (F · t) (F' x t) x) :
    HasFDerivAt (fun x ↦ ∫ t in a..b, F x t ∂μ) (∫ t in a..b, F' x₀ t ∂μ) x₀ := by
  rw [ae_restrict_uIoc_iff] at h_diff h_bound
  simp_rw [AEStronglyMeasurable.aestronglyMeasurable_uIoc_iff, eventually_and] at hF_meas hF'_meas
  exact
    (hasFDerivAt_integral_of_dominated_of_fderiv_le hs hF_meas.1 hF_int.1 hF'_meas.1 h_bound.1
          bound_integrable.1 h_diff.1).sub
      (hasFDerivAt_integral_of_dominated_of_fderiv_le hs hF_meas.2 hF_int.2 hF'_meas.2 h_bound.2
        bound_integrable.2 h_diff.2)

/-- A convenient special case of `hasFDerivAt_integral_of_dominated_of_fderiv_le`:
if there exist a neighbourhood `u` of `x₀` and a compact set `k` such that `F.uncurry : H × α → E`
is continuous and continuously differentiable in the first argument on `u ×ˢ k`, then for any
finite-measure set `s ⊆ k` a derivative of `fun x => ∫ a in s, F x a ∂μ` in `x₀` can be computed as
`∫ a in s, fderiv 𝕜 (fun x ↦ F x a) x₀ ∂μ`. -/
theorem hasFDerivAt_integral_of_continuousOn_fderiv [TopologicalSpace α]
    [OpensMeasurableSpace α] {F : H → α → E} {x₀ : H} {u : Set H} (hu : u ∈ 𝓝 x₀) {k s : Set α}
    (hk : IsCompact k) (hs : MeasurableSet s) (hs' : μ s ≠ ⊤) (hsk : s ⊆ k)
    (hF₁ : ContinuousOn F.uncurry (u ×ˢ k))
    (hF₂ : ∀ a ∈ k, DifferentiableOn 𝕜 (fun x ↦ F x a) u)
    (hF₃ : ContinuousOn (fun x ↦ fderiv 𝕜 (fun y ↦ F y x.2) x.1) (u ×ˢ k)) :
    HasFDerivAt (fun x => ∫ a in s, F x a ∂μ)
      (∫ a in s, fderiv 𝕜 (fun x ↦ F x a) x₀ ∂μ) x₀ := by
  -- wlog shrink u to an open neighbourhood
  wlog hu' : IsOpen u with h
  · have ⟨u', hu'⟩ := _root_.mem_nhds_iff.1 hu
    exact h (hu'.2.1.mem_nhds hu'.2.2) hk hs hs' hsk (hF₁.mono <| prod_mono_left hu'.1)
      (fun a ha ↦ (hF₂ a ha).mono hu'.1) (hF₃.mono <| prod_mono_left hu'.1) hu'.2.1
  have hxu := mem_of_mem_nhds hu
  let F' := fun x : H × α ↦ ‖fderiv 𝕜 (fun y ↦ F y x.2) x.1‖
  have hF' : ContinuousOn F' _ := continuous_norm.comp_continuousOn hF₃
  -- via a compactness argument, find an `ε > 0` such that `F'` is bounded on `ball x₀ ε × k`
  let ⟨ε, hε, hε', B, hB⟩ :
      ∃ ε > 0, ball x₀ ε ⊆ u ∧ ∃ B, ∀ x ∈ ball x₀ ε ×ˢ k, F' x < B := by
    let ⟨B, hB⟩ := (isCompact_singleton.prod hk).bddAbove_image <|
      hF'.mono <| prod_mono_left <| singleton_subset_iff.2 hxu
    have ⟨v, hv, hv'⟩ := generalized_tube_lemma_left (s := {x₀}) isCompact_singleton
      hk (s' := u) (n := F' ⁻¹' (Iio (B + 1))) (by
        refine nhdsSetWithin_mono_left ?_ <| hF'.preimage_mem_nhdsSetWithin_of_mem_nhdsSet
          (t := Iic B) (u := Iio (B + 1)) <| isOpen_Iio.mem_nhdsSet.2 (by simp)
        intro x hx
        exact ⟨prod_mono_left (by simp [hxu]) hx, mem_upperBounds.1 hB _ <| mem_image_of_mem _ hx⟩)
    rw [nhdsSetWithin_singleton, hu'.nhdsWithin_eq hxu] at hv
    have ⟨ε, hε, hε'⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hv (hu))
    exact ⟨ε, hε, hε'.trans inter_subset_right, B + 1,
      fun x hx ↦ hv' <| prod_mono_left (hε'.trans inter_subset_left) hx⟩
  -- now apply `hasFDerivAt_integral_of_dominated_of_fderiv_le` with the obtained `ε` and bound
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ ↦ B)
    (F' := fun x a ↦ fderiv 𝕜 (fun x ↦ F x a) x) (ball_mem_nhds x₀ hε)
  · refine eventually_nhds_iff.2 ⟨u, fun x hx ↦ ?_, hu', hxu⟩
    apply (hF₁.uncurry_left _ hx).aestronglyMeasurable_of_subset_isCompact hk hs hsk
  · apply (hF₁.uncurry_left _ hxu).integrableOn_of_subset_isCompact hk hs hsk hs'
  · apply (hF₃.uncurry_left _ hxu).aestronglyMeasurable_of_subset_isCompact hk hs hsk
  · filter_upwards [ae_restrict_mem hs] with a ha x hx using (hB (x, a) ⟨hx, hsk ha⟩).le
  · apply integrableOn_const hs'
  · filter_upwards [ae_restrict_mem hs] with a ha x hx
    apply DifferentiableAt.hasFDerivAt
    exact (hF₂ a (hsk ha) x (hε' hx)).differentiableAt (hu'.mem_nhds (hε' hx))

/-- A version of `hasFDerivAt_integral_of_continuousOn_fderiv` where `α` is required to be Hausdorff
but `s` is not required to be measurable. -/
theorem hasFDerivAt_integral_of_continuousOn_fderiv_of_t2Space [TopologicalSpace α] [T2Space α]
    [OpensMeasurableSpace α] {F : H → α → E} {x₀ : H} {u : Set H} (hu : u ∈ 𝓝 x₀) {k s : Set α}
    (hk : IsCompact k) (hs' : μ s ≠ ⊤) (hsk : s ⊆ k)
    (hF₁ : ContinuousOn F.uncurry (u ×ˢ k))
    (hF₂ : ∀ a ∈ k, DifferentiableOn 𝕜 (fun x ↦ F x a) u)
    (hF₃ : ContinuousOn (fun x ↦ fderiv 𝕜 (fun y ↦ F y x.2) x.1) (u ×ˢ k)) :
    HasFDerivAt (fun x => ∫ a in s, F x a ∂μ)
      (∫ a in s, fderiv 𝕜 (fun x ↦ F x a) x₀ ∂μ) x₀ := by
  have : μ.restrict (k ∩ toMeasurable μ s) = μ.restrict s :=
    Measure.restrict_inter_toMeasurable hs' hk.measurableSet hsk
  simp only [← this]
  apply hasFDerivAt_integral_of_continuousOn_fderiv hu hk
    (hk.measurableSet.inter (measurableSet_toMeasurable _ _)) ?_ inter_subset_left hF₁ hF₂ hF₃
  apply ((measure_mono inter_subset_right).trans_lt ?_).ne
  rw [measure_toMeasurable]
  exact hs'.lt_top

/-- A convenient special case of `hasFDerivAt_integral_of_continuousOn_fderiv`:
if `f.uncurry : H × H' → E` is continuously differentiable on `u ×ˢ k` for a neighbourhood `u`
of `x₀` and a compact set `k`, then for any finite-measure set `s ⊆ k` a derivative of
`fun x => ∫ a in s, f x a ∂μ` in `x₀` can be computed as
`∫ a in s, fderiv 𝕜 (fun x ↦ f x a) x₀ ∂μ`. -/
theorem hasFDerivAt_integral_of_contDiffOn {μ : Measure H'} {f : H → H' → E} {x₀ : H}
    {u : Set H} (hu : u ∈ 𝓝 x₀) {k s : Set H'}
    (hk : IsCompact k) (hs' : μ s ≠ ⊤) (hsk : s ⊆ k)
    (hF : ContDiffOn 𝕜 1 f.uncurry (u ×ˢ k)) :
    HasFDerivAt (fun x => ∫ a in s, f x a ∂μ) (∫ a in s, fderiv 𝕜 (fun x ↦ f x a) x₀ ∂μ) x₀ := by
  wlog hu' : IsOpen u with h
  · have ⟨u', hu'⟩ := _root_.mem_nhds_iff.1 hu
    exact h (hu'.2.1.mem_nhds hu'.2.2) hk hs' hsk (hF.mono <| prod_mono_left hu'.1) hu'.2.1
  refine hasFDerivAt_integral_of_continuousOn_fderiv_of_t2Space hu hk hs' hsk hF.continuousOn
    (fun a ha ↦ hF.differentiableOn_one.comp (by fun_prop)
      fun x hx ↦ (⟨hx, ha⟩ : (x, a) ∈ _ ×ˢ _)) ?_
  intro x hx
  rcases contDiffWithinAt_nat.1 (hF x hx) with ⟨w, hw, p, hp⟩
  rw [insert_eq_of_mem hx] at hw
  obtain ⟨o, o', o_open, xoo', oo'w, hoo'w⟩ :
      ∃ o p, IsOpen o ∧ x ∈ o ×ˢ p ∧ o ×ˢ p ⊆ w ∧ o ×ˢ p ∈ 𝓝[u ×ˢ k] x := by
    obtain ⟨w', w'_open, xw', hw'⟩ : ∃ w', IsOpen w' ∧ x ∈ w' ∧ w' ∩ u ×ˢ k ⊆ w :=
      mem_nhdsWithin.1 hw
    obtain ⟨o, p, o_open, p_open, xo, xp, opw'⟩ : ∃ o p, IsOpen o ∧ IsOpen p ∧ x.1 ∈ o ∧ x.2 ∈ p
      ∧ o ×ˢ p ⊆ w' :=  isOpen_prod_iff.1 w'_open x.1 x.2 xw'
    refine ⟨o ∩ u, p ∩ k, o_open.inter hu', by grind, by grind, ?_⟩
    exact mem_nhdsWithin.2 ⟨o ×ˢ p, o_open.prod p_open, ⟨xo, xp⟩, by grind⟩
  apply ContinuousWithinAt.mono_of_mem_nhdsWithin _ hoo'w
  have : EqOn (fun (x : H × H') ↦ fderiv 𝕜 (fun y ↦ f y x.2) x.1)
      (fun x ↦ (continuousMultilinearCurryFin1 𝕜 (H × H') E (p x 1)) ∘L (.inl 𝕜 H H'))
      (o ×ˢ o') := by
    intro y hy
    apply (HasFDerivWithinAt.hasFDerivAt ?_ (o_open.mem_nhds hy.1)).fderiv
    apply (hp.hasFDerivWithinAt (x := y) one_ne_zero (oo'w hy)).comp (f := fun z ↦ (z, y.2))
    · exact (hasFDerivAt_prodMk_left y.1 y.2).hasFDerivWithinAt
    · intro z hz
      exact oo'w ⟨hz, hy.2⟩
  apply ContinuousWithinAt.congr_of_mem ?_ this xoo'
  have := (hp.cont 1 le_rfl).mono oo'w x xoo'
  fun_prop

/-- Iterated differentiation under integral of `x ↦ ∫ F x a` on an open set `s`, assuming that each
function `x ↦ F x a` has a Taylor series of order `n`, with uniform integrability conditions on
the successive derivatives. -/
theorem hasFTaylorSeriesOn_integral_of_le_bound {n : WithTop ℕ∞} {bound : ℕ → α → ℝ}
    {p : H → α → FormalMultilinearSeries 𝕜 H E} (hs : IsOpen s)
    (hF_meas : ∀ x ∈ s, ∀ (i : ℕ), i ≤ n → AEStronglyMeasurable (p x · i) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ∀ (i : ℕ), i ≤ n → ‖p x a i‖ ≤ bound i a)
    (bound_integrable : ∀ (i : ℕ), i ≤ n → Integrable (bound i) μ)
    (h_diff : ∀ᵐ a ∂μ, HasFTaylorSeriesUpToOn n (F · a) (p · a) s) :
    HasFTaylorSeriesUpToOn n (fun x ↦ ∫ a, F x a ∂μ) (fun x i ↦ ∫ a, p x a i ∂μ) s := by
  constructor
  · intro x hx
    simp only [ContinuousMultilinearMap.curry0_apply, Matrix.zero_empty]
    rw [ContinuousMultilinearMap.integral_apply]
    · apply integral_congr_ae
      filter_upwards [h_diff] with a ha
      simp [← ha.zero_eq x hx]
    · apply Integrable.mono' (bound_integrable 0 (by simp)) (hF_meas x hx 0 (by simp))
      filter_upwards [h_bound] with a ha using ha x hx 0 (by simp)
  · intro i hi x hx
    have h'i : (i + 1 : ℕ) ≤ n := ENat.add_one_natCast_le_withTop_of_lt hi
    apply HasFDerivAt.hasFDerivWithinAt
    change HasFDerivAt (fun x ↦ ∫ a, p x a i ∂μ)
      ((continuousMultilinearCurryLeftEquiv 𝕜 (fun i ↦ H) E).toContinuousLinearEquiv
        (∫ a, p x a i.succ ∂μ)) x
    -- next line should not be necessary...
    let A : NormedSpace ℝ (H →L[𝕜] (H [×i]→L[𝕜] E)) := ContinuousLinearMap.toNormedSpace
    rw [← ContinuousLinearEquiv.integral_comp_comm]
    have s_mem : s ∈ 𝓝 x := hs.mem_nhds hx
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := s) (bound := bound (i + 1)) s_mem
    · filter_upwards [s_mem] with y hy using hF_meas _ hy _ hi.le
    · apply Integrable.mono' (bound_integrable i hi.le) (hF_meas _ hx _ hi.le)
      filter_upwards [h_bound] with a ha using ha x hx i hi.le
    · apply Continuous.comp_aestronglyMeasurable (by fun_prop)
      exact hF_meas x hx i.succ h'i
    · filter_upwards [h_bound] with a ha y hy
      simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.norm_map]
      exact ha _ hy _ h'i
    · apply bound_integrable _ h'i
    · filter_upwards [h_diff] with a ha y hy
      exact (ha.fderivWithin i hi y hy).hasFDerivAt (hs.mem_nhds hy)
  · intro i hi
    apply continuousOn_of_dominated (bound := bound i)
    · intro y hy
      exact hF_meas y hy i hi
    · intro y hy
      filter_upwards [h_bound] with a ha using ha y hy i hi
    · apply bound_integrable i hi
    · filter_upwards [h_diff] with a ha using ha.cont i hi

open ContinuousMultilinearMap in
theorem hasFTaylorSeriesOn_setIntegral_of_le_const
    {n : WithTop ℕ∞} {C : ℕ → ℝ} {μ : Measure H'}
    {p : H × H' → FormalMultilinearSeries 𝕜 (H × H') E} (hs : IsOpen s)
    {t : Set H'} {F : H → H' → E} (ht : IsSeparable t) (tmeas : MeasurableSet t) (hmut : μ t ≠ ⊤)
    (hF : HasFTaylorSeriesUpToOn n F.uncurry p (s ×ˢ t))
    (h_bound : ∀ x ∈ s, ∀ a ∈ t, ∀ (i : ℕ), i ≤ n → ‖p (x, a) i‖ ≤ C i) :
    HasFTaylorSeriesUpToOn n (fun x ↦ ∫ a in t, F x a ∂μ)
      (fun x i ↦ ∫ a in t, (p (x, a) i).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inl 𝕜 H H') ∂μ) s := by
  apply hasFTaylorSeriesOn_integral_of_le_bound hs (bound := fun i a ↦ C i * ∏ (j : Fin i), 1)
  · intro x hx i hi
    apply ContinuousOn.aestronglyMeasurable_of_isSeparable ?_ tmeas ht
    apply Continuous.comp_continuousOn (g := compContinuousLinearMapL _) (by fun_prop)
      (f := fun y ↦ p (x, y) i)
    apply (hF.cont i hi).comp (by fun_prop)
    intro w hw
    exact ⟨hx, hw⟩
  · apply ae_restrict_of_forall_mem tmeas (fun w hw ↦ ?_)
    intro x hx i hi
    apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
    have : ‖p (x, w) i‖ ≤ C i := h_bound x hx w hw i hi
    gcongr
    · exact le_trans (by positivity) this
    · exact ContinuousLinearMap.norm_inl_le_one 𝕜 H H'
  · intro i hi
    exact integrableOn_const hmut
  · apply ae_restrict_of_forall_mem tmeas (fun w hw ↦ ?_)
    let g : H →ᴬ[𝕜] H × H' :=
    { toFun := fun x ↦ (x, w)
      linear := LinearMap.inl 𝕜 H H'
      map_vadd' p v := by simp
      cont := by fun_prop }
    apply (hF.comp_continuousAffineMap g).mono
    simp only [ContinuousAffineMap.coe_mk, AffineMap.coe_mk, g]
    grind

open ContinuousMultilinearMap in
/-- If `f.uncurry : H × H' → E` is `Cⁿ` on `u ×ˢ k` for an open set `u` and a compact set `k`, then
given any finite-measure subset `s₀` of `k` the parametric integral `fun x ↦ ∫ a in s₀, f x a ∂μ`
is `Cⁿ` on `u` too. -/
lemma ContDiffOn.parametric_integral
    {μ : Measure H'} {f : H → H' → E} {u : Set H} (hu : IsOpen u)
    {s₀ k : Set H'} (hk : IsCompact k) {n : ℕ∞} (hs₀ : s₀ ⊆ k)
    (hf : ContDiffOn 𝕜 n f.uncurry (u ×ˢ k)) (mus₀ : μ s₀ ≠ ⊤) :
    ContDiffOn 𝕜 n (fun x ↦ ∫ a in s₀, f x a ∂μ) u := by
  /- Locally, this is already proved in `hasFTaylorSeriesOn_setIntegral_of_le_const` (which moreover
  gives a formula for the successive derivatives). To globalize, one covers the compact set `k`
  with finitely many sets on which the local property golds. Technically, this is more conveniently
  done using the induction principle `IsCompact.induction_on` in which one only needs to check
  the property locally, and invariance under binary union. -/
  intro x hx
  apply contDiffWithinAt_iff_forall_nat_le.2 (fun m hm ↦ ?_)
  suffices ∃ s, k ∩ k ⊆ s ∧ s ⊆ k ∧ MeasurableSet s ∧ ∀ t ⊆ s, MeasurableSet t → μ t ≠ ⊤ →
      ContDiffWithinAt 𝕜 m (fun x ↦ ∫ a in t, f x a ∂μ) u x by
    rcases this with ⟨s, ks, sk, -, hs⟩
    rw [show s = k by grind] at hs
    have : ContDiffWithinAt 𝕜 m (fun x ↦ ∫ a in k ∩ toMeasurable μ s₀, f x a ∂μ) u x := by
      apply hs _ inter_subset_left (hk.measurableSet.inter (measurableSet_toMeasurable _ _))
      apply ((measure_mono inter_subset_right).trans_lt ?_).ne
      rw [measure_toMeasurable]
      exact mus₀.lt_top
    convert this using 3
    exact (Measure.restrict_inter_toMeasurable mus₀ hk.measurableSet hs₀).symm
  apply IsCompact.induction_on (s := k)
    (p := fun s₀ ↦ ∃ s, k ∩ s₀ ⊆ s ∧ s ⊆ k ∧ MeasurableSet s ∧ ∀ t ⊆ s, MeasurableSet t →
      μ t ≠ ⊤ → ContDiffWithinAt 𝕜 m (fun x ↦ ∫ a in t, f x a ∂μ) u x) hk
  · simp only [inter_empty, empty_subset, true_and]
    exact ⟨∅, by simpa using contDiffWithinAt_const⟩
  · grind
  · -- check invariance of the property under binary union
    rintro s s' ⟨t, kt, tk, tmeas, ht⟩ ⟨t', kt', t'k, t'meas, ht'⟩
    refine ⟨t ∪ t', by grind, by grind, tmeas.union t'meas, fun v hv vmeas muv ↦ ?_⟩
    let v₁ := v ∩ t
    let v₂ := v \ v₁
    have v₁meas : MeasurableSet v₁ := vmeas.inter tmeas
    have v₂meas : MeasurableSet v₂ := vmeas.diff v₁meas
    have muv₁ : μ v₁ ≠ ⊤ := ((measure_mono inter_subset_left).trans_lt muv.lt_top).ne
    have muv₂ : μ v₂ ≠ ⊤ := ((measure_mono diff_subset).trans_lt muv.lt_top).ne
    have : ContDiffWithinAt 𝕜 m (fun x ↦ ∫ a in v₁, f x a ∂μ + ∫ a in v₂, f x a ∂μ) u x :=
      (ht v₁ inter_subset_right v₁meas muv₁).add (ht' v₂ (by grind) v₂meas muv₂)
    apply this.congr_of_mem (fun y hy ↦ ?_) hx
    rw [show v = v₁ ∪ v₂ by grind, setIntegral_union disjoint_sdiff_left.symm v₂meas]
    · exact (hf.continuousOn.uncurry_left _ hy).integrableOn_of_subset_isCompact
        hk v₁meas (inter_subset_right.trans tk) muv₁
    · exact (hf.continuousOn.uncurry_left _ hy).integrableOn_of_subset_isCompact
        hk v₂meas (by grind only [= subset_def, = mem_diff, = mem_union]) muv₂
  -- check the property locally using `hasFTaylorSeriesOn_setIntegral_of_le_const`
  intro y hy
  obtain ⟨v, v_mem, p, hp⟩ : ∃ v ∈ 𝓝[insert (x, y) (u ×ˢ k)] (x, y), ∃ p,
    HasFTaylorSeriesUpToOn m (Function.uncurry f) p v := hf (x, y) ⟨hx, hy⟩ m hm
  obtain ⟨u', u'_mem, k', k'_mem, u'_open,  k'meas, k'k, hk'v, hk'_bound⟩ :
      ∃ u' ∈ 𝓝 x, ∃ k' ∈ 𝓝[k] y, IsOpen u' ∧ MeasurableSet k' ∧ k' ⊆ k ∧ u' ×ˢ k' ⊆ v
      ∧ ∀ N ≤ m, ∀ z ∈ u' ×ˢ k', ‖p z N‖ < 1 + ‖p (x, y) N‖ := by
    rw [show insert (x, y) (u ×ˢ k) = u ×ˢ k from insert_eq_of_mem (by exact ⟨hx, hy⟩)] at v_mem
    let v'' := ⋂ N ∈ Finset.Iic m, {z | ‖p z N‖ < 1 + ‖p (x, y) N‖}
    have : v'' ∈ 𝓝[u ×ˢ k] (x, y) := by
      apply (Filter.biInter_finset_mem _).2 (fun i hi ↦ ?_)
      apply nhdsWithin_le_of_mem v_mem
      have xyv : (x, y) ∈ v := mem_of_mem_nhdsWithin (by exact ⟨hx, hy⟩) v_mem
      have : ContinuousWithinAt (fun z ↦ ‖p z i‖) v (x, y) :=
        (hp.cont i (by simpa using hi) (x, y) xyv).norm
      exact this.preimage_mem_nhdsWithin (Iio_mem_nhds (by linarith))
    have v'_mem : v ∩ v'' ∈ 𝓝[u ×ˢ k] (x, y) := by
      apply Filter.inter_mem v_mem this
    rw [nhdsWithin_prod_eq, Filter.mem_prod_iff, IsOpen.nhdsWithin_eq hu hx] at v'_mem
    rcases v'_mem with ⟨u', u'_mem, t', t'_mem, ht'⟩
    rw [mem_nhdsWithin] at t'_mem
    rcases t'_mem with ⟨t'', t''_open, t''_mem, ht''⟩
    rcases _root_.mem_nhds_iff.1 u'_mem with ⟨u'', hu'', u''_open, xu''⟩
    refine ⟨u'', u''_open.mem_nhds xu'', t'' ∩ k, ?_, u''_open,
      t''_open.measurableSet.inter hk.measurableSet, inter_subset_right, ?_, ?_⟩
    · rw [inter_comm]
      exact inter_mem_nhdsWithin _ (t''_open.mem_nhds t''_mem)
    · exact Subset.trans (by gcongr) (ht'.trans inter_subset_left)
    · intro i hi z z_mem
      have : z ∈ v'' := by
        have : u'' ×ˢ (t'' ∩ k) ⊆ v'' := Subset.trans (by gcongr) (ht'.trans inter_subset_right)
        exact this z_mem
      simp only [Finset.mem_Iic, mem_iInter, mem_setOf_eq, v''] at this
      exact this i hi
  refine ⟨k', k'_mem, k', inter_subset_right, k'k, k'meas, fun t tk' tmeas hmut ↦ ?_⟩
  have : HasFTaylorSeriesUpToOn m (fun x ↦ ∫ a in t, f x a ∂μ)
      (fun x i ↦ ∫ a in t, (p (x, a) i).compContinuousLinearMap
        (fun _ ↦ ContinuousLinearMap.inl 𝕜 H H') ∂μ) u' := by
    apply hasFTaylorSeriesOn_setIntegral_of_le_const u'_open (hk.isSeparable.mono (tk'.trans k'k))
      tmeas hmut (hp.mono (by grind)) (C := fun i ↦ 1 + ‖p (x, y) i‖)
    intro x' hx' a ha i hi
    exact (hk'_bound i (mod_cast hi) (x', a) ⟨hx', tk' ha⟩).le
  apply ContDiffWithinAt.mono_of_mem_nhdsWithin ?_ (nhdsWithin_le_nhds u'_mem)
  exact contDiffWithinAt_nat.2 ⟨u', nhdsWithin_le_nhds u'_mem, _, this⟩

/-- If `f.uncurry : H × H' → E` is `Cⁿ`, the parametric integral `fun x ↦ ∫ a in s₀, f x a ∂μ`
over a finite-measure set `s₀` contained in a compact set `k` is `Cⁿ` too. -/
lemma ContDiff.parametric_integral {μ : Measure H'} {f : H → H' → E}
    {k s₀ : Set H'} (hk : IsCompact k) (hs₀ : s₀ ⊆ k) (mus₀ : μ s₀ ≠ ⊤) {n : ℕ∞}
    (hf : ContDiff 𝕜 n f.uncurry) :
    ContDiff 𝕜 n (fun x ↦ ∫ a in s₀, f x a ∂μ) :=
  contDiffOn_univ.1 <| hf.contDiffOn.parametric_integral isOpen_univ hk hs₀ mus₀

section

variable {F : 𝕜 → α → E} {x₀ : 𝕜} {s : Set 𝕜}

/-- Derivative under integral of `x ↦ ∫ F x a` at a given point `x₀ : 𝕜`, `𝕜 = ℝ` or `𝕜 = ℂ`,
assuming `F x₀` is integrable, `x ↦ F x a` is locally Lipschitz on a neighborhood of `x₀` for ae `a`
(with a neighborhood independent of `a`) with integrable Lipschitz bound, and `F x` is
ae-measurable for `x` in a possibly smaller neighborhood of `x₀`. -/
theorem hasDerivAt_integral_of_dominated_loc_of_lip {F' : α → E} (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    (hF'_meas : AEStronglyMeasurable F' μ)
    (h_lipsch : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs <| bound a) (F · a) s)
    (bound_integrable : Integrable (bound : α → ℝ) μ)
    (h_diff : ∀ᵐ a ∂μ, HasDerivAt (F · a) (F' a) x₀) :
    Integrable F' μ ∧ HasDerivAt (fun x ↦ ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) x₀ := by
  set L : E →L[𝕜] 𝕜 →L[𝕜] E := ContinuousLinearMap.smulRightL 𝕜 𝕜 E 1
  replace h_diff : ∀ᵐ a ∂μ, HasFDerivAt (F · a) (L (F' a)) x₀ :=
    h_diff.mono fun x hx ↦ hx.hasFDerivAt
  have hm : AEStronglyMeasurable (L ∘ F') μ := L.continuous.comp_aestronglyMeasurable hF'_meas
  obtain ⟨hF'_int, key⟩ := hasFDerivAt_integral_of_dominated_loc_of_lip
    hs hF_meas hF_int hm h_lipsch bound_integrable h_diff
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
theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le (hs : s ∈ 𝓝 x₀)
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) μ) (hF_int : Integrable (F x₀) μ)
    {F' : 𝕜 → α → E} (hF'_meas : AEStronglyMeasurable (F' x₀) μ)
    (h_bound : ∀ᵐ a ∂μ, ∀ x ∈ s, ‖F' x a‖ ≤ bound a) (bound_integrable : Integrable bound μ)
    (h_diff : ∀ᵐ a ∂μ, ∀ x ∈ s, HasDerivAt (F · a) (F' x a) x) :
    Integrable (F' x₀) μ ∧ HasDerivAt (fun n ↦ ∫ a, F n a ∂μ) (∫ a, F' x₀ a ∂μ) x₀ := by
  rcases Metric.mem_nhds_iff.1 hs with ⟨ε, ε_pos, hε⟩
  have x₀_in : x₀ ∈ ball x₀ ε := mem_ball_self ε_pos
  have diff_x₀ : ∀ᵐ a ∂μ, HasDerivAt (F · a) (F' x₀ a) x₀ :=
    h_diff.mono fun a ha ↦ ha x₀ (hε x₀_in)
  have : ∀ᵐ a ∂μ, LipschitzOnWith (Real.nnabs (bound a)) (fun x : 𝕜 ↦ F x a) (ball x₀ ε) := by
    apply (h_diff.and h_bound).mono
    rintro a ⟨ha_deriv, ha_bound⟩
    refine (convex_ball _ _).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x x_in ↦ (ha_deriv x (hε x_in)).hasDerivWithinAt) fun x x_in ↦ ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs]
    exact (ha_bound x (hε x_in)).trans (le_abs_self _)
  exact hasDerivAt_integral_of_dominated_loc_of_lip (ball_mem_nhds x₀ ε_pos) hF_meas hF_int
    hF'_meas this bound_integrable diff_x₀

end
