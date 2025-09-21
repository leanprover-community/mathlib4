/-
Copyright (c) 2023 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-!
# Rademacher's theorem: a Lipschitz function is differentiable almost everywhere

This file proves Rademacher's theorem: a Lipschitz function between finite-dimensional real vector
spaces is differentiable almost everywhere with respect to the Lebesgue measure. This is the content
of `LipschitzWith.ae_differentiableAt`. Versions for functions which are Lipschitz on sets are also
given (see `LipschitzOnWith.ae_differentiableWithinAt`).

## Implementation

There are many proofs of Rademacher's theorem. We follow the one by Morrey, which is not the most
elementary but maybe the most elegant once necessary prerequisites are set up.
* Step 0: without loss of generality, one may assume that `f` is real-valued.
* Step 1: Since a one-dimensional Lipschitz function has bounded variation, it is differentiable
  almost everywhere. With a Fubini argument, it follows that given any vector `v` then `f` is ae
  differentiable in the direction of `v`. See `LipschitzWith.ae_lineDifferentiableAt`.
* Step 2: the line derivative `LineDeriv ℝ f x v` is ae linear in `v`. Morrey proves this by a
  duality argument, integrating against a smooth compactly supported function `g`, passing the
  derivative to `g` by integration by parts, and using the linearity of the derivative of `g`.
  See `LipschitzWith.ae_lineDeriv_sum_eq`.
* Step 3: consider a countable dense set `s` of directions. Almost everywhere, the function `f`
  is line-differentiable in all these directions and the line derivative is linear. Approximating
  any direction by a direction in `s` and using the fact that `f` is Lipschitz to control the error,
  it follows that `f` is Fréchet-differentiable at these points.
  See `LipschitzWith.hasFDerivAt_of_hasLineDerivAt_of_closure`.

## References

* [Pertti Mattila, Geometry of sets and measures in Euclidean spaces, Theorem 7.3][Federer1996]
-/

open Filter MeasureTheory Measure Module Metric Set Asymptotics

open scoped NNReal ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {C D : ℝ≥0} {f g : E → ℝ} {s : Set E}
  {μ : Measure E}

namespace LipschitzWith

/-!
### Step 1: A Lipschitz function is ae differentiable in any given direction

This follows from the one-dimensional result that a Lipschitz function on `ℝ` has bounded
variation, and is therefore ae differentiable, together with a Fubini argument.
-/


theorem memLp_lineDeriv (hf : LipschitzWith C f) (v : E) :
    MemLp (fun x ↦ lineDeriv ℝ f x v) ∞ μ :=
  memLp_top_of_bound (aestronglyMeasurable_lineDeriv hf.continuous μ)
    (C * ‖v‖) (.of_forall fun _x ↦ norm_lineDeriv_le_of_lipschitz ℝ hf)

variable [FiniteDimensional ℝ E] [IsAddHaarMeasure μ]

theorem ae_lineDifferentiableAt
    (hf : LipschitzWith C f) (v : E) :
    ∀ᵐ p ∂μ, LineDifferentiableAt ℝ f p v := by
  let L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v
  suffices A : ∀ p, ∀ᵐ (t : ℝ) ∂volume, LineDifferentiableAt ℝ f (p + t • v) v from
    ae_mem_of_ae_add_linearMap_mem L.toLinearMap volume μ
      (measurableSet_lineDifferentiableAt hf.continuous) A
  intro p
  have : ∀ᵐ (s : ℝ), DifferentiableAt ℝ (fun t ↦ f (p + t • v)) s :=
    (hf.comp ((LipschitzWith.const p).add L.lipschitz)).ae_differentiableAt_real
  filter_upwards [this] with s hs
  have h's : DifferentiableAt ℝ (fun t ↦ f (p + t • v)) (s + 0) := by simpa using hs
  have : DifferentiableAt ℝ (fun t ↦ s + t) 0 := differentiableAt_id.const_add _
  simp only [LineDifferentiableAt]
  convert h's.comp 0 this with _ t
  simp only [add_assoc, Function.comp_apply, add_smul]

theorem locallyIntegrable_lineDeriv (hf : LipschitzWith C f) (v : E) :
    LocallyIntegrable (fun x ↦ lineDeriv ℝ f x v) μ :=
  (hf.memLp_lineDeriv v).locallyIntegrable le_top

/-!
### Step 2: the ae line derivative is linear

Surprisingly, this is the hardest step. We prove it using an elegant but slightly sophisticated
argument by Morrey, with a distributional flavor: we integrate against a smooth function, and push
the derivative to the smooth function by integration by parts. As the derivative of a smooth
function is linear, this gives the result.
-/

theorem integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul
    (hf : LipschitzWith C f) (hg : Integrable g μ) (v : E) :
    Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, lineDeriv ℝ f x v * g x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ (C * ‖v‖) * ‖g x‖)
  · filter_upwards with t
    apply AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
    apply aestronglyMeasurable_const.smul
    apply AEStronglyMeasurable.sub _ hf.continuous.measurable.aestronglyMeasurable
    apply AEMeasurable.aestronglyMeasurable
    exact hf.continuous.measurable.comp_aemeasurable' (aemeasurable_id'.add_const _)
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    filter_upwards with x
    calc ‖t⁻¹ • (f (x + t • v) - f x) * g x‖
      = (t⁻¹ * ‖f (x + t • v) - f x‖) * ‖g x‖ := by simp [norm_mul, ht.le]
    _ ≤ (t⁻¹ * (C * ‖(x + t • v) - x‖)) * ‖g x‖ := by
      gcongr; exact LipschitzWith.norm_sub_le hf (x + t • v) x
    _ = (C * ‖v‖) *‖g x‖ := by simp [field, norm_smul, abs_of_nonneg ht.le]
  · exact hg.norm.const_mul _
  · filter_upwards [hf.ae_lineDifferentiableAt v] with x hx
    exact hx.hasLineDerivAt.tendsto_slope_zero_right.mul tendsto_const_nhds

theorem integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'
    (hf : LipschitzWith C f) (h'f : HasCompactSupport f) (hg : Continuous g) (v : E) :
    Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, lineDeriv ℝ f x v * g x ∂μ)) := by
  let K := cthickening (‖v‖) (tsupport f)
  have K_compact : IsCompact K := IsCompact.cthickening h'f
  apply tendsto_integral_filter_of_dominated_convergence
      (K.indicator (fun x ↦ (C * ‖v‖) * ‖g x‖))
  · filter_upwards with t
    apply AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
    apply aestronglyMeasurable_const.smul
    apply AEStronglyMeasurable.sub _ hf.continuous.measurable.aestronglyMeasurable
    apply AEMeasurable.aestronglyMeasurable
    exact hf.continuous.measurable.comp_aemeasurable' (aemeasurable_id'.add_const _)
  · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    have t_pos : 0 < t := ht.1
    filter_upwards with x
    by_cases hx : x ∈ K
    · calc ‖t⁻¹ • (f (x + t • v) - f x) * g x‖
        = (t⁻¹ * ‖f (x + t • v) - f x‖) * ‖g x‖ := by simp [norm_mul, t_pos.le]
      _ ≤ (t⁻¹ * (C * ‖(x + t • v) - x‖)) * ‖g x‖ := by
        gcongr; exact LipschitzWith.norm_sub_le hf (x + t • v) x
      _ = (C * ‖v‖) *‖g x‖ := by simp [field, norm_smul, abs_of_nonneg t_pos.le]
      _ = K.indicator (fun x ↦ (C * ‖v‖) * ‖g x‖) x := by rw [indicator_of_mem hx]
    · have A : f x = 0 := by
        rw [← Function.notMem_support]
        contrapose! hx
        exact self_subset_cthickening _ (subset_tsupport _ hx)
      have B : f (x + t • v) = 0 := by
        rw [← Function.notMem_support]
        contrapose! hx
        apply mem_cthickening_of_dist_le _ _ (‖v‖) (tsupport f) (subset_tsupport _ hx)
        simp only [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg t_pos.le]
        exact mul_le_of_le_one_left (norm_nonneg v) ht.2
      simp only [B, A, _root_.sub_self, smul_eq_mul, mul_zero, zero_mul, norm_zero]
      exact indicator_nonneg (fun y _hy ↦ by positivity) _
  · rw [integrable_indicator_iff K_compact.measurableSet]
    apply ContinuousOn.integrableOn_compact K_compact
    exact (Continuous.mul continuous_const hg.norm).continuousOn
  · filter_upwards [hf.ae_lineDifferentiableAt v] with x hx
    exact hx.hasLineDerivAt.tendsto_slope_zero_right.mul tendsto_const_nhds

/-- Integration by parts formula for the line derivative of Lipschitz functions, assuming one of
them is compactly supported. -/
theorem integral_lineDeriv_mul_eq
    (hf : LipschitzWith C f) (hg : LipschitzWith D g) (h'g : HasCompactSupport g) (v : E) :
    ∫ x, lineDeriv ℝ f x v * g x ∂μ = ∫ x, lineDeriv ℝ g x (-v) * f x ∂μ := by
  /- Write down the line derivative as the limit of `(f (x + t v) - f x) / t` and
  `(g (x - t v) - g x) / t`, and therefore the integrals as limits of the corresponding integrals
  thanks to the dominated convergence theorem. At fixed positive `t`, the integrals coincide
  (with the change of variables `y = x + t v`), so the limits also coincide. -/
  have A : Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
              (𝓝 (∫ x, lineDeriv ℝ f x v * g x ∂μ)) :=
    integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul
      hf (hg.continuous.integrable_of_hasCompactSupport h'g) v
  have B : Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (g (x + t • (-v)) - g x)) * f x ∂μ) (𝓝[>] 0)
              (𝓝 (∫ x, lineDeriv ℝ g x (-v) * f x ∂μ)) :=
    integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul' hg h'g hf.continuous (-v)
  suffices S1 : ∀ (t : ℝ), ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ =
                            ∫ x, (t⁻¹ • (g (x + t • (-v)) - g x)) * f x ∂μ by
    simp only [S1] at A; exact tendsto_nhds_unique A B
  intro t
  suffices S2 : ∫ x, (f (x + t • v) - f x) * g x ∂μ = ∫ x, f x * (g (x + t • (-v)) - g x) ∂μ by
    simp only [smul_eq_mul, mul_assoc, integral_const_mul, S2, mul_comm (f _)]
  have S3 : ∫ x, f (x + t • v) * g x ∂μ = ∫ x, f x * g (x + t • (-v)) ∂μ := by
    rw [← integral_add_right_eq_self _ (t • (-v))]; simp
  simp_rw [_root_.sub_mul, _root_.mul_sub]
  rw [integral_sub, integral_sub, S3]
  · apply Continuous.integrable_of_hasCompactSupport
    · exact hf.continuous.mul (hg.continuous.comp (continuous_add_right _))
    · exact (h'g.comp_homeomorph (Homeomorph.addRight (t • (-v)))).mul_left
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport h'g.mul_left
  · apply Continuous.integrable_of_hasCompactSupport
    · exact (hf.continuous.comp (continuous_add_right _)).mul hg.continuous
    · exact h'g.mul_left
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport h'g.mul_left

/-- The line derivative of a Lipschitz function is almost everywhere linear with respect to fixed
coefficients. -/
theorem ae_lineDeriv_sum_eq
    (hf : LipschitzWith C f) {ι : Type*} (s : Finset ι) (a : ι → ℝ) (v : ι → E) :
    ∀ᵐ x ∂μ, lineDeriv ℝ f x (∑ i ∈ s, a i • v i) = ∑ i ∈ s, a i • lineDeriv ℝ f x (v i) := by
  /- Clever argument by Morrey: integrate against a smooth compactly supported function `g`, switch
  the derivative to `g` by integration by parts, and use the linearity of the derivative of `g` to
  conclude that the initial integrals coincide. -/
  apply ae_eq_of_integral_contDiff_smul_eq (hf.locallyIntegrable_lineDeriv _)
    (locallyIntegrable_finset_sum _ (fun i hi ↦ (hf.locallyIntegrable_lineDeriv (v i)).smul (a i)))
    (fun g g_smooth g_comp ↦ ?_)
  simp_rw [Finset.smul_sum]
  have A : ∀ i ∈ s, Integrable (fun x ↦ g x • (a i • fun x ↦ lineDeriv ℝ f x (v i)) x) μ :=
    fun i hi ↦ (g_smooth.continuous.integrable_of_hasCompactSupport g_comp).smul_of_top_left
      ((hf.memLp_lineDeriv (v i)).const_smul (a i))
  rw [integral_finset_sum _ A]
  suffices S1 : ∫ x, lineDeriv ℝ f x (∑ i ∈ s, a i • v i) * g x ∂μ
      = ∑ i ∈ s, a i * ∫ x, lineDeriv ℝ f x (v i) * g x ∂μ by
    dsimp only [smul_eq_mul, Pi.smul_apply]
    simp_rw [← mul_assoc, mul_comm _ (a _), mul_assoc, integral_const_mul, mul_comm (g _), S1]
  suffices S2 : ∫ x, (∑ i ∈ s, a i * fderiv ℝ g x (v i)) * f x ∂μ =
                  ∑ i ∈ s, a i * ∫ x, fderiv ℝ g x (v i) * f x ∂μ by
    obtain ⟨D, g_lip⟩ : ∃ D, LipschitzWith D g :=
      ContDiff.lipschitzWith_of_hasCompactSupport g_comp g_smooth (mod_cast le_top)
    simp_rw [integral_lineDeriv_mul_eq hf g_lip g_comp]
    simp_rw [(g_smooth.differentiable (mod_cast le_top)).differentiableAt.lineDeriv_eq_fderiv]
    simp only [map_neg, _root_.map_sum, map_smul, smul_eq_mul, neg_mul]
    simp only [integral_neg, mul_neg, Finset.sum_neg_distrib, neg_inj]
    exact S2
  suffices B : ∀ i ∈ s, Integrable (fun x ↦ a i * (fderiv ℝ g x (v i) * f x)) μ by
    simp_rw [Finset.sum_mul, mul_assoc, integral_finset_sum s B, integral_const_mul]
  intro i _hi
  let L : StrongDual ℝ E → ℝ := fun f ↦ f (v i)
  change Integrable (fun x ↦ a i * ((L ∘ (fderiv ℝ g)) x * f x)) μ
  refine (Continuous.integrable_of_hasCompactSupport ?_ ?_).const_mul _
  · exact ((g_smooth.continuous_fderiv (mod_cast le_top)).clm_apply continuous_const).mul
      hf.continuous
  · exact ((g_comp.fderiv ℝ).comp_left rfl).mul_right

/-!
### Step 3: construct the derivative using the line derivatives along a basis
-/

theorem ae_exists_fderiv_of_countable
    (hf : LipschitzWith C f) {s : Set E} (hs : s.Countable) :
    ∀ᵐ x ∂μ, ∃ (L : StrongDual ℝ E), ∀ v ∈ s, HasLineDerivAt ℝ f (L v) x v := by
  have B := Basis.ofVectorSpace ℝ E
  have I1 : ∀ᵐ (x : E) ∂μ, ∀ v ∈ s, lineDeriv ℝ f x (∑ i, (B.repr v i) • B i) =
                                  ∑ i, B.repr v i • lineDeriv ℝ f x (B i) :=
    (ae_ball_iff hs).2 (fun v _ ↦ hf.ae_lineDeriv_sum_eq _ _ _)
  have I2 : ∀ᵐ (x : E) ∂μ, ∀ v ∈ s, LineDifferentiableAt ℝ f x v :=
    (ae_ball_iff hs).2 (fun v _ ↦ hf.ae_lineDifferentiableAt v)
  filter_upwards [I1, I2] with x hx h'x
  let L : StrongDual ℝ E :=
    LinearMap.toContinuousLinearMap (B.constr ℝ (fun i ↦ lineDeriv ℝ f x (B i)))
  refine ⟨L, fun v hv ↦ ?_⟩
  have J : L v = lineDeriv ℝ f x v := by convert (hx v hv).symm <;> simp [L, B.sum_repr v]
  simpa [J] using (h'x v hv).hasLineDerivAt

omit [MeasurableSpace E] in
/-- If a Lipschitz functions has line derivatives in a dense set of directions, all of them given by
a single continuous linear map `L`, then it admits `L` as Fréchet derivative. -/
theorem hasFDerivAt_of_hasLineDerivAt_of_closure
    {f : E → F} (hf : LipschitzWith C f) {s : Set E} (hs : sphere 0 1 ⊆ closure s)
    {L : E →L[ℝ] F} {x : E} (hL : ∀ v ∈ s, HasLineDerivAt ℝ f (L v) x v) :
    HasFDerivAt f L x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
  intro ε εpos
  obtain ⟨δ, δpos, hδ⟩ : ∃ δ, 0 < δ ∧ (C + ‖L‖ + 1) * δ = ε :=
    ⟨ε / (C + ‖L‖ + 1), by positivity, mul_div_cancel₀ ε (by positivity)⟩
  obtain ⟨q, hqs, q_fin, hq⟩ : ∃ q, q ⊆ s ∧ q.Finite ∧ sphere 0 1 ⊆ ⋃ y ∈ q, ball y δ := by
    have : sphere 0 1 ⊆ ⋃ y ∈ s, ball y δ := by
      apply hs.trans (fun z hz ↦ ?_)
      obtain ⟨y, ys, hy⟩ : ∃ y ∈ s, dist z y < δ := Metric.mem_closure_iff.1 hz δ δpos
      exact mem_biUnion ys hy
    exact (isCompact_sphere 0 1).elim_finite_subcover_image (fun y _hy ↦ isOpen_ball) this
  have I : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ v ∈ q, ‖f (x + t • v) - f x - t • L v‖ ≤ δ * ‖t‖ := by
    apply (Finite.eventually_all q_fin).2 (fun v hv ↦ ?_)
    apply Asymptotics.IsLittleO.def ?_ δpos
    exact hasLineDerivAt_iff_isLittleO_nhds_zero.1 (hL v (hqs hv))
  obtain ⟨r, r_pos, hr⟩ : ∃ (r : ℝ), 0 < r ∧ ∀ (t : ℝ), ‖t‖ < r →
      ∀ v ∈ q, ‖f (x + t • v) - f x - t • L v‖ ≤ δ * ‖t‖ := by
    rcases Metric.mem_nhds_iff.1 I with ⟨r, r_pos, hr⟩
    exact ⟨r, r_pos, fun t ht v hv ↦ hr (mem_ball_zero_iff.2 ht) v hv⟩
  apply Metric.mem_nhds_iff.2 ⟨r, r_pos, fun v hv ↦ ?_⟩
  rcases eq_or_ne v 0 with rfl | v_ne
  · simp
  obtain ⟨w, ρ, w_mem, hvw, hρ⟩ : ∃ w ρ, w ∈ sphere 0 1 ∧ v = ρ • w ∧ ρ = ‖v‖ := by
    refine ⟨‖v‖⁻¹ • v, ‖v‖, by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 v_ne)], ?_, rfl⟩
    simp [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 v_ne)]
  have norm_rho : ‖ρ‖ = ρ := by rw [hρ, norm_norm]
  have rho_pos : 0 ≤ ρ := by simp [hρ]
  obtain ⟨y, yq, hy⟩ : ∃ y ∈ q, ‖w - y‖ < δ := by simpa [← dist_eq_norm] using hq w_mem
  have : ‖y - w‖ < δ := by rwa [norm_sub_rev]
  calc  ‖f (x + v) - f x - L v‖
      = ‖f (x + ρ • w) - f x - ρ • L w‖ := by simp [hvw]
    _ = ‖(f (x + ρ • w) - f (x + ρ • y)) + (ρ • L y - ρ • L w)
          + (f (x + ρ • y) - f x - ρ • L y)‖ := by congr; abel
    _ ≤ ‖f (x + ρ • w) - f (x + ρ • y)‖ + ‖ρ • L y - ρ • L w‖
          + ‖f (x + ρ • y) - f x - ρ • L y‖ := norm_add₃_le
    _ ≤ C * ‖(x + ρ • w) - (x + ρ • y)‖ + ρ * (‖L‖ * ‖y - w‖) + δ * ρ := by
      gcongr
      · exact hf.norm_sub_le _ _
      · rw [← smul_sub, norm_smul, norm_rho]
        gcongr
        exact L.lipschitz.norm_sub_le _ _
      · conv_rhs => rw [← norm_rho]
        apply hr _ _ _ yq
        simpa [norm_rho, hρ] using hv
    _ ≤ C * (ρ * δ) + ρ * (‖L‖ * δ) + δ * ρ := by
      simp only [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, norm_rho]; gcongr
    _ = ((C + ‖L‖ + 1) * δ) * ρ := by ring
    _ = ε * ‖v‖ := by rw [hδ, hρ]

/-- A real-valued function on a finite-dimensional space which is Lipschitz is
differentiable almost everywere. Superseded by
`LipschitzWith.ae_differentiableAt` which works for functions taking value in any
finite-dimensional space. -/
theorem ae_differentiableAt_of_real (hf : LipschitzWith C f) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x := by
  obtain ⟨s, s_count, s_dense⟩ : ∃ (s : Set E), s.Countable ∧ Dense s :=
    TopologicalSpace.exists_countable_dense E
  have hs : sphere 0 1 ⊆ closure s := by rw [s_dense.closure_eq]; exact subset_univ _
  filter_upwards [hf.ae_exists_fderiv_of_countable s_count]
  rintro x ⟨L, hL⟩
  exact (hf.hasFDerivAt_of_hasLineDerivAt_of_closure hs hL).differentiableAt

end LipschitzWith

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsAddHaarMeasure μ]

namespace LipschitzOnWith

/-- A real-valued function on a finite-dimensional space which is Lipschitz on a set is
differentiable almost everywere in this set. Superseded by
`LipschitzOnWith.ae_differentiableWithinAt_of_mem` which works for functions taking value in any
finite-dimensional space. -/
theorem ae_differentiableWithinAt_of_mem_of_real (hf : LipschitzOnWith C f s) :
    ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  obtain ⟨g, g_lip, hg⟩ : ∃ (g : E → ℝ), LipschitzWith C g ∧ EqOn f g s := hf.extend_real
  filter_upwards [g_lip.ae_differentiableAt_of_real] with x hx xs
  exact hx.differentiableWithinAt.congr hg (hg xs)

/-- A function on a finite-dimensional space which is Lipschitz on a set and taking values in a
product space is differentiable almost everywere in this set. Superseded by
`LipschitzOnWith.ae_differentiableWithinAt_of_mem` which works for functions taking value in any
finite-dimensional space. -/
theorem ae_differentiableWithinAt_of_mem_pi
    {ι : Type*} [Fintype ι] {f : E → ι → ℝ} {s : Set E}
    (hf : LipschitzOnWith C f s) : ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  have A : ∀ i : ι, LipschitzWith 1 (fun x : ι → ℝ ↦ x i) := fun i => LipschitzWith.eval i
  have : ∀ i : ι, ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ (fun x : E ↦ f x i) s x := fun i ↦ by
    apply ae_differentiableWithinAt_of_mem_of_real
    exact LipschitzWith.comp_lipschitzOnWith (A i) hf
  filter_upwards [ae_all_iff.2 this] with x hx xs
  exact differentiableWithinAt_pi.2 (fun i ↦ hx i xs)

/-- *Rademacher's theorem*: a function between finite-dimensional real vector spaces which is
Lipschitz on a set is differentiable almost everywere in this set. -/
theorem ae_differentiableWithinAt_of_mem {f : E → F} (hf : LipschitzOnWith C f s) :
    ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ f s x := by
  have A := (Basis.ofVectorSpace ℝ F).equivFun.toContinuousLinearEquiv
  suffices H : ∀ᵐ x ∂μ, x ∈ s → DifferentiableWithinAt ℝ (A ∘ f) s x by
    filter_upwards [H] with x hx xs
    have : f = (A.symm ∘ A) ∘ f := by
      simp only [ContinuousLinearEquiv.symm_comp_self, Function.id_comp]
    rw [this]
    exact A.symm.differentiableAt.comp_differentiableWithinAt x (hx xs)
  apply ae_differentiableWithinAt_of_mem_pi
  exact A.lipschitz.comp_lipschitzOnWith hf

/-- *Rademacher's theorem*: a function between finite-dimensional real vector spaces which is
Lipschitz on a set is differentiable almost everywere in this set. -/
theorem ae_differentiableWithinAt {f : E → F} (hf : LipschitzOnWith C f s)
    (hs : MeasurableSet s) :
    ∀ᵐ x ∂(μ.restrict s), DifferentiableWithinAt ℝ f s x := by
  rw [ae_restrict_iff' hs]
  exact hf.ae_differentiableWithinAt_of_mem

end LipschitzOnWith

/-- *Rademacher's theorem*: a Lipschitz function between finite-dimensional real vector spaces is
differentiable almost everywhere. -/
theorem LipschitzWith.ae_differentiableAt {f : E → F} (h : LipschitzWith C f) :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ f x := by
  rw [← lipschitzOnWith_univ] at h
  simpa [differentiableWithinAt_univ] using h.ae_differentiableWithinAt_of_mem

/-- In a real finite-dimensional normed vector space,
  the norm is almost everywhere differentiable. -/
theorem ae_differentiableAt_norm :
    ∀ᵐ x ∂μ, DifferentiableAt ℝ (‖·‖) x := lipschitzWith_one_norm.ae_differentiableAt

omit [MeasurableSpace E] in
/-- In a real finite-dimensional normed vector space,
  the set of points where the norm is differentiable at is dense. -/
theorem dense_differentiableAt_norm :
    Dense {x : E | DifferentiableAt ℝ (‖·‖) x} :=
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  let w := Basis.ofVectorSpace ℝ E
  MeasureTheory.Measure.dense_of_ae (ae_differentiableAt_norm (μ := w.addHaar))
