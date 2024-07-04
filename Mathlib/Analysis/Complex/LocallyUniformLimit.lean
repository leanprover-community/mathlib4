/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara
-/
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.NormedSpace.FunctionSeries

#align_import analysis.complex.locally_uniform_limit from "leanprover-community/mathlib"@"fe44cd36149e675eb5dec87acc7e8f1d6568e081"

/-!
# Locally uniform limits of holomorphic functions

This file gathers some results about locally uniform limits of holomorphic functions on an open
subset of the complex plane.

## Main results

* `TendstoLocallyUniformlyOn.differentiableOn`: A locally uniform limit of holomorphic functions
  is holomorphic.
* `TendstoLocallyUniformlyOn.deriv`: Locally uniform convergence implies locally uniform
  convergence of the derivatives to the derivative of the limit.
-/


open Set Metric MeasureTheory Filter Complex intervalIntegral

open scoped Real Topology

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] {U K : Set ℂ}
  {z : ℂ} {M r δ : ℝ} {φ : Filter ι} {F : ι → ℂ → E} {f g : ℂ → E}

namespace Complex

section Cderiv

/-- A circle integral which coincides with `deriv f z` whenever one can apply the Cauchy formula for
the derivative. It is useful in the proof that locally uniform limits of holomorphic functions are
holomorphic, because it depends continuously on `f` for the uniform topology. -/
noncomputable def cderiv (r : ℝ) (f : ℂ → E) (z : ℂ) : E :=
  (2 * π * I : ℂ)⁻¹ • ∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • f w
#align complex.cderiv Complex.cderiv

theorem cderiv_eq_deriv (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hr : 0 < r)
    (hzr : closedBall z r ⊆ U) : cderiv r f z = deriv f z :=
  two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable hU hzr hf (mem_ball_self hr)
#align complex.cderiv_eq_deriv Complex.cderiv_eq_deriv

theorem norm_cderiv_le (hr : 0 < r) (hf : ∀ w ∈ sphere z r, ‖f w‖ ≤ M) :
    ‖cderiv r f z‖ ≤ M / r := by
  have hM : 0 ≤ M := by
    obtain ⟨w, hw⟩ : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    exact (norm_nonneg _).trans (hf w hw)
  have h1 : ∀ w ∈ sphere z r, ‖((w - z) ^ 2)⁻¹ • f w‖ ≤ M / r ^ 2 := by
    intro w hw
    simp only [mem_sphere_iff_norm, norm_eq_abs] at hw
    simp only [norm_smul, inv_mul_eq_div, hw, norm_eq_abs, map_inv₀, Complex.abs_pow]
    exact div_le_div hM (hf w hw) (sq_pos_of_pos hr) le_rfl
  have h2 := circleIntegral.norm_integral_le_of_norm_le_const hr.le h1
  simp only [cderiv, norm_smul]
  refine (mul_le_mul le_rfl h2 (norm_nonneg _) (norm_nonneg _)).trans (le_of_eq ?_)
  field_simp [_root_.abs_of_nonneg Real.pi_pos.le]
  ring
#align complex.norm_cderiv_le Complex.norm_cderiv_le

theorem cderiv_sub (hr : 0 < r) (hf : ContinuousOn f (sphere z r))
    (hg : ContinuousOn g (sphere z r)) : cderiv r (f - g) z = cderiv r f z - cderiv r g z := by
  have h1 : ContinuousOn (fun w : ℂ => ((w - z) ^ 2)⁻¹) (sphere z r) := by
    refine ((continuous_id'.sub continuous_const).pow 2).continuousOn.inv₀ fun w hw h => hr.ne ?_
    rwa [mem_sphere_iff_norm, sq_eq_zero_iff.mp h, norm_zero] at hw
  simp_rw [cderiv, ← smul_sub]
  congr 1
  simpa only [Pi.sub_apply, smul_sub] using
    circleIntegral.integral_sub ((h1.smul hf).circleIntegrable hr.le)
      ((h1.smul hg).circleIntegrable hr.le)
#align complex.cderiv_sub Complex.cderiv_sub

theorem norm_cderiv_lt (hr : 0 < r) (hfM : ∀ w ∈ sphere z r, ‖f w‖ < M)
    (hf : ContinuousOn f (sphere z r)) : ‖cderiv r f z‖ < M / r := by
  obtain ⟨L, hL1, hL2⟩ : ∃ L < M, ∀ w ∈ sphere z r, ‖f w‖ ≤ L := by
    have e1 : (sphere z r).Nonempty := NormedSpace.sphere_nonempty.mpr hr.le
    have e2 : ContinuousOn (fun w => ‖f w‖) (sphere z r) := continuous_norm.comp_continuousOn hf
    obtain ⟨x, hx, hx'⟩ := (isCompact_sphere z r).exists_isMaxOn e1 e2
    exact ⟨‖f x‖, hfM x hx, hx'⟩
  exact (norm_cderiv_le hr hL2).trans_lt ((div_lt_div_right hr).mpr hL1)
#align complex.norm_cderiv_lt Complex.norm_cderiv_lt

theorem norm_cderiv_sub_lt (hr : 0 < r) (hfg : ∀ w ∈ sphere z r, ‖f w - g w‖ < M)
    (hf : ContinuousOn f (sphere z r)) (hg : ContinuousOn g (sphere z r)) :
    ‖cderiv r f z - cderiv r g z‖ < M / r :=
  cderiv_sub hr hf hg ▸ norm_cderiv_lt hr hfg (hf.sub hg)
#align complex.norm_cderiv_sub_lt Complex.norm_cderiv_sub_lt

theorem _root_.TendstoUniformlyOn.cderiv (hF : TendstoUniformlyOn F f φ (cthickening δ K))
    (hδ : 0 < δ) (hFn : ∀ᶠ n in φ, ContinuousOn (F n) (cthickening δ K)) :
    TendstoUniformlyOn (cderiv δ ∘ F) (cderiv δ f) φ K := by
  rcases φ.eq_or_neBot with rfl | hne
  · simp only [TendstoUniformlyOn, eventually_bot, imp_true_iff]
  have e1 : ContinuousOn f (cthickening δ K) := TendstoUniformlyOn.continuousOn hF hFn
  rw [tendstoUniformlyOn_iff] at hF ⊢
  rintro ε hε
  filter_upwards [hF (ε * δ) (mul_pos hε hδ), hFn] with n h h' z hz
  simp_rw [dist_eq_norm] at h ⊢
  have e2 : ∀ w ∈ sphere z δ, ‖f w - F n w‖ < ε * δ := fun w hw1 =>
    h w (closedBall_subset_cthickening hz δ (sphere_subset_closedBall hw1))
  have e3 := sphere_subset_closedBall.trans (closedBall_subset_cthickening hz δ)
  have hf : ContinuousOn f (sphere z δ) :=
    e1.mono (sphere_subset_closedBall.trans (closedBall_subset_cthickening hz δ))
  simpa only [mul_div_cancel_right₀ _ hδ.ne.symm] using norm_cderiv_sub_lt hδ e2 hf (h'.mono e3)
#align tendsto_uniformly_on.cderiv TendstoUniformlyOn.cderiv

end Cderiv

section Weierstrass

theorem tendstoUniformlyOn_deriv_of_cthickening_subset (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) {δ : ℝ} (hδ : 0 < δ) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : cthickening δ K ⊆ U) :
    TendstoUniformlyOn (deriv ∘ F) (cderiv δ f) φ K := by
  have h1 : ∀ᶠ n in φ, ContinuousOn (F n) (cthickening δ K) := by
    filter_upwards [hF] with n h using h.continuousOn.mono hKU
  have h2 : IsCompact (cthickening δ K) := hK.cthickening
  have h3 : TendstoUniformlyOn F f φ (cthickening δ K) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hf (cthickening δ K) hKU h2
  apply (h3.cderiv hδ h1).congr
  filter_upwards [hF] with n h z hz
  exact cderiv_eq_deriv hU h hδ ((closedBall_subset_cthickening hz δ).trans hKU)
#align complex.tendsto_uniformly_on_deriv_of_cthickening_subset Complex.tendstoUniformlyOn_deriv_of_cthickening_subset

theorem exists_cthickening_tendstoUniformlyOn (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ δ > 0, cthickening δ K ⊆ U ∧ TendstoUniformlyOn (deriv ∘ F) (cderiv δ f) φ K := by
  obtain ⟨δ, hδ, hKδ⟩ := hK.exists_cthickening_subset_open hU hKU
  exact ⟨δ, hδ, hKδ, tendstoUniformlyOn_deriv_of_cthickening_subset hf hF hδ hK hU hKδ⟩
#align complex.exists_cthickening_tendsto_uniformly_on Complex.exists_cthickening_tendstoUniformlyOn

/-- A locally uniform limit of holomorphic functions on an open domain of the complex plane is
holomorphic (the derivatives converge locally uniformly to that of the limit, which is proved
as `TendstoLocallyUniformlyOn.deriv`). -/
theorem _root_.TendstoLocallyUniformlyOn.differentiableOn [φ.NeBot]
    (hf : TendstoLocallyUniformlyOn F f φ U) (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U)
    (hU : IsOpen U) : DifferentiableOn ℂ f U := by
  rintro x hx
  obtain ⟨K, ⟨hKx, hK⟩, hKU⟩ := (compact_basis_nhds x).mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨δ, _, _, h1⟩ := exists_cthickening_tendstoUniformlyOn hf hF hK hU hKU
  have h2 : interior K ⊆ U := interior_subset.trans hKU
  have h3 : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) (interior K) := by
    filter_upwards [hF] with n h using h.mono h2
  have h4 : TendstoLocallyUniformlyOn F f φ (interior K) := hf.mono h2
  have h5 : TendstoLocallyUniformlyOn (deriv ∘ F) (cderiv δ f) φ (interior K) :=
    h1.tendstoLocallyUniformlyOn.mono interior_subset
  have h6 : ∀ x ∈ interior K, HasDerivAt f (cderiv δ f x) x := fun x h =>
    hasDerivAt_of_tendsto_locally_uniformly_on' isOpen_interior h5 h3 (fun _ => h4.tendsto_at) h
  have h7 : DifferentiableOn ℂ f (interior K) := fun x hx =>
    (h6 x hx).differentiableAt.differentiableWithinAt
  exact (h7.differentiableAt (interior_mem_nhds.mpr hKx)).differentiableWithinAt
#align tendsto_locally_uniformly_on.differentiable_on TendstoLocallyUniformlyOn.differentiableOn

theorem _root_.TendstoLocallyUniformlyOn.deriv (hf : TendstoLocallyUniformlyOn F f φ U)
    (hF : ∀ᶠ n in φ, DifferentiableOn ℂ (F n) U) (hU : IsOpen U) :
    TendstoLocallyUniformlyOn (deriv ∘ F) (deriv f) φ U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  rcases φ.eq_or_neBot with rfl | hne
  · simp only [TendstoUniformlyOn, eventually_bot, imp_true_iff]
  rintro K hKU hK
  obtain ⟨δ, hδ, hK4, h⟩ := exists_cthickening_tendstoUniformlyOn hf hF hK hU hKU
  refine h.congr_right fun z hz => cderiv_eq_deriv hU (hf.differentiableOn hF hU) hδ ?_
  exact (closedBall_subset_cthickening hz δ).trans hK4
#align tendsto_locally_uniformly_on.deriv TendstoLocallyUniformlyOn.deriv

end Weierstrass

section Tsums

/-- If the terms in the sum `∑' (i : ι), F i` are uniformly bounded on `U` by a
summable function, and each term in the sum is differentiable on `U`, then so is the sum. -/
theorem differentiableOn_tsum_of_summable_norm {u : ι → ℝ} (hu : Summable u)
    (hf : ∀ i : ι, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    (hF_le : ∀ (i : ι) (w : ℂ), w ∈ U → ‖F i w‖ ≤ u i) :
    DifferentiableOn ℂ (fun w : ℂ => ∑' i : ι, F i w) U := by
  classical
  have hc := (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
  refine hc.differentiableOn (eventually_of_forall fun s => ?_) hU
  exact DifferentiableOn.sum fun i _ => hf i
#align complex.differentiable_on_tsum_of_summable_norm Complex.differentiableOn_tsum_of_summable_norm

/-- If the terms in the sum `∑' (i : ι), F i` are uniformly bounded on `U` by a
summable function, then the sum of `deriv F i` at a point in `U` is the derivative of the
sum. -/
theorem hasSum_deriv_of_summable_norm {u : ι → ℝ} (hu : Summable u)
    (hf : ∀ i : ι, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    (hF_le : ∀ (i : ι) (w : ℂ), w ∈ U → ‖F i w‖ ≤ u i) (hz : z ∈ U) :
    HasSum (fun i : ι => deriv (F i) z) (deriv (fun w : ℂ => ∑' i : ι, F i w) z) := by
  rw [HasSum]
  have hc := (tendstoUniformlyOn_tsum hu hF_le).tendstoLocallyUniformlyOn
  convert (hc.deriv (eventually_of_forall fun s =>
    DifferentiableOn.sum fun i _ => hf i) hU).tendsto_at hz using 1
  ext1 s
  exact (deriv_sum fun i _ => (hf i).differentiableAt (hU.mem_nhds hz)).symm
#align complex.has_sum_deriv_of_summable_norm Complex.hasSum_deriv_of_summable_norm

end Tsums

end Complex
