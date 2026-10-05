/-
Copyright (c) 2026 Emlis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emlis
-/
module

public import Mathlib

/-!
# Polylogarithm

We define the polylogarithm `Li_s(z)`, and relate it to its integral representation and to
its power series. The function `Complex.polylog` defined below has a
junk value (`Classical.choice ‹Nonempty ℂ›`) when `z = 1` and `s.re ≤ 1`.
When `z ∈ Ici 1 ×ℂ {0}`, it takes the limit from the lower half-plane.

## Main definitions

* `Complex.polylogKernel`: the integrand `polylogKernel z t = z / (cexp t - z)`.
* `Complex.polylogIntegral`: the integral representation
  `polylogIntegral s z = 1 / Gamma s * mellin (polylogKernel z) s`
* `Complex.polylogSeries`: the power series `polylogSeries s z = ∑' n, z ^ (n + 1) / (n + 1) ^ s`.
* `Complex.polylog`: the polylogarithm `Li_ s z`.

## Main statements

* `Complex.polylog_eq_polylogSeries`: `Li_ s z = polylogSeries s z` for `‖z‖ < 1`.
* `Complex.summable_polylogSeries_of_norm_lt` and `Complex.summable_polylogSeries_of_norm_le`:
  the defining series is summable for `‖z‖ < 1`, respectively for `‖z‖ ≤ 1` when `1 < s.re`.
* `Complex.polylog_eq_polylogIntegral`: `Li_ s z = polylogIntegral s z` for `0 < s.re` and `z`
  off the branch cut.
* `Complex.mul_deriv_polylog_add_one`: the recurrence `z * deriv (Li_ (s + 1) ·) z = Li_ s z`, for
  `z` off the branch cut.
* `Complex.analyticOnNhd_polylog_right`: `Li_ s` is analytic on the complement of the branch cut.

## Notation

The following notation is localized in `ComplexPolylog`:

* `Li_ s z` is `Complex.polylog s z` i.e. $\operatorname{Li}_s(z)$.

Use `open scoped ComplexPolylog` to use this.

## References

* <https://dlmf.nist.gov/25.12>

## Tags

polylogarithm

## TODO

+ prove `Complex.analyticOnNhd_polylog_left`: `Li_ · z` is analytic on all of `ℂ` for `z ≠ 1`
+ prove `Complex.polylog_one_eq_riemannZeta`: `Li_ s 1 = ζ s` for `1 < s.re`
+ prove some formulas and special values

-/

public noncomputable section

open Set Real Filter Topology MeasureTheory Asymptotics

namespace Complex

variable {s z : ℂ} {r t : ℝ} {n : ℕ}

theorem notMem_Ici_one_reProdIm_of_norm_lt_one (hz : ‖z‖ < 1) : z ∉ Ici 1 ×ℂ {0} := by
  contrapose! hz
  exact hz.left.trans <| re_le_norm z

theorem isClosed_Ici_one_reProdIm : IsClosed (Ici 1 ×ℂ {0}) :=
  isClosed_Ici.reProdIm isClosed_singleton

private lemma exp_sub_ne_zero (ht : 0 ≤ t) (hz : z ∉ Ici 1 ×ℂ {0}) :
    cexp t - z ≠ 0 := by
  intro nh
  simp [← sub_eq_zero.mp nh, mem_reProdIm, exp_ofReal_re, ht.not_gt] at hz

section PolylogKernel

/-- The kernel `z / (cexp t - z)` of the Mellin transform used in the integral representation of
the polylogarithm. For `z` off the branch cut `Ici 1 ×ℂ {0}` the function `polylogKernel z` is
analytic on `Ici 0`, and it is `O (rexp (-t))` at `t → +∞`. -/
@[expose, pp_nodot] def polylogKernel (z : ℂ) (t : ℝ) : ℂ :=
  z / (cexp t - z)

@[simp]
theorem polylogKernel_zero_left : polylogKernel 0 = fun _ : ℝ => 0 := by
  unfold polylogKernel
  simp

theorem analyticAt_polylogKernel_left (hz : z ∉ Ici 1 ×ℂ {0}) (ht : 0 ≤ t) :
    AnalyticAt ℂ (fun z => polylogKernel z t) z :=
  analyticAt_id.div (analyticAt_const.sub analyticAt_id) <| exp_sub_ne_zero ht hz

theorem analyticAt_polylogKernel_right (hz : z ∉ Ici 1 ×ℂ {0}) (ht : 0 ≤ t) :
    AnalyticAt ℝ (polylogKernel z) t :=
  analyticAt_const.div (analyticAt_cexp.restrictScalars.comp (ofRealCLM.analyticAt t)
    |>.sub analyticAt_const) <| exp_sub_ne_zero ht hz

theorem polylogKernel_isBigO :
    polylogKernel z =O[atTop] fun t : ℝ => (rexp (-t) : ℂ) := by
  unfold polylogKernel
  simp only [div_eq_mul_inv, ofReal_exp, ofReal_neg, exp_neg]
  refine IsBigO.const_mul_left (IsBigO.inv_rev ?_ ?_) z
  · suffices Tendsto (fun t : ℝ => ‖cexp t‖) atTop atTop from
      IsEquivalent.refl.add_const_of_norm_tendsto_atTop (c := -z) this |>.isBigO_symm
    simp [tendsto_exp_atTop]
  · filter_upwards with t ht using exp_ne_zero t ht |>.elim

private theorem deriv_polylogKernel (ht : 0 ≤ t) (hz : z ∉ Ici 1 ×ℂ {0}) :
    deriv (fun z => polylogKernel z t) z = cexp t / (cexp t - z) ^ 2 ∧
      deriv (fun t => polylogKernel z t) t = - z * cexp t / (cexp t - z) ^ 2 := by
  have : cexp t - z ≠ 0 := exp_sub_ne_zero ht hz
  have : deriv ofReal t = 1 := hasDerivAt_id (t : ℂ) |>.comp_ofReal.deriv
  unfold polylogKernel
  simp (disch := first | fun_prop | assumption | simp) [this]

theorem deriv_polylogKernel_isBigO :
    deriv (fun t => polylogKernel z t) =O[atTop] fun t : ℝ => (rexp (-t) : ℂ) := by
  have hnorm : Tendsto (fun t : ℝ => ‖cexp (t : ℂ)‖) atTop atTop := by
    simpa [norm_exp_ofReal] using tendsto_exp_atTop
  have hderiv : (fun t : ℝ => deriv (fun t => polylogKernel z t) t) =ᶠ[atTop]
      fun t : ℝ => -z * cexp (t : ℂ) / (cexp (t : ℂ) - z) ^ 2 := by
    filter_upwards [hnorm.eventually (eventually_gt_atTop ‖z‖)] with t ht
    have : cexp (t : ℂ) - z ≠ 0 := sub_ne_zero.mpr fun h => (lt_irrefl ‖z‖) (h ▸ ht)
    have h2 : deriv ofReal t = 1 := (hasDerivAt_id (t : ℂ)).comp_ofReal.deriv
    simp (disch := first | assumption | fun_prop | simp) [polylogKernel, h2]
  have hden : (fun t : ℝ => cexp (t : ℂ) - z) =Θ[atTop] (fun t : ℝ => cexp (t : ℂ)) := by
    simpa [sub_eq_add_neg] using (IsEquivalent.refl.add_const_of_norm_tendsto_atTop hnorm).isTheta
  have : (fun t : ℝ => cexp (t : ℂ) / (cexp (t : ℂ) - z) ^ 2) =O[atTop]
      fun t : ℝ => (rexp (-t) : ℂ) :=
    IsTheta.isBigO <| IsTheta.trans (IsTheta.div (isTheta_refl _ _) (hden.pow 2)) <|
      EventuallyEq.isTheta <| Eventually.of_forall fun t => by
        simp [ofReal_exp, div_eq_mul_inv, pow_two, exp_neg]
  refine hderiv.isEquivalent.isBigO.trans ?_
  convert this.const_mul_left (-z) using 2
  ring_nf

private theorem mul_deriv_polylogKernel (ht : 0 ≤ t) (hz : z ∉ Ici 1 ×ℂ {0}) :
    z * deriv (fun z => polylogKernel z t) z = - deriv (fun t => polylogKernel z t) t := by
  simp only [deriv_polylogKernel ht hz]
  ring

private theorem polylogKernel_eq_tsum (ht : 0 < t) (hz : ‖z‖ < 1) :
    polylogKernel z t = ∑' n : ℕ, z ^ (n + 1) * cexp (-t * (n + 1)) := by
  have : ‖z * cexp (-t)‖ < 1 := by
    simp only [Complex.norm_mul, norm_exp, neg_re, ofReal_re]
    grw [hz, one_mul]
    grind [exp_le_one_iff]
  conv in _ * _ =>
    rw [mul_comm (-t : ℂ), ← n.cast_add_one, ← nsmul_eq_mul, exp_nsmul, ← mul_pow, pow_succ']
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one this]
  simp [exp_neg, field]
  rfl

end PolylogKernel

section Recurrence

/-- The integral representation of the polylogarithm,
$$ \operatorname{Li}_s(z) = \dfrac{1}{\Gamma(s)}
\int_0^\infty t^{s-1}\dfrac{z}{e^t - z} \mathrm{d}t $$
It is valid for `0 < s.re` when `z` is off the branch cut `Ici 1 ×ℂ {0}`,
and also for `z = 1` when `1 < s.re`. -/
@[expose, pp_nodot, dlmf 25.12.11] def polylogIntegral (s z : ℂ) : ℂ :=
  1 / Gamma s * mellin (polylogKernel z) s

private theorem polylogIntegral_and (hs : 0 < s.re) (hz : z ∉ Ici 1 ×ℂ {0}) :
    MellinConvergent (polylogKernel z) s ∧ DifferentiableAt ℂ (polylogIntegral · z) s := by
  have hiker : LocallyIntegrableOn (polylogKernel z) (Ioi 0) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt fun t ht =>
      continuousAt_const.div (by fun_prop) (exp_sub_ne_zero ht.le hz)
  have hker0 : polylogKernel z =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) :=
    analyticAt_polylogKernel_right hz le_rfl |>.continuousAt.continuousWithinAt.isBigO_one
      (F := ℝ) |>.congr_right fun _ => by simp
  have hkerinf : polylogKernel z =O[atTop] fun t : ℝ => rexp (-1 * t) := by
    simpa using isBigO_ofReal_right.mp (polylogKernel_isBigO (z := z))
  refine ⟨mellinConvergent_of_isBigO_rpow_exp one_pos hiker hkerinf hker0 hs, ?_⟩
  have : DifferentiableAt ℂ (fun s => (Gamma s)⁻¹ * mellin (polylogKernel z) s) s :=
    differentiable_one_div_Gamma.differentiableAt.mul <|
      mellin_differentiableAt_of_isBigO_rpow_exp one_pos hiker hkerinf hker0 hs
  simpa only [polylogIntegral, one_div] using this

theorem polylogIntegral_convergent (hs : 0 < s.re) (hz : z ∉ Ici 1 ×ℂ {0}) :
    MellinConvergent (polylogKernel z) s :=
  polylogIntegral_and hs hz |>.left

private lemma hasDerivAt_mellin_polylogKernel_add_one (hs : -1 < s.re) (hz : z ∉ Ici 1 ×ℂ {0}) :
    HasDerivAt (fun z => ∫ t : ℝ in Ioi 0, t ^ s * polylogKernel z t)
      (∫ t : ℝ in Ioi 0, deriv (fun z => t ^ s * polylogKernel z t) z) z := by
  obtain ⟨ε, hε₀, hε⟩ : ∃ ε > 0, Metric.ball z ε ⊆ (Ici 1 ×ℂ {0})ᶜ :=
    Metric.isOpen_iff.mp isClosed_Ici_one_reProdIm.isOpen_compl z hz
  have hbε2bε : Metric.ball z (ε / 2) ⊆ Metric.ball z ε := by
    grind [Metric.ball_subset_ball]
  obtain ⟨M, hM₀, hM⟩ :
      ∃ M > 0, ∀ w ∈ Metric.ball z (ε / 2), ∀ t ≥ 0, rexp t / ‖cexp t - w‖ ≤ M := by
    refine ⟨1 + (‖z‖ + ε / 2) / (ε / 2), by positivity, fun w hw t ht => ?_⟩
    have hmem : cexp t ∈ (Ici 1 ×ℂ {0} : Set ℂ) := by simp [mem_reProdIm, exp_ofReal_re, ht]
    have hεz : ε ≤ ‖cexp t - z‖ := not_lt.mp fun nh => hε (by simpa [dist_eq_norm]) hmem
    have hwz : ‖w - z‖ < ε / 2 := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hεw : ε / 2 ≤ ‖cexp t - w‖ := by linarith [norm_sub_le_norm_sub_add_norm_sub (cexp t) w z]
    calc
      rexp t / ‖cexp t - w‖ ≤ (‖cexp t - w‖ + (‖z‖ + ε / 2)) / ‖cexp t - w‖ := by
        apply div_le_div_of_nonneg_right ?_ (norm_nonneg _)
        linarith [norm_le_norm_add_norm_sub' w z,
          norm_exp_ofReal t ▸ norm_le_norm_add_norm_sub' (cexp t) w]
      _ = 1 + (‖z‖ + ε / 2) / ‖cexp t - w‖ := by
        rw [add_div, div_self <| ne_of_gt <| by linarith]
      _ ≤ 1 + (‖z‖ + ε / 2) / (ε / 2) := by gcongr
  set F : ℂ -> ℝ -> ℂ := fun z t => t ^ s * polylogKernel z t
  set bdd : ℝ -> ℝ := fun t => M ^ 2 * (t ^ s.re * rexp (-t))
  have hdF {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∉ Ici 1 ×ℂ {0}) :
      deriv (fun z => F z t) z = t ^ s * (cexp t / (cexp t - z) ^ 2) := by
    simp [F, deriv_polylogKernel ht hz]
  have hiF : IntegrableOn (F z) (Ioi 0) := by
    have : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s + 1 - 1) • polylogKernel z t) (Ioi 0) :=
      polylogIntegral_convergent (by grind [add_re, one_re]) hz
    simpa
  have hFbdd : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioi 0), ∀ w ∈ Metric.ball z (ε / 2),
      ‖t ^ s * (cexp t / (cexp t - w) ^ 2)‖ ≤ M ^ 2 * (t ^ s.re * rexp (-t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    rw [norm_mul, norm_div, norm_exp, ofReal_re, norm_pow, mul_left_comm,
      norm_cpow_eq_rpow_re_of_pos ht]
    gcongr
    · exact rpow_nonneg ht.le s.re
    · simp only [Real.exp_neg, fieldLe]
      rw [← div_pow]
      gcongr
      exact hM w hw t ht.le
  have hibdd : IntegrableOn bdd (Ioi 0) := by
    apply Integrable.const_mul
    have := integrableOn_rpow_mul_exp_neg_mul_rpow hs one_pos one_pos
    simpa
  have hmbdd : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioi 0), ∀ w ∈ Metric.ball z (ε / 2),
      HasDerivAt (fun x ↦ F x t) (t ^ s * (cexp t / (cexp t - w) ^ 2)) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    rw [← hdF ht.le (hε (hbε2bε hw))]
    exact DifferentiableAt.const_mul
      (analyticAt_polylogKernel_left (hε (hbε2bε hw)) ht.le).differentiableAt _ |>.hasDerivAt
  convert And.right <| hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z <| half_pos hε₀)
    (.of_forall fun z => Measurable.aestronglyMeasurable <| by unfold F polylogKernel; fun_prop)
    hiF (Measurable.aestronglyMeasurable <| by fun_prop) hFbdd hibdd hmbdd using 1
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => hdF ht.le hz

theorem differentiableAt_polylogIntegral_right (hs : 0 < s.re) (hz : z ∉ Ici 1 ×ℂ {0}) :
    DifferentiableAt ℂ (polylogIntegral s ·) z := by
  apply DifferentiableAt.const_mul
  convert hasDerivAt_mellin_polylogKernel_add_one (s := s - 1) (by simpa) hz |>.differentiableAt
  rfl

theorem differentiableAt_polylogIntegral_left (hs : 0 < s.re) (hz : z ∉ Ici 1 ×ℂ {0}) :
    DifferentiableAt ℂ (polylogIntegral · z) s :=
  polylogIntegral_and hs hz |>.right

private lemma mul_deriv_polylogIntegral_add_one_aux (hs : 0 < s.re) (hz : z ∉ Ici 1 ×ℂ {0}) :
    -∫ t : ℝ in Ioi 0, t ^ s * deriv (fun t => polylogKernel z t) t =
      ∫ t : ℝ in Ioi 0, polylogKernel z t * deriv (fun t : ℝ => (t : ℂ) ^ s) t := by
  by_cases hz₀ : z = 0
  · simp [hz₀]
  have hs₀ : s ≠ 0 := ne_zero_of_re_pos hs
  set u : ℝ -> ℂ := fun t : ℝ => (t : ℂ) ^ s
  set v : ℝ -> ℂ := polylogKernel z
  -- Differentiability
  have hdu (t : ℝ) (ht : 0 < t) : HasDerivAt u (s * t ^ (s - 1)) t :=
    hasDerivAt_ofReal_cpow_const ht.ne' hs₀
  have hdv (t : ℝ) (ht : 0 ≤ t) : HasDerivAt v (deriv v t) t :=
    analyticAt_polylogKernel_right hz ht |>.differentiableAt.hasDerivAt
  -- Asymptotics
  have hau : u =O[atTop] fun t : ℝ => rexp (1 / 2 * t) := by
    refine IsBigO.of_norm_left <| IsBigO.trans (Filter.EventuallyEq.isBigO ?_)
      (isLittleO_rpow_exp_pos_mul_atTop s.re (by simp)).isBigO
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [norm_cpow_eq_rpow_re_of_pos ht]
  have hadu : deriv u =O[atTop] fun t : ℝ => rexp (1 / 2 * t) := by
    refine IsBigO.of_norm_left <| IsBigO.trans (Filter.EventuallyEq.isBigO ?_) <|
      (isLittleO_rpow_exp_pos_mul_atTop (s.re - 1) (by simp)).isBigO.const_mul_left ‖s‖
    filter_upwards [eventually_gt_atTop 0] with t ht
    rw [hdu t ht |>.deriv, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]
  have hexp (x : ℝ) : rexp (1 / 2 * x) * rexp (-x) = rexp (-(1 / 2) * x) := by
    rw [← Real.exp_add]
    ring_nf
  have hudv : (u * deriv v) =O[atTop] fun x => rexp (-(1 / 2) * x) :=
    IsBigO.congr_right (IsBigO.mul hau <| isBigO_ofReal_right.mp deriv_polylogKernel_isBigO) hexp
  have hduv : (deriv u * v) =O[atTop] fun x => rexp (-(1 / 2) * x) :=
    IsBigO.congr_right (IsBigO.mul hadu <| isBigO_ofReal_right.mp polylogKernel_isBigO) hexp
  have huv : (u * v) =O[atTop] fun x => rexp (-(1 / 2) * x) :=
    IsBigO.congr_right (IsBigO.mul hau <| isBigO_ofReal_right.mp polylogKernel_isBigO) hexp
  -- Continuity
  have hcu : Continuous u := continuous_ofReal_cpow_const hs
  have hcv : ContinuousOn v (Ici 0) :=
    continuousOn_of_forall_continuousAt fun t ht => hdv t ht |>.continuousAt
  have hcudv : ContinuousOn (u * deriv v) (Ici 0) := by
    apply hcu.continuousOn.mul <| .congr (.div (by fun_prop) (by fun_prop) fun t ht => ?_)
      fun t ht => deriv_polylogKernel ht hz |>.right
    simpa using exp_sub_ne_zero ht hz
  have hcduv : ContinuousOn (deriv u * v) (Ioi 0) := by
    apply ContinuousOn.mul ?_ <| hcv.mono Ioi_subset_Ici_self
    apply ContinuousOn.congr ?_ fun t ht => hasDerivAt_ofReal_cpow_const (by grind) hs₀ |>.deriv
    apply ContinuousOn.const_mul fun x hx =>
      continuousAt_ofReal_cpow_const x (s - 1) (by grind) |>.continuousWithinAt
  -- Integrability, add a lemma in `MeasureTheory/Integral/ExpDecay.lean`?
  have hiudv : IntegrableOn (u * deriv v) (Ioi 0) := by
    have : IntegrableOn (fun x => rexp (-0 * x) • (u * deriv v) x) (Ici 0) :=
      integrableOn_exp_neg_smul_of_isBigO_exp (b := 0)
        (ContinuousOn.locallyIntegrableOn hcudv measurableSet_Ici) hudv (by simp)
    simp only [neg_zero, zero_mul, Real.exp_zero, Pi.mul_apply, one_smul] at this
    exact integrableOn_Ici_iff_integrableOn_Ioi (by finiteness) |>.mp this
  have hiduv : IntegrableOn (deriv u * v) (Ioi 0) := by
    rw [← Ioo_union_Ici_eq_Ioi one_pos]
    refine IntegrableOn.union ?_ ?_
    · obtain ⟨M, hM⟩ : ∃ M, ∀ t ∈ Icc 0 1, ‖v t‖ ≤ M :=
        isCompact_Icc.exists_bound_of_continuousOn (hcv.mono fun t => And.left)
      have : IntegrableOn (fun t : ℝ => (‖s‖ * t ^ (s.re - 1)) * M) (Ioo 0 1) := by
        apply Integrable.const_mul ?_ ‖s‖ |>.mul_const M
        exact intervalIntegral.integrableOn_Ioo_rpow_iff one_pos |>.mpr (by linarith)
      apply this.mono' <| (hcduv.mono fun t => And.left).aestronglyMeasurable measurableSet_Ioo
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      grw [Pi.mul_apply, norm_mul, hM t (Ioo_subset_Icc_self ht),
        hdu t ht.left |>.deriv, norm_mul, norm_cpow_eq_rpow_re_of_pos ht.left,
        sub_re, one_re]
    · have : IntegrableOn (fun x => rexp (-0 * x) • (deriv u * v) x) (Ici 1) :=
        integrableOn_exp_neg_smul_of_isBigO_exp (b := 0)
          (ContinuousOn.locallyIntegrableOn (hcduv.mono (by grind)) measurableSet_Ici)
          hduv (by simp)
      simp only [neg_zero, zero_mul, Real.exp_zero, Pi.mul_apply, one_smul] at this
      exact this
  -- Limits
  have huv0 : Tendsto (u * v) (𝓝[>] 0) (𝓝 0) := by
    have : (u * v) 0 = 0 := by simp [u, hs₀]
    refine this ▸ ContinuousWithinAt.tendsto ?_
    exact ContinuousWithinAt.mul hcu.continuousWithinAt <|
      ContinuousWithinAt.mono (hcv 0 <| le_refl 0) Ioi_subset_Ici_self
  have huvinf : Tendsto (u * v) atTop (𝓝 0) :=
    huv.trans_tendsto <| tendsto_exp_atBot.comp <|
      tendsto_const_mul_atBot_of_neg (by norm_num) |>.mpr tendsto_id
  -- Done
  grind [integral_Ioi_mul_deriv_eq_deriv_mul (fun t ht => hdu t ht |>.differentiableAt.hasDerivAt)
    (fun t ht => hdv t ht.le) hiudv hiduv huv0 huvinf]

theorem mul_deriv_polylogIntegral_add_one (hs : 0 < s.re) (hz : z ∉ Ici 1 ×ℂ {0}) :
    z * deriv (polylogIntegral (s + 1)) z = polylogIntegral s z := by
  have hs₀ : s ≠ 0 := ne_zero_of_re_pos hs
  have hΓs₀ : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  unfold polylogIntegral mellin
  simp only [deriv_const_mul_field', Gamma_add_one s hs₀, field, add_sub_cancel_right, smul_eq_mul]
  calc
    _ = z * (∫ t : ℝ in Ioi 0, deriv (fun z : ℂ => t ^ s * polylogKernel z t) z) :=
      congrArg _ <| hasDerivAt_mellin_polylogKernel_add_one (by grind : -1 < s.re) hz |>.deriv
    _ = ∫ t : ℝ in Ioi 0, t ^ s * (z * deriv (fun z : ℂ => polylogKernel z t) z) := by
      simp only [deriv_const_mul_field', ← integral_const_mul]
      ac_rfl
    _ = ∫ t : ℝ in Ioi 0, t ^ s * - deriv (fun t : ℝ => polylogKernel z t) t :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht =>
        congr_arg _ <| mul_deriv_polylogKernel ht.le hz
    _ = - ∫ t : ℝ in Ioi 0, t ^ s * deriv (fun t : ℝ => polylogKernel z t) t := by
      simp [integral_neg]
    _ = ∫ t : ℝ in Ioi 0, polylogKernel z t * deriv (fun t : ℝ => (t : ℂ) ^ s) t :=
      mul_deriv_polylogIntegral_add_one_aux hs hz
    _ = ∫ t : ℝ in Ioi 0, polylogKernel z t * (s * t ^ (s - 1)) :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht =>
        congrArg _ <| deriv_ofReal_cpow_const ht.ne' hs₀
    _ = ∫ t : ℝ in Ioi 0, s * (t ^ (s - 1) * polylogKernel z t) := by ac_rfl
    _ = s * ∫ t : ℝ in Ioi 0, t ^ (s - 1) * polylogKernel z t := by
      rw [← integral_const_mul]

theorem analyticOnNhd_polylogIntegral_right (hs : 0 < s.re) :
    AnalyticOnNhd ℂ (polylogIntegral s ·) (Ici 1 ×ℂ {0})ᶜ :=
  DifferentiableOn.analyticOnNhd
    (fun _ hz => (differentiableAt_polylogIntegral_right hs hz).differentiableWithinAt)
    isClosed_Ici_one_reProdIm.isOpen_compl

theorem analyticOnNhd_polylogIntegral_left (hz : z ∉ Ici 1 ×ℂ {0}) :
    AnalyticOnNhd ℂ (polylogIntegral · z) { s : ℂ | 0 < s.re } :=
  DifferentiableOn.analyticOnNhd
    (fun _ hs => (differentiableAt_polylogIntegral_left hs hz).differentiableWithinAt)
    (isOpen_re_gt 0)

end Recurrence

section PolylogDef

/-- The `n`-th function in this family is `Li_ s z` off the branch cut if `-n < s.re` -/
private def polylogAux1 : ℕ -> ℂ -> ℂ -> ℂ
  | 0 => polylogIntegral
  | n + 1 => fun s z : ℂ => z * deriv (polylogAux1 n (s + 1)) z

/-- The polylogarithm as a function of `z` off the branch cut, for all complex `s` -/
private def polylogAux2 (s z : ℂ) : ℂ :=
  polylogAux1 ⌊1 - s.re⌋₊ s z

open Classical in
/-- The polylogarithm function $\operatorname{Li}_s(z)$ -/
@[irreducible, pp_nodot, wikidata Q1238449, dlmf 25.12]
def polylog (s z : ℂ) : ℂ :=
  if z ∉ Ici 1 ×ℂ {0} then polylogAux2 s z else
    limUnder (𝓝[{ z : ℂ | z.im < 0 }] z) (polylogAux2 s)

@[inherit_doc] scoped[ComplexPolylog] notation "Li_ " => Complex.polylog
recommended_spelling "polylog" for "Li_" in [polylog, ComplexPolylog.«termLi_»]

open scoped ComplexPolylog

private theorem polylogAux1_zero : polylogAux1 0 = polylogIntegral := rfl

private theorem polylogAux2_of_re_pos (hs : 0 < s.re) : polylogAux2 s = polylogIntegral s := by
  unfold polylogAux2
  convert congrFun polylogAux1_zero s
  refine Nat.floor_eq_zero.mpr ?_
  simpa

private theorem polylog_of_notMem (hz : z ∉ Ici 1 ×ℂ {0}) : polylog s z = polylogAux2 s z := by
  simp [polylog, hz]

private theorem deriv_polylog_of_notMem (hz : z ∉ Ici 1 ×ℂ {0}) :
    deriv (Li_ s) z = deriv (polylogAux2 s) z := by
  apply EventuallyEq.deriv_eq
  filter_upwards [isClosed_Ici_one_reProdIm.compl_mem_nhds hz]
    with z hz using polylog_of_notMem hz

theorem mul_deriv_polylog_add_one (hz : z ∉ Ici 1 ×ℂ {0}) :
    z * deriv (Li_ (s + 1)) z = Li_ s z := by
  rw [polylog_of_notMem hz, deriv_polylog_of_notMem hz]
  unfold polylogAux2
  by_cases hs : 0 < s.re
  · rw [Nat.floor_eq_zero.mpr (by grind [add_re, one_re]), Nat.floor_eq_zero.mpr (by simpa)]
    simp only [polylogAux1_zero, mul_deriv_polylogIntegral_add_one hs hz]
  · suffices ⌊1 - s.re⌋₊ = ⌊1 - (s + 1).re⌋₊ + 1 by
      rw [this]
      rfl
    rw [← Nat.floor_add_one] <;> simp_all [neg_add_eq_sub]

theorem limUnder_nhdsWithin_im_neg_polylog (hz : z ∈ Ici 1 ×ℂ {0}) :
    limUnder (𝓝[{ z : ℂ | z.im < 0 }] z) (Li_ s) = Li_ s z := by
  unfold polylog
  simp only [hz, not_true_eq_false, ↓reduceIte]
  apply EventuallyEq.limUnder_eq
  filter_upwards [self_mem_nhdsWithin] with w hw using ite_eq_left <| by grind [mem_reProdIm]

theorem analyticOnNhd_polylog_right : AnalyticOnNhd ℂ (Li_ s) (Ici 1 ×ℂ {0})ᶜ := by
  have (n : ℕ) (s : ℂ) (hs : 0 < (s + n).re) :
      AnalyticOnNhd ℂ (polylogAux1 n s) (Ici 1 ×ℂ {0})ᶜ := by
    induction n generalizing s with
    | zero => exact analyticOnNhd_polylogIntegral_right (by simpa using hs)
    | succ n ih =>
      refine analyticOnNhd_id.mul (ih (s + 1) ?_).deriv
      simpa [add_assoc, add_comm, add_left_comm] using hs
  refine this ⌊1 - s.re⌋₊ s ?_ |>.congr isClosed_Ici_one_reProdIm.isOpen_compl fun z hz => ?_
  · rw [add_re, natCast_re]
    linarith [Nat.lt_floor_add_one (1 - s.re)]
  · unfold polylog
    exact (ite_eq_left hz).symm

section

/-- The polylogarithm series $\sum_{n}^{\infty} \frac{z^n}{n^s}$.
For `‖z‖ < 1` it converges absolutely for all complex `s` and equals the polylogarithm.
For `‖z‖ ≤ 1`, absolute convergence requires `1 < s.re`.

See also `polylog_eq_polylogSeries` and `summable_polylogSeries_of_norm_le`. -/
@[dlmf 25.12.10]
def polylogSeries (s z : ℂ) : ℂ :=
  ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ s

theorem _root_.Real.summable_polylogSeries_of_abs_lt {x : ℝ} (y : ℝ) (hx : |x| < 1) :
    Summable fun n : ℕ => x ^ (n + 1) / (n + 1) ^ y := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, -y ≤ k := exists_nat_ge (-y)
  have hg : Summable fun n : ℕ => (n + 1 : ℕ) ^ k * |x| ^ (n + 1) :=
    summable_nat_add_iff (f := fun n : ℕ => n ^ k * |x| ^ n) 1 |>.mpr <|
      summable_pow_mul_geometric_of_norm_lt_one k (by simpa using hx : ‖(|x| : ℝ)‖ < 1)
  refine Summable.of_norm_bounded hg fun n => ?_
  rw [norm_div, norm_pow, ← Nat.cast_add_one, norm_rpow_of_nonneg <| Nat.cast_nonneg _,
    div_eq_mul_inv, mul_comm, ← rpow_neg (mod_cast Nat.zero_le _)]
  grw [rpow_le_rpow_of_exponent_le (mod_cast n.succ_pos) hk, rpow_natCast]
  norm_cast

theorem summable_polylogSeries_of_norm_lt (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => z ^ (n + 1) / (n + 1) ^ s := by
  refine Summable.of_norm ?_
  convert Real.summable_polylogSeries_of_abs_lt (x := ‖z‖) (y := s.re) (by simpa using hz) using 1
  ext n
  rw [norm_div, norm_pow, ← n.cast_add_one, norm_natCast_cpow_of_pos n.succ_pos s]
  simp

theorem summable_polylogSeries_of_norm_le (hs : 1 < s.re) (hz : ‖z‖ ≤ 1) :
    Summable fun n : ℕ => z ^ (n + 1) / (n + 1) ^ s := by
  apply (summable_nat_add_iff 1 |>.mpr <| summable_nat_rpow_inv.mpr hs).of_norm_bounded fun n => ?_
  grw [norm_div, norm_pow, ← n.cast_add_one, ← ofReal_natCast (n + 1),
    norm_cpow_eq_rpow_re_of_pos (mod_cast n.add_one_pos) s, inv_eq_one_div, hz, one_pow]

private lemma polylogIntegral_eq_polylogSeries_aux (hs : 0 < s.re) (hz : ‖z‖ < 1) :
    ∑' n : ℕ, ∫ t : ℝ in Ioi 0, z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1))) =
      ∫ t : ℝ in Ioi 0, ∑' n : ℕ, z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1))) := by
  have hi (c : ℝ) : IntegrableOn (fun t => c * (rexp (-t) * t ^ (s.re - 1))) (Ioi 0) :=
    Real.GammaIntegral_convergent hs |>.const_mul c
  have hbdd (n : ℕ) : ∀ t ∈ Ioi (0 : ℝ), ‖z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1)))‖ ≤
      ‖z‖ ^ (n + 1) * (rexp (-t) * t ^ (s.re - 1)) := fun t (ht : 0 < t) => by
    suffices ‖z‖ ^ (n + 1) * (t ^ (s.re - 1) * rexp (-(t * (n + 1)))) ≤
        ‖z‖ ^ (n + 1) * (t ^ (s.re - 1) * rexp (-t)) by
      simpa [norm_cpow_eq_rpow_re_of_pos ht, norm_exp, mul_comm]
    gcongr
    nlinarith
  have hi' (n : ℕ) : IntegrableOn
      (fun t : ℝ => z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1)))) (Ioi 0) := by
    apply (hi (‖z‖ ^ (n + 1))).mono' (ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi) ?_
    · apply ContinuousOn.const_mul (b := _) <| continuousOn_of_forall_continuousAt fun t ht =>
        (continuousAt_ofReal_cpow_const t (s - 1) <| Or.inr ht.ne').mul ?_
      fun_prop
    · exact ae_restrict_iff' measurableSet_Ioi |>.mpr <| .of_forall (hbdd n)
  refine integral_tsum_of_summable_integral_norm hi' ?_
  apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) (fun n => ?_) <|
    (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right (‖z‖ * Real.Gamma s.re)
  apply (setIntegral_mono_on (hi' n).norm (hi _) measurableSet_Ioi (hbdd n)).trans_eq
  rw [integral_const_mul, ← Real.Gamma_eq_integral hs]
  ring

theorem polylogIntegral_eq_polylogSeries (hs : 0 < s.re) (hz : ‖z‖ < 1) :
    polylogIntegral s z = polylogSeries s z := calc
  1 / Gamma s * ∫ t : ℝ in Ioi 0, t ^ (s - 1) * polylogKernel z t
    = 1 / Gamma s * ∫ t : ℝ in Ioi 0, ∑' n : ℕ,
      t ^ (s - 1) * (z ^ (n + 1) * cexp (-t * (n + 1))) := by
    refine congrArg _ <| setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [tsum_mul_left, polylogKernel_eq_tsum ht hz]
  _ = 1 / Gamma s * ∫ t : ℝ in Ioi 0, ∑' n : ℕ,
      z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1))) := by ac_rfl
  _ = 1 / Gamma s * ∑' n : ℕ, ∫ t : ℝ in Ioi 0,
      z ^ (n + 1) * (t ^ (s - 1) * cexp (-t * (n + 1))) :=
    congrArg _ <| polylogIntegral_eq_polylogSeries_aux hs hz |>.symm
  _ = ∑' n : ℕ, z ^ (n + 1) * 1 / Gamma s * ∫ t : ℝ in Ioi 0,
      t ^ (s - 1) * cexp (-t * (n + 1)) := by
    simp_rw [← tsum_mul_left, ← integral_const_mul]
    ring_nf
  _ = ∑' n : ℕ, z ^ (n + 1) * 1 / Gamma s * (Gamma s / (n + 1) ^ s) := tsum_congr fun n => by
    congr 1
    have hn : (0 : ℝ) < n + 1 := mod_cast Nat.zero_lt_succ n
    simpa [field, arg_eq_pi_iff, hn.not_gt, mul_comm, inv_cpow_eq_ite] using
      integral_cpow_mul_exp_neg_mul_Ioi hs hn
  _ = ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ s := by
    field_simp [Gamma_ne_zero_of_re_pos hs]

private lemma mul_deriv_polylogSeries_add_one_aux (hz : ‖z‖ < 1) :
    deriv (fun z : ℂ => ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ (s + 1)) z =
      ∑' n : ℕ, deriv (fun z : ℂ => z ^ (n + 1) / (n + 1) ^ (s + 1)) z := by
  obtain ⟨r, hrz, hr⟩ : ∃ r, r ∈ Ioo ‖z‖ 1 := DenselyOrdered.dense ‖z‖ 1 hz
  have hr₀ : 0 < r := norm_nonneg z |>.trans_lt hrz
  apply HasDerivAt.deriv
  apply hasDerivAt_tsum_of_isPreconnected (y₀ := 0) (t := Metric.ball (0 : ℂ) r)
    (u := fun n : ℕ => (n + 1) * r ^ n / (n + 1) ^ (s.re + 1)) ?_ Metric.isOpen_ball
    Metric.isPreconnected_ball (fun n z' hz' => DifferentiableAt.hasDerivAt (by simp)) ?_
    (by simpa only [Metric.mem_ball, dist_self]) (by simp) (by simpa)
  · conv in _ / _ =>
      rw [rpow_add (mod_cast Nat.add_one_pos n), rpow_one, mul_comm]
      rw [mul_div_mul_right (r ^ n) ((↑n + 1) ^ s.re) (mod_cast Nat.add_one_ne_zero n)]
    convert @Real.summable_polylogSeries_of_abs_lt r s.re (by grind) |>.const_smul (1 / r) with n
    simp [field, pow_succ]
  · intro n z' hz'
    simp only [deriv_div_const, differentiableAt_fun_id, deriv_fun_pow, Nat.cast_add,
      Nat.cast_one, add_tsub_cancel_right, deriv_id'', mul_one, Complex.norm_div,
      Complex.norm_mul, norm_pow]
    norm_cast
    gcongr
    · simp only [Metric.mem_ball, dist_zero_right] at hz'
      exact hz'.le
    · rw [← ofReal_natCast, norm_cpow_eq_rpow_re_of_pos <| mod_cast Nat.add_one_pos n]
      simp

theorem mul_deriv_polylogSeries_add_one (hz : ‖z‖ < 1) :
    z * deriv (polylogSeries (s + 1)) z = polylogSeries s z := calc
  z * deriv (fun z : ℂ => ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ (s + 1)) z
    = z * ∑' n : ℕ, deriv (fun z : ℂ => z ^ (n + 1) / (n + 1) ^ (s + 1)) z :=
    congrArg _ <| mul_deriv_polylogSeries_add_one_aux hz
  _ = ∑' n : ℕ, z * deriv (fun z : ℂ => z ^ (n + 1)) z / (n + 1) ^ (s + 1) := by
    simp only [deriv_div_const, ← tsum_mul_left]
    ring_nf
  _ = ∑' n : ℕ, z ^ (n + 1) / (n + 1) ^ s := tsum_congr fun n => by
    simp [field, cpow_add (x := n + 1) _ _ (mod_cast by simp), cpow_one]
    ring

/-- The polylogarithm equals its integral representation
when `hs : 0 < s.re` and `z` is off the branch cut. -/
theorem polylog_eq_polylogIntegral (hs : 0 < s.re) (hz : z ∉ Ici 1 ×ℂ {0}) :
    Li_ s z = polylogIntegral s z := by
  rw [polylog_of_notMem hz, polylogAux2_of_re_pos hs]

/-- The polylogarithm equals its series representation in the unit disc `‖z‖ < 1` -/
theorem polylog_eq_polylogSeries (hz : ‖z‖ < 1) :
    Li_ s z = polylogSeries s z := by
  revert z
  suffices ∀ z, ‖z‖ < 1 -> polylog (s + ⌊1 - s.re⌋₊) z = polylogSeries (s + ⌊1 - s.re⌋₊) z by
    generalize ⌊1 - s.re⌋₊ = n at *
    induction n with
    | zero => simpa
    | succ n ih =>
      refine fun _ _ => ih (fun z hz => ?_) ‹_›
      rw [← mul_deriv_polylogSeries_add_one hz,
        ← mul_deriv_polylog_add_one <| notMem_Ici_one_reProdIm_of_norm_lt_one hz]
      refine congrArg _ <| EventuallyEq.deriv_eq ?_
      filter_upwards [IsOpen.mem_nhds (Metric.isOpen_ball (x := 0)) (by simpa)] with z hz
      simpa [add_assoc] using this z (by simpa using hz)
  suffices 0 < (s + ↑⌊1 - s.re⌋₊).re by
    intro z hz
    rw [polylog_of_notMem <| notMem_Ici_one_reProdIm_of_norm_lt_one hz,
      polylogAux2_of_re_pos this, polylogIntegral_eq_polylogSeries this hz]
  simp only [add_re, natCast_re]
  linarith [Nat.lt_floor_add_one (1 - s.re)]

theorem polylog_eq_tsum_pnat (hz : ‖z‖ < 1) :
    Li_ s z = ∑' n : ℕ+, z ^ n.val / n ^ s := by
  simp [polylog_eq_polylogSeries hz, tsum_pnat_eq_tsum_succ (f := fun n : ℕ => z ^ n / n ^ s)]
  rfl

theorem hasSum_polylog_of_norm_lt (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => z ^ (n + 1) / (n + 1) ^ s) (polylog s z) :=
  summable_polylogSeries_of_norm_lt hz |>.hasSum_iff.mpr <| polylog_eq_polylogSeries hz |>.symm

@[simp]
theorem polylog_zero_right : Li_ s 0 = 0 := by
  simp [polylog_eq_polylogSeries, polylogSeries]

end

end PolylogDef

end Complex
