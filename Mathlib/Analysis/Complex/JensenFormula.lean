/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.Harmonic.Poisson
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage

import Mathlib.Algebra.FiniteSupport.Basic

/-!
# Jensen's Formula of Complex Analysis

If a function `g : ℂ → ℂ` is analytic without zero on the closed ball with center `c` and radius
`R`, then `log ‖g ·‖` is harmonic, and the mean value theorem of harmonic functions asserts that the
circle average `circleAverage (log ‖g ·‖) c R` equals `log ‖g c‖`.  Note that `g c` equals
`meromorphicTrailingCoeffAt g c` and see `AnalyticOnNhd.circleAverage_log_norm_of_ne_zero` for the
precise statement.

Jensen's Formula, formulated in `MeromorphicOn.circleAverage_log_norm` below, generalizes this to
the setting where `g` is merely meromorphic. In that case, the `circleAverage (log ‖g ·‖) c R`
equals `log ‖meromorphicTrailingCoeffAt g c‖` plus a correction term that accounts for the zeros and
poles of `g` within the ball.
-/

public section

open Filter MeromorphicAt MeasureTheory MeromorphicOn Metric Real Set Topology
open scoped ComplexConjugate


/-!
## Preparatory Material

In preparation to the proof of Jensen's formula, compute several circle averages and reformulate
some of the terms that appear in the formula and its proof.
-/

-- Auxiliary definitition for `circleAverage_re_herglotzRieszKernel_mul_log`. Shorthand for the
-- integrand in our computations
private noncomputable def herglotzLogIntegrand (w ρ : ℂ) : ℂ → ℝ :=
  (Complex.re ∘ herglotzRieszKernel 0 w) • (Real.log ‖· - ρ‖)

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Continuity of the
-- herglotzLogIntegrand.
private lemma continuousAt_herglotzLogIntegrand {w ρ z : ℂ} (hz_w : z ≠ w) (hz_ρ : z ≠ ρ) :
    ContinuousAt (herglotzLogIntegrand w ρ) z := by
  have : ‖z - ρ‖ ≠ 0 := by simp_all [sub_eq_zero]
  simp only [herglotzLogIntegrand, herglotzRieszKernel_fun_def, sub_zero, smul_eq_mul]
  fun_prop (disch := grind)

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Continuity of the
-- herglotzLogIntegrand.
private lemma continuous_herglotzLogIntegrand_circle {w ρ : ℂ} {R r : ℝ} (hρ : ‖ρ‖ = R)
    (hr_lt : r < R) (hwr : ‖w‖ < r) :
    Continuous (fun θ ↦ herglotzLogIntegrand w ρ (circleMap 0 r θ)) := by
  rw [continuous_iff_continuousAt]
  intro θ
  apply ContinuousAt.comp (continuousAt_herglotzLogIntegrand _ _) (by fun_prop)
  all_goals
    by_contra h
    grind [norm_circleMap_zero, lt_of_le_of_lt (Complex.norm_nonneg w) hwr]

open Complex in
-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Computation for the
-- boundedness required by the dominated convergence theorem, Part I.
private lemma const_mul_norm_sub_circleMap_le_norm_sub_circleMap {r₀ r R : ℝ} {ρ : ℂ} (hρ : ‖ρ‖ = R)
    (hr₀ : 0 < r₀) (hR : 0 < R) (hr₀r : r₀ ≤ r) (hrR : r ≤ R) (θ : ℝ) :
    sqrt (r₀ / R) * ‖circleMap 0 R θ - ρ‖ ≤ ‖circleMap 0 r θ - ρ‖ := by
  have h_cos_law (r₁ : ℝ) :
      ‖circleMap 0 r₁ θ - ρ‖ ^ 2 = r₁ ^ 2 + R ^ 2 - 2 * r₁ * R * Real.cos (θ - Complex.arg ρ) := by
    rw [← ofReal_inj, ← normSq_eq_norm_sq, normSq_sub ]
    suffices (circleMap 0 r₁ θ * (conj) ρ).re = r₁ * ‖ρ‖ * Real.cos (θ - ρ.arg) by
      simp [normSq_eq_norm_sq, hρ, -mul_re, this, mul_assoc]
    conv_lhs => rw [← norm_mul_exp_arg_mul_I ρ, ← circleMap_zero, conj_circleMap_zero,
      circleMap_zero_mul, circleMap_zero_re, ← sub_eq_add_neg]
  have : (r₀ / R) * ‖circleMap 0 R θ - ρ‖ ^ 2 ≤ ‖circleMap 0 r θ - ρ‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hR]
    nlinarith [h_cos_law r, h_cos_law R, mul_le_mul_of_nonneg_left hr₀r hR.le,
      mul_le_mul_of_nonneg_left hrR hR.le, neg_one_le_cos, cos_le_one]
  grw [← sqrt_sq (norm_nonneg _), ← sqrt_mul (by positivity), this, sqrt_sq (norm_nonneg _)]

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Computation for the
-- boundedness required by the dominated convergence theorem, Part II.
private lemma norm_herglotzLogIntegrand_circleMap_le {w ρ : ℂ} {R r₀ r : ℝ} (hR : 0 < R)
  (hρ : ‖ρ‖ = R) (hr₀ : 0 < r₀) (hw : ‖w‖ < r₀) (hr₀r : r₀ ≤ r) (hrR : r ≤ R) (θ : ℝ)
  (hdR : 0 < ‖circleMap 0 R θ - ρ‖) :
  ‖herglotzLogIntegrand w ρ (circleMap 0 r θ)‖ ≤ ((R + ‖w‖) / (r₀ - ‖w‖))
    * (|log (2 * R)| + |log (sqrt (r₀ / R))| + |log ‖circleMap 0 R θ - ρ‖|) := by
  simp only [herglotzLogIntegrand, Pi.smul_apply', Function.comp_apply, smul_eq_mul, norm_mul,
    norm_eq_abs]
  have ⟨hrw, hr⟩ : 0 < r₀ - ‖w‖ ∧ 0 < r := by grind
  have h_norm_sub₁ := const_mul_norm_sub_circleMap_le_norm_sub_circleMap hρ hr₀ hR hr₀r hrR θ
  have h_norm_sub₂ : 0 < ‖circleMap 0 r θ - ρ‖ := lt_of_lt_of_le (by positivity) h_norm_sub₁
  gcongr
  · simp only [herglotzRieszKernel_def, sub_zero]
    calc
     |((circleMap 0 r θ + w) / (circleMap 0 r θ - w)).re|
     _ ≤ ‖circleMap 0 r θ + w‖ / ‖circleMap 0 r θ - w‖ := by grw [Complex.abs_re_le_norm, norm_div]
     _ ≤ (r + ‖w‖) / (r - ‖w‖) := by
        grw [norm_add_le, ← norm_sub_norm_le]
        all_goals simp only [norm_circleMap_zero, abs_of_pos hr]; grind
      _ ≤ (R + ‖w‖) / (r₀ - ‖w‖) := by gcongr
  · apply abs_le.mpr ⟨_, _⟩
    · have h_log_lower_bound :
          log ‖circleMap 0 r θ - ρ‖ ≥ log (sqrt (r₀ / R)) + log ‖circleMap 0 R θ - ρ‖ := by
        rw [← log_mul (by positivity) (by positivity)]
        gcongr
      grind
    · calc log ‖circleMap 0 r θ - ρ‖
      _ ≤ |log (2 * R)| + 0 + 0 := by
        grw [← le_abs_self, norm_sub_le, hρ, two_mul, norm_circleMap_zero, abs_of_pos hr, hrR]
        simp
      _ ≤ |log (2 * R)| + |log √(r₀ / R)| + |log ‖circleMap 0 R θ - ρ‖| := by
        gcongr <;> positivity

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Dominated convergence
-- theorem: circle average can be computed by a sequence of circle averages integrating over circles
-- in the interior
private theorem herglotzLogIntegrand_circleAverage_tendsto {ρ w : ℂ} {R : ℝ} (hR : 0 < R)
    (hρ : ‖ρ‖ = R) (hw : ‖w‖ < R) {r : ℕ → ℝ} (hr_lt : ∀ n, r n < R)
    (hr_tendsto : Tendsto r atTop (nhds R)) :
    Tendsto (fun n ↦ circleAverage (herglotzLogIntegrand w ρ) 0 (r n)) atTop
      (nhds (circleAverage (herglotzLogIntegrand w ρ) 0 R)) := by
  -- Apply the dominated convergence theorem.
  let bound := fun θ ↦ ((R + ‖w‖) / ((R + ‖w‖) / 2 - ‖w‖)) * (|log (2 * R)|
    + |log (sqrt ((R + ‖w‖) / 2 / R))| + |log ‖circleMap 0 R θ - ρ‖|)
  apply Filter.Tendsto.smul tendsto_const_nhds _
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
  · -- The herglotzLogIntegrand is AEStronglyMeasurable
    filter_upwards [hr_tendsto.eventually (lt_mem_nhds hw)] with n hn
    exact continuous_herglotzLogIntegrand_circle hρ (hr_lt n) hn |>.aestronglyMeasurable
  · -- Pointwise boundedness outside a null set
    filter_upwards [hr_tendsto.eventually (le_mem_nhds (by linarith : (R + ‖w‖) / 2 < R))] with n hn
    have h_bound {θ : ℝ} :
        ‖herglotzLogIntegrand w ρ (circleMap 0 (r n) θ)‖ ≤ bound θ ∨ ‖circleMap 0 R θ - ρ‖ = 0 := by
      refine Classical.or_iff_not_imp_right.mpr fun h ↦ ?_
      apply norm_herglotzLogIntegrand_circleMap_le hR hρ (by positivity) (by linarith) hn
        (hr_lt n).le
      simpa using h
    apply measure_mono_null (t := {θ | ‖circleMap 0 R θ - ρ‖ = 0}) (by grind)
    simpa [sub_eq_zero] using
      (countable_singleton ρ).preimage_circleMap 0 (hR.ne') |>.measure_zero _
  · -- IntervalIntegrable bound volume 0 (2 * π)
    apply (IntervalIntegrable.add (by simp) (by continuity)).add ?_ |>.const_mul
    exact .abs <| MeromorphicOn.circleIntegrable_log_norm (f := fun z ↦ z - ρ) (by intro; fun_prop)
  · -- Pointwise convergence outside a null set
    have h_measure_zero : volume {θ : ℝ | circleMap 0 R θ = w ∨ circleMap 0 R θ = ρ} = 0 :=
      countable_singleton w |>.preimage_circleMap 0 (hR.ne') |>.union
        ((countable_singleton ρ).preimage_circleMap 0 (hR.ne')) |>.measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h_measure_zero] with θ hθ _
    apply (continuousAt_herglotzLogIntegrand (by tauto) (by tauto)).tendsto.comp
    exact tendsto_const_nhds.add <|
      (Complex.continuous_ofReal.continuousAt.tendsto.comp hr_tendsto).mul tendsto_const_nhds

-- Auxiliary lemma for `circleAverage_re_herglotzRieszKernel_mul_log`. Statement in case where the
-- center equals zero.
theorem circleAverage_re_herglotzRieszKernel_mul_log₀ {w ρ : ℂ} {R : ℝ} (hρ : ρ ∈ sphere 0 R)
    (hw : w ∈ ball 0 R) :
    circleAverage ((Complex.re ∘ herglotzRieszKernel 0 w) • (log ‖· - ρ‖)) (0 : ℂ) R
      = log ‖w - ρ‖ := by
  have hR : 0 < R := pos_of_mem_ball hw
  rw [mem_sphere_iff_norm, sub_zero] at hρ
  rw [mem_ball_iff_norm, sub_zero] at hw
  let r : ℕ → ℝ := fun n ↦ R - (R - ‖w‖) / (n + 2)
  have hr_lt (n : ℕ) : r n < R := by
    simp_all only [sub_lt_self_iff, sub_pos, div_pos_iff_of_pos_left, r]
    positivity
  have hr_pos (n : ℕ) : 0 < r n := by
    simp_all only [sub_lt_self_iff, sub_pos, div_pos_iff_of_pos_left, r]
    apply (div_lt_iff₀ (by linarith)).2
    calc R - ‖w‖
      _ ≤ R * 1 := by aesop
      _ < R * (n + 2) := by gcongr; grind
  have hr_tendsto : Tendsto r atTop (nhds R) :=
    sub_zero R ▸ (tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <|
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have DCT := herglotzLogIntegrand_circleAverage_tendsto hR hρ hw hr_lt hr_tendsto
  have {n : ℕ} : circleAverage (herglotzLogIntegrand w ρ) 0 (r n) = log ‖w - ρ‖ := by
    unfold herglotzLogIntegrand
    apply InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul
    · refine ⟨fun z hz ↦ ?_, fun x hx ↦ ?_⟩
      · exact AnalyticAt.harmonicAt_log_norm (by fun_prop) (by grind [mem_ball, dist_zero_right])
      · suffices ‖x - ρ‖ ≠ 0 by fun_prop (disch := assumption)
        suffices x ≠ ρ by simpa [sub_eq_zero]
        have key := by simpa using closure_ball_subset_closedBall hx
        grind
    · simp only [mem_ball, dist_zero_right, lt_sub_iff_add_lt, r]
      field_simp
      calc ‖w‖ * (n + 2) + (R - ‖w‖) = ‖w‖ * (n + 1) + R := by ring
        _ < R * (n + 1) + R := by gcongr
        _ = R * (n + 2) := by ring
  aesop

/--
Analogue of the **Poisson Integral Formula** for the circle average function `log ‖· - ρ‖` along the
circle with radius `‖ρ‖`.

- See `InnerProductSpace.HarmonicContOnCl.circleAverage_re_herglotzRieszKernel_smul` in the file
  `Mathlib/Analysis/Complex/Harmonic/Poisson` for the classic Poisson Integral Formula, for harmonic
  functions without logarithmic poles.

- See `MeromorphicOn.extract_zeros_poles` in the file
  `Mathlib/Analysis/Meromorphic/FactorizedRational` for a construction that splits factors of the
  form `· - ρ` off arbitrary meromorphic functions.
-/
theorem circleAverage_re_herglotzRieszKernel_mul_log {w ρ c : ℂ} {R : ℝ} (hρ : ρ ∈ sphere c R)
    (hw : w ∈ ball c R) :
    circleAverage ((Complex.re ∘ herglotzRieszKernel c w) * (log ‖· - ρ‖)) c R = log ‖w - ρ‖ := by
  simp only [← circleAverage_map_add_const, Pi.mul_apply, Function.comp_apply, add_zero]
  conv =>
    left; arg 1
    intro z
    rw [(by ring : (z + 0 + c) - ρ = z - (ρ - c))]
    arg 1; arg 1
    rw [add_zero, herglotzRieszKernel_add_const c w z]
  have : (fun z ↦ (herglotzRieszKernel 0 (w - c) z).re * log ‖z - (ρ - c)‖) =
    (Complex.re ∘ herglotzRieszKernel 0 (w - c)) • (log ‖· - (ρ - c)‖) := by rfl
  rw [this, circleAverage_re_herglotzRieszKernel_mul_log₀ (by simp_all)
    (by simp_all [mem_ball_iff_norm.1 hw])]
  simp

/--
Let `D : ℂ → ℤ` be a function with locally finite support within the closed ball with center `c` and
radius `R`, such as the zero- and pole divisor of a meromorphic function.  Then, the circle average
of the function `∑ᶠ u, (D u * log ‖· - u‖)` over the boundary of the ball equals
`∑ᶠ u, D u * log R`.
-/
@[simp]
lemma circleAverage_log_norm_factorizedRational {R : ℝ} {c : ℂ}
    (D : Function.locallyFinsuppWithin (closedBall c |R|) ℤ) :
    circleAverage (∑ᶠ u, (D u * log ‖· - u‖)) c R = ∑ᶠ u, D u * log R := by
  have h := D.finiteSupport (isCompact_closedBall c |R|)
  calc circleAverage (∑ᶠ u, (D u * log ‖· - u‖)) c R
  _ = circleAverage (∑ u ∈ h.toFinset, (D u * log ‖· - u‖)) c R := by
    rw [finsum_eq_sum_of_support_subset]
    intro u
    contrapose
    aesop
  _ = ∑ i ∈ h.toFinset, circleAverage (fun x ↦ D i * log ‖x - i‖) c R := by
    rw [circleAverage_sum]
    intro u hu
    apply IntervalIntegrable.const_mul
    apply (analyticOnNhd_id.sub analyticOnNhd_const).meromorphicOn.circleIntegrable_log_norm
  _ = ∑ u ∈ h.toFinset, D u * log R := by
    apply Finset.sum_congr rfl
    intro u hu
    simp_rw [← smul_eq_mul, circleAverage_fun_smul]
    congr
    rw [circleAverage_log_norm_sub_const_of_mem_closedBall]
    apply D.supportWithinDomain
    simp_all
  _ = ∑ᶠ u, D u * log R := by
    rw [finsum_eq_sum_of_support_subset]
    intro u
    aesop

/--
If  `g : ℂ → ℂ` is analytic without zero on the closed ball with center `c` and radius `R`, then the
circle average `circleAverage (log ‖g ·‖) c R` equals `log ‖g c‖`.
-/
@[simp]
lemma AnalyticOnNhd.circleAverage_log_norm_of_ne_zero {R : ℝ} {c : ℂ} {g : ℂ → ℂ}
    (h₁g : AnalyticOnNhd ℂ g (closedBall c |R|)) (h₂g : ∀ u ∈ closedBall c |R|, g u ≠ 0) :
    circleAverage (Real.log ‖g ·‖) c R = Real.log ‖g c‖ :=
  HarmonicOnNhd.circleAverage_eq (fun x hx ↦ (h₁g x hx).harmonicAt_log_norm (h₂g x hx))

/--
Reformulation of a finsum that appears in Jensen's formula and in the definition of the counting
function of Value Distribution Theory, as discussed in
`Mathlib/Analysis/Complex/ValueDistribution/CountingFunction.lean`.
-/
lemma countingFunction_finsum_eq_finsum_add {c : ℂ} {R : ℝ} {D : ℂ → ℤ} (hR : R ≠ 0)
    (hD : D.HasFiniteSupport) :
    ∑ᶠ u, D u * (log R - log ‖c - u‖) = ∑ᶠ u, D u * log (R * ‖c - u‖⁻¹) + D c * log R := by
  by_cases h : c ∈ D.support
  · have {g : ℂ → ℝ} : (fun u ↦ D u * g u).support ⊆ hD.toFinset :=
      fun x ↦ by simp +contextual
    simp only [finsum_eq_sum_of_support_subset _ this,
      Finset.sum_eq_sum_diff_singleton_add ((Set.Finite.mem_toFinset hD).mpr h), sub_self,
      norm_zero, log_zero, sub_zero, inv_zero, mul_zero, add_zero, add_left_inj]
    refine Finset.sum_congr rfl fun x hx ↦ ?_
    simp only [Finset.mem_sdiff, Finset.notMem_singleton] at hx
    rw [log_mul hR (inv_ne_zero (norm_ne_zero_iff.mpr (sub_eq_zero.not.2 hx.2.symm))), log_inv]
    ring
  · simp_all only [Function.mem_support, Decidable.not_not, Int.cast_zero, zero_mul, add_zero]
    refine finsum_congr fun x ↦ ?_
    by_cases h₁ : c = x
    · simp_all
    · rw [log_mul hR (inv_ne_zero (norm_ne_zero_iff.mpr (sub_eq_zero.not.2 h₁))), log_inv]
      ring

/-!
## Jensen's Formula
-/

/--
**Jensen's Formula**: If `f : ℂ → ℂ` is meromorphic on the closed ball with center `c` and radius
`R`, then the `circleAverage (log ‖f ·‖) c R` equals `log ‖meromorphicTrailingCoeffAt f c‖` plus a
correction term that accounts for the zeros and poles of `f` within the ball.

See `Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const` for a
reformulation in terms of the logarithmic counting function of Value Distribution Theory.
-/
theorem MeromorphicOn.circleAverage_log_norm {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0)
    (h₁f : MeromorphicOn f (closedBall c |R|)) :
    circleAverage (log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) u * log (R * ‖c - u‖⁻¹)
        + divisor f (closedBall c |R|) c * log R + log ‖meromorphicTrailingCoeffAt f c‖ := by
  -- Shorthand notation to keep line size in check
  let CB := closedBall c |R|
  by_cases h₂f : ∀ u ∈ CB, meromorphicOrderAt f u ≠ ⊤
  · have h₃f := (divisor f CB).finiteSupport (isCompact_closedBall c |R|)
    -- Extract zeros & poles and compute
    obtain ⟨g, h₁g, h₂g, h₃g⟩ := h₁f.extract_zeros_poles (by simp_all) h₃f
    calc circleAverage (log ‖f ·‖) c R
    _ = circleAverage ((∑ᶠ u, (divisor f CB u * log ‖· - u‖)) + (log ‖g ·‖)) c R := by
      have h₄g := extract_zeros_poles_log h₂g h₃g
      rw [circleAverage_congr_codiscreteWithin (codiscreteWithin.mono sphere_subset_closedBall h₄g)
        hR]
    _ = circleAverage (∑ᶠ u, (divisor f CB u * log ‖· - u‖)) c R + circleAverage (log ‖g ·‖) c R :=
      circleAverage_add (circleIntegrable_log_norm_factorizedRational (divisor f CB))
        ((h₁g.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm)
    _ = ∑ᶠ u, divisor f CB u * log R + log ‖g c‖ := by
      simp only [circleAverage_log_norm_factorizedRational, add_right_inj]
      rw [h₁g.circleAverage_log_norm_of_ne_zero]
      exact fun u hu ↦ h₂g ⟨u, hu⟩
    _ = ∑ᶠ u, divisor f CB u * log R
      + (log ‖meromorphicTrailingCoeffAt f c‖ - ∑ᶠ u, divisor f CB u * log ‖c - u‖) := by
      have t₀ : c ∈ CB := by simp [CB]
      have t₁ : AccPt c (𝓟 CB) := by
        apply accPt_iff_frequently_nhdsNE.mpr
        apply compl_notMem
        apply mem_nhdsWithin.mpr
        use ball c |R|
        simpa [hR] using fun _ ⟨h, _⟩ ↦ ball_subset_closedBall h
      simp [MeromorphicOn.log_norm_meromorphicTrailingCoeffAt_extract_zeros_poles h₃f t₀ t₁
        (h₁f c t₀) (h₁g c t₀) (h₂g ⟨c, t₀⟩) h₃g]
    _ = ∑ᶠ u, divisor f CB u * log R - ∑ᶠ u, divisor f CB u * log ‖c - u‖
      + log ‖meromorphicTrailingCoeffAt f c‖ := by
      ring
    _ = (∑ᶠ u, divisor f CB u * (log R - log ‖c - u‖)) + log ‖meromorphicTrailingCoeffAt f c‖ := by
      rw [← finsum_sub_distrib]
      · simp_rw [← mul_sub]
      repeat apply h₃f.subset (fun _ ↦ (by simp_all))
    _ = ∑ᶠ u, divisor f CB u * log (R * ‖c - u‖⁻¹) + divisor f CB c * log R
      + log ‖meromorphicTrailingCoeffAt f c‖ := by
      rw [countingFunction_finsum_eq_finsum_add hR h₃f]
  · -- Trivial case: `f` vanishes on a codiscrete set
    have h₂f : ¬∀ (u : ↑(closedBall c |R|)), meromorphicOrderAt f ↑u ≠ ⊤ := by aesop
    rw [← h₁f.exists_meromorphicOrderAt_ne_top_iff_forall
      ⟨nonempty_closedBall.mpr (abs_nonneg R), (convex_closedBall c |R|).isPreconnected⟩] at h₂f
    push Not at h₂f
    have : divisor f CB = 0 := by
      ext x
      by_cases h : x ∈ CB
      <;> simp_all [CB]
    simp only [CB, this, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply, Int.cast_zero,
      zero_mul, finsum_zero, add_zero, zero_add]
    rw [MeromorphicAt.meromorphicTrailingCoeffAt_of_order_eq_top (by aesop), norm_zero, log_zero]
    have : f =ᶠ[codiscreteWithin CB] 0 := by
      filter_upwards [h₁f.meromorphicNFAt_mem_codiscreteWithin, self_mem_codiscreteWithin CB]
        with z h₁z h₂z
      simpa [h₂f ⟨z, h₂z⟩] using (not_iff_not.2 h₁z.meromorphicOrderAt_eq_zero_iff)
    rw [circleAverage_congr_codiscreteWithin (f₂ := 0) _ hR]
    · simp only [circleAverage, mul_inv_rev, Pi.zero_apply, intervalIntegral.integral_zero,
        smul_eq_mul, mul_zero]
    apply Filter.codiscreteWithin.mono (U := CB) sphere_subset_closedBall
    filter_upwards [this] with z hz
    simp_all

/-- **Jensen's Formula** specialized to the case that `f` is analytic and `f c ≠ 0`. -/
theorem AnalyticOnNhd.circleAverage_log_norm {c : ℂ} {R : ℝ} {f : ℂ → ℂ} (hR : R ≠ 0)
    (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|))
    (h₂f : f c ≠ 0) :
    circleAverage (Real.log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) u * Real.log (R * ‖c - u‖⁻¹) + Real.log ‖f c‖ := by
  rw [h₁f.meromorphicOn.circleAverage_log_norm hR, h₁f.divisor_apply (by simp),
    (h₁f c (by simp)).analyticOrderAt_eq_zero.mpr h₂f,
    (h₁f c (by simp)).meromorphicTrailingCoeffAt_of_ne_zero h₂f]
  simp

/--
**Jensen's Inequality**: Estimates the number of zeros of `f` in a ball of radius `r`
given that `f` is analytic and bounded by `M` on a larger ball of radius `R`.
-/
theorem AnalyticOnNhd.sum_divisor_le {c : ℂ} {r R M : ℝ} {f : ℂ → ℂ} (r_pos : 0 < |r|)
    (r_lt_R : |r| < |R|) (hM : 1 ≤ M) (h₁f : AnalyticOnNhd ℂ f (closedBall c |R|))
    (h₂f : f c ≠ 0)
    (f_bound : ∀ z ∈ sphere c |R|, ‖f z‖ ≤ M) :
    ∑ᶠ u, divisor f (closedBall c |r|) u ≤ Real.log (M / ‖f c‖) / Real.log (R / r) := by
  -- Push the coerssion inside the sum
  trans ∑ᶠ u, (divisor f (closedBall c |r|) u : ℝ)
  · exact map_finsum (Int.castRingHom ℝ)
      ((divisor _ _).finiteSupport <| isCompact_closedBall ..) |>.le
  -- Rearrange: move `log R/r` to the LHS and inside the sum.
  have hrR : 1 < |R / r| := by simpa [abs_div, one_lt_div r_pos]
  suffices ∑ᶠ u, divisor f (closedBall c |r|) u * Real.log (R / r) ≤ Real.log (M / ‖f c‖) by
    rwa [← finsum_mul, ← le_div_iff₀] at this
    simpa using log_pos hrR
  have jensen := h₁f.circleAverage_log_norm (abs_ne_zero.mp (by linarith)) h₂f
  -- Estimate the circleAverage using the bound on f
  have integral_bound : circleAverage (fun x ↦ Real.log ‖f x‖) c R ≤ Real.log M := by
    apply circleAverage_mono_on_of_le_circle
    · exact (h₁f.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    · peel f_bound with z hz _
      obtain (h | h) := eq_zero_or_norm_pos (f z)
      · simpa [h] using log_nonneg hM
      · gcongr
  calc
  -- Bound by the sum from Jensen's formula
  _ ≤ ∑ᶠ u, ((divisor f (closedBall c |R|)) u) * Real.log (R * ‖c - u‖⁻¹) := by
    refine finsum_le_finsum' ?_ ?_ fun u ↦ ?_
    · exact (divisor f (closedBall c |r|)).finiteSupport (isCompact_closedBall ..) |>.subset
        fun _ _ ↦ (by simp_all)
    · exact (divisor f (closedBall c |R|)).finiteSupport (isCompact_closedBall ..) |>.subset
        fun _ _ ↦ (by simp_all)
    · -- Core bound: estimate the summand by splitting on which ball u is in
      by_cases h1 : u ∈ closedBall c |R|
      · by_cases h2 : u ∈ closedBall c |r|
        · --In the smaller ball: the divisors agree and we bound the log factor
          simp only [(h₁f.mono (closedBall_subset_closedBall r_lt_R.le)), h2,
            AnalyticOnNhd.divisor_apply, h₁f, h1]
          by_cases! h3 : u = c --Need to use the divisor is 0 at c rather than comparing the logs
          · rw [h3, (h₁f c (by simp)).analyticOrderAt_eq_zero.mpr h₂f]
            simp
          simp +singlePass only [← log_abs]
          gcongr 2
          · simp
          · have : ‖c - u‖ ≠ 0 := by simpa [sub_eq_zero] using h3.symm
            simpa [field, abs_div, r_pos.trans r_lt_R, dist_eq_norm'] using h2
        · --In the larger ball but not the smaller so LHS is 0 and RHS nonnegative
          simp only [h2, not_false_eq_true, Function.locallyFinsuppWithin.apply_eq_zero_of_notMem,
            Int.cast_zero, zero_mul]
          refine mul_nonneg (mod_cast h₁f.divisor_nonneg ..) ?_
          apply log_abs _ ▸ log_nonneg
          simp only [mem_closedBall, dist_eq_norm', not_le] at h1 h2
          have : ‖c - u‖ ≠ 0 := (r_pos.trans h2).ne'
          simpa [field]
      · --Outside the larger ball so both sides are 0
        have : u ∉ closedBall c |r| := by
          simp_all
          linarith
        simp [h1, this]
  _ ≤ Real.log M - Real.log ‖f c‖ := by linarith --Uses jensen and integral_bound
  _ = _ := by rw [← log_div (by linarith) (norm_ne_zero_iff.mpr h₂f)]
