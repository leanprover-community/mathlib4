/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
module

public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# The Hardy–Littlewood maximal function

The (centered) Hardy–Littlewood maximal function of a function `f` on a
normed space `E` over `ℝ`, with respect to a measure `μ`, is

`maximalFunction μ f x = sup over r > 0 of the average of ‖f‖ over ball x r`.

It is valued in `ℝ≥0∞`, the averages being taken with `laverage`.
This file sets up the definition and its basic API, and proves that
the maximal function of a locally integrable function is measurable,
via continuity (hence lower semicontinuity) of ball averages. The
Hardy–Littlewood maximal inequalities (weak type `(1, 1)` via the
Besicovitch covering theorem, and strong type `(p, p)`) are developed
separately.
-/

public section

open MeasureTheory ENNReal Metric Filter Topology

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
  {F : Type*} [SeminormedAddCommGroup F]


/-- The centered Hardy–Littlewood maximal function of `f` with respect to
the measure `μ`: at each point `x`, the supremum over all radii `r > 0` of
the average of `‖f‖` over the ball of radius `r` centered at `x`. -/
noncomputable def maximalFunction (μ : Measure E) (f : E → F) (x : E) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), ⨍⁻ y in Metric.ball x r, ‖f y‖ₑ ∂μ

theorem maximalFunction_zero (μ : Measure E) :
    maximalFunction μ (0 : E → F) = 0 := by
  funext x
  simp [maximalFunction]

theorem maximalFunction_congr_ae {μ : Measure E} {f g : E → F}
    (h : f =ᵐ[μ] g) : maximalFunction μ f = maximalFunction μ g := by
  funext x
  refine iSup_congr fun r => iSup_congr fun _ => ?_
  exact laverage_congr ((h.filter_mono ae_restrict_le).mono fun y hy => by
    change ‖f y‖ₑ = ‖g y‖ₑ
    rw [hy])

theorem maximalFunction_mono {μ : Measure E} {f g : E → F}
    (h : ∀ x, ‖f x‖ ≤ ‖g x‖) (x : E) :
    maximalFunction μ f x ≤ maximalFunction μ g x := by
  refine iSup_mono fun r => iSup_mono fun _ => ?_
  refine laverage_mono_ae (Filter.Eventually.of_forall fun y => ?_)
  change ‖f y‖ₑ ≤ ‖g y‖ₑ
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (h y)

/-- Working abbreviation for B2: the average of `‖f‖` over `ball x r`. -/
noncomputable def ballAverage (μ : Measure E) (f : E → F) (r : ℝ) (x : E) : ℝ≥0∞ :=
  ⨍⁻ y in Metric.ball x r, ‖f y‖ₑ ∂μ

/-- [GLUE] `maximalFunction` is the supremum of the ball averages. -/
theorem maximalFunction_eq_iSup_ballAverage (μ : Measure E) (f : E → F) (x : E) :
    maximalFunction μ f x = ⨆ (r : ℝ) (_ : 0 < r), ballAverage μ f r x := by
  simp only [maximalFunction, ballAverage]

variable [BorelSpace E]

/-- [GLUE] The translation identity for set integrals over balls, for a
Haar measure: integrating over `ball x r` is integrating the translated
function over the fixed `ball 0 r`. -/
theorem lintegral_ball_translate (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] (F : E → ℝ≥0∞) (r : ℝ) (x : E) :
    ∫⁻ y in Metric.ball x r, F y ∂μ
      = ∫⁻ z in Metric.ball 0 r, F (z + x) ∂μ := by
  have hpt : ∀ z, (Metric.ball x r).indicator F (x + z)
      = (Metric.ball 0 r).indicator (fun z => F (z + x)) z := by
    intro z
    by_cases hz : z ∈ Metric.ball 0 r
    · have hx : x + z ∈ Metric.ball x r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hz, add_comm]
    · have hx : x + z ∉ Metric.ball x r := by
        simpa [Metric.mem_ball, dist_eq_norm] using hz
      rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hz]
  rw [← lintegral_indicator Metric.isOpen_ball.measurableSet,
    ← lintegral_indicator Metric.isOpen_ball.measurableSet,
    ← lintegral_add_left_eq_self ((Metric.ball x r).indicator F) x]
  exact lintegral_congr_ae (Filter.Eventually.of_forall hpt)

/-- [GLUE] Route B change of variables: for a Haar measure the average
over `ball x r` is the average over the FIXED ball `ball 0 r` of the
translated function, and the normalizing factor does not depend on `x`
(it is the `F = 1` case of `lintegral_ball_translate`). -/
theorem ballAverage_translate (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] (f : E → F)
    (r : ℝ) (x : E) :
    ballAverage μ f r x
      = (∫⁻ z in Metric.ball 0 r, ‖f (z + x)‖ₑ ∂μ) / μ (Metric.ball 0 r) := by
  have hden : μ (Metric.ball x r) = μ (Metric.ball 0 r) := by
    have h := lintegral_ball_translate μ (fun _ => 1) r x
    simpa [lintegral_const] using h
  unfold ballAverage
  rw [laverage_eq, Measure.restrict_apply_univ,
    lintegral_ball_translate μ (fun y => ‖f y‖ₑ) r x, hden]

-- From Step 1 on, the target is a normed space over `ℝ`: the `Lp`
-- density API (`BoundedContinuousFunction.toLp_denseRange`) is stated
-- for normed targets, and the cutoff argument multiplies by real
-- scalars. Steps 2 and the glue above only need a seminormed target.
variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Step 1 (David's architecture): approximation on the fixed compact
`closedBall x₀ (r + 1)`. Derivation: BCF density in L¹ of the restricted
(finite, weakly regular) measure on `closedBall x₀ (r + 2)`, bridge to
`∫⁻` of the enorm, then cut off by `max 0 (1 - infDist · K₁)`, which is
`1` on `K₁ = closedBall x₀ (r + 1)` and supported in `K₂`. The
hypothesis lives on `r + 2` because the cutoff needs the shell
`r + 1 < dist < r + 2` to fall in (David's adjustment, 2026-11-26). -/
theorem exists_continuous_approx (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {f : E → F} {x₀ : E} {r : ℝ}
    (hr : 0 < r)
    (hf : IntegrableOn f (Metric.closedBall x₀ (r + 2)) μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g : E → F, Continuous g ∧ HasCompactSupport g ∧
      ∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ < ε := by
  set K₁ := Metric.closedBall x₀ (r + 1) with hK₁def
  set K₂ := Metric.closedBall x₀ (r + 2) with hK₂def
  have hK₂lt : μ K₂ < ∞ := (isCompact_closedBall x₀ (r + 2)).measure_lt_top
  have hK₂fin : μ K₂ ≠ ∞ := hK₂lt.ne
  have : IsFiniteMeasure (μ.restrict K₂) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have : (μ.restrict K₂).WeaklyRegular :=
    MeasureTheory.Measure.WeaklyRegular.restrict_of_measure_ne_top hK₂fin
  have : Fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩
  obtain ⟨δ, hδpos, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
    by_cases hεtop : ε = ∞
    · exact ⟨1, one_pos, by simp [hεtop]⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε hεtop, by rw [ENNReal.ofReal_toReal hεtop]⟩
  have hfMem : MemLp f 1 (μ.restrict K₂) := memLp_one_iff_integrable.mpr hf
  obtain ⟨g, hgδ⟩ : ∃ g : BoundedContinuousFunction E F,
      ‖hfMem.toLp f - BoundedContinuousFunction.toLp 1 (μ.restrict K₂) ℝ g‖ < δ := by
    have hd := BoundedContinuousFunction.toLp_denseRange F (μ.restrict K₂) ℝ
      (p := 1) ENNReal.one_ne_top
    have hmem : hfMem.toLp f ∈ closure
        (Set.range (BoundedContinuousFunction.toLp 1 (μ.restrict K₂) ℝ)) := by
      rw [hd.closure_range]; trivial
    obtain ⟨y, hy, hdist⟩ := (Metric.mem_closure_iff.mp hmem) δ hδpos
    obtain ⟨g, rfl⟩ := hy
    exact ⟨g, by rwa [dist_eq_norm] at hdist⟩
  have hnorm : eLpNorm (fun y => f y - g y) 1 (μ.restrict K₂)
      = ENNReal.ofReal ‖hfMem.toLp f
          - BoundedContinuousFunction.toLp 1 (μ.restrict K₂) ℝ g‖ := by
    have h1 : eLpNorm (fun y => f y - g y) 1 (μ.restrict K₂)
        = eLpNorm (hfMem.toLp f
            - BoundedContinuousFunction.toLp 1 (μ.restrict K₂) ℝ g)
          1 (μ.restrict K₂) := by
      refine eLpNorm_congr_ae ?_
      exact ((hfMem.coeFn_toLp).sub
        (BoundedContinuousFunction.coeFn_toLp 1 (μ.restrict K₂) ℝ g)).symm.trans
        (Lp.coeFn_sub _ _).symm
    rw [h1, ← ENNReal.ofReal_toReal (Lp.memLp _).eLpNorm_lt_top.ne, Lp.norm_def]
  -- the cutoff: 1 on K₁, supported in K₂
  set φ : E → ℝ := fun y => max 0 (1 - Metric.infDist y K₁) with hφdef
  have hφcont : Continuous φ :=
    Continuous.max continuous_const
      (continuous_const.sub (Metric.continuous_infDist_pt K₁))
  have hφ1 : ∀ y ∈ K₁, φ y = 1 := by
    intro y hy
    simp [hφdef, Metric.infDist_zero_of_mem hy]
  set gcut : E → F := fun y => φ y • g y with hgcutdef
  have hgcutcont : Continuous gcut := hφcont.smul g.continuous
  have hgcutsupp : HasCompactSupport gcut := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall x₀ (r + 2))
      (isClosed_tsupport gcut) (closure_minimal ?_ Metric.isClosed_closedBall)
    intro y hy
    rw [Function.mem_support] at hy
    have hφy : φ y ≠ 0 := by
      intro h
      exact hy (by simp [hgcutdef, h])
    have hlt : Metric.infDist y K₁ < 1 := by
      by_contra hcon
      push Not at hcon
      exact hφy (by simp [hφdef, sub_nonpos.mpr hcon])
    obtain ⟨z, hzK₁, hzy⟩ := (Metric.infDist_lt_iff
      ⟨x₀, by rw [hK₁def]; exact Metric.mem_closedBall_self (by linarith)⟩).mp hlt
    rw [Metric.mem_closedBall]
    calc dist y x₀ ≤ dist y z + dist z x₀ := dist_triangle y z x₀
      _ ≤ 1 + (r + 1) := add_le_add (le_of_lt hzy)
          (by rwa [hK₁def, Metric.mem_closedBall] at hzK₁)
      _ = r + 2 := by ring
  refine ⟨gcut, hgcutcont, hgcutsupp, ?_⟩
  calc ∫⁻ y in K₁, ‖f y - gcut y‖ₑ ∂μ
      = ∫⁻ y in K₁, ‖f y - g y‖ₑ ∂μ := by
        refine lintegral_congr_ae ?_
        refine Set.EqOn.aeEq_restrict (s := K₁) (μ := μ) ?_
          (Metric.isClosed_closedBall.measurableSet)
        intro y hy
        rw [hgcutdef]
        simp [hφ1 y hy]
    _ ≤ ∫⁻ y in K₂, ‖f y - g y‖ₑ ∂μ := by
        refine lintegral_mono_set ?_
        intro y hy
        rw [hK₁def, Metric.mem_closedBall] at hy
        rw [hK₂def, Metric.mem_closedBall]
        linarith
    _ = eLpNorm (fun y => f y - g y) 1 (μ.restrict K₂) :=
        (eLpNorm_one_eq_lintegral_eNorm
          (hfMem.aestronglyMeasurable.sub g.continuous.aestronglyMeasurable)).symm
    _ = ENNReal.ofReal ‖hfMem.toLp f
          - BoundedContinuousFunction.toLp 1 (μ.restrict K₂) ℝ g‖ := hnorm
    _ < ENNReal.ofReal δ :=
        (ENNReal.ofReal_lt_ofReal_iff hδpos).mpr hgδ
    _ ≤ ε := hδε

omit [NormedSpace ℝ F] in
/-- Step 2, route B (David's mathematics): continuity of the average for
continuous compactly supported `g`. Via `ballAverage_translate` the
domain and the normalizing factor are fixed; the integrand
`z ↦ ‖g (z + x)‖ₑ` converges pointwise as `x → x₀` (continuity of `g`
and of the enorm), and is dominated by the constant `ofReal C` where
`C` bounds `‖g‖` (compact support); conclude by the filter form of
dominated convergence, `tendsto_lintegral_filter_of_dominated_convergence'`,
and `ENNReal.Tendsto.const_mul` for the constant normalizing factor. -/
theorem continuousAt_ballAverage_of_continuous (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {g : E → F} (hg : Continuous g)
    (hgc : HasCompactSupport g) {r : ℝ} (hr : 0 < r) (x₀ : E) :
    ContinuousAt (ballAverage μ g r) x₀ := by
  have hK : IsCompact (tsupport g) := hgc
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z, ‖g z‖ ≤ C := by
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ tsupport g
    · exact le_trans (hC z hz) (le_max_left _ _)
    · have hgz : g z = 0 := by
        by_contra hne
        exact hz (subset_tsupport _ (Function.mem_support.mpr hne))
      rw [hgz]
      simp only [norm_zero]
      exact le_max_right C 0
  have hfin : μ (Metric.ball (0 : E) r) ≠ ∞ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0 : E) r).measure_lt_top.ne
      (measure_mono Metric.ball_subset_closedBall)
  have hInt : Filter.Tendsto (fun x => ∫⁻ z in Metric.ball 0 r, ‖g (z + x)‖ₑ ∂μ)
      (𝓝 x₀) (𝓝 (∫⁻ z in Metric.ball 0 r, ‖g (z + x₀)‖ₑ ∂μ)) := by
    refine tendsto_lintegral_filter_of_dominated_convergence' (fun _ => ENNReal.ofReal C)
      (Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall fun z => ?_)
      ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (ContinuousENorm.continuous_eNorm.comp
        (hg.comp (Homeomorph.addRight x).continuous)).aemeasurable
    · rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hC _)
    · rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    · exact (ContinuousENorm.continuous_eNorm.comp
        (hg.comp (Homeomorph.addLeft z).continuous)).tendsto x₀
  have htr : ballAverage μ g r
      = fun x => (∫⁻ z in Metric.ball 0 r, ‖g (z + x)‖ₑ ∂μ)
          / μ (Metric.ball 0 r) :=
    funext fun x => ballAverage_translate μ g r x
  rw [htr]
  have hpos : μ (Metric.ball (0 : E) r) ≠ 0 :=
    ne_of_gt (Metric.isOpen_ball.measure_pos μ (Metric.nonempty_ball.mpr hr))
  have hmul := ENNReal.Tendsto.const_mul hInt (Or.inr (ENNReal.inv_ne_top.mpr hpos))
  change Filter.Tendsto (fun x => (∫⁻ z in Metric.ball 0 r, ‖g (z + x)‖ₑ ∂μ)
      / μ (Metric.ball 0 r)) (𝓝 x₀)
    (𝓝 ((∫⁻ z in Metric.ball 0 r, ‖g (z + x₀)‖ₑ ∂μ) / μ (Metric.ball 0 r)))
  simpa only [ENNReal.div_eq_inv_mul] using hmul

/-- Step 3 (David's mathematics): the squeeze. For `x` within `1` of
`x₀`, `ball x r ⊆ closedBall x₀ (r + 1)`, and pointwise
`‖f‖ₑ ≤ ‖g‖ₑ + ‖f - g‖ₑ` (and symmetrically) with `laverage_mono_ae`
bounds both `ballAverage f x` and `ballAverage f x₀` against
`ballAverage g` up to the fixed error of Step 1; order-topology
characterization of `Tendsto` in `ℝ≥0∞` closes it. -/
theorem continuousAt_ballAverage (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ]
    {f : E → F} {r : ℝ} (hr : 0 < r)
    (x₀ : E) (hf : LocallyIntegrable f μ) :
    ContinuousAt (ballAverage μ f r) x₀ := by
  have hfK₂ : IntegrableOn f (Metric.closedBall x₀ (r + 2)) μ :=
    hf.integrableOn_isCompact (isCompact_closedBall x₀ (r + 2))
  have hc0 : μ (Metric.ball (0 : E) r) ≠ 0 :=
    ne_of_gt (Metric.isOpen_ball.measure_pos μ (Metric.nonempty_ball.mpr hr))
  have hcfin : μ (Metric.ball (0 : E) r) ≠ ∞ :=
    ne_top_of_le_ne_top (isCompact_closedBall (0 : E) r).measure_lt_top.ne
      (measure_mono Metric.ball_subset_closedBall)
  -- One-sided bound: for `x` within `1` of `x₀`, the average of `u` over
  -- `ball x r` is at most the average of `v` plus the fixed `K₁`-error
  -- of `u - v`, over the constant denominator. Pointwise enorm triangle
  -- inequality, `lintegral_mono`, and monotonicity in the set; the only
  -- hypothesis on `v` is the integrability that makes its enorm
  -- a.e. measurable on the small ball.
  have hbound : ∀ u v : E → F, IntegrableOn v (Metric.closedBall x₀ (r + 2)) μ →
      ∀ x : E, dist x x₀ < 1 →
      ballAverage μ u r x ≤ ballAverage μ v r x
        + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖u y - v y‖ₑ ∂μ)
          / μ (Metric.ball 0 r) := by
    intro u v hv x hx
    have hsub : Metric.ball x r ⊆ Metric.closedBall x₀ (r + 1) := by
      intro y hy
      rw [Metric.mem_closedBall]
      exact le_trans (dist_triangle y x x₀)
        (le_of_lt (add_lt_add (Metric.mem_ball.mp hy) hx))
    have hsub₂ : Metric.ball x r ⊆ Metric.closedBall x₀ (r + 2) :=
      hsub.trans (Metric.closedBall_subset_closedBall (by linarith : r + 1 ≤ r + 2))
    have hvm : AEMeasurable (fun y => ‖v y‖ₑ) (μ.restrict (Metric.ball x r)) :=
      (hv.mono_set hsub₂).aestronglyMeasurable.eNorm
    have hInt : ∫⁻ y in Metric.ball x r, ‖u y‖ₑ ∂μ
        ≤ ∫⁻ y in Metric.ball x r, ‖v y‖ₑ ∂μ
          + ∫⁻ y in Metric.closedBall x₀ (r + 1), ‖u y - v y‖ₑ ∂μ := by
      calc ∫⁻ y in Metric.ball x r, ‖u y‖ₑ ∂μ
          ≤ ∫⁻ y in Metric.ball x r, (‖v y‖ₑ + ‖u y - v y‖ₑ) ∂μ := by
            apply lintegral_mono
            intro y
            have h : v y + (u y - v y) = u y := by abel
            calc ‖u y‖ₑ = ‖v y + (u y - v y)‖ₑ := by rw [h]
              _ ≤ ‖v y‖ₑ + ‖u y - v y‖ₑ := eNorm_add_le _ _
        _ = ∫⁻ y in Metric.ball x r, ‖v y‖ₑ ∂μ
            + ∫⁻ y in Metric.ball x r, ‖u y - v y‖ₑ ∂μ :=
            lintegral_add_left' hvm _
        _ ≤ ∫⁻ y in Metric.ball x r, ‖v y‖ₑ ∂μ
            + ∫⁻ y in Metric.closedBall x₀ (r + 1), ‖u y - v y‖ₑ ∂μ :=
            add_le_add le_rfl (lintegral_mono_set hsub)
    rw [lintegral_ball_translate μ (fun y => ‖u y‖ₑ) r x,
      lintegral_ball_translate μ (fun y => ‖v y‖ₑ) r x] at hInt
    rw [ballAverage_translate μ u r x, ballAverage_translate μ v r x]
    simp only [ENNReal.div_eq_inv_mul]
    calc (μ (Metric.ball 0 r))⁻¹ * ∫⁻ z in Metric.ball 0 r, ‖u (z + x)‖ₑ ∂μ
        ≤ (μ (Metric.ball 0 r))⁻¹
            * (∫⁻ z in Metric.ball 0 r, ‖v (z + x)‖ₑ ∂μ
              + ∫⁻ y in Metric.closedBall x₀ (r + 1), ‖u y - v y‖ₑ ∂μ) :=
          mul_le_mul' le_rfl hInt
      _ = (μ (Metric.ball 0 r))⁻¹ * ∫⁻ z in Metric.ball 0 r, ‖v (z + x)‖ₑ ∂μ
            + (μ (Metric.ball 0 r))⁻¹
              * ∫⁻ y in Metric.closedBall x₀ (r + 1), ‖u y - v y‖ₑ ∂μ :=
          mul_add _ _ _
  -- The squeeze, in the `Icc` characterization of convergence in `ℝ≥0∞`.
  apply ENNReal.tendsto_nhds_of_Icc
  intro ε hε
  by_cases hεtop : ε = ∞
  · subst hεtop
    filter_upwards with x
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · rw [tsub_eq_zero_of_le le_top]
      exact bot_le
    · calc ballAverage μ f r x ≤ ∞ := le_top
        _ = ballAverage μ f r x₀ + ∞ := by simp
  · have hε3 : (0 : ℝ≥0∞) < ε / 3 :=
      ENNReal.div_pos (ne_of_gt hε) (by norm_num)
    have hε3fin : ε / 3 ≠ ∞ := ENNReal.div_ne_top hεtop (by norm_num)
    obtain ⟨g, hg, hgc, hD⟩ := exists_continuous_approx μ hr hfK₂
      (ε := μ (Metric.ball 0 r) * (ε / 3))
      (mul_ne_zero hc0 (ne_of_gt hε3))
    have hgK₂ : IntegrableOn g (Metric.closedBall x₀ (r + 2)) μ :=
      (hg.integrable_of_hasCompactSupport hgc).integrableOn
    have hDc : (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
        / μ (Metric.ball 0 r) < ε / 3 := by
      rw [ENNReal.div_lt_iff (Or.inl hc0) (Or.inl hcfin), mul_comm]
      exact hD
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ z, ‖g z‖ ≤ C := by
      obtain ⟨C, hC⟩ := hgc.isCompact.exists_bound_of_continuousOn hg.continuousOn
      refine ⟨max C 0, fun z => ?_⟩
      by_cases hz : z ∈ tsupport g
      · exact le_trans (hC z hz) (le_max_left _ _)
      · have hgz : g z = 0 := by
          by_contra hne
          exact hz (subset_tsupport _ (Function.mem_support.mpr hne))
        rw [hgz]
        simp only [norm_zero]
        exact le_max_right C 0
    have hle : (∫⁻ z in Metric.ball 0 r, ‖g (z + x₀)‖ₑ ∂μ)
        ≤ ∫⁻ _ in Metric.ball 0 r, ENNReal.ofReal C ∂μ :=
      lintegral_mono fun z => by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hC _)
    have hIg₀ : (∫⁻ z in Metric.ball 0 r, ‖g (z + x₀)‖ₑ ∂μ) ≠ ∞ :=
      ne_top_of_le_ne_top (by
        rw [lintegral_const, Measure.restrict_apply_univ]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcfin) hle
    have hAg₀ : ballAverage μ g r x₀ ≠ ∞ := by
      rw [ballAverage_translate μ g r x₀]
      exact ENNReal.div_ne_top hIg₀ hc0
    have hmid := (ENNReal.tendsto_nhds hAg₀).mp
      (continuousAt_ballAverage_of_continuous μ hg hgc hr x₀) (ε / 3) hε3
    have hsum : ε / 3 + ε / 3 + ε / 3 = ε := by
      have h3 : (3 : ℝ≥0∞) ≠ 0 := by norm_num
      have h3' : (3 : ℝ≥0∞) ≠ ∞ := by norm_num
      calc ε / 3 + ε / 3 + ε / 3 = (ε / 3) * 3 := by ring
        _ = ε := ENNReal.div_mul_cancel h3 h3'
    have hDsymm : (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖g y - f y‖ₑ ∂μ)
        = ∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ :=
      lintegral_congr fun y => eNorm_sub_rev _ _
    filter_upwards [Metric.ball_mem_nhds x₀ (show (0 : ℝ) < 1 by norm_num), hmid]
      with x hx hxm
    have hdx : dist x x₀ < 1 := Metric.mem_ball.mp hx
    have hfgx := hbound f g hgK₂ x hdx
    have hfgx₀ := hbound f g hgK₂ x₀ (by simp)
    have hgf : ballAverage μ g r x₀ ≤ ballAverage μ f r x₀
        + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
          / μ (Metric.ball 0 r) := by
      have h := hbound g f hfK₂ x₀ (by simp)
      rwa [hDsymm] at h
    have hgfx : ballAverage μ g r x ≤ ballAverage μ f r x
        + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
          / μ (Metric.ball 0 r) := by
      have h := hbound g f hfK₂ x hdx
      rwa [hDsymm] at h
    have hrearr : ∀ a b c d : ℝ≥0∞, ((a + b) + c) + d = a + ((b + c) + d) :=
      fun a b c d => by rw [add_assoc, add_assoc, add_assoc]
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · -- lower bound: `A f x₀ - ε ≤ A f x`
      have hgx₀ : ballAverage μ g r x₀ ≤ ballAverage μ g r x + ε / 3 := by
        have h := tsub_le_iff_left.mp hxm.1
        rwa [add_comm] at h
      have hchain : ballAverage μ f r x₀ ≤ ballAverage μ f r x + ε := by
        calc ballAverage μ f r x₀
            ≤ ballAverage μ g r x₀
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) := hfgx₀
          _ ≤ (ballAverage μ g r x + ε / 3)
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) := add_le_add_left hgx₀ _
          _ ≤ (ballAverage μ f r x
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) + ε / 3)
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) := add_le_add_left (add_le_add_left hgfx _) _
          _ = ballAverage μ f r x
              + (((∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                  / μ (Metric.ball 0 r) + ε / 3)
                + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                  / μ (Metric.ball 0 r)) := hrearr _ _ _ _
          _ ≤ ballAverage μ f r x + (ε / 3 + ε / 3 + ε / 3) :=
              add_le_add le_rfl (add_le_add (add_le_add hDc.le le_rfl) hDc.le)
          _ = ballAverage μ f r x + ε := by rw [hsum]
      exact tsub_le_iff_right.mpr hchain
    · -- upper bound: `A f x ≤ A f x₀ + ε`
      have hchain : ballAverage μ f r x ≤ ballAverage μ f r x₀ + ε := by
        calc ballAverage μ f r x
            ≤ ballAverage μ g r x
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) := hfgx
          _ ≤ (ballAverage μ g r x₀ + ε / 3)
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) := add_le_add_left hxm.2 _
          _ ≤ (ballAverage μ f r x₀
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) + ε / 3)
              + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                / μ (Metric.ball 0 r) := add_le_add_left (add_le_add_left hgf _) _
          _ = ballAverage μ f r x₀
              + (((∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                  / μ (Metric.ball 0 r) + ε / 3)
                + (∫⁻ y in Metric.closedBall x₀ (r + 1), ‖f y - g y‖ₑ ∂μ)
                  / μ (Metric.ball 0 r)) := hrearr _ _ _ _
          _ ≤ ballAverage μ f r x₀ + (ε / 3 + ε / 3 + ε / 3) :=
              add_le_add le_rfl (add_le_add (add_le_add hDc.le le_rfl) hDc.le)
          _ = ballAverage μ f r x₀ + ε := by rw [hsum]
      exact hchain

/-- [GLUE] Assembly: a supremum of continuous functions into `ℝ≥0∞`
whose superlevel sets are open is lower semicontinuous.
SKETCH (fill when Step 3 lands; a first attempt timed out in `whnf`
on the `hid` simp — revisit then): `lowerSemicontinuous_iff_isOpen_preimage`,
`{x | t < M f x} = ⋃ r, ⋃ _ : 0 < r, {x | t < A_r x}` via `lt_iSup_iff`
plus the empty-index case (`iSup_of_empty`), then `isOpen_iUnion` of
`isOpen_lt continuous_const (continuous_iff_continuousAt.mpr
fun x₀ => continuousAt_ballAverage μ hr x₀ hf)`. -/
theorem lowerSemicontinuous_maximalFunction (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → F}
    (hf : LocallyIntegrable f μ) :
    LowerSemicontinuous (maximalFunction μ f) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro t
  have hset : (maximalFunction μ f) ⁻¹' Set.Ioi t
      = ⋃ r : ℝ, ⋃ _ : 0 < r, (ballAverage μ f r) ⁻¹' Set.Ioi t := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_iUnion]
    constructor
    · intro h
      rw [maximalFunction_eq_iSup_ballAverage] at h
      obtain ⟨r, hr'⟩ := lt_iSup_iff.mp h
      obtain ⟨hr, hrt⟩ := lt_iSup_iff.mp hr'
      exact ⟨r, hr, hrt⟩
    · rintro ⟨r, hr, hrt⟩
      rw [maximalFunction_eq_iSup_ballAverage]
      exact lt_of_lt_of_le hrt
        ((le_iSup (fun _ : 0 < r => ballAverage μ f r x) hr).trans
          (le_iSup (fun r => ⨆ _ : 0 < r, ballAverage μ f r x) r))
  rw [hset]
  apply isOpen_iUnion
  intro r
  apply isOpen_iUnion
  intro hr
  exact isOpen_lt continuous_const (continuous_iff_continuousAt.mpr fun x₀ =>
    continuousAt_ballAverage μ hr x₀ hf)

/-- B2's deliverable: measurability of the maximal function. -/
theorem measurable_maximalFunction (μ : Measure E)
    [MeasureTheory.Measure.IsAddHaarMeasure μ] {f : E → F}
    (hf : LocallyIntegrable f μ) :
    Measurable (maximalFunction μ f) :=
  (lowerSemicontinuous_maximalFunction μ hf).measurable

end MeasureTheory
